use std::cell::UnsafeCell;
use std::mem::{self, MaybeUninit};
use std::sync::Arc;
use std::sync::atomic::{AtomicU8, Ordering as AtomicOrdering};
use std::{error, fmt, ptr};

// NOTE: this is based on
// https://github.com/rust-lang/futures-rs/blob/de9274e655b2fff8c9630a259a473b71a6b79dda/futures-channel/src/oneshot.rs
// with some ideas stolen from
// https://github.com/faern/oneshot/blob/25274e995ee0a702b3e9e1ac81e577f8c3ce0892/src/lib.rs
// but without async stuff.

// NOTE: enum is way too inconvenient to use with atomics.
const STATE_EMPTY: u8 = 1;
const STATE_SENT: u8 = 2;
const STATE_DISCONNECTED: u8 = 3;

#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TryRecvError {
    Empty,
    Disconnected,
}

impl error::Error for TryRecvError {}

impl fmt::Display for TryRecvError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Empty => f.write_str("the channel is empty"),
            Self::Disconnected => f.write_str("the channel is disconnected"),
        }
    }
}

#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SendError {
    Disconnected,
}

impl error::Error for SendError {}

impl fmt::Display for SendError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Disconnected => f.write_str("the channel is disconnected"),
        }
    }
}

struct Channel<T> {
    // NOTE: unsafe cell enables interior mutability; atomic state ensures "safety".
    value: UnsafeCell<MaybeUninit<T>>,
    state: AtomicU8,
}

impl<T> Default for Channel<T> {
    fn default() -> Self {
        Self {
            value: UnsafeCell::new(MaybeUninit::uninit()),
            state: AtomicU8::new(STATE_EMPTY),
        }
    }
}

impl<T> Channel<T> {}

pub struct Sender<T> {
    channel: Arc<Channel<T>>,
}

unsafe impl<T: Send> Send for Sender<T> {}
unsafe impl<T: Sync> Sync for Sender<T> {}

impl<T> Drop for Sender<T> {
    fn drop(&mut self) {
        match self.channel.state.load(AtomicOrdering::Relaxed) {
            STATE_EMPTY => {
                // NOTE: (atomic ordering) matches the one used in `send` method. the receiver
                // needs to see this disconnection / syncs with receiver's Acquire.
                self.channel
                    .state
                    .store(STATE_DISCONNECTED, AtomicOrdering::Release);
            }
            STATE_DISCONNECTED => {}
            _ => unreachable!(),
        }
    }
}

impl<T> Sender<T> {
    pub fn send(self, payload: T) -> Result<(), SendError> {
        // TODO: consider elaborating more on this?
        // SAFETY: the receiver only ever accesses this memory if we are in the State::Sent.
        unsafe { &mut *self.channel.value.get() }.write(payload);

        // NOTE: (atomic ordering) Release ensures the write happens-before any receiver that sees
        // Sent state via Acquire loads.
        let state = self.channel.state.swap(STATE_SENT, AtomicOrdering::Release);

        // NOTE: don't run Drop impl.
        mem::forget(self);

        match state {
            STATE_EMPTY => Ok(()),
            STATE_DISCONNECTED => Err(SendError::Disconnected),
            _ => unreachable!(),
        }
    }
}

pub struct Receiver<T> {
    channel: Arc<Channel<T>>,
}

unsafe impl<T: Send> Send for Receiver<T> {}
unsafe impl<T: Send> Sync for Receiver<T> {}

impl<T> Drop for Receiver<T> {
    fn drop(&mut self) {
        // NOTE: (atomic ordering) syncs with sender's Release.
        match self
            .channel
            .state
            .swap(STATE_DISCONNECTED, AtomicOrdering::Acquire)
        {
            STATE_EMPTY => {}
            STATE_SENT => unsafe {
                // TODO: is it ok to do a replace here?
                ptr::replace(self.channel.value.get(), MaybeUninit::uninit()).assume_init_drop();
            },
            STATE_DISCONNECTED => {}
            _ => unreachable!(),
        }
    }
}

impl<T> Receiver<T> {
    pub fn try_recv(&self) -> Result<T, TryRecvError> {
        // NOTE: (atomic ordering) syncs with sender's Release.
        match self.channel.state.load(AtomicOrdering::Acquire) {
            STATE_EMPTY => Err(TryRecvError::Empty),
            STATE_SENT => {
                // NOTE: (atomic ordering) at this point the sender is consumed, thus nobody else
                // will read the state.
                self.channel
                    .state
                    .store(STATE_DISCONNECTED, AtomicOrdering::Relaxed);
                Ok(unsafe {
                    // TODO: is it ok to do a replace here?
                    ptr::replace(self.channel.value.get(), MaybeUninit::uninit()).assume_init()
                })
            }
            STATE_DISCONNECTED => Err(TryRecvError::Disconnected),
            _ => unreachable!(),
        }
    }
}

pub fn channel<T>() -> (Sender<T>, Receiver<T>) {
    let channel = Arc::new(Channel::<T>::default());
    let sender = Sender {
        channel: Arc::clone(&channel),
    };
    let receiver = Receiver { channel };
    (sender, receiver)
}

#[cfg(test)]
mod tests {
    use std::thread;

    use super::*;

    #[test]
    fn send_try_recv() {
        let (send, recv) = channel::<i32>();
        send.send(42).unwrap();
        assert_eq!(recv.try_recv(), Ok(42));
    }

    #[test]
    fn try_recv_empty() {
        let (_send, recv) = channel::<i32>();
        assert_eq!(recv.try_recv(), Err(TryRecvError::Empty));
    }

    #[test]
    fn try_recv_after_sender_dropped() {
        let (send, recv) = channel::<i32>();
        drop(send);
        assert_eq!(recv.try_recv(), Err(TryRecvError::Disconnected));
    }

    #[test]
    fn send_after_receiver_dropped() {
        let (send, recv) = channel::<i32>();
        drop(recv);
        assert_eq!(send.send(42), Err(SendError::Disconnected));
    }

    #[test]
    fn multiple_receive_attempts() {
        let (send, recv) = channel();
        send.send(42).unwrap();
        assert_eq!(recv.try_recv(), Ok(42));
        assert_eq!(recv.try_recv(), Err(TryRecvError::Disconnected));
        assert_eq!(recv.try_recv(), Err(TryRecvError::Disconnected));
    }

    #[test]
    fn drop_value_when_receiver_dropped() {
        struct Droppable {
            drop_count: Arc<AtomicU8>,
        }

        impl Drop for Droppable {
            fn drop(&mut self) {
                self.drop_count.fetch_add(1, AtomicOrdering::SeqCst);
            }
        }

        let drop_count = Arc::new(AtomicU8::new(0));
        let droppable = Droppable {
            drop_count: Arc::clone(&drop_count),
        };

        let (send, recv) = channel();
        assert_eq!(send.send(droppable), Ok(()));
        drop(recv);
        assert_eq!(drop_count.load(AtomicOrdering::SeqCst), 1);
    }

    #[test]
    fn arc_clone_receiver() {
        let (send, recv) = channel();

        let recv1 = Arc::new(recv);
        let recv2 = Arc::clone(&recv1);

        send.send(42).unwrap();

        let handle1 = {
            let recv = Arc::clone(&recv1);
            thread::spawn(move || recv.try_recv())
        };

        let handle2 = {
            let recv = Arc::clone(&recv2);
            thread::spawn(move || recv.try_recv())
        };

        let result1 = handle1.join().unwrap();
        let result2 = handle2.join().unwrap();

        assert!(matches!(
            (result1, result2),
            (Ok(42), Err(TryRecvError::Disconnected)) | (Err(TryRecvError::Disconnected), Ok(42))
        ));
    }
}
