use core::marker::PhantomData;
use core::ops;
use core::ptr;
use core::slice;

use alloc::AllocError;

use crate::array::{PushError, PushErrorKind};
use crate::arraymemory::{ArrayMemory, GrowMode, GrowableArrayMemory};

fn wrap_add(i: usize, add: usize, cap: usize) -> usize {
    i.wrapping_add(add) % cap
}

fn wrap_sub(i: usize, sub: usize, cap: usize) -> usize {
    i.wrapping_add(cap).wrapping_sub(sub) % cap
}

fn slice_ranges(cap: usize, len: usize, front: usize) -> (ops::Range<usize>, ops::Range<usize>) {
    let back = wrap_add(front, len, cap);
    if back > front {
        (front..back, 0..0)
    } else {
        (front..cap, 0..back)
    }
}

#[derive(Debug)]
pub struct ArrayDeque<T, M: ArrayMemory<T>> {
    mem: M,
    len: usize,
    // NOTE: back = (front + len) % cap
    front: usize,
    _ty: PhantomData<T>,
}

impl<T, M: ArrayMemory<T>> ArrayDeque<T, M> {
    #[inline]
    const fn is_zst() -> bool {
        size_of::<T>() == 0
    }

    #[inline]
    pub fn new_in(mem: M) -> Self {
        Self {
            mem,
            len: 0,
            front: 0,
            _ty: PhantomData,
        }
    }

    /// will always return `usize::MAX` if `T` is zero-sized.
    #[inline]
    pub fn cap(&self) -> usize {
        if Self::is_zst() {
            usize::MAX
        } else {
            self.mem.ptr().len()
        }
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.len
    }

    fn try_reserve(&mut self, additional: usize, mode: GrowMode) -> Result<(), AllocError> {
        let maybe_new_cap = self.len.checked_add(additional).ok_or(AllocError)?;
        self.mem.grow(maybe_new_cap, mode, |old_ptr, new_ptr| {
            let old_cap = old_ptr.len();

            let old_ptr = old_ptr.cast::<T>().as_ptr();
            let new_ptr = new_ptr.cast::<T>().as_ptr();

            let (front, back) = slice_ranges(old_cap, self.len, self.front);
            unsafe {
                ptr::copy_nonoverlapping(old_ptr.add(front.start), new_ptr, front.len());
                ptr::copy_nonoverlapping(old_ptr, new_ptr.add(front.len()), back.len());
            }

            self.front = 0;
        })
    }

    pub fn try_reserve_exact(&mut self, additional: usize) -> Result<(), AllocError> {
        self.try_reserve(additional, GrowMode::Exact)
    }

    pub fn try_reserve_amortized(&mut self, additional: usize) -> Result<(), AllocError> {
        self.try_reserve(additional, GrowMode::Amortized)
    }

    fn ptr(&self) -> *mut T {
        self.mem.ptr().as_ptr().cast::<T>()
    }

    fn write(&mut self, i: usize, value: T) {
        unsafe { self.ptr().add(i).write(value) };
    }

    fn read(&self, i: usize) -> T {
        unsafe { self.ptr().add(i).read() }
    }

    pub fn try_push_back(&mut self, value: T) -> Result<(), PushError<T>> {
        if let Err(alloc_error) = self.try_reserve_amortized(1) {
            return Err(PushError {
                kind: PushErrorKind::OutOfMemory(alloc_error),
                value,
            });
        }

        let old_back = wrap_add(self.front, self.len, self.cap());
        self.len += 1;
        self.write(old_back, value);
        Ok(())
    }

    pub fn try_push_front(&mut self, value: T) -> Result<(), PushError<T>> {
        if let Err(alloc_error) = self.try_reserve_amortized(1) {
            return Err(PushError {
                kind: PushErrorKind::OutOfMemory(alloc_error),
                value,
            });
        }

        self.front = wrap_sub(self.front, 1, self.cap());
        self.len += 1;
        self.write(self.front, value);
        Ok(())
    }

    pub fn pop_back(&mut self) -> Option<T> {
        if self.len == 0 {
            return None;
        }

        self.len -= 1;
        let back = wrap_add(self.front, self.len, self.cap());
        Some(self.read(back))
    }

    pub fn pop_front(&mut self) -> Option<T> {
        if self.len == 0 {
            return None;
        }

        let old_front = self.front;
        self.front = wrap_add(old_front, 1, self.cap());
        self.len -= 1;
        Some(self.read(old_front))
    }

    pub fn get(&self, i: usize) -> Option<&T> {
        if i >= self.len {
            return None;
        }
        let i = wrap_add(self.front, i, self.cap());
        unsafe { Some(&*self.ptr().add(i)) }
    }

    pub fn get_mut(&mut self, i: usize) -> Option<&mut T> {
        if i >= self.len {
            return None;
        }
        let i = wrap_add(self.front, i, self.cap());
        unsafe { Some(&mut *self.ptr().add(i)) }
    }

    fn as_slices_mut(&mut self) -> (&mut [T], &mut [T]) {
        let (front, back) = slice_ranges(self.cap(), self.len, self.front);
        dbg!(&front, &back);
        unsafe {
            (
                slice::from_raw_parts_mut(self.ptr().add(front.start), front.len()),
                slice::from_raw_parts_mut(self.ptr().add(back.start), back.len()),
            )
        }
    }

    /// removes all items, has no effect on the allocated capacity.
    pub fn clear(&mut self) {
        todo!();
        // let (front, back) = self.as_slices_mut();
        // unsafe {
        //     (front as *mut [T]).drop_in_place();
        //     (back as *mut [T]).drop_in_place();
        // };
        // self.len = 0;
        // self.front = 0;
    }
}

impl<T, M: ArrayMemory<T>> ops::Index<usize> for ArrayDeque<T, M> {
    type Output = T;

    #[inline]
    fn index(&self, index: usize) -> &T {
        self.get(index).expect("oob")
    }
}

impl<T, M: ArrayMemory<T>> ops::IndexMut<usize> for ArrayDeque<T, M> {
    #[inline]
    fn index_mut(&mut self, index: usize) -> &mut T {
        self.get_mut(index).expect("oob")
    }
}

impl<T, M: ArrayMemory<T>> Drop for ArrayDeque<T, M> {
    fn drop(&mut self) {
        self.clear();
    }
}

#[cfg(not(no_global_oom_handling))]
mod oom {
    use crate::{eek, this_is_fine};

    use super::*;

    impl<T, M: ArrayMemory<T>> ArrayDeque<T, M> {
        pub fn push_back(&mut self, value: T) {
            match self.try_push_back(value) {
                Ok(..) => {}
                Err(PushError {
                    kind: PushErrorKind::OutOfMemory(alloc_error),
                    ..
                }) => eek(alloc_error),
            }
        }

        pub fn push_front(&mut self, value: T) {
            match self.try_push_front(value) {
                Ok(..) => {}
                Err(PushError {
                    kind: PushErrorKind::OutOfMemory(alloc_error),
                    ..
                }) => eek(alloc_error),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::testutil::struct_with_counted_drop;

    use super::*;

    #[test]
    fn test_simple() {
        let mut dq = ArrayDeque::<_, _>::new_in(GrowableArrayMemory::new_in(alloc::Global));
        assert_eq!(dq.len(), 0);
        dq.push_front(17);
        dq.push_front(42);
        dq.push_back(137);
        assert_eq!(dq.len(), 3);
        dq.push_back(137);
        assert_eq!(dq.len(), 4);
        // assert_eq!(*d.front().unwrap(), 42);
        // assert_eq!(*d.back().unwrap(), 137);
        let mut i = dq.pop_front();
        assert_eq!(i, Some(42));
        i = dq.pop_back();
        assert_eq!(i, Some(137));
        i = dq.pop_back();
        assert_eq!(i, Some(137));
        i = dq.pop_back();
        assert_eq!(i, Some(17));
        assert_eq!(dq.len(), 0);
        dq.push_back(3);
        assert_eq!(dq.len(), 1);
        dq.push_front(2);
        assert_eq!(dq.len(), 2);
        dq.push_back(4);
        assert_eq!(dq.len(), 3);
        dq.push_front(1);
        assert_eq!(dq.len(), 4);
        assert_eq!(dq[0], 1);
        assert_eq!(dq[1], 2);
        assert_eq!(dq[2], 3);
        assert_eq!(dq[3], 4);
    }

    #[test]
    fn test_grow() {
        const N: usize = 66;

        let mut dq = ArrayDeque::<_, _>::new_in(GrowableArrayMemory::new_in(alloc::Global));
        for i in 0..N {
            dq.push_front(i);
        }
        assert_eq!(dq.len(), N);
        for i in 0..N {
            assert_eq!(dq[i], N - 1 - i);
        }

        let mut dq = ArrayDeque::<_, _>::new_in(GrowableArrayMemory::new_in(alloc::Global));
        for i in 0..N {
            dq.push_back(i);
        }
        for i in 0..N {
            assert_eq!(dq[i], i);
        }
    }

    #[test]
    fn test_drop() {
        struct_with_counted_drop!(Elem, DROPS);

        let mut dq = ArrayDeque::<_, _>::new_in(GrowableArrayMemory::new_in(alloc::Global));
        dq.push_back(Elem);
        dq.push_front(Elem);
        dq.push_back(Elem);
        dq.push_front(Elem);
        drop(dq);

        assert_eq!(DROPS.get(), 4);
    }
}
