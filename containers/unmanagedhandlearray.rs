use core::any::{TypeId, type_name};
use core::hash::{Hash, Hasher};
use core::marker::PhantomData;
use core::{fmt, mem, ops};

use alloc::Allocator;

use crate::array::PushError;
use crate::unmanagedexponentialarray::UnmanagedExponentialArray;

const DANGLING_GENERATION: u32 = 0;
const FIRST_GENERATION: u32 = 1;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ErasedHandle {
    pub index: u32,
    pub generation: u32,
}

impl Default for ErasedHandle {
    #[inline]
    fn default() -> Self {
        Self::DANGLING
    }
}

unsafe impl Send for ErasedHandle {}
unsafe impl Sync for ErasedHandle {}

impl ErasedHandle {
    /// Useful for two-phase initialization.
    ///
    /// In two-phase initialization, a dangling handle is created first, and later replaced
    /// with a valid handle after the associated entry has been initialized.
    ///
    /// It is better to avoid using this value to represent the absence of a handle, prefer
    /// `Option<ErasedHandle>`.
    pub const DANGLING: Self = Self {
        index: 0,
        generation: DANGLING_GENERATION,
    };

    #[inline]
    pub fn is_dangling(&self) -> bool {
        self.eq(&Self::DANGLING)
    }

    #[inline]
    pub fn to_u64(&self) -> u64 {
        ((self.index as u64) << 32) | (self.generation as u64)
    }

    #[inline]
    pub fn from_u64(value: u64) -> Self {
        Self {
            index: (value >> 32) as u32,
            generation: value as u32,
        }
    }
}

// Yikes! `AnyHandle` is fat, there's `TypeId` within (which takes up 16 bytes alone).
//
// `AnyHandle` stores `TypeId` which implements `Hash`, `PartialOrd`, and `Ord`, it is worth noting
// that the hashes and ordering will vary between Rust releases. Beware of relying on them inside
// of your code!
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AnyHandle {
    pub index: u32,
    pub generation: u32,
    pub type_id: TypeId,
}

impl Default for AnyHandle {
    #[inline]
    fn default() -> Self {
        Self::DANGLING
    }
}

unsafe impl Send for AnyHandle {}
unsafe impl Sync for AnyHandle {}

impl AnyHandle {
    /// Useful for two-phase initialization.
    ///
    /// In two-phase initialization, a dangling handle is created first, and later replaced
    /// with a valid handle after the associated entry has been initialized.
    ///
    /// It is better to avoid using this value to represent the absence of a handle, prefer
    /// `Option<AnyHandle>`.
    pub const DANGLING: Self = Self {
        index: 0,
        generation: DANGLING_GENERATION,
        type_id: unsafe { mem::zeroed() },
    };

    #[inline]
    pub fn is_dangling(&self) -> bool {
        self.eq(&Self::DANGLING)
    }

    #[inline]
    pub fn to_erased(&self) -> ErasedHandle {
        ErasedHandle {
            index: self.index,
            generation: self.generation,
        }
    }
}

/// A non-owning, cheap-to-copy reference to an entry in a [`HandleArray`].
pub struct Handle<T> {
    pub index: u32,
    pub generation: u32,
    type_marker: PhantomData<T>,
}

// :BlindDerive
impl<T> fmt::Debug for Handle<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Handle")
            .field("index", &self.index)
            .field("generation", &self.generation)
            .field("type_marker", &type_name::<T>())
            .finish()
    }
}

// :BlindDerive
impl<T> Clone for Handle<T> {
    #[inline]
    fn clone(&self) -> Self {
        *self
    }
}

// :BlindDerive
impl<T> Copy for Handle<T> {}

// :BlindDerive
impl<T> PartialEq for Handle<T> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.index == other.index && self.generation == other.generation
    }
}

// :BlindDerive
impl<T> Eq for Handle<T> {}

// :BlindDerive
impl<T> PartialOrd for Handle<T> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

// :BlindDerive
impl<T> Ord for Handle<T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.index
            .cmp(&other.index)
            .then(self.generation.cmp(&other.generation))
    }
}

// :BlindDerive
impl<T> Hash for Handle<T> {
    // NOTE: this is very non collision free hash
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.index.hash(state);
        self.generation.hash(state);
    }
}

// :BlindDerive
impl<T> Default for Handle<T> {
    #[inline]
    fn default() -> Self {
        Self::DANGLING
    }
}

// NOTE: handles don't carry data. it is safet to send/share them between threads.
unsafe impl<T> Send for Handle<T> {}
unsafe impl<T> Sync for Handle<T> {}

impl<T> Handle<T> {
    /// Useful for two-phase initialization.
    ///
    /// In two-phase initialization, a dangling handle is created first, and later replaced
    /// with a valid handle after the associated entry has been initialized.
    ///
    /// It is better to avoid using this value to represent the absence of a handle, prefer
    /// `Option<Handle<T>>`.
    pub const DANGLING: Self = Self {
        index: 0,
        generation: DANGLING_GENERATION,
        type_marker: PhantomData,
    };

    #[inline]
    pub fn is_dangling(&self) -> bool {
        self.eq(&Self::DANGLING)
    }

    #[inline]
    fn new(index: u32, generation: u32) -> Self {
        Self {
            index,
            generation,
            type_marker: PhantomData,
        }
    }

    #[inline]
    pub fn to_erased(&self) -> ErasedHandle {
        ErasedHandle {
            index: self.index,
            generation: self.generation,
        }
    }

    /// SAFETY: it's on you to know where the erased handle came from.
    #[inline]
    pub fn from_erased(erased_handle: ErasedHandle) -> Self {
        Handle {
            index: erased_handle.index,
            generation: erased_handle.generation,
            type_marker: PhantomData,
        }
    }
}

impl<T: 'static> Handle<T> {
    #[inline]
    pub fn to_any(&self) -> AnyHandle {
        AnyHandle {
            index: self.index,
            generation: self.generation,
            type_id: TypeId::of::<T>(),
        }
    }

    /// If this function is called with AnyHandle that is dangling or that was created with type
    /// other then `T` - `None` will be returned.
    #[inline]
    pub fn try_from_any(any_handle: AnyHandle) -> Option<Self> {
        if any_handle.type_id == TypeId::of::<T>() {
            Some(Handle {
                index: any_handle.index,
                generation: any_handle.generation,
                type_marker: PhantomData,
            })
        } else {
            None
        }
    }
}

#[derive(Debug)]
enum EntryKind<T> {
    Occupied(T),
    Vacant { next_free: Option<u32> },
    Reserved,
}

#[derive(Debug)]
struct Entry<T> {
    kind: EntryKind<T>,
    generation: u32,
}

// MAYBE: rename Ticket to Token or something like that.
//
/// A reference to a reserved entry in a [`HandleArray`].
pub struct Ticket<T> {
    index: u32,
    type_marker: PhantomData<T>,
}

impl<T> Drop for Ticket<T> {
    fn drop(&mut self) {
        panic!("entry must be returned to array it was taken from!");
    }
}

impl<T> Ticket<T> {
    #[inline]
    fn new(index: u32) -> Self {
        Self {
            index,
            type_marker: PhantomData,
        }
    }
}

// NOTE: i always stuble upon shit https://github.com/rust-lang/rust/issues/50676
type Entries<T> = UnmanagedExponentialArray!(Entry<T>, 4);

/// An encapsulated exponential array that allows to refer to items by [`Handle`].
/// Items are never moved once allocated.
///
/// ## reading:
///
/// - <https://floooh.github.io/2018/06/17/handles-vs-pointers.html>
/// - <https://verdagon.dev/blog/generational-references>
///
/// ## alternatives:
///
/// - <https://github.com/orlp/slotmap>
/// - <https://github.com/LPGhatguy/thunderdome>
/// - <https://github.com/fitzgen/generational-arena>
/// - <https://docs.rs/fyrox/latest/fyrox/core/pool/struct.Pool.html>
#[derive(Debug)]
pub struct UnmanagedHandleArray<T> {
    entries: Entries<T>,
    // MAYBE: it might be cheaper to store a free list.
    free_head: Option<u32>,
}

// :BlindDerive
impl<T> Default for UnmanagedHandleArray<T> {
    fn default() -> Self {
        Self {
            entries: Entries::default(),
            free_head: None,
        }
    }
}

impl<T> UnmanagedHandleArray<T> {
    #[inline]
    pub fn len(&self) -> u32 {
        u32::try_from(self.entries.len()).unwrap_or_else(|_| panic!("entries.len() overflored u32"))
    }

    // ----

    #[inline]
    fn get_entry_by_handle(&self, handle: Handle<T>) -> Option<&Entry<T>> {
        let entry = self.entries.get(handle.index as usize)?;
        if entry.generation != handle.generation {
            return None;
        }
        Some(entry)
    }

    #[inline]
    fn get_entry_by_handle_mut(&mut self, handle: Handle<T>) -> Option<&mut Entry<T>> {
        let entry = self.entries.get_mut(handle.index as usize)?;
        if entry.generation != handle.generation {
            return None;
        }
        Some(entry)
    }

    // ----

    pub fn get(&self, handle: Handle<T>) -> Option<&T> {
        match self.get_entry_by_handle(handle) {
            Some(Entry {
                kind: EntryKind::Occupied(value),
                ..
            }) => Some(value),
            _ => None,
        }
    }

    pub fn get_mut(&mut self, handle: Handle<T>) -> Option<&mut T> {
        match self.get_entry_by_handle_mut(handle) {
            Some(Entry {
                kind: EntryKind::Occupied(value),
                ..
            }) => Some(value),
            _ => None,
        }
    }

    // ----

    /// Construct a value with the handle it would be given. The handle is _not_ valid until
    /// function has finished executing.
    pub fn try_push_with(
        &mut self,
        alloc: impl Allocator,
        f: impl FnOnce(Handle<T>) -> T,
    ) -> Result<Handle<T>, PushError<T>> {
        // NOTE: loop to find a valid (not overflowed) free index
        while let Some(index) = self.free_head.take() {
            let entry = &mut self.entries[index as usize];

            let EntryKind::Vacant { next_free } = entry.kind else {
                panic!("attempt to push into non-vacant entry at index {index}");
            };
            self.free_head = next_free;

            // QUOTE: Once the generation counter would 'overflow', disable that array slot, so
            // that no new handles are returned for this slot.
            // https://floooh.github.io/2018/06/17/handles-vs-pointers.html
            let Some(generation) = entry.generation.checked_add(1) else {
                continue;
            };
            let handle = Handle::new(index, generation);

            entry.generation = generation;
            entry.kind = EntryKind::Occupied(f(handle));

            return Ok(handle);
        }

        let handle = Handle::new(self.entries.len() as u32, FIRST_GENERATION);
        match self.entries.try_push(
            alloc,
            Entry {
                kind: EntryKind::Occupied(f(handle)),
                generation: handle.generation,
            },
        ) {
            Ok(..) => Ok(handle),
            Err(PushError {
                kind,
                value:
                    Entry {
                        kind: EntryKind::Occupied(value),
                        ..
                    },
            }) => Err(PushError { kind, value }),
            _ => unreachable!(),
        }
    }

    #[inline]
    pub fn try_push(&mut self, alloc: impl Allocator, value: T) -> Result<Handle<T>, PushError<T>> {
        self.try_push_with(alloc, |_| value)
    }

    pub fn remove(&mut self, handle: Handle<T>) -> Option<T> {
        let next_free = self.free_head;
        let Some(entry) = self.get_entry_by_handle_mut(handle) else {
            return None;
        };
        let EntryKind::Occupied(value) =
            mem::replace(&mut entry.kind, EntryKind::Vacant { next_free })
        else {
            panic!("attempt to remove value of non occupied entry at handle {handle:?}")
        };
        self.free_head = Some(handle.index);
        Some(value)
    }

    /// Tries to take ownership of the value at the given handle.
    ///
    /// Returns a [`Ticket`] representing a temporary reservation of an entry, along with the owned
    /// value, or `None` if the given handle is invalid or entry is not occupied.
    ///
    /// All existing handles pointing to the entry will be invalid until the value is returned
    /// using the [`put_back`] method.
    ///
    /// If you lose the [`Ticket`], the entry will remain unusable forever.
    ///
    /// [`put_back`]: Self::put_back
    pub fn try_take(&mut self, handle: Handle<T>) -> Option<(Ticket<T>, T)> {
        let entry = self.get_entry_by_handle_mut(handle)?;
        let EntryKind::Occupied(value) = mem::replace(&mut entry.kind, EntryKind::Reserved) else {
            return None;
        };
        Some((Ticket::new(handle.index), value))
    }

    /// Puts back the value into the entry associated with the given [`Ticket`] that was previously
    /// obtained with [`try_take`] or [`take`]. See [`try_take`] for more info.
    ///
    /// [`try_take`]: Self::try_take
    /// [`take`]: Self::take
    pub fn put_back(&mut self, ticket: Ticket<T>, value: T) {
        let entry = &mut self.entries[ticket.index as usize];
        entry.kind = EntryKind::Occupied(value);
        // NOTE: forget is called to not invoke manually implemented pinvalidanicking drop.
        mem::forget(ticket);
    }

    pub fn iter(&self) -> impl Iterator<Item = (Handle<T>, &T)> {
        self.entries
            .iter()
            .enumerate()
            .filter_map(|(index, entry)| match entry.kind {
                EntryKind::Occupied(ref value) => {
                    Some((Handle::new(index as u32, entry.generation), value))
                }
                _ => None,
            })
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = (Handle<T>, &mut T)> {
        self.entries
            .iter_mut()
            .enumerate()
            .filter_map(|(index, entry)| match entry.kind {
                EntryKind::Occupied(ref mut value) => {
                    Some((Handle::new(index as u32, entry.generation), value))
                }
                _ => None,
            })
    }

    /// Returns a potentially dangling `Handle` for the entry at the given index.
    pub fn handle_from_index(&self, index: u32) -> Handle<T> {
        if let Some(entry) = self.entries.get(index as usize) {
            return Handle::new(index, entry.generation);
        }
        Handle::DANGLING
    }
}

// NOTE: i wish there were a some kind of don't care mut/non-mut thingy.
macro_rules! occupied_or_panic {
    ($value:expr, $handle:expr) => {{
        let handle = $handle;
        match $value {
            Some(Entry { kind, .. }) => match kind {
                EntryKind::Occupied(value) => value,
                EntryKind::Vacant { .. } => panic!("dangling handle: {handle:?}"),
                EntryKind::Reserved => panic!("reserved handle: {handle:?}"),
            },
            None => panic!("dangling handle: {handle:?}"),
        }
    }};
}

impl<T> ops::Index<Handle<T>> for UnmanagedHandleArray<T> {
    type Output = T;

    #[inline]
    fn index(&self, handle: Handle<T>) -> &Self::Output {
        occupied_or_panic!(self.get_entry_by_handle(handle), handle)
    }
}

impl<T> ops::IndexMut<Handle<T>> for UnmanagedHandleArray<T> {
    #[inline]
    fn index_mut(&mut self, handle: Handle<T>) -> &mut Self::Output {
        occupied_or_panic!(self.get_entry_by_handle_mut(handle), handle)
    }
}

#[cfg(not(no_global_oom_handling))]
mod oom {
    use alloc::eek;

    use crate::array::PushErrorKind;

    use super::*;

    impl<T> UnmanagedHandleArray<T> {
        #[track_caller]
        pub fn push_with(
            &mut self,
            alloc: impl Allocator,
            f: impl FnOnce(Handle<T>) -> T,
        ) -> Handle<T> {
            match self.try_push_with(alloc, f) {
                Ok(handle) => handle,
                Err(PushError {
                    kind: PushErrorKind::OutOfMemory(alloc_error),
                    ..
                }) => eek(alloc_error),
            }
        }

        #[inline]
        pub fn push(&mut self, alloc: impl Allocator, value: T) -> Handle<T> {
            self.push_with(alloc, |_| value)
        }
    }
}

#[cfg(test)]
mod tests {
    use core::any::type_name_of_val;

    use alloc::Global;

    use super::*;

    #[test]
    fn test_push_and_remove() {
        let mut this = UnmanagedHandleArray::default();
        let handle = this.push(Global, "hello");

        assert_eq!(this.entries.len(), 1);
        assert_eq!(this.free_head, None);

        let res = this.remove(handle);

        assert_eq!(res, Some("hello"));
        assert_eq!(this.entries.len(), 1);
        assert_eq!(this.free_head, Some(0));
    }

    #[test]
    fn test_remove_at_dangling_handle() {
        let mut this = UnmanagedHandleArray::<()>::default();
        let handle = Handle::DANGLING;
        assert_eq!(this.remove(handle), None)
    }

    #[test]
    fn test_take_and_put_back() {
        let mut this = UnmanagedHandleArray::default();
        let handle = this.push(Global, 42u8);

        let (ticket, value) = this.try_take(handle).unwrap();
        assert_eq!(type_name_of_val(&value), "u8");

        this.put_back(ticket, value);
    }

    #[test]
    #[should_panic]
    fn test_drop_ticket_without_put_back() {
        let mut this = UnmanagedHandleArray::default();
        let handle = this.push(Global, "hello");
        _ = this.try_take(handle);
    }

    #[test]
    fn test_erased_handle_roundtrip() {
        let handle = Handle::<()>::new(42, FIRST_GENERATION);
        let erased_handle = handle.to_erased();
        let reconstructed = Handle::<()>::from_erased(erased_handle);
        assert_eq!(reconstructed, handle);
    }

    #[test]
    fn test_any_handle_roundtrip() {
        let handle = Handle::<()>::new(42, FIRST_GENERATION);
        let any_handle = handle.to_any();
        let reconstructed = Handle::<()>::try_from_any(any_handle).unwrap();
        assert_eq!(reconstructed, handle);
    }

    #[test]
    fn test_u64_handle_roundtrip() {
        let handle = Handle::<()>::new(42, FIRST_GENERATION);
        let u64_handle = handle.to_erased().to_u64();
        let reconstructed = Handle::<()>::from_erased(ErasedHandle::from_u64(u64_handle));
        assert_eq!(reconstructed, handle);
    }

    #[test]
    fn test_free_chain() {
        let mut this = UnmanagedHandleArray::default();
        let h1 = this.push(Global, 10);
        let h2 = this.push(Global, 20);
        let h3 = this.push(Global, 30);

        // remove in order: builds chain 2 -> 1 -> 0
        this.remove(h1);
        this.remove(h2);
        this.remove(h3);

        let first_round_cap = this.entries.cap();

        // reuse should follow lifo: 2, 1, 0
        let r1 = this.push(Global, 100);
        assert_eq!(r1.index, 2);
        assert_ne!(r1.generation, h3.generation); // generation bumped

        let r2 = this.push(Global, 200);
        assert_eq!(r2.index, 1);

        let r3 = this.push(Global, 300);
        assert_eq!(r3.index, 0);

        // old handles invalid, new ones valid
        assert_eq!(this.get(h1), None);
        assert_eq!(this.get(h2), None);
        assert_eq!(this.get(h3), None);
        assert_eq!(this.get(r1), Some(&100));
        assert_eq!(this.get(r2), Some(&200));
        assert_eq!(this.get(r3), Some(&300));

        let second_round_cap = this.entries.cap();
        // backing array must not have grown
        assert_eq!(first_round_cap, second_round_cap);
    }
}
