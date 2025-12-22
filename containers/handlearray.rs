use std::any::TypeId;
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;
use std::mem;
use std::num::NonZeroU32;

use alloc::{AllocError, Allocator};

use crate::array::{Array, GrowableArray, PushError};

/// The idea to use `NonZeroU32` is borrowed from [thunderdome][1].
///
/// [1]: https://github.com/LPGhatguy/thunderdome/blob/9e0a6dc3d2e6d402a2f985e47a876156d42c198b/src/generation.rs
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
struct Generation(NonZeroU32);

impl Generation {
    /// Useful for two-phase initialization.
    const DANGLING: Self = Self(unsafe { NonZeroU32::new_unchecked(u32::MAX) });

    #[inline]
    #[expect(dead_code)]
    fn is_dangling(&self) -> bool {
        self.eq(&Self::DANGLING)
    }

    #[inline]
    fn new() -> Self {
        Self(unsafe { NonZeroU32::new_unchecked(1) })
    }

    #[inline]
    fn try_bump(self) -> Option<Self> {
        self.0.checked_add(1).map(Self)
    }
}

/// Type-erased handle.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ErasedHandle {
    index: u32,
    generation: Generation,
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
        generation: Generation::DANGLING,
    };

    #[inline]
    pub fn is_dangling(&self) -> bool {
        self.eq(&Self::DANGLING)
    }
}

// Yikes! `AnyHandle` is fat, there's `TypeId` within (which takes up 16 bytes alone).
//
// `AnyHandle` stores `TypeId` which implements `Hash`, `PartialOrd`, and `Ord`, it is worth noting
// that the hashes and ordering will vary between Rust releases. Beware of relying on them inside
// of your code!
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AnyHandle {
    index: u32,
    generation: Generation,
    type_id: TypeId,
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
        generation: Generation::DANGLING,
        type_id: unsafe { mem::zeroed() },
    };

    #[inline]
    pub fn is_dangling(&self) -> bool {
        self.eq(&Self::DANGLING)
    }

    #[inline]
    pub fn type_id(&self) -> TypeId {
        self.type_id
    }

    #[inline]
    pub fn as_erased(&self) -> ErasedHandle {
        ErasedHandle {
            index: self.index,
            generation: self.generation,
        }
    }
}

/// A non-owning, cheap-to-copy reference to an entry in a [`HandleArray`].
pub struct Handle<T> {
    index: u32,
    generation: Generation,
    type_marker: PhantomData<T>,
}

// @BlindDerive
impl<T> std::fmt::Debug for Handle<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Handle")
            .field("index", &self.index)
            .field("generation", &self.generation)
            .field("type_marker", &std::any::type_name::<T>())
            .finish()
    }
}

// @BlindDerive
impl<T> Clone for Handle<T> {
    #[inline]
    fn clone(&self) -> Self {
        *self
    }
}

// @BlindDerive
impl<T> Copy for Handle<T> {}

// @BlindDerive
impl<T> PartialEq for Handle<T> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.index == other.index && self.generation == other.generation
    }
}

// @BlindDerive
impl<T> Eq for Handle<T> {}

// @BlindDerive
impl<T> Hash for Handle<T> {
    // NOTE: this is very non collision free hash
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.index.hash(state);
        self.generation.hash(state);
    }
}

// @BlindDerive
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
        generation: Generation::DANGLING,
        type_marker: PhantomData,
    };

    #[inline]
    pub fn is_dangling(&self) -> bool {
        self.eq(&Self::DANGLING)
    }

    #[inline]
    fn new(index: u32, generation: Generation) -> Self {
        Self {
            index,
            generation,
            type_marker: PhantomData,
        }
    }

    #[inline]
    pub fn as_erased(&self) -> ErasedHandle {
        ErasedHandle {
            index: self.index,
            generation: self.generation,
        }
    }

    /// Make sure you know what you are doing with this, there are no checks that will tell you
    /// otherwise.
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
    pub fn as_any(&self) -> AnyHandle {
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
    generation: Generation,
}

// TODO: rename Ticket to Token or something like that.
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

// NOTE: handle array by its nature is unordered. it's an obvious aspect of it.
//   where's sortedarray has the word "sorted" in its name i don't believe name of this thing must
//   include word unordered.

/// An encapsulated dynamic array that allows to refer to entries by [`Handle`].
///
/// Methods with the `try_` prefix return `Option`, allowing for graceful error handling. These
/// methods are suitable when failures are expected and should be handled without crashing the
/// program.
///
/// Methods without the `try_` prefix can panic. They assume valid input and are intended for cases
/// where failure is considered a logic error or a violation of preconditions, which should never
/// occur under normal circumstances.
///
/// This is an attempt to align with Rust's philosophy of making failure explicit and providing a
/// way to handle errors in a controlled manner, while also allowing for performance optimizations
/// and simpler code paths when failures are truly unexpected.
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
#[derive(Debug, Default)]
pub struct HandleArray<T, A: Allocator> {
    // NOTE: i don't see any reason for making it possible to use other flavors of Array here.
    entries: GrowableArray<Entry<T>, A>,
    free_head: Option<u32>,
}

impl<T, A: Allocator> HandleArray<T, A> {
    #[inline]
    pub fn new_in(alloc: A) -> Self {
        Self {
            entries: Array::new_growable_in(alloc),
            free_head: None,
        }
    }

    #[inline]
    pub fn try_with_cap(self, cap: usize) -> Result<Self, AllocError> {
        Ok(Self {
            entries: self.entries.try_with_cap(cap)?,
            ..self
        })
    }

    #[inline]
    pub fn len(&self) -> u32 {
        u32::try_from(self.entries.len()).unwrap_or_else(|_| panic!("entries.len() overflored u32"))
    }

    // ----

    #[inline]
    fn try_get_entry_by_handle(&self, handle: Handle<T>) -> Option<&Entry<T>> {
        let Some(entry) = self.entries.get(handle.index as usize) else {
            return None;
        };
        if entry.generation != handle.generation {
            return None;
        }
        Some(entry)
    }

    #[allow(dead_code, reason = "i want to keep this for symmetry")]
    #[inline]
    fn get_entry_by_handle(&self, handle: Handle<T>) -> &Entry<T> {
        let entry = &self.entries[handle.index as usize];
        if entry.generation != handle.generation {
            panic!("danglign handle: {handle:?}");
        }
        entry
    }

    #[inline]
    fn try_get_entry_by_handle_mut(&mut self, handle: Handle<T>) -> Option<&mut Entry<T>> {
        let Some(entry) = self.entries.get_mut(handle.index as usize) else {
            return None;
        };
        if entry.generation != handle.generation {
            return None;
        }
        Some(entry)
    }

    #[inline]
    fn get_entry_by_handle_mut(&mut self, handle: Handle<T>) -> &mut Entry<T> {
        let entry = &mut self.entries[handle.index as usize];
        if entry.generation != handle.generation {
            panic!("danglign handle: {handle:?}");
        }
        entry
    }

    // ----

    pub fn try_get(&self, handle: Handle<T>) -> Option<&T> {
        match self.try_get_entry_by_handle(handle) {
            Some(Entry {
                kind: EntryKind::Occupied(value),
                ..
            }) => Some(value),
            _ => None,
        }
    }

    pub fn get(&self, handle: Handle<T>) -> &T {
        match self.get_entry_by_handle(handle).kind {
            EntryKind::Occupied(ref value) => value,
            EntryKind::Vacant { .. } => panic!("dangling handle: {handle:?}"),
            EntryKind::Reserved => panic!("reserved handle: {handle:?}"),
        }
    }

    pub fn try_get_mut(&mut self, handle: Handle<T>) -> Option<&mut T> {
        match self.try_get_entry_by_handle_mut(handle) {
            Some(Entry {
                kind: EntryKind::Occupied(value),
                ..
            }) => Some(value),
            _ => None,
        }
    }

    pub fn get_mut(&mut self, handle: Handle<T>) -> &mut T {
        match self.get_entry_by_handle_mut(handle).kind {
            EntryKind::Occupied(ref mut value) => value,
            EntryKind::Vacant { .. } => panic!("dangling handle: {handle:?}"),
            EntryKind::Reserved => panic!("reserved handle: {handle:?}"),
        }
    }

    // ----

    /// Construct a value with the handle it would be given. The handle is _not_ valid until
    /// function has finished executing.
    pub fn try_push_with(
        &mut self,
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
            let Some(generation) = entry.generation.try_bump() else {
                continue;
            };
            let handle = Handle::new(index, generation);

            entry.generation = generation;
            entry.kind = EntryKind::Occupied(f(handle));

            return Ok(handle);
        }

        let handle = Handle::new(self.entries.len() as u32, Generation::new());
        match self.entries.try_push(Entry {
            kind: EntryKind::Occupied(f(handle)),
            generation: handle.generation,
        }) {
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
    pub fn try_push(&mut self, value: T) -> Result<Handle<T>, PushError<T>> {
        self.try_push_with(|_| value)
    }

    // TODO: non-panicking try_remove

    pub fn remove(&mut self, handle: Handle<T>) -> T {
        let next_free = self.free_head;
        let entry = self.get_entry_by_handle_mut(handle);
        let EntryKind::Occupied(value) =
            mem::replace(&mut entry.kind, EntryKind::Vacant { next_free })
        else {
            panic!("attempt to remove value of non occupied entry at handle {handle:?}")
        };
        self.free_head = Some(handle.index);
        value
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
        let entry = self.try_get_entry_by_handle_mut(handle)?;
        let EntryKind::Occupied(value) = mem::replace(&mut entry.kind, EntryKind::Reserved) else {
            return None;
        };
        Some((Ticket::new(handle.index), value))
    }

    /// Same as [`try_take`], but panics if handle is invalid.
    ///
    /// [`try_take`]: Self::try_take
    #[inline]
    pub fn take(&mut self, handle: Handle<T>) -> (Ticket<T>, T) {
        // TODO: consider being more granular with panic messages.
        self.try_take(handle)
            .unwrap_or_else(|| panic!("could not take value at handle {:?}", handle))
    }

    /// Puts back the value into the entry associated with the given [`Ticket`] that was previously
    /// obtained with [`try_take`] or [`take`]. See [`try_take`] for more info.
    ///
    /// [`try_take`]: Self::try_take
    /// [`take`]: Self::take
    pub fn put_back(&mut self, ticket: Ticket<T>, value: T) {
        let entry = &mut self.entries[ticket.index as usize];
        entry.kind = EntryKind::Occupied(value);
        // NOTE: forget is called to not invoke manually implemented panicking drop.
        std::mem::forget(ticket);
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

    pub fn iter_values(&self) -> impl Iterator<Item = &T> {
        self.entries.iter().filter_map(|entry| match entry.kind {
            EntryKind::Occupied(ref value) => Some(value),
            _ => None,
        })
    }

    pub fn iter_values_mut(&mut self) -> impl Iterator<Item = &mut T> {
        self.entries
            .iter_mut()
            .filter_map(|entry| match entry.kind {
                EntryKind::Occupied(ref mut value) => Some(value),
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

#[cfg(not(no_global_oom_handling))]
mod oom {
    use crate::{array::PushErrorKind, eek, this_is_fine};

    use super::*;

    impl<T, A: Allocator> HandleArray<T, A> {
        #[inline]
        pub fn with_cap(self, cap: usize) -> Self {
            this_is_fine(self.try_with_cap(cap))
        }

        // ----

        pub fn push_with(&mut self, f: impl FnOnce(Handle<T>) -> T) -> Handle<T> {
            match self.try_push_with(f) {
                Ok(handle) => handle,
                Err(PushError {
                    kind: PushErrorKind::OutOfMemory(alloc_error),
                    ..
                }) => eek(alloc_error),
            }
        }

        #[inline]
        pub fn push(&mut self, value: T) -> Handle<T> {
            self.push_with(|_| value)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_push_and_remove() {
        let mut this = HandleArray::<_, alloc::Global>::default();
        let handle = this.push("hello");

        assert_eq!(this.entries.len(), 1);
        assert_eq!(this.free_head, None);

        let res = this.remove(handle);

        assert_eq!(res, "hello");
        assert_eq!(this.entries.len(), 1);
        assert_eq!(this.free_head, Some(0));
    }

    #[test]
    #[should_panic]
    fn test_remove_at_invalid_handle() {
        let mut this = HandleArray::<(), alloc::Global>::default();
        let handle = Handle::DANGLING;
        this.remove(handle);
    }

    #[test]
    fn test_take_and_put_back() {
        let mut this = HandleArray::<_, alloc::Global>::default();
        let handle = this.push(42u8);

        let (ticket, value) = this.take(handle);
        assert_eq!(std::any::type_name_of_val(&value), "u8");

        this.put_back(ticket, value);
    }

    #[test]
    #[should_panic]
    fn test_drop_ticket_without_put_back() {
        let mut this = HandleArray::<_, alloc::Global>::default();
        let handle = this.push("hello");
        this.take(handle);
    }

    #[test]
    fn test_erased_handle_roundtrip() {
        let handle = Handle::<()>::new(42, Generation::new());
        let erased_handle = handle.as_erased();
        let reconstructed = Handle::<()>::from_erased(erased_handle);
        assert_eq!(reconstructed, handle);
    }

    #[test]
    fn test_any_handle_roundtrip() {
        let handle = Handle::<()>::new(42, Generation::new());
        let any_handle = handle.as_any();
        let reconstructed = Handle::<()>::try_from_any(any_handle).unwrap();
        assert_eq!(reconstructed, handle);
    }

    #[test]
    fn test_free_chain() {
        let mut this = HandleArray::<i32, alloc::Global>::default();
        let h1 = this.push(10);
        let h2 = this.push(20);
        let h3 = this.push(30);

        // remove in order: builds chain 2 -> 1 -> 0
        this.remove(h1);
        this.remove(h2);
        this.remove(h3);

        let first_round_cap = this.entries.cap();

        // reuse should follow lifo: 2, 1, 0
        let r1 = this.push(100);
        assert_eq!(r1.index, 2);
        assert_ne!(r1.generation, h3.generation); // generation bumped

        let r2 = this.push(200);
        assert_eq!(r2.index, 1);

        let r3 = this.push(300);
        assert_eq!(r3.index, 0);

        // old handles invalid, new ones valid
        assert_eq!(this.try_get(h1), None);
        assert_eq!(this.try_get(h2), None);
        assert_eq!(this.try_get(h3), None);
        assert_eq!(this.try_get(r1), Some(&100));
        assert_eq!(this.try_get(r2), Some(&200));
        assert_eq!(this.try_get(r3), Some(&300));

        let second_round_cap = this.entries.cap();
        // backing array must not have grown
        assert_eq!(first_round_cap, second_round_cap);
    }
}
