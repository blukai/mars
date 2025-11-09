// use core::{alloc::Layout, mem::MaybeUninit, ops, ptr::NonNull};
//
// use crate::{AllocError, Allocator};

// pub struct Box<T: ?Sized, A: Allocator> {
//     ptr: NonNull<T>,
//     alloc: A,
// }
//
// impl<T, A: Allocator> Box<T, A> {
//     #[inline]
//     const fn is_zst() -> bool {
//         size_of::<T>() == 0
//     }
//
//     #[inline]
//     pub unsafe fn from_raw_in(raw: *mut T, alloc: A) -> Self {
//         Box {
//             ptr: unsafe { NonNull::new_unchecked(raw) },
//             alloc,
//         }
//     }
//
//     pub fn try_new_uninit_in(alloc: A) -> Result<Box<MaybeUninit<T>, A>, AllocError> {
//         let ptr = if Self::is_zst() {
//             NonNull::dangling()
//         } else {
//             let layout = Layout::new::<MaybeUninit<T>>();
//             alloc.allocate(layout)?.cast()
//         };
//         unsafe { Ok(Box::from_raw_in(ptr.as_ptr(), alloc)) }
//     }
//
//     #[inline]
//     pub fn try_new_in(x: T, alloc: A) -> Result<Self, AllocError> {
//         let mut this = Self::try_new_uninit_in(alloc)?;
//         this.write(x);
//         unsafe { Ok(this.assume_init()) }
//     }
//
//     #[inline]
//     pub fn new_in(x: T, alloc: A) -> Self {
//         todo!()
//     }
// }
//
// impl<T, A: Allocator> Box<MaybeUninit<T>, A> {
//     /// SAFETY: caller must ensure that the value is in an initialized state.
//     #[inline]
//     pub unsafe fn assume_init(self) -> Box<T, A> {
//         let (raw, alloc) = Box::into_raw_with_allocator(self);
//         unsafe { Box::from_raw_in(raw as *mut T, alloc) }
//     }
// }
//
// impl<T: ?Sized, A: Allocator> ops::Deref for Box<T, A> {
//     type Target = T;
//
//     #[inline]
//     fn deref(&self) -> &T {
//         unsafe { self.ptr.as_ref() }
//     }
// }
//
// impl<T: ?Sized, A: Allocator> ops::DerefMut for Box<T, A> {
//     #[inline]
//     fn deref_mut(&mut self) -> &mut T {
//         unsafe { self.ptr.as_mut() }
//     }
// }

// impl<T, A: Allocator> Box<MaybeUninit<T>, A> {
//     /// SAFETY: caller must ensure that the value is in an initialized state.
//     pub unsafe fn assume_init(self) -> Box<T, A> {
//         let raw = Self::into_raw(self);
//
//         // SAFETY: `raw` comes from a previous call to `Box::into_raw`. By the safety requirements
//         // of this function, the value inside the `Box` is in an initialized state. Hence, it is
//         // safe to reconstruct the `Box` as `Box<T, A>`.
//         unsafe { Box::from_raw(raw.cast()) }
//     }
//
//     /// Writes the value and converts to `Box<T, A>`.
//     pub fn write(mut self, value: T) -> Box<T, A> {
//         (*self).write(value);
//
//         // SAFETY: We've just initialized `b`'s value.
//         unsafe { self.assume_init() }
//     }
// }
