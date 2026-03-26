// NOTE: here i am exploring idea of / solution to generic cascading/explosion.
//
//   imagine you've got something like
//   struct DrawData<A: Allocator> { .. }
//   and then when you want to pass it around you have to parametrize every single struct and
//   function with A:
//   pub fn render<F: Allocator>(&mut self, draw_data: &sx::DrawData<F>, ..);
//   fn draw_text<F: Allocator, A: Allocator>(&mut self, draw_data: &sx::DrawData<F>, .. other stuff uses A ..);
//
//   it's not a big deal when it's a lone isolated case,
//   but when you get like 10, 20 + of such functions, etc.. things become too noisy.
//
//   i often want to be precise about certain things and i often end up dragging multiple
//   allocators around.
//   not fun.
//   it's just borderline annoying and unnecessary.
//   in majority of cases only the owner needs to know who the allocator guy is, at creation-time.
//   and then the owned needs to do a drop.
//
//   the trade-off here is that your A: Allocator maye have been zero sized;
//   but now you'll be dragging around two pointers (or a fat pointer if you wish).
//   is it worth it? will see.

use std::alloc::Layout;
use std::ptr::NonNull;

use crate::{AllocError, Allocator, Global};

#[derive(Debug, Clone, Copy)]
pub struct ErasedAllocator(*const dyn Allocator);

// NOTE: this is just for your awareness. ErasedAllocator is a fat pointer.
const _: () = assert!(size_of::<ErasedAllocator>() == size_of::<usize>() * 2);

impl ErasedAllocator {
    /// SAFETY: the allocator reference (&A) you pass-in must outlive both this ErasedAllocator and
    /// all the data allocated through it.
    pub unsafe fn new<A: Allocator + 'static>(alloc: &A) -> Self {
        Self(alloc)
    }
}

unsafe impl Allocator for ErasedAllocator {
    #[inline(always)]
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        unsafe { (*self.0).allocate(layout) }
    }

    #[inline(always)]
    fn allocate_zeroed(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        unsafe { (*self.0).allocate_zeroed(layout) }
    }

    #[inline(always)]
    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
        unsafe { (*self.0).deallocate(ptr, layout) }
    }

    #[inline(always)]
    unsafe fn grow(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<[u8]>, AllocError> {
        unsafe { (*self.0).grow(ptr, old_layout, new_layout) }
    }

    #[inline(always)]
    unsafe fn grow_zeroed(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<[u8]>, AllocError> {
        unsafe { (*self.0).grow_zeroed(ptr, old_layout, new_layout) }
    }

    #[inline(always)]
    unsafe fn shrink(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<[u8]>, AllocError> {
        unsafe { (*self.0).shrink(ptr, old_layout, new_layout) }
    }

    #[inline(always)]
    fn by_ref(&self) -> &Self
    where
        Self: Sized,
    {
        self
    }
}

impl Default for ErasedAllocator {
    fn default() -> Self {
        unsafe { Self::new(&Global) }
    }
}
