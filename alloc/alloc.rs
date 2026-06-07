// NOTE: re-export alloc from allocator-api2.
//   i don't really want to copypaste it in because there are some nice crates, like hashbrown,
//   that support allocator-api2.
pub use allocator_api2::alloc::{AllocError, Allocator, Global, System};

pub use arena::*;
pub use erased::*;
pub use temp::*;

mod arena;
mod erased;
mod temp;

#[inline]
pub(crate) const fn align_up(value: usize, align: usize) -> usize {
    debug_assert!(align.is_power_of_two());
    (value + align - 1) & !(align - 1)
}

// NOTE(blukai): alloc::handle_alloc_error wants layout arg, but it doesn't really do anything
// useful with it and it's annoying to jiggle it around.
//
// NOTE(blukai): whoever calls eek must be annotated with #[track_caller].
//   this allows to immediately reveal who oomed.
//   :TrackOomCallerLocation
#[cfg(not(no_global_oom_handling))]
#[cold]
#[track_caller]
pub fn eek(_err: AllocError) -> ! {
    let loc = core::panic::Location::caller();
    let (file, line, column) = (loc.file(), loc.line(), loc.column());
    panic!("allocation failed at {file}:{line}:{column}");
}

// NOTE(blukai): whoever calls eek must be annotated with #[track_caller].
//   :TrackOomCallerLocation
#[cfg(not(no_global_oom_handling))]
#[track_caller]
#[inline(always)]
pub fn this_is_fine<T>(result: Result<T, AllocError>) -> T {
    match result {
        Ok(ok) => ok,
        Err(err) => eek(err),
    }
}

// TODO: can you do some kind of contextualization of allocator (thread-scoped)?
// something akin to:
//
// thread_local! {
//     static ALLOC_OVERRIDE: Cell<AllocatorKind> = Cell::new(AllocatorKind::Default);
// }
// and then in global_allocator thingie
// ALLOC_OVERRIDE.with(|k| match k.get() {
//     AllocatorKind::Arena => ARENA.alloc(layout),
//     AllocatorKind::Default => System.alloc(layout),
// })
//
// before you do anything though - look into postgress allocator. it i have heard or read
// somewhere that it mayhaps does something similar, so this idea is inspied by that.
//
// here you would switch to temp alloc (or arena with checkpoint) compile shader and discard
// everything after you're done and don't need "code" anymore.
