pub mod cstring;
pub mod memory;
pub mod string;
pub mod vector;

#[cfg(test)]
pub(crate) mod testutil;

// NOTE(blukai): alloc::handle_alloc_error wants layout arg, but it doesn't really do anything
// useful with it and it's annoying to jiggle it around.
#[cfg(not(no_global_oom_handling))]
#[cold]
pub(crate) fn eek(_err: alloc::AllocError) -> ! {
    panic!("allocation failed");
}

#[cfg(not(no_global_oom_handling))]
#[inline]
pub(crate) fn this_is_fine<T>(result: Result<T, alloc::AllocError>) -> T {
    match result {
        Ok(ok) => ok,
        Err(err) => eek(err),
    }
}
