//! on today's episode of my yak shaving show:
//! accessing the command line arguments (argc, argv) in rust not from `#[no_main]`'s main.
//!
//! by "`#[no_main]`'s main" i mean this:
//!
//! ```example
//! #![no_main]
//! #[unsafe(no_mangle)]
//! pub fn main(argc: c_int, argv: *mut *mut c_char) {}
//! ```
//!
//! ----
//! glibc passes argc, argv, and envp to functions in .init_array, as a non-standard
//! extension.
//!   std hooks into it, see `library/std/src/sys/args/unix.rs`.
//!   there argv are const, but there's really no way to guarantee its imutability, is there? see
//!   <https://github.com/rust-lang/rust/issues/105999>
//!
//! you might find this interesting:
//!   - glibc (where the thing actually happens):
//!     <https://sourceware.org/git/?p=glibc.git;a=blob;f=csu/libc-start.c;h=6f3d52e223d8f32dfecf1364c4665e54c6170f28;hb=HEAD#l145>
//!   - musl (where the thing does NOT happen):
//!     <https://git.musl-libc.org/cgit/musl/tree/src/env/__libc_start_main.c#n64>
//!
//! musl does not do the same thing glibc does, and it does not seem like there's an alterantive.
//! in musl maining lists i found following thread:
//!   <https://www.openwall.com/lists/musl/2020/07/15/2>
//!
//!   subject:
//!   musl attribute constructor does not pass argc and argv as expected?
//!
//!   response:
//!   ```quote
//!   This is intentional. Relying on the glibc-specific behavior here is
//!   not portable. The ELF spec does not define arguments being passed to
//!   init_array functions, and other (non-glibc) implementations don't do
//!   it either.
//!
//!   Aside from trying to discourage nonportable things (musl was pretty
//!   aggressive about this early on, a bit less so now), this particular
//!   behavior is one where failing hard seems to have been a better choice.
//!   The main case we found of software trying to use the ctor arguments
//!   was in an attempt to relocate argv/environ prior to program entry in
//!   order to make space to do a "setproctitle" operation. This is highly
//!   unsafe, as the dynamic linker and/or __libc_start_main entry-point
//!   code have already saved pointers to some things found there, and will
//!   break in subtle but potentially dangerous ways that might not be
//!   noticed until long after deployment. Crashing immediately in the ctor
//!   trying to poke at them, on the other hand, caused the bad code to be
//!   found and fixed.
//!   ```
//!
//! mdempsky in go repo:
//!   <https://github.com/golang/go/issues/13492#issuecomment-162256441>
//!
//!   is stating the following:
//!   ```quote
//!   I just looked at glibc, Bionic, uClibc, musl, and dietlibc, as well as the dynamic linkers
//!   for FreeBSD, NetBSD, and OpenBSD. It looks like only glibc passes (argc, argv, envp) to the
//!   DSO init functions.
//!   ```
//!
//! ----
//! on apple there's `_NSGetArgc` and `_NSGetArgv`, this is also what std is relying on
//!   - <https://github.com/apple-oss-distributions/Libc/blob/63976b830a836a22649b806fe62e8614fe3e5555/include/crt_externs.h#L41>
//!
//! ----
//! on windows there's `GetCommandLineA`, `GetCommandLineW`, there's also `CommandLineToArgvW`, it
//! doesn't seem like would be better then just relying on std really because `CommandLineToArgvW`
//! allocates.
//!   - <https://learn.microsoft.com/en-us/windows/win32/api/shellapi/nf-shellapi-commandlinetoargvw>
//!   - <https://learn.microsoft.com/en-us/cpp/cpp/main-function-command-line-args>
//!
//! ----
//! additional reading:
//!   - <https://maskray.me/blog/2021-11-07-init-ctors-init-array>
//!   - <https://daviddeley.com/autohotkey/parameters/parameters.htm>

use std::ffi::{CStr, OsStr, c_char, c_int};

#[cfg(all(target_env = "gnu", target_os = "linux"))]
mod glibc {
    // NOTE: this is based on how std hooks into argc, argv, see `library/std/src/sys/args/unix.rs`.
    //   also note that in std argv is const, but there's really no way to guarantee its
    //   imutability, is there? see https://github.com/rust-lang/rust/issues/105999.

    use std::ffi::{c_char, c_int};
    use std::ptr::null_mut;

    static mut ARGC: c_int = 0;
    static mut ARGV: *mut *mut c_char = null_mut();

    extern "C" fn init(argc: c_int, argv: *mut *mut c_char, _envp: *mut *mut c_char) {
        unsafe {
            ARGC = argc;
            ARGV = argv;
        }
    }

    #[used]
    #[unsafe(link_section = ".init_array")]
    static INIT: extern "C" fn(c_int, *mut *mut c_char, *mut *mut c_char) = init;

    pub fn argc_argv() -> (c_int, *mut *mut c_char) {
        unsafe { (ARGC, ARGV) }
    }
}

/// NOTE: this will return None on all targets that are not linux+glibc, but can be extended to
/// work on apple.
pub fn argc_argv() -> Option<(c_int, *mut *mut c_char)> {
    #[cfg(all(target_env = "gnu", target_os = "linux"))]
    return Some(glibc::argc_argv());

    #[allow(unreachable_code)]
    None
}

// NOTE: this handles standard c/cpp argc,argv.
//   everything pretty straightforward for unix systems.
//   things also appear to be the same for windows, see
//   https://learn.microsoft.com/en-us/cpp/cpp/main-function-command-line-args?view=msvc-170#example-of-command-line-argument-parsing
pub struct ArgIter {
    argc: isize,
    argv: *mut *mut c_char,
    i: isize,
}

impl ArgIter {
    pub fn new(argc: c_int, argv: *mut *mut c_char) -> Self {
        Self {
            argc: argc as isize,
            argv,
            i: 0,
        }
    }
}

impl Iterator for ArgIter {
    type Item = &'static OsStr;

    fn next(&mut self) -> Option<Self::Item> {
        if self.i == self.argc {
            return None;
        }

        // SAFETY: `argv` is non-null if `argc` is positive, and it is guaranteed to be at
        // least as long as `argc`.
        let ptr = unsafe { self.argv.offset(self.i).read() };
        self.i += 1;

        // NOTE: ptr may be null
        //   see https://github.com/rust-lang/rust/issues/105999
        //   rust's std is bailing out on null ptr, but i don't agree, let's keep going.
        if ptr.is_null() {
            return self.next();
        }

        let cstr = unsafe { CStr::from_ptr(ptr) };
        // NOTE: this is not questionable for unix systems;
        //   but what about windows? shoudln't be a problem either, see
        //   https://learn.microsoft.com/en-us/cpp/cpp/main-function-command-line-args?view=msvc-170#example-of-command-line-argument-parsing
        let osstr = unsafe { OsStr::from_encoded_bytes_unchecked(cstr.to_bytes()) };
        Some(osstr)
    }
}
