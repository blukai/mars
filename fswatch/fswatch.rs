use core::ffi::c_int;
use core::{error, fmt, ops};

// NOTE: i did consider using OsStr, but concluded that it would be more pain then good.
//   OsStr is just way too inconvenient and awkward to deal with; it's weird and inconvenient, it
//   also roundtrips.
//
//   i did choose str, which isn't the most optimal, but most natural and convenient for this.
//
//   windows paths cannot be represented as valid utf8, but i don't care, do i?

#[derive(Debug)]
pub enum Error {
    Errno(c_int),
}

impl error::Error for Error {}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Errno(errno) => write!(f, "errno: {errno} (0x{errno:x})"),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct EventFlags(pub u16);

// NOTE: you can do Tab/:/l0r1.
#[rustfmt::skip]
impl EventFlags {
    pub const CREATED : Self = Self(0b0000000000000001);
    pub const MODIFIED: Self = Self(0b0000000000000010);
    pub const REMOVED : Self = Self(0b0000000000000100);
}

impl EventFlags {
    pub fn empty() -> Self {
        Self(0)
    }

    pub fn all() -> Self {
        Self::CREATED | Self::MODIFIED | Self::REMOVED
    }
}

impl ops::BitOr for EventFlags {
    type Output = Self;
    fn bitor(self, rhs: Self) -> Self::Output {
        Self(self.0 | rhs.0)
    }
}

impl ops::BitOrAssign for EventFlags {
    fn bitor_assign(&mut self, rhs: Self) {
        self.0 |= rhs.0
    }
}

impl ops::BitAnd for EventFlags {
    type Output = Self;
    fn bitand(self, rhs: Self) -> Self::Output {
        Self(self.0 & rhs.0)
    }
}

impl ops::BitAndAssign for EventFlags {
    fn bitand_assign(&mut self, rhs: Self) {
        self.0 &= rhs.0
    }
}

impl ops::Not for EventFlags {
    type Output = Self;
    fn not(self) -> Self::Output {
        Self(!self.0)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Event<'a> {
    pub flags: EventFlags,
    // NOTE: path is a directory name that was given to the add_directory function + entry.
    //
    //   for example you gave it "./gamedata" who contains "slug.slang" and you want to receive
    //   notifications when slug.slang is modified -> the path would be "./gamedata/slug.slang".
    pub path: &'a str,
}

#[cfg(any(target_os = "linux", target_os = "android"))]
mod inotify {
    use core::ffi::{CStr, c_char, c_int, c_void};

    use alloc::Allocator;
    use containers::boxed::Box;
    use containers::cstring::FixedCString;
    use containers::string::FixedString;
    use containers::unmanagedexponentialarray::UnmanagedExponentialArray;

    use super::{Error, Event, EventFlags};

    use sys::*;

    mod sys {
        #![allow(non_camel_case_types, dead_code)]

        use core::ffi::{c_char, c_int, c_void};

        // ----
        // NOTE: the following is from errno.h

        unsafe extern "C" {
            pub fn __errno_location() -> *mut c_int;
        }

        // NOTE: these come from
        //   errno.h -> bits/errno.h -> linux/errno.h -> asm/errno.h -> asm-generic/errno.h -> asm-generic/errno-base.h
        pub const EAGAIN: c_int = 11; // Try again

        // ----
        // NOTE: the following is from sys/inotify.h

        unsafe extern "C" {
            pub fn inotify_init1(flags: c_int) -> c_int;
            pub fn inotify_add_watch(fd: c_int, name: *const c_char, mask: u32) -> c_int;
        }

        // NOTE: these come from
        //   sys/inotify.h -> bits/inotify.h
        //
        // these are octals, but weirdly enough there's nothing indicates that in bits/inotify.h?
        pub const IN_CLOEXEC: c_int = 0o02000000;
        pub const IN_NONBLOCK: c_int = 0o00004000;

        // Supported events suitable for MASK parameter of INOTIFY_ADD_WATCH.
        pub const IN_ACCESS: u32 = 0x00000001; // File was accessed.
        pub const IN_MODIFY: u32 = 0x00000002; // File was modified.
        pub const IN_ATTRIB: u32 = 0x00000004; // Metadata changed.
        pub const IN_CLOSE_WRITE: u32 = 0x00000008; // Writtable file was closed.
        pub const IN_CLOSE_NOWRITE: u32 = 0x00000010; // Unwrittable file closed.
        pub const IN_CLOSE: u32 = IN_CLOSE_WRITE | IN_CLOSE_NOWRITE; // Close.
        pub const IN_OPEN: u32 = 0x00000020; // File was opened.
        pub const IN_MOVED_FROM: u32 = 0x00000040; // File was moved from X.
        pub const IN_MOVED_TO: u32 = 0x00000080; // File was moved to Y.
        pub const IN_MOVE: u32 = IN_MOVED_FROM | IN_MOVED_TO; // Moves.
        pub const IN_CREATE: u32 = 0x00000100; // Subfile was created.
        pub const IN_DELETE: u32 = 0x00000200; // Subfile was deleted.
        pub const IN_DELETE_SELF: u32 = 0x00000400; // Self was deleted.
        pub const IN_MOVE_SELF: u32 = 0x00000800; // Self was moved.

        // NOTE: there are also special flags, some of which were introduced in different versions. i
        // omited them.

        #[repr(C)]
        #[derive(Debug, Clone, Copy)]
        pub struct inotify_event {
            pub wd: c_int,         // Watch descriptor.
            pub mask: u32,         // Watch mask.
            pub cookie: u32,       // Cookie to synchronize two events.
            pub len: u32,          // Length (including NULs) of name.
            pub name: [c_char; 0], // Name.
        }

        // NOTE: inotify_event struct's last field is `char name __flexarr;`,
        //   what is __flexarr? see https://stackoverflow.com/a/21589518
        //   i did an actual test:
        //     #include <stdio.h>
        //     #include <sys/inotify.h>
        //     int main() {
        //         printf("%d\n", sizeof(struct inotify_event));
        //         return 0;
        //     }
        //     $ cc x.c -o x && ./x
        //     16
        const _: () = assert!(size_of::<inotify_event>() == 16);

        // ----
        // NOTE: the following is from unistd.h

        pub type size_t = usize;
        pub type ssize_t = isize;

        unsafe extern "C" {
            pub fn close(fd: c_int) -> c_int;
            pub fn read(fd: c_int, buf: *mut c_void, count: size_t) -> ssize_t;
        }

        // ----
        // NOTE: the following is from linux/limits.h

        pub const PATH_MAX: c_int = 4096;
    }

    fn errno() -> c_int {
        unsafe {
            let ptr = __errno_location();
            if ptr.is_null() { -1 } else { *ptr }
        }
    }

    fn event_flags_to_mask(event_flags: EventFlags) -> u32 {
        let mut mask = 0;
        if (event_flags & EventFlags::CREATED) == EventFlags::CREATED {
            mask |= IN_CREATE;
        }
        if (event_flags & EventFlags::MODIFIED) == EventFlags::MODIFIED {
            mask |= IN_MODIFY;
        }
        if (event_flags & EventFlags::REMOVED) == EventFlags::REMOVED {
            mask |= IN_DELETE | IN_DELETE_SELF;
        }
        mask
    }

    fn mask_to_event_flags(mask: u32) -> EventFlags {
        let mut event_flags = EventFlags::empty();
        if (mask & IN_MODIFY) == IN_MODIFY {
            event_flags |= EventFlags::MODIFIED
        }
        if (mask & IN_CREATE) == IN_CREATE {
            event_flags |= EventFlags::CREATED
        }
        if (mask & IN_DELETE) == IN_DELETE {
            event_flags |= EventFlags::REMOVED
        }
        if (mask & IN_DELETE_SELF) == IN_DELETE_SELF {
            event_flags |= EventFlags::REMOVED
        }
        event_flags
    }

    struct WatchDescriptor {
        wd: c_int,
        // MAYBE: don't do fixed?
        path: FixedCString<{ PATH_MAX as usize }>,
    }

    // QUOTE:
    //   > Some systems cannot read integer variables if they are not properly aligned.  On other
    //   systems, incorrect alignment may decrease performance.  Hence, the buffer used for reading
    //   from the inotify file descriptor should have the same alignment as struct inotify_event.
    //   - man inotify
    #[repr(align(4))]
    struct ReadBuf([u8; 4096]);

    // NOTE: Buf's alignment must match alignment of inotify_event.
    const _: () = assert!(align_of::<ReadBuf>() == align_of::<inotify_event>());

    // NOTE: this will never reallocate; arena/bump-friendly stuff.
    pub struct Inotify<A: Allocator> {
        inotify_fd: c_int,
        watch_descriptors: UnmanagedExponentialArray!(WatchDescriptor, 4),
        read_buf: &'static mut ReadBuf,
        read_buf_len: u32,
        read_buf_pos: u32,
        path_buf: &'static mut FixedString<{ PATH_MAX as usize }>,
        alloc: A,
    }

    impl<A: Allocator> Inotify<A> {
        pub fn init(alloc: A) -> Result<Self, Error> {
            unsafe {
                let inotify_fd = inotify_init1(IN_NONBLOCK);
                if inotify_fd == -1 {
                    return Err(Error::Errno(errno()));
                }
                let (read_buf, _) =
                    Box::leak_with_alloc(Box::<ReadBuf, _>::new_uninit_in(&alloc).assume_init());
                let (path_buf, _) =
                    Box::leak_with_alloc(Box::new_in(FixedString::default(), &alloc));
                Ok(Self {
                    inotify_fd,
                    watch_descriptors: UnmanagedExponentialArray::default(),
                    read_buf,
                    read_buf_len: 0,
                    read_buf_pos: 0,
                    path_buf,
                    alloc,
                })
            }
        }

        pub fn add_directory(
            &mut self,
            path: &str,
            event_flags: EventFlags,
            recursirve: bool,
        ) -> Result<(), Error> {
            if recursirve {
                todo!("recursirve");
            }

            unsafe {
                let path = FixedCString::from_str(path);
                let mask = event_flags_to_mask(event_flags);

                // NOTE: if you give it empty path (for example) it would produce ENOENT errno.
                let wd = inotify_add_watch(self.inotify_fd, path.as_ptr() as *const c_char, mask);
                if wd == -1 {
                    return Err(Error::Errno(errno()));
                }

                if let Some(idx) = self.watch_descriptors.iter().position(|it| it.wd == wd) {
                    self.watch_descriptors[idx] = WatchDescriptor { wd, path };
                } else {
                    self.watch_descriptors
                        .push(&self.alloc, WatchDescriptor { wd, path });
                }

                Ok(())
            }
        }

        // NOTE: you may want to call this maybe like once per second or something. might not be
        // worth calling every frame (in an event loop).
        pub fn next_event(&mut self) -> Result<Option<Event<'_>>, Error> {
            unsafe {
                if self.read_buf_pos >= self.read_buf_len {
                    match read(
                        self.inotify_fd,
                        self.read_buf.0.as_mut_ptr() as *mut c_void,
                        self.read_buf.0.len(),
                    ) {
                        -1 if errno() == EAGAIN => return Ok(None),
                        -1 => return Err(Error::Errno(errno())),
                        0 => return Ok(None),
                        n if n >= 0 => {
                            self.read_buf_len = n as u32;
                            self.read_buf_pos = 0;
                        }
                        other => panic!("unexpected read return: {other}"),
                    }
                }

                let event = &*(self.read_buf.0[self.read_buf_pos as usize..].as_ptr()
                    as *const inotify_event);
                self.read_buf_pos += size_of::<inotify_event>() as u32 + event.len;

                let flags = mask_to_event_flags(event.mask);
                let path = {
                    // QUOTE:
                    //   > This filename is null-terminated, and may include further null bytes
                    //   ('\0') to align subsequent reads to a suitable address boundary.
                    //   - man inotify
                    let name = CStr::from_ptr(event.name.as_ptr());

                    self.path_buf.clear();
                    if let Some(it) = self.watch_descriptors.iter().find(|it| it.wd == event.wd) {
                        // NOTE: add_directory did recieve &str which was turned into CString.
                        self.path_buf
                            .push_str(str::from_utf8_unchecked(it.path.to_bytes()));
                        if !self.path_buf.ends_with('/') {
                            self.path_buf.push_char('/');
                        }
                    } else {
                        // NOTE: can we get here?
                    }
                    // NOTE: linux required names to be valid utf8, doeosn't it?
                    self.path_buf.push_str(name.to_str().expect("invalid name"));
                    &self.path_buf
                };
                Ok(Some(Event { flags, path }))
            }
        }
    }

    impl<A: Allocator> Drop for Inotify<A> {
        fn drop(&mut self) {
            unsafe {
                close(self.inotify_fd);
                self.watch_descriptors.deinit(&self.alloc);
                drop(Box::from_raw_in(self.read_buf, &self.alloc));
                drop(Box::from_raw_in(self.path_buf, &self.alloc));
            }
        }
    }
}

#[cfg(target_os = "windows")]
mod windows {
    // TODO: impl windows.
    //
    // NOTE: windows doesn't care if the string is valid or not xd.
}

// NOTE: i just list all the osese listed in https://en.wikipedia.org/wiki/Kqueue
#[cfg(any(
    target_os = "freebsd",
    target_os = "netbsd",
    target_os = "openbsd",
    target_os = "dragonfly",
    target_os = "macos"
))]
mod kqueue {
    // TODO: impl kqueue
    //
    // NOTE: xnu's PATH_MAX is 1024 (see sys/syslimits.h)
}

#[cfg(any(target_os = "linux", target_os = "android"))]
pub type FsWatch<A> = inotify::Inotify<A>;

// #[cfg(target_os = "windows")]
// pub type FsWatch<A> = windows::?<A>;

// #[cfg(any(
//     target_os = "freebsd",
//     target_os = "netbsd",
//     target_os = "openbsd",
//     target_os = "dragonfly",
//     target_os = "macos"
// ))]
// pub type FsWatch<A> = kqueue::Kqueue<A>;

// NOTE: refs:
//   - man inotify
//   - https://man.freebsd.org/cgi/man.cgi?kqueue
//   - https://developer.apple.com/documentation/coreservices/file_system_events/1455361-fseventstreameventflags
//   - https://learn.microsoft.com/en-us/windows/win32/api/winnt/ns-winnt-file_notify_information
