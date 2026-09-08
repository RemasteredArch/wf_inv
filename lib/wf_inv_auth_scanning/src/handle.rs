// SPDX-License-Identifier: MPL-2.0
//
// Copyright © 2025-2026 RemasteredArch
//
// This Source Code Form is subject to the terms of the Mozilla Public License, version 2.0. If a
// copy of the Mozilla Public License was not distributed with this file, You can obtain one at
// <https://mozilla.org/MPL/2.0/>.

use std::fmt::{Debug, Display};

#[cfg(windows)]
mod windows {
    use windows::Win32::{Foundation, System::Diagnostics::Debug};

    // TO-DO: ["Generally, an application should call CloseHandle once for each handle it
    // opens."](https://learn.microsoft.com/en-us/windows/win32/api/handleapi/nf-handleapi-closehandle)
    //
    // This would be trivial to implement using `Rc`, as this wrapper is already widely used.
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    #[repr(transparent)]
    pub struct Handle(pub Foundation::HANDLE);

    impl super::Handle for Handle {
        type Error = windows::core::Error;

        unsafe fn raw_read(
            &self,
            addr: usize,
            data: *mut u8,
            size: usize,
        ) -> Result<(), Self::Error> {
            unsafe { Debug::ReadProcessMemory(self.0, addr as *const _, data.cast(), size, None) }
        }
    }
}

#[cfg(target_os = "linux")]
mod linux {
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    #[repr(transparent)]
    pub struct Handle(pub nix::unistd::Pid);

    impl super::Handle for Handle {
        type Error = nix::Error;

        unsafe fn raw_read(
            &self,
            addr: usize,
            data: *mut u8,
            size: usize,
        ) -> Result<(), Self::Error> {
            // TO-DO: should `raw_read` just take a slice reference and make it the caller's
            // responsibility to form?
            let mut local_iov = [std::io::IoSliceMut::new(unsafe {
                std::slice::from_raw_parts_mut(data, size)
            })];
            let remote_iov = [nix::sys::uio::RemoteIoVec {
                base: addr,
                len: size,
            }];

            // TO-DO: implement privilege escalation to obtain the necessary `ptrace` permissions to
            // use `process_vm_readv`.
            let bytes_copied =
                nix::sys::uio::process_vm_readv(self.0, &mut local_iov, &remote_iov)?;
            // A partial write can occur if only part of an remote I/O vector is on an
            // invalid/non-resident page, resulting in only the parts other than those on the
            // failing page being written. This doesn't raise an error, so we raise it ourselves.
            if bytes_copied != size {
                return Err(nix::Error::EIO);
            }

            Ok(())
        }
    }
}

#[cfg(windows)]
pub use windows::Handle as PlatformHandle;

#[cfg(target_os = "linux")]
pub use linux::Handle as PlatformHandle;

pub trait Handle: Debug
where
    Self::Error: Display,
{
    type Error;

    unsafe fn raw_read(&self, addr: usize, data: *mut u8, size: usize) -> Result<(), Self::Error>;
}
