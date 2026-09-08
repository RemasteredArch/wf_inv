// SPDX-License-Identifier: MPL-2.0
//
// Copyright © 2025-2026 RemasteredArch
//
// This Source Code Form is subject to the terms of the Mozilla Public License, version 2.0. If a
// copy of the Mozilla Public License was not distributed with this file, You can obtain one at
// <https://mozilla.org/MPL/2.0/>.

#[cfg(windows)]
mod windows;

#[cfg(target_os = "linux")]
mod linux;

use crate::handle::PlatformHandle;

#[cfg(windows)]
use windows::ProcessIter;

#[cfg(target_os = "linux")]
use linux::ProcessIter;

#[derive(Debug)]
pub struct Process {
    name: Box<str>,
    handle: PlatformHandle,
}

impl Process {
    #[must_use]
    pub fn find_by_executable_name(name: &str) -> Option<Self> {
        ProcessIter::new()
            .ok()?
            .find(|process| process.name() == name)
            .and_then(|process| process.open().ok())
    }

    #[must_use]
    pub const fn name(&self) -> &str {
        &self.name
    }

    #[must_use]
    pub(crate) const fn handle(&self) -> PlatformHandle {
        self.handle
    }
}

trait OpenableProcess {
    type Error;

    fn name(&self) -> &str;
    fn open(self) -> Result<Process, Self::Error>;
}

// Sanity check that the required methods are present and have the correct signature.
const _: fn(&str) -> Option<Process> = Process::find_by_executable_name;
const _: fn(&Process) -> &str = Process::name;
