// SPDX-License-Identifier: MPL-2.0
//
// Copyright © 2025-2026 RemasteredArch
//
// This Source Code Form is subject to the terms of the Mozilla Public License, version 2.0. If a
// copy of the Mozilla Public License was not distributed with this file, You can obtain one at
// <https://mozilla.org/MPL/2.0/>.

use std::ffi;

use windows::Win32::System::Memory;

use crate::handle::PlatformHandle;

/// Check that a region is neither guarded no marked as no access.
///
/// - "Region" here means a continuous set of pages with the same settings.
/// - Assumes that `flags` comes from the [`Memory::MEMORY_BASIC_INFORMATION`] provided by
///   [`Memory::VirtualQueryEx`].
#[must_use]
fn is_region_readable(flags: Memory::PAGE_PROTECTION_FLAGS) -> bool {
    // Perform a bitwise AND, then see if it equals the provided flag.
    let and_eq = |flag| flags & flag == flag;

    !and_eq(Memory::PAGE_GUARD) && flags != Memory::PAGE_NOACCESS
}

pub(super) struct Regions {
    addr: usize,
    handle: PlatformHandle,
}

impl Regions {
    #[must_use]
    pub const fn new(handle: PlatformHandle) -> Self {
        Self { addr: 0, handle }
    }
}

impl Iterator for Regions {
    type Item = super::Region;

    fn next(&mut self) -> Option<Self::Item> {
        let mut mem_info = Memory::MEMORY_BASIC_INFORMATION::default();

        while unsafe {
            Memory::VirtualQueryEx(
                self.handle.0,
                Some(self.addr as *const ffi::c_void),
                &raw mut mem_info,
                size_of_val(&mem_info),
            )
        } == size_of_val(&mem_info)
        {
            let region = super::Region {
                addr: mem_info.BaseAddress as usize,
                size: mem_info.RegionSize,
                handle: self.handle,
            };
            self.addr = mem_info.BaseAddress as usize + mem_info.RegionSize;

            if mem_info.State != Memory::MEM_COMMIT || !is_region_readable(mem_info.Protect) {
                continue;
            }

            return Some(region);
        }

        None
    }
}
