// SPDX-License-Identifier: MPL-2.0
//
// Copyright © 2025-2026 RemasteredArch
//
// This Source Code Form is subject to the terms of the Mozilla Public License, version 2.0. If a
// copy of the Mozilla Public License was not distributed with this file, You can obtain one at
// <https://mozilla.org/MPL/2.0/>.

use std::ffi;

use windows::Win32::{
    Foundation,
    System::{Diagnostics::ToolHelp, Threading},
};

use crate::handle::PlatformHandle;

use super::OpenableProcess;

pub struct SnapshottedProcess {
    name: Box<str>,
    pid: u32,
}

impl OpenableProcess for SnapshottedProcess {
    type Error = windows::core::Error;

    fn name(&self) -> &str {
        &self.name
    }

    fn open(self) -> Result<super::Process, Self::Error> {
        let Self { name, pid } = self;

        // This might not actually be safe. Oh well.
        let handle = PlatformHandle(unsafe {
            Threading::OpenProcess(Threading::PROCESS_ALL_ACCESS, false, pid)
        }?);

        Ok(super::Process { name, handle })
    }
}

pub struct ProcessIter {
    snapshot: Foundation::HANDLE,
    process_entry: Option<ToolHelp::PROCESSENTRY32>,
}

impl ProcessIter {
    pub fn new() -> windows::core::Result<Self> {
        unsafe { ToolHelp::CreateToolhelp32Snapshot(ToolHelp::TH32CS_SNAPPROCESS, 0) }.map(
            |snapshot| Self {
                snapshot,
                process_entry: None,
            },
        )
    }
}

impl Iterator for ProcessIter {
    type Item = SnapshottedProcess;

    fn next(&mut self) -> Option<Self::Item> {
        let process_entry = if let Some(process_entry) = self.process_entry.as_mut() {
            // Get the next process.
            unsafe { ToolHelp::Process32Next(self.snapshot, std::ptr::from_mut(process_entry)) }
                .ok()?;
            *process_entry
        } else {
            // Get the first process.
            let mut process_entry = ToolHelp::PROCESSENTRY32 {
                // `dwSize` being set to the actual size of the struct in bytes is a safety invariant.
                dwSize: u32::try_from(size_of::<ToolHelp::PROCESSENTRY32>())
                    .expect("a reasonable struct would not exceed `u32::MAX` bytes"),
                ..Default::default()
            };
            unsafe { ToolHelp::Process32First(self.snapshot, &raw mut process_entry) }.ok()?;

            self.process_entry = Some(process_entry);
            process_entry
        };

        // Safety: I have no idea if this is safe, but I figure that `[i8; _]` and `[u8; _]` are
        // _probably_ equivalent.
        let path_as_bytes = unsafe {
            std::mem::transmute::<
                [i8; Foundation::MAX_PATH as usize],
                [u8; Foundation::MAX_PATH as usize],
            >(process_entry.szExeFile)
        };

        Some(SnapshottedProcess {
            name: ffi::CStr::from_bytes_until_nul(&path_as_bytes)
                .unwrap()
                .to_string_lossy()
                .into(),
            pid: process_entry.th32ProcessID,
        })
    }
}
