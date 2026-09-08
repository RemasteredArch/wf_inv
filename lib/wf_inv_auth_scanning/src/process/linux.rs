// SPDX-License-Identifier: MPL-2.0
//
// Copyright © 2026 RemasteredArch
//
// This Source Code Form is subject to the terms of the Mozilla Public License, version 2.0. If a
// copy of the Mozilla Public License was not distributed with this file, You can obtain one at
// <https://mozilla.org/MPL/2.0/>.

use std::{
    ffi::OsString,
    io::{BufRead, BufReader, Read},
    os::unix::ffi::OsStringExt,
    path::PathBuf,
};

use nix::unistd::Pid;

use crate::handle::PlatformHandle;

use super::OpenableProcess;

pub struct SnapshottedProcess {
    name: Box<str>,
    pid: Pid,
}

impl OpenableProcess for SnapshottedProcess {
    type Error = std::convert::Infallible;

    /// Returns the base name of the first entry in `proc_pid_cmdline(5)` if not empty, or the
    /// contents of `proc_pid_comm(5)` otherwise.
    fn name(&self) -> &str {
        &self.name
    }

    fn open(self) -> Result<super::Process, Self::Error> {
        let Self { name, pid } = self;
        let handle = PlatformHandle(pid);

        Ok(super::Process { name, handle })
    }
}

pub struct ProcessIter {
    proc_dir: std::fs::ReadDir,
}

impl ProcessIter {
    pub fn new() -> std::io::Result<Self> {
        // TO-DO: this can be places other than `/proc`.
        std::fs::read_dir("/proc").map(|proc_dir| Self { proc_dir })
    }
}

impl Iterator for ProcessIter {
    type Item = SnapshottedProcess;

    fn next(&mut self) -> Option<Self::Item> {
        fn is_pid_dir(entry: &std::fs::DirEntry) -> bool {
            entry
                .file_name()
                .to_str()
                .is_some_and(|str| str.chars().all(|char| char.is_ascii_digit()))
        }

        // TO-DO: real error handling --- stop `.ok`ing errors!
        let mut entry = self.proc_dir.next()?.ok()?;
        while !is_pid_dir(&entry) {
            entry = self.proc_dir.next()?.ok()?;
        }

        let mut name = String::new();
        std::fs::File::open(entry.path().join("comm"))
            .unwrap()
            .read_to_string(&mut name)
            .unwrap();
        if name.chars().last().is_some_and(|c| c == '\n') {
            name.pop();
        }

        let mut exe = Vec::new();
        BufReader::new(std::fs::File::open(entry.path().join("cmdline")).unwrap())
            .read_until(0, &mut exe)
            .unwrap();
        exe.pop_if(|&mut last| last == 0);

        // Convert Windows-style absolute paths to Unix relative paths. Does nothing to handle UNC
        // paths or forward slashes inside of path elements.
        if exe
            .get(0..b"_:\\".len())
            .is_some_and(|bytes| bytes[0].is_ascii_alphabetic() && &bytes[1..] == b":\\")
        {
            for byte in &mut exe {
                // 7-bit ASCII characters only ever represent themselves in UTF-8 text, so we can
                // just haphazardly replace them without worried about continuation bytes.
                if *byte == b'\\' {
                    *byte = b'/';
                }
            }
        }

        // TO-DO: how is `from_vec` allowed to exist? There's absolutely no checking that the string
        // does not, in fact, contain a null byte?!
        let exe = PathBuf::from(OsString::from_vec(exe));
        let exe = if exe.is_empty() {
            String::new()
        } else {
            exe.file_name().unwrap().to_string_lossy().into()
        };

        let pid = Pid::from_raw(entry.file_name().to_str().unwrap().parse().unwrap());

        Some(SnapshottedProcess {
            // Prefer the name derived from the path to the executable if available, otherwise fall
            // back to the command name provided by the kernel.
            name: if exe.is_empty() {
                name.into_boxed_str()
            } else {
                exe.into()
            },
            pid,
        })
    }
}
