use std::{collections::HashMap, ffi, fmt::Display, ops::Range};

use windows::Win32::{
    Foundation,
    System::{Diagnostics::Debug, Memory},
};

mod process;

pub use process::Process;

fn panic_on_last_error() {
    let error = unsafe { windows::Win32::Foundation::GetLastError() };
    panic!("{error:?}");
}

/// A [`Sized`] and stack-allocated equivalent to [`str`].
#[derive(Debug, PartialEq, Eq, Hash)]
struct ArrayStr<const LEN: usize>([u8; LEN]);

impl<const LEN: usize> ArrayStr<LEN> {
    pub const fn new(str: [u8; LEN]) -> Option<Self> {
        if str::from_utf8(&str).is_err() {
            return None;
        }

        Some(Self(str))
    }
}

impl<const LEN: usize> AsRef<str> for ArrayStr<LEN> {
    fn as_ref(&self) -> &str {
        str::from_utf8(&self.0).unwrap()
    }
}

impl<const LEN: usize> Display for ArrayStr<LEN> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_ref())
    }
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub struct Login {
    account_id: ArrayStr<{ Self::ACCOUNT_ID_LEN }>,
    token: Box<str>,
}

impl Login {
    const ACCOUNT_ID_LEN: usize = 24;

    pub fn account_id(&self) -> &str {
        self.account_id.as_ref()
    }

    pub fn token(&self) -> &str {
        self.token.as_ref()
    }

    pub fn to_api_query(&self) -> String {
        format!("?accountId={}&nonce={}", self.account_id(), self.token())
    }
}

#[derive(Debug)]
struct Region {
    addr: usize,
    size: usize,
    handle: Foundation::HANDLE,
}

impl Region {
    pub const fn to_range(&self) -> Range<usize> {
        self.addr..(self.addr + self.size)
    }

    unsafe fn raw_read(
        &self,
        addr: usize,
        data: *mut u8,
        size: usize,
    ) -> windows::core::Result<()> {
        unsafe { Debug::ReadProcessMemory(self.handle, addr as *const _, data.cast(), size, None) }
    }

    pub fn read<T: Sized>(&self, addr: usize) -> Option<T> {
        let range = self.to_range();
        if !range.contains(&addr) || !range.contains(&(addr + size_of::<T>())) {
            return None;
        }

        unsafe {
            let mut data: T = std::mem::zeroed();

            self.raw_read(addr, (&raw mut data).cast(), size_of::<T>())
                .ok()
                .map(|()| data)
        }
    }

    pub fn buffer(&self) -> Vec<u8> {
        // Buffer must be under the impression that it's of the correct size, so we initialize it
        // with zeros before even filling it with the correct data.
        let mut buffer = vec![0; self.size];
        unsafe {
            self.raw_read(self.addr, buffer.as_mut_ptr(), self.size)
                .unwrap_or_else(|error| {
                    eprintln!("Error: {error} upon trying to read region {self:?}");
                    panic_on_last_error();
                });
        }

        buffer
    }

    pub fn scan(&self, pattern: &[u8]) -> Option<usize> {
        let buffer = self.buffer();

        for buffer_addr in 0..buffer.len() {
            let Some(subslice) = buffer.get(buffer_addr..(buffer_addr + pattern.len())) else {
                break;
            };

            if subslice == pattern {
                return Some(self.addr + buffer_addr);
            }
        }

        None
    }
}

/// Check that a region is neither guarded no marked as no access.
///
/// - "Region" here means a continuous set of pages with the same settings.
/// - Assumes that `flags` comes from the [`Memory::MEMORY_BASIC_INFORMATION`] provided by
///   [`Memory::VirtualQueryEx`].
fn is_region_readable(flags: Memory::PAGE_PROTECTION_FLAGS) -> bool {
    // Perform a bitwise AND, then see if it equals the provided flag.
    let and_eq = |flag| flags & flag == flag;

    !and_eq(Memory::PAGE_GUARD) && flags != Memory::PAGE_NOACCESS
}

struct Regions {
    addr: usize,
    handle: Foundation::HANDLE,
}

impl Regions {
    pub const fn new(handle: Foundation::HANDLE) -> Self {
        Self { addr: 0, handle }
    }
}

impl Iterator for Regions {
    type Item = Region;

    fn next(&mut self) -> Option<Self::Item> {
        let mut mem_info = Memory::MEMORY_BASIC_INFORMATION::default();

        while unsafe {
            Memory::VirtualQueryEx(
                self.handle,
                Some(self.addr as *const ffi::c_void),
                &raw mut mem_info,
                size_of_val(&mem_info),
            )
        } == size_of_val(&mem_info)
        {
            let region = Region {
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

pub struct LoginScanner {
    handle: Foundation::HANDLE,
}

impl LoginScanner {
    pub const fn from_process(process: &Process) -> Self {
        Self {
            handle: process.handle(),
        }
    }

    pub fn find_auth(&self) -> Option<Login> {
        const ACCOUNT_ID_PREFIX: [u8; 11] = *b"?accountId=";
        const TOKEN_PREFIX: [u8; 7] = *b"&nonce=";

        println!("Starting search");

        let regions = Regions::new(self.handle);
        let mut candidates = HashMap::<Login, usize>::new();

        for region in regions {
            let Some(mut addr) = region.scan(&ACCOUNT_ID_PREFIX) else {
                continue;
            };

            // Sanity check that the scan _did_ match on the correct string.
            let account_id_prefix: [u8; ACCOUNT_ID_PREFIX.len()] = region.read(addr).unwrap();
            assert_eq!(account_id_prefix, ACCOUNT_ID_PREFIX);
            // Skip past the matched string.
            addr += ACCOUNT_ID_PREFIX.len();

            // Check that the account ID prefix and account ID are followed by the token prefix.
            let token_prefix: [u8; TOKEN_PREFIX.len()] =
                region.read(addr + Login::ACCOUNT_ID_LEN).unwrap();
            if token_prefix != TOKEN_PREFIX {
                println!("real {token_prefix:?} != expected {TOKEN_PREFIX:?}, skipping");
                continue;
            }

            // Actually read the account ID.
            let account_id: [u8; Login::ACCOUNT_ID_LEN] = region.read(addr).unwrap();
            addr += Login::ACCOUNT_ID_LEN + TOKEN_PREFIX.len();

            // Actually read the token.
            let mut token = Vec::new();
            loop {
                let char: u8 = region.read(addr).unwrap();
                addr += 1;

                if !char.is_ascii_digit() {
                    break;
                }

                token.push(char);
            }

            let login = Login {
                account_id: ArrayStr::new(account_id).unwrap(),
                token: str::from_utf8(token.as_slice())
                    .expect("`token` should only have ascii numerics")
                    .into(),
            };

            // If this login has shown up twice already, assume it's the correct one and return it.
            if let Some(count) = candidates.get_mut(&login) {
                if *count == 2 {
                    return Some(login);
                }

                *count += 1;
            } else {
                candidates.insert(login, 1);
            }
        }

        None
    }
}
