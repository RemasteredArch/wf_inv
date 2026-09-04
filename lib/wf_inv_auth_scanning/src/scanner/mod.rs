mod windows;

#[cfg(windows)]
pub use windows::LoginScanner;

// Sanity check that the required methods are present and have the correct signature.
const _: fn(&crate::Process) -> LoginScanner = LoginScanner::from_process;
const _: fn(&LoginScanner) -> Option<crate::Login> = LoginScanner::find_auth;
