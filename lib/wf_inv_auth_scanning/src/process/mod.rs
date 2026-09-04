mod windows;

#[cfg(windows)]
pub use windows::Process;

// Sanity check that the required methods are present and have the correct signature.
const _: fn(&str) -> Option<Process> = Process::find_by_executable_name;
const _: fn(&Process) -> &str = Process::name;
