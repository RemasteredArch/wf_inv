#![cfg(windows)]

mod scanning;

use scanning::{LoginScanner, Process};

fn main() {
    let process = match Process::find_by_executable_name("Warframe.x64.exe") {
        Some(p) => p,
        None => panic!("Could not find Warframe's process!"),
    };

    let auth = LoginScanner::from_process(&process)
        .find_auth()
        .expect("no login found!");

    println!("{}", auth.to_api_query());
}
