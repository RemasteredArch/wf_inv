#![cfg(windows)]

use wf_inv_auth_scanning::{LoginScanner, Process};

fn main() {
    let Some(process) = Process::find_by_executable_name("Warframe.x64.exe") else {
        panic!("Could not find Warframe's process!");
    };

    let auth = LoginScanner::from_process(&process)
        .find_auth()
        .expect("no login found!");

    println!("{}", auth.to_api_query());
}
