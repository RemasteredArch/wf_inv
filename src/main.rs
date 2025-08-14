#![cfg(windows)]

mod scanning;

use poggers::structures::process::{Process, implement::utils::ProcessUtils};

use scanning::LoginScanner;

fn main() {
    let process = match Process::find_by_name("Warframe.x64.exe") {
        Ok(p) => p,
        Err(e) => panic!("Error finding Warframe's process: {e}"),
    };

    let auth = LoginScanner::new(&process.get_base_module().unwrap())
        .find_auth()
        .expect("no login found!");

    println!("{}", auth.to_api_query());
}
