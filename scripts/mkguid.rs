#! /usr/bin/env -S cargo +nightly -Zscript

---cargo
[package]
edition = "2024"

[dependencies]
fastrand = "2.5.0"
---

/// Prints a GUID for WiX, e.g., `4770FC69-8EE8-4C2E-B08D-ADF865C3C8D0`.
fn main() {
    let mut guid = String::with_capacity(36);

    let digits = std::iter::repeat_with(|| fastrand::digit(16).to_ascii_uppercase());
    for segment_length in [8, 4, 4, 4, 12] {
        guid.extend(digits.take(segment_length).chain(Some('-')));
    }
    assert_eq!(guid.pop(), Some('-'));

    println!("{guid}");
}
