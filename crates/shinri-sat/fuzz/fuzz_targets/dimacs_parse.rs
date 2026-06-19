#![no_main]
use libfuzzer_sys::fuzz_target;

// The DIMACS reader must never panic on arbitrary input (spec §9).
fuzz_target!(|data: &[u8]| {
    if let Ok(s) = std::str::from_utf8(data) {
        let _ = shinri_sat::dimacs::parse_dimacs(s);
    }
});
