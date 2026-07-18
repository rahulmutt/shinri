#![no_main]
use libfuzzer_sys::fuzz_target;
use shinri_core::Context;
use shinri_parser::{StreamItem, StreamingParser};

// The repo's one untrusted-input boundary (docs/threat-model.md): arbitrary
// bytes fed through the same streaming path the CLI uses (driver.rs) must
// never panic. Ok/Err command results are both fine; only a crash is a bug.
fuzz_target!(|data: &[u8]| {
    if data.len() > 1 << 16 {
        return; // keep individual inputs bounded
    }
    let Ok(src) = std::str::from_utf8(data) else {
        return;
    };
    let mut ctx = Context::new();
    let mut sp = StreamingParser::new();
    sp.push_str(src);
    loop {
        match sp.next_command(&mut ctx) {
            StreamItem::Command(_) => {}
            StreamItem::NeedMore | StreamItem::Done => break,
        }
    }
    // EOF flush: emits at most one trailing-partial-command diagnostic.
    let _ = sp.finish(&mut ctx);
});
