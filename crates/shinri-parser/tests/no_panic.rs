use proptest::prelude::*;
use shinri_core::Context;
use shinri_parser::Parser;

proptest! {
    #![proptest_config(ProptestConfig::with_cases(4000))]

    /// The parser must never panic on arbitrary input — only return commands
    /// or diagnostics (design §8, Global Constraint: never panic on input).
    #[test]
    fn never_panics_on_arbitrary_text(src in ".{0,200}") {
        let mut ctx = Context::new();
        let mut p = Parser::new(&src);
        let mut budget = 1000;
        while let Some(_c) = p.next_command(&mut ctx) {
            budget -= 1;
            if budget == 0 { break; }
        }
    }
}
