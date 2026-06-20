//! SMT-LIB 2.6 frontend: logos lexer + interning recursive descent (design §9.1).

mod lexer;

pub use lexer::{Lexer, Span, Token};
