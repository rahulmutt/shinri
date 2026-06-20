//! SMT-LIB 2.6 frontend: logos lexer + interning recursive descent (design §9.1).

mod env;
mod lexer;
mod parser;

pub use env::{Env, Macro};
pub use lexer::{Lexer, Span, Token};
pub use parser::{Diagnostic, Parser};
