// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! MySQL mysqldump stream processor / mutator in Rust
//!
//! This crate allows to parse and the insert values of a mysqldump file
//! and change them on the fly. Its intended usage is to anonymize a
//! mysqldump backup in order to safely allow to be shared between
//! developers.
//!
//! ```rust,no_run
//! use mysqldump_mutator::{InsertContext, Parser, SQLContextType, Token};
//! # use std::fs::File;
//! # use std::io::{self, BufReader};
//! # fn main() -> io::Result<()> {
//! # let file: String = std::env::args().collect::<Vec<String>>()[1].clone();
//!
//! let _ = Parser::parse_mysqldump(
//!     BufReader::new(File::open(&file)?),
//!     |context, token| match context {
//!         // You can get the origial token content with token.to_string()
//!         // Check the Token struct methods
//!         SQLContextType::Insert(InsertContext::Value((table_name, column_index)))
//!             if table_name == "users" && column_index == &3 =>
//!         {
//!             // You can change the value of the column in an inser.  
//!             // Columns are identifies by index.  
//!             Token::new(&"[REDACTED]".to_string(), Some('\''))
//!         }
//!         SQLContextType::ColumnDefinition((_table_name, _column_name, _column_index)) => {
//!             // Here you can take note of what index is each column in each table.
//! #           token
//!         }
//!         _ => token, // Or just return the original token
//!     },
//!     |tokens| {
//!         for token in tokens {
//!             // Token has implemented the Display trait.
//!             // Given that no token was replaced, this would generate an output.  
//!             // byte-by-byte equal to the input.  
//!             print!("{}", token)
//!         }
//!     },
//! );
//! # Ok(())
//! # }
//! ```
//!

#![warn(clippy::all)]
#![forbid(unsafe_code)]

mod ast;
mod dialect;
mod parser;
mod tokenizer;

pub use parser::Parser;
pub use parser::{InsertContext, SQLContextType};
pub use tokenizer::Token;
