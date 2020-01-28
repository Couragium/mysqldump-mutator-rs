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

use crate::ast::Ident;
#[cfg(feature = "bigdecimal")]
use bigdecimal::BigDecimal;
use std::fmt;

/// Primitive SQL values such as number and string
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Value {
    /// Numeric literal
    #[cfg(not(feature = "bigdecimal"))]
    Number(String),
    #[cfg(feature = "bigdecimal")]
    Number(BigDecimal),
    /// 'string value'
    SingleQuotedString(String),
    /// N'string value'
    NationalStringLiteral(String),
    /// X'hex value'
    HexStringLiteral(String),
    /// Boolean value true or false
    Boolean(bool),
    Identifier(Ident),
    /// `NULL` value
    Null,
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Value::Number(v) => write!(f, "{}", v),
            Value::SingleQuotedString(v) => write!(f, "'{}'", escape_single_quote_string(v)),
            Value::NationalStringLiteral(v) => write!(f, "N'{}'", v),
            Value::HexStringLiteral(v) => write!(f, "X'{}'", v),
            Value::Boolean(v) => write!(f, "{}", v),
            Value::Identifier(i) => write!(f, "{}", i),
            Value::Null => write!(f, "NULL"),
        }
    }
}

pub struct EscapeSingleQuoteString<'a>(&'a str);

impl<'a> fmt::Display for EscapeSingleQuoteString<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for c in self.0.chars() {
            if c == '\'' {
                write!(f, "\'\'")?;
            } else {
                write!(f, "{}", c)?;
            }
        }
        Ok(())
    }
}

pub fn escape_single_quote_string(s: &str) -> EscapeSingleQuoteString<'_> {
    EscapeSingleQuoteString(s)
}
