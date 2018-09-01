use std::cmp::PartialEq;
use std::fmt::Debug;

use super::tokenizer::*;

// https://jakewheat.github.io/sql-overview/sql-2011-foundation-grammar.html

/// ANSI SQL:2011 Data Types
#[derive(Debug)]
pub enum SQLDataType<T> {
    /// BOOLEAN
    Boolean,
    /// NUMERIC, DECIMAL, DEC
    Numeric { precision: usize, scale: Option<usize> },
    /// SMALLINT
    SmallInt,
    /// INT, INTEGER
    Int,
    /// BIGINT
    BigInt,
    /// Floating point: `FLOAT(precision)`
    Float(usize),
    /// REAL
    Real,
    /// Double: `DOUBLE PRECISION`
    Double,
    /// Fixed-length character. `CHAR, CHARACTER`
    Char(usize),
    /// Variable-length character: `VARCHAR, CHARACTER VARYING, CHAR VARYING`
    VarChar(usize),
    /// Character Large Object: `CHARACTER LARGE OBJECT, CHAR LARGE OBJECT, CLOB`
    Clob(usize),
    /// Fixed-length character. `NCHAR, NATIONAL CHAR, NATIONAL CHARACTER`
    NChar(usize),
    /// Variable-length character: `NCHAR VARYING, NATIONAL CHARACTER VARYING, NATIONAL CHAR VARYING`
    NVarChar(usize),
    /// National Character Large Object: `NATIONAL CHARACTER LARGE OBJECT, NCHAR LARGE OBJECT, NCLOB`
    NClob(usize),
    /// Fixed-length binary
    Binary(usize),
    /// Variable-length binary
    VarBinary(usize),
    /// Binary large object
    Blob(usize),
    /// Date
    Date,
    /// Time: `TIME [(precision)] [WITH TIME ZONE | WITHOUT TIME ZONE]`
    Time { precision: usize, tz: bool },
    /// Time: `TIMESTAMP [(precision)] [WITH TIME ZONE | WITHOUT TIME ZONE]`
    Timestamp { precision: usize, tz: bool },
    /// Custom data type
    Custom(T)
}



#[derive(Debug)]
pub enum SQLOperator<T> {
    Plus,
    Minus,
    Mult,
    Div,
    Eq,
    Gt,
    GtEq,
    Lt,
    LtEq,
    Custom(T) // extension point for vendor-specific operators
}

/// SQL Expressions
#[derive(Debug)]
pub enum SQLExpr<T> {
    /// Identifier e.g. table name or column name
    Identifier(String),
    /// Literal value
    Literal(String),
    /// Binary expression e.g. `1 + 2` or `fname LIKE "A%"`
    Binary(Box<SQLExpr<T>>, SQLOperator<T>, Box<SQLExpr<T>>),
    /// Function invocation with function name and list of argument expressions
    FunctionCall(String, Vec<SQLExpr<T>>),
    Insert,
    Update,
    Delete,
    Select,
    CreateTable,
    /// Custom expression (vendor-specific)
    Custom(T)
}

#[derive(Debug)]
pub enum ParserError<S, PE>
    where S: Debug + PartialEq {

    WrongToken { expected: Vec<SQLToken<S>>, actual: SQLToken<S>, line: usize, col: usize },
    Custom(PE)
}

impl<S, TE> From<TokenizerError<TE>> for ParserError<S, TE>
    where S: Debug + PartialEq {

    fn from(_: TokenizerError<TE>) -> Self {
        unimplemented!()
    }
}


trait Parser<S, PE>
    where S: Debug + PartialEq {

    /// parse the prefix and stop once an infix operator is reached
    fn parse_prefix(&mut self) -> Result<Box<SQLExpr<S>>, ParserError<S, PE>> ;
    /// parse the next infix expression, returning None if the precedence has changed
    fn parse_infix(&mut self, left: SQLExpr<S>) -> Result<Option<Box<SQLExpr<S>>>, ParserError<S, PE>>;
}

//
//
//struct GenericParser {
//    tokenizer: SQLTokenizer
//}
//
//impl GenericParser {
//
//    fn parse_expr(&mut self, precedence: u8) -> Result<Box<SQLExpr>, ParserError> {
//
//        let mut expr = self.parse_prefix()?;
//
//        // loop while there are more tokens and until the precedence changes
//        while let Some(token) = self.tokenizer.peek_token()? {
//
//            let next_precedence = self.get_precedence(&token);
//
//            if precedence >= next_precedence {
//                break;
//            }
//
//            expr = self.parse_infix(expr, next_precedence)?;
//        }
//
//        Ok(expr)
//    }
//
//    fn parse_prefix(&mut self) -> Result<Box<SQLExpr>, ParserError> {
//
//        match self.tokenizer.peek_token()? {
//            Some(SQLToken::Keyword(ref k)) => match k.to_uppercase().as_ref() {
//                "INSERT" => unimplemented!(),
//                "UPDATE" => unimplemented!(),
//                "DELETE" => unimplemented!(),
//                "SELECT" => unimplemented!(),
//                "CREATE" => unimplemented!(),
//                _ => unimplemented!()
//            },
//            _ => unimplemented!()
//        }
//        unimplemented!()
//    }
//
//    fn parse_infix(&mut self, expr: Box<SQLExpr>, precedence: u8) -> Result<Box<SQLExpr>, ParserError> {
//
//        match self.tokenizer.next_token()? {
//            Some(tok) => {
//                match tok {
//                    SQLToken::Eq | SQLToken::Gt | SQLToken::GtEq |
//                    SQLToken::Lt | SQLToken::LtEq => Ok(Box::new(SQLExpr::Binary(
//                        expr,
//                        self.to_sql_operator(&tok),
//                        self.parse_expr(precedence)?
//                    ))),
//                    _ => Err(ParserError::WrongToken {
//                        expected: vec![SQLToken::Eq, SQLToken::Gt], //TODO: complete
//                        actual: tok,
//                        line: 0,
//                        col: 0
//                    })
//                }
//            },
//            None => Err(ParserError::TBD)
//        }
//    }
//
//    fn to_sql_operator(&self, token: &SQLToken) -> SQLOperator {
//        unimplemented!()
//    }
//
//    fn get_precedence(&self, token: &SQLToken) -> u8 {
//        unimplemented!()
//    }
//
//    /// parse a list of SQL expressions separated by a comma
//    fn parse_expr_list(&mut self, precedence: u8) -> Result<Vec<SQLExpr>, ParserError> {
//        unimplemented!()
//    }
//
//}
//
////impl GenericParser {
////
////    fn tokenizer(&mut self) -> &mut SQLTokenizer {
////        &mut self.tokenizer
////    }
////
////    fn parse_keywords(&mut self, keywords: Vec<&str>) -> Result<bool, ParserError> {
////        unimplemented!()
////    }
////
//////    fn parse_identifier(&mut self) -> Result<String, ParserError>;
////
////}
//

//
//
//#[cfg(test)]
//mod tests {
//
//    use super::SQLToken::*;
//    use super::*;
//    #[test]
//    fn parse_Acme_create_table() {
//
//        // CREATE TABLE test (col1 int8) HASH (col1)
//        let tokens = vec![
//            k("CREATE"), k("TABLE"), i("test"), LParen,
//            i("col1"), k("int8"),
//            RParen,
//            k("HASH"), LParen, i("col1"), RParen
//        ];
//
//        //let parser = AcmeParser { generic_parser: }
//    }
//    }
//
//    fn k(s: &str) -> SQLToken {
//        Keyword(s.to_string())
//    }
//
//    fn i(s: &str) -> SQLToken {
//        Identifier(s.to_string())
//    }
//
//
//}


