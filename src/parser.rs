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

//! SQL Parser

use log::debug;

use super::ast::*;
use super::dialect::keywords;
use super::dialect::Dialect;
use super::tokenizer::*;
use std::error::Error;
use std::fmt;

#[derive(Debug, Clone, PartialEq)]
pub enum ParserError {
    TokenizerError(String),
    ParserError(String),
    Ignored,
    End,
}

// Use `Parser::expected` instead, if possible
macro_rules! parser_err {
    ($MSG:expr) => {
        Err(ParserError::ParserError($MSG.to_string()))
    };
}

#[derive(PartialEq)]
pub enum IsOptional {
    Optional,
    Mandatory,
}
use IsOptional::*;

pub enum IsLateral {
    Lateral,
    NotLateral,
}

impl From<TokenizerError> for ParserError {
    fn from(e: TokenizerError) -> Self {
        ParserError::TokenizerError(format!("{:?}", e))
    }
}

impl fmt::Display for ParserError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "sql parser error: {}",
            match self {
                ParserError::TokenizerError(s) => s,
                ParserError::ParserError(s) => s,
                ParserError::Ignored => "Ignored",
                ParserError::End => "EOF",
            }
        )
    }
}

impl Error for ParserError {}

#[derive(Debug, Clone)]
enum SQLContextType {
    None,
    CreateTable(String),
    ColumnDefinition((String, String, usize)),
    Insert(InsertContext),
}

#[derive(Debug, Clone)]
enum InsertContext {
    None,
    Table(String),
    Value((String, usize)),
}

#[derive(Debug)]
pub struct SQLContext {
    context: SQLContextType,
}

impl Default for SQLContext {
    fn default() -> Self {
        SQLContext::new()
    }
}

impl SQLContext {
    pub fn new() -> SQLContext {
        debug!("SQLContext::new");
        SQLContext {
            context: SQLContextType::None,
        }
    }

    fn started_create_table(&mut self, table: String) {
        debug!("started_create_table {:?} {}", self.context, table);

        if let SQLContextType::None = self.context {
            return self.context = SQLContextType::CreateTable(table);
        }

        panic!("Invalid context state");
    }

    fn ended_create_table(&mut self) {
        debug!("ended_create_table {:?}", self.context);

        if let SQLContextType::CreateTable(_) = self.context {
            return self.context = SQLContextType::None;
        }

        panic!("Invalid context state");
    }

    fn started_column_definition(&mut self, column: String, index: usize) {
        debug!(
            "started_column_definition {:?} {} {}",
            self.context, column, index
        );

        if let SQLContextType::CreateTable(table) = &self.context {
            return self.context = SQLContextType::ColumnDefinition((table.clone(), column, index));
        }

        panic!("Invalid context state");
    }

    fn ended_column_definition(&mut self) {
        debug!("ended_column_definition {:?}", self.context);

        if let SQLContextType::ColumnDefinition((table, _, _)) = &self.context {
            return self.context = SQLContextType::CreateTable(table.clone());
        }

        panic!("Invalid context state");
    }

    fn started_insert(&mut self) {
        debug!("started_insert {:?}", self.context);

        if let SQLContextType::None = self.context {
            return self.context = SQLContextType::Insert(InsertContext::None);
        }

        panic!("Invalid context state");
    }

    fn ended_insert(&mut self) {
        debug!("ended_insert {:?}", self.context);

        if let SQLContextType::Insert(_) = self.context {
            return self.context = SQLContextType::None;
        }

        panic!("Invalid context state");
    }

    fn started_insert_table(&mut self, table: String) {
        debug!("started_insert_table {:?} {}", self.context, table);

        if let SQLContextType::Insert(InsertContext::None) = self.context {
            return self.context = SQLContextType::Insert(InsertContext::Table(table));
        }

        panic!("Invalid context state");
    }

    fn ended_insert_table(&mut self) {
        debug!("ended_insert_table");

        if let SQLContextType::Insert(InsertContext::Table(_)) = self.context {
            return self.context = SQLContextType::Insert(InsertContext::None);
        }

        panic!("Invalid context state");
    }

    fn started_insert_value(&mut self, column: usize) {
        debug!("started_insert_value {:?} {}", self.context, column);

        if let SQLContextType::Insert(InsertContext::Table(table)) = &self.context {
            return self.context =
                SQLContextType::Insert(InsertContext::Value((table.clone(), column)));
        }

        panic!("Invalid context state");
    }

    fn ended_insert_value(&mut self) {
        debug!("ended_insert_value {:?}", self.context);

        if let SQLContextType::Insert(InsertContext::Value((table, _))) = &self.context {
            return self.context = SQLContextType::Insert(InsertContext::Table(table.clone()));
        }

        panic!("Invalid context state");
    }
}

/// SQL Parser
pub struct Parser<'a> {
    index: usize,
    commited_tokens: Vec<Token>,
    tokenizer: Tokenizer<'a>,
    last_tokens: Vec<Token>,
    context: SQLContext,
    value_handler: Option<&'a dyn Fn(&SQLContext, Token) -> Token>,
    commit_handler: Option<&'a dyn Fn(&[Token])>,
}

impl<'a> Parser<'a> {
    /// Parse the specified tokens
    pub fn new(
        dialect: &'a (dyn Dialect + 'a),
        sql: &'a mut dyn std::io::BufRead,
        handler: &'a dyn Fn(&SQLContext, Token) -> Token,
        commit_handler: &'a dyn Fn(&[Token]),
    ) -> Self {
        Parser {
            index: 0,
            commited_tokens: vec![],
            tokenizer: Tokenizer::new(dialect, sql),
            last_tokens: vec![],
            context: SQLContext::new(),
            value_handler: Some(handler),
            commit_handler: Some(commit_handler),
        }
    }

    /// Parse a SQL statement and produce an Abstract Syntax Tree (AST)
    pub fn parse_sql(
        dialect: &dyn Dialect,
        sql: &mut dyn std::io::BufRead,
        handler: &'a dyn Fn(&SQLContext, Token) -> Token,
        commit_handler: &'a dyn Fn(&[Token]),
    ) -> Result<Vec<Statement>, ParserError> {
        let mut parser = Parser::new(dialect, sql, handler, commit_handler);
        let mut stmts = Vec::new();
        let mut expecting_statement_delimiter = false;

        loop {
            // ignore empty statements (between successive statement delimiters)
            while parser.consume_token(&Token::SemiColon) {
                expecting_statement_delimiter = false;
            }

            if parser.peek_token().is_none() {
                break;
            } else if expecting_statement_delimiter {
                let token = parser.peek_token();
                return parser.expected("end of statement", token);
            }

            let result = parser.parse_statement();

            parser.commit_tokens();

            if let Err(ParserError::Ignored) = result {
                continue;
            }

            if let Err(error) = result {
                return Err(error);
            }

            if let Ok(statement) = result {
                stmts.push(statement);
                expecting_statement_delimiter = true;
            }
        }
        Ok(stmts)
    }

    /// Parse a single top-level statement (such as SELECT, INSERT, CREATE, etc.),
    /// stopping before the statement separator, if any.
    fn parse_statement(&mut self) -> Result<Statement, ParserError> {
        match self.next_token() {
            Some(Token::Word(ref w)) if w.keyword != "" => match w.keyword.as_ref() {
                "CREATE" => Ok(self.parse_create()?),
                "INSERT" => Ok(self.parse_insert()?),
                _ => Err(ParserError::Ignored),
            },
            None => Err(ParserError::End),
            _ => Err(ParserError::Ignored),
            // TODO: Diferenciate between None and Some with other value
        }
    }

    /// Parse a new expression
    fn parse_expr(&mut self) -> Result<Expr, ParserError> {
        self.parse_subexpr(0)
    }

    /// Parse tokens until the precedence changes
    fn parse_subexpr(&mut self, precedence: u8) -> Result<Expr, ParserError> {
        debug!("parsing expr");
        let mut expr = self.parse_prefix()?;
        debug!("prefix: {:?}", expr);
        loop {
            let next_precedence = self.get_next_precedence()?;
            //debug!("next precedence: {:?}", next_precedence);
            if precedence >= next_precedence {
                break;
            }

            expr = self.parse_infix(expr, next_precedence)?;
        }
        Ok(expr)
    }

    /// Parse an expression prefix
    fn parse_prefix(&mut self) -> Result<Expr, ParserError> {
        let tok = self
            .next_token()
            .ok_or_else(|| ParserError::ParserError("Unexpected EOF".to_string()))?;
        let expr = match tok {
            Token::Word(w) => match w.keyword.as_ref() {
                "TRUE" | "FALSE" | "NULL" => {
                    self.prev_token();
                    Ok(Expr::Value(self.parse_value()?))
                }
                // Here `w` is a word, check if it's a part of a multi-part
                // identifier, a function call, or a simple identifier:
                _ => Ok(Expr::Identifier(w.to_ident())),
            },
            Token::Number(_)
            | Token::SingleQuotedString(_)
            | Token::NationalStringLiteral(_)
            | Token::HexStringLiteral(_) => {
                self.prev_token();
                Ok(Expr::Value(self.parse_value()?))
            }
            unexpected => self.expected("an expression", Some(unexpected)),
        }?;

        if self.parse_keyword("COLLATE") {
            Ok(Expr::Collate {
                expr: Box::new(expr),
                collation: self.parse_object_name()?,
            })
        } else {
            Ok(expr)
        }
    }

    /// Parse an operator following an expression
    fn parse_infix(&mut self, expr: Expr, precedence: u8) -> Result<Expr, ParserError> {
        debug!("parsing infix");
        let tok = self.next_token().unwrap(); // safe as EOF's precedence is the lowest

        let regular_binary_operator = match tok {
            Token::Eq => Some(BinaryOperator::Eq),
            Token::Neq => Some(BinaryOperator::NotEq),
            Token::Gt => Some(BinaryOperator::Gt),
            Token::GtEq => Some(BinaryOperator::GtEq),
            Token::Lt => Some(BinaryOperator::Lt),
            Token::LtEq => Some(BinaryOperator::LtEq),
            Token::Plus => Some(BinaryOperator::Plus),
            Token::Minus => Some(BinaryOperator::Minus),
            Token::Mult => Some(BinaryOperator::Multiply),
            Token::Mod => Some(BinaryOperator::Modulus),
            Token::Div => Some(BinaryOperator::Divide),
            Token::Word(ref k) => match k.keyword.as_ref() {
                "AND" => Some(BinaryOperator::And),
                "OR" => Some(BinaryOperator::Or),
                "LIKE" => Some(BinaryOperator::Like),
                "NOT" => {
                    if self.parse_keyword("LIKE") {
                        Some(BinaryOperator::NotLike)
                    } else {
                        None
                    }
                }
                _ => None,
            },
            _ => None,
        };

        if let Some(op) = regular_binary_operator {
            Ok(Expr::BinaryOp {
                left: Box::new(expr),
                op,
                right: Box::new(self.parse_subexpr(precedence)?),
            })
        } else if let Token::Word(ref k) = tok {
            match k.keyword.as_ref() {
                "IS" => {
                    if self.parse_keyword("NULL") {
                        Ok(Expr::IsNull(Box::new(expr)))
                    } else if self.parse_keywords(&["NOT", "NULL"]) {
                        Ok(Expr::IsNotNull(Box::new(expr)))
                    } else {
                        let token = self.peek_token();
                        self.expected("NULL or NOT NULL after IS", token)
                    }
                }
                "NOT" | "IN" | "BETWEEN" => {
                    self.prev_token();
                    let negated = self.parse_keyword("NOT");
                    if self.parse_keyword("IN") {
                        self.parse_in(expr, negated)
                    } else if self.parse_keyword("BETWEEN") {
                        self.parse_between(expr, negated)
                    } else {
                        let token = self.peek_token();
                        self.expected("IN or BETWEEN after NOT", token)
                    }
                }
                // Can only happen if `get_next_precedence` got out of sync with this function
                _ => panic!("No infix parser for token {:?}", tok),
            }
        } else if Token::DoubleColon == tok {
            self.parse_pg_cast(expr)
        } else {
            // Can only happen if `get_next_precedence` got out of sync with this function
            panic!("No infix parser for token {:?}", tok)
        }
    }

    /// Parses the parens following the `[ NOT ] IN` operator
    fn parse_in(&mut self, expr: Expr, negated: bool) -> Result<Expr, ParserError> {
        self.expect_token(&Token::LParen)?;
        let in_op = if self.parse_keyword("SELECT") || self.parse_keyword("WITH") {
            self.prev_token();
            Expr::InSubquery {
                expr: Box::new(expr),
                subquery: Box::new(self.parse_query()?),
                negated,
            }
        } else {
            Expr::InList {
                expr: Box::new(expr),
                list: self.parse_comma_separated(|parser| parser.parse_expr())?,
                negated,
            }
        };
        self.expect_token(&Token::RParen)?;
        Ok(in_op)
    }

    /// Parses `BETWEEN <low> AND <high>`, assuming the `BETWEEN` keyword was already consumed
    fn parse_between(&mut self, expr: Expr, negated: bool) -> Result<Expr, ParserError> {
        // Stop parsing subexpressions for <low> and <high> on tokens with
        // precedence lower than that of `BETWEEN`, such as `AND`, `IS`, etc.
        let low = self.parse_subexpr(Self::BETWEEN_PREC)?;
        self.expect_keyword("AND")?;
        let high = self.parse_subexpr(Self::BETWEEN_PREC)?;
        Ok(Expr::Between {
            expr: Box::new(expr),
            negated,
            low: Box::new(low),
            high: Box::new(high),
        })
    }

    /// Parse a postgresql casting style which is in the form of `expr::datatype`
    fn parse_pg_cast(&mut self, expr: Expr) -> Result<Expr, ParserError> {
        Ok(Expr::Cast {
            expr: Box::new(expr),
            data_type: self.parse_data_type()?,
        })
    }

    const BETWEEN_PREC: u8 = 20;
    const PLUS_MINUS_PREC: u8 = 30;

    /// Get the precedence of the next token
    fn get_next_precedence(&mut self) -> Result<u8, ParserError> {
        if let Some(token) = self.peek_token() {
            debug!("get_next_precedence() {:?}", token);

            match &token {
                Token::Word(k) if k.keyword == "OR" => Ok(5),
                Token::Word(k) if k.keyword == "AND" => Ok(10),
                Token::Word(k) if k.keyword == "NOT" => Ok(0),
                Token::Word(k) if k.keyword == "IS" => Ok(17),
                Token::Word(k) if k.keyword == "IN" => Ok(Self::BETWEEN_PREC),
                Token::Word(k) if k.keyword == "BETWEEN" => Ok(Self::BETWEEN_PREC),
                Token::Word(k) if k.keyword == "LIKE" => Ok(Self::BETWEEN_PREC),
                Token::Eq | Token::Lt | Token::LtEq | Token::Neq | Token::Gt | Token::GtEq => {
                    Ok(20)
                }
                Token::Plus | Token::Minus => Ok(Self::PLUS_MINUS_PREC),
                Token::Mult | Token::Div | Token::Mod => Ok(40),
                Token::DoubleColon => Ok(50),
                _ => Ok(0),
            }
        } else {
            Ok(0)
        }
    }

    /// Return the first non-whitespace token that has not yet been processed
    /// (or None if reached end-of-file)
    fn peek_token(&mut self) -> Option<Token> {
        self.peek_nth_token(0)
    }

    /// Return nth non-whitespace token that has not yet been processed
    fn peek_nth_token(&mut self, mut n: usize) -> Option<Token> {
        let mut index = self.index;
        loop {
            index += 1;
            match self.tokenizer.peek_token(index - self.index - 1) {
                Ok(Some(Token::Whitespace(_))) => continue,
                Ok(non_whitespace) => {
                    if n == 0 {
                        return non_whitespace;
                    }
                    n -= 1;
                }
                _ => return None,
            }
        }
    }

    fn check_ahead<F>(&mut self, max: usize, check_fn: F) -> bool
    where
        F: Fn(&Token) -> bool,
    {
        for n in 0..max {
            let found_token = self.peek_nth_token(n);
            if let Some(found_token) = found_token {
                if check_fn(&found_token) {
                    return true;
                }
            }
        }

        false
    }

    fn execute_value_handler(&mut self) {
        let token = self.commited_tokens.pop();

        if let Some(token) = token {
            if let Some(value_handler) = self.value_handler {
                let token = value_handler(&self.context, token);

                if self.last_tokens.pop().is_some() {
                    self.last_tokens.push(token.clone());
                }

                self.commited_tokens.push(token);
            } else {
                self.commited_tokens.push(token);
            }
        }
    }

    /// Return the first non-whitespace token that has not yet been processed
    /// (or None if reached end-of-file) and mark it as processed. OK to call
    /// repeatedly after reaching EOF.
    fn next_token(&mut self) -> Option<Token> {
        self.last_tokens.truncate(0);
        loop {
            self.index += 1;
            match self.tokenizer.next_token() {
                Ok(Some(Token::Whitespace(token))) => {
                    self.last_tokens.push(Token::Whitespace(token.clone()));
                    self.commited_tokens.push(Token::Whitespace(token.clone()));
                    continue;
                }
                Ok(Some(token)) => {
                    self.last_tokens.push(token.clone());
                    self.commited_tokens.push(token.clone());
                    return Some(token);
                }
                _ => return None,
            }
        }
    }

    /// Push back the last one non-whitespace token. Must be called after
    /// `next_token()`, otherwise might panic. OK to call after
    /// `next_token()` indicates an EOF.
    fn prev_token(&mut self) {
        self.last_tokens.reverse();
        for token in self.last_tokens.drain(0..) {
            self.commited_tokens.pop();
            let token = token.clone();
            self.tokenizer.pushback_token(token);
        }
    }

    fn commit_tokens(&mut self) {
        self.last_tokens.truncate(0);
        for token in self.commited_tokens.drain(0..) {
            if let Some(handler) = self.commit_handler {
                handler(&[token]);
            }
        }
    }

    /// Report unexpected token
    fn expected<T>(&self, expected: &str, found: Option<Token>) -> Result<T, ParserError> {
        parser_err!(format!(
            "Expected {}, found: {}",
            expected,
            found.map_or_else(|| "EOF".to_string(), |t| format!("{}", t))
        ))
    }

    /// Look for an expected keyword and consume it if it exists
    #[must_use]
    fn parse_keyword(&mut self, expected: &'static str) -> bool {
        // Ideally, we'd accept a enum variant, not a string, but since
        // it's not trivial to maintain the enum without duplicating all
        // the keywords three times, we'll settle for a run-time check that
        // the string actually represents a known keyword...
        assert!(keywords::ALL_KEYWORDS.contains(&expected));
        match self.peek_token() {
            Some(Token::Word(ref k)) if expected.eq_ignore_ascii_case(&k.keyword) => {
                self.next_token();
                true
            }
            _ => false,
        }
    }

    /// Look for an expected sequence of keywords and consume them if they exist
    #[must_use]
    // TODO: Fix the index rollback. It should use keywords pushback.
    fn parse_keywords(&mut self, keywords: &[&'static str]) -> bool {
        let mut parse_keywords = true;

        for (index, word) in keywords.iter().enumerate() {
            let found_token = self.peek_nth_token(index);

            match found_token {
                Some(Token::Word(found_word)) if found_word.keyword == *word => {},
                _ => {
                    parse_keywords = false;
                    break;
                }
            }
        }

        if parse_keywords {
            for (_, word) in keywords.iter().enumerate() {
                if !self.parse_keyword(word) {
                    return false;
                }
            }
            return true;
        }

        false
    }

    /// Bail out if the current token is not an expected keyword, or consume it if it is
    fn expect_keyword(&mut self, expected: &'static str) -> Result<(), ParserError> {
        let token = self.peek_token();
        if self.parse_keyword(expected) {
            Ok(())
        } else {
            self.expected(expected, token)
        }
    }

    /// Bail out if the following tokens are not the expected sequence of
    /// keywords, or consume them if they are.
    fn expect_keywords(&mut self, expected: &[&'static str]) -> Result<(), ParserError> {
        for kw in expected {
            self.expect_keyword(kw)?;
        }
        Ok(())
    }

    /// Consume the next token if it matches the expected token, otherwise return false
    #[must_use]
    fn consume_token(&mut self, expected: &Token) -> bool {
        match &self.peek_token() {
            Some(t) if *t == *expected => {
                self.next_token();
                true
            }
            _ => false,
        }
    }

    /// Bail out if the current token is not an expected keyword, or consume it if it is
    fn expect_token(&mut self, expected: &Token) -> Result<(), ParserError> {
        let token = self.peek_token();
        if self.consume_token(expected) {
            Ok(())
        } else {
            self.expected(&expected.to_string(), token)
        }
    }

    /// Parse a comma-separated list of 1+ items accepted by `F`
    fn parse_comma_separated<T, F>(&mut self, mut f: F) -> Result<Vec<T>, ParserError>
    where
        F: FnMut(&mut Parser) -> Result<T, ParserError>,
    {
        let mut values = vec![];
        loop {
            values.push(f(self)?);
            if !self.consume_token(&Token::Comma) {
                break;
            }
        }
        Ok(values)
    }

    /// Parse a SQL CREATE statement
    fn parse_create(&mut self) -> Result<Statement, ParserError> {
        if self.is_after_newline() {
            if self.parse_keyword("TABLE") {
                return self.parse_create_table();
            } else if self.check_ahead(15, |token| match token {
                Token::Word(word) if word.keyword == "PROCEDURE" => true,
                _ => false,
            }) {
                self.take_create_procedure();
                return Err(ParserError::Ignored);
            }
        };

        Err(ParserError::Ignored)
    }

    fn is_after_newline(&mut self) -> bool {
        if let Token::Whitespace(Whitespace::Newline) = self.last_tokens[self.last_tokens.len() - 2]
        {
            true
        } else {
            false
        }
    }

    fn take_create_procedure(&mut self) {
        //take until BEGIN
        //TAKE UNTIL END
        //  IN CASE OF IF OR LOOP, take until END IF or END LOOP recursively.
        self.take_until(40, |_parser, token| match token {
            Token::Word(word) if word.keyword == "BEGIN" => true,
            _ => false,
        });
        self.next_token();
        self.take_until(20000, |parser, token| match token {
            Token::Word(_) if parser.peek_if_control_flow_start() => {
                parser.take_control_flow_block();
                true
            }
            Token::Word(word) if word.keyword == "END" => false,
            _ => true,
        });
    }

    fn take_control_flow_block(&mut self) {
        let end_tokens = match self.next_token() {
            Some(Token::Word(word)) if word.keyword == "IF" => vec!["END", "IF"],
            Some(Token::Word(word)) if word.keyword == "LOOP" => vec!["END", "LOOP"],
            Some(Token::Word(word)) if word.keyword == "BEGIN" => vec!["END"],
            _ => return,
        };

        loop {
            match self.peek_token() {
                Some(Token::Word(_)) if self.peek_if_control_flow_start() => {
                    self.take_control_flow_block();
                }
                Some(_) => {
                    if self.parse_keywords(&end_tokens) {
                        return;
                    }

                    self.next_token();
                }
                None => break,
            }
        }
    }

    fn peek_if_control_flow_start(&mut self) -> bool {
        match self.peek_token() {
            Some(Token::Word(word))
                if word.keyword == "IF" || word.keyword == "LOOP" || word.keyword == "BEGIN" =>
            {
                true
            }
            _ => false,
        }
    }

    fn parse_create_table(&mut self) -> Result<Statement, ParserError> {
        let table_name = self.parse_object_name()?;
        self.context.started_create_table(format!("{}", table_name));
        // parse optional column list (schema)
        let (columns, constraints) = self.parse_columns()?;

        let with_options = self.parse_with_options()?;

        self.context.ended_create_table();

        Ok(Statement::CreateTable {
            name: table_name,
            columns,
            constraints,
            with_options,
            external: false,
            file_format: None,
            location: None,
        })
    }

    fn take_until<F>(&mut self, max: usize, check_fn: F)
    where
        F: Fn(&mut Parser, &Token) -> bool,
    {
        for _ in 0..max {
            match self.peek_token() {
                Some(token) if check_fn(self, &token) => self.next_token(),
                _ => return,
            };
        }
    }

    fn parse_columns(&mut self) -> Result<(Vec<ColumnDef>, Vec<TableConstraint>), ParserError> {
        let mut columns = vec![];
        let mut constraints = vec![];
        if !self.consume_token(&Token::LParen) || self.consume_token(&Token::RParen) {
            return Ok((columns, constraints));
        }

        loop {
            debug!("Parsing column! :D");
            if let Some(constraint) = self.parse_optional_table_constraint()? {
                debug!("Is a optional table constrain! {:?}", constraint);
                constraints.push(constraint);
            } else if let Some(Token::Word(column_name)) = self.peek_token() {
                self.context
                    .started_column_definition(format!("{}", column_name), columns.len());

                self.next_token();

                self.execute_value_handler();

                let data_type = self.parse_data_type()?;

                let data_config = if let Some(Token::LParen) = self.peek_token() {
                    self.parse_data_config()?
                } else {
                    vec![]
                };
                let collation = if self.parse_keyword("COLLATE") {
                    Some(self.parse_object_name()?)
                } else {
                    None
                };
                let mut options = vec![];
                loop {
                    let token = self.peek_token();
                    match token {
                        None | Some(Token::Comma) | Some(Token::RParen) => break,
                        _ => options.push(self.parse_column_option_def()?),
                    }
                }

                columns.push(ColumnDef {
                    name: column_name.to_ident(),
                    data_type,
                    data_config,
                    collation,
                    options,
                });

                self.context.ended_column_definition();
            } else {
                let token = self.peek_token();
                return self.expected("column name or constraint definition", token);
            }
            let comma = self.consume_token(&Token::Comma);
            if self.consume_token(&Token::RParen) {
                // allow a trailing comma, even though it's not in standard
                break;
            } else if !comma {
                let token = self.peek_token();
                return self.expected("',' or ')' after column definition", token);
            }
        }

        Ok((columns, constraints))
    }

    fn parse_column_option_def(&mut self) -> Result<ColumnOptionDef, ParserError> {
        let name = if self.parse_keyword("CONSTRAINT") {
            Some(self.parse_identifier()?)
        } else {
            None
        };

        let option = if self.parse_keywords(&["NOT", "NULL"]) {
            ColumnOption::NotNull
        } else if self.parse_keyword("NULL") {
            ColumnOption::Null
        } else if self.parse_keyword("AUTO_INCREMENT") {
            ColumnOption::Autoincrement
        } else if self.parse_keyword("DEFAULT") {
            ColumnOption::Default(self.parse_expr()?)
        } else if self.parse_keywords(&["PRIMARY", "KEY"]) {
            ColumnOption::Unique { is_primary: true }
        } else if self.parse_keyword("UNIQUE") {
            ColumnOption::Unique { is_primary: false }
        } else if self.parse_keyword("REFERENCES") {
            let foreign_table = self.parse_object_name()?;
            let referred_columns = self.parse_parenthesized_column_list(Mandatory)?;
            ColumnOption::ForeignKey {
                foreign_table,
                referred_columns,
            }
        } else if self.parse_keyword("CHECK") {
            self.expect_token(&Token::LParen)?;
            let expr = self.parse_expr()?;
            self.expect_token(&Token::RParen)?;
            ColumnOption::Check(expr)
        } else {
            let token = self.peek_token();
            return self.expected("column option", token);
        };

        let column_definition = ColumnOptionDef { name, option };

        Ok(column_definition)
    }

    fn parse_optional_table_constraint(&mut self) -> Result<Option<TableConstraint>, ParserError> {
        let name = if self.parse_keyword("CONSTRAINT") {
            Some(self.parse_identifier()?)
        } else {
            None
        };
        match self.next_token() {
            Some(Token::Word(ref k))
                if k.keyword == "PRIMARY" || k.keyword == "UNIQUE" || k.keyword == "KEY" =>
            {
                let is_primary = k.keyword == "PRIMARY";
                if is_primary {
                    self.expect_keyword("KEY")?;
                }

                if k.keyword == "UNIQUE" {
                    let _ = self.consume_token(&Token::Word(Word {
                        value: "KEY".to_string(),
                        quote_style: None,
                        keyword: "KEY".to_string(),
                    }));
                }

                let _index_name = match self.peek_token() {
                    Some(Token::Word(word)) if word.keyword == "" => self.next_token(),
                    _ => None,
                };

                let columns = self.parse_parenthesized_column_list(Mandatory)?;
                Ok(Some(TableConstraint::Unique {
                    name,
                    columns,
                    is_primary,
                }))
            }
            Some(Token::Word(ref k)) if k.keyword == "FOREIGN" => {
                self.expect_keyword("KEY")?;
                let columns = self.parse_parenthesized_column_list(Mandatory)?;
                self.expect_keyword("REFERENCES")?;
                let foreign_table = self.parse_object_name()?;
                let referred_columns = self.parse_parenthesized_column_list(Mandatory)?;
                Ok(Some(TableConstraint::ForeignKey {
                    name,
                    columns,
                    foreign_table,
                    referred_columns,
                }))
            }
            Some(Token::Word(ref k)) if k.keyword == "CHECK" => {
                self.expect_token(&Token::LParen)?;
                let expr = Box::new(self.parse_expr()?);
                self.expect_token(&Token::RParen)?;
                Ok(Some(TableConstraint::Check { name, expr }))
            }
            unexpected => {
                if name.is_some() {
                    self.expected("PRIMARY, UNIQUE, FOREIGN, or CHECK", unexpected)
                } else {
                    self.prev_token();
                    Ok(None)
                }
            }
        }
    }

    fn parse_with_options(&mut self) -> Result<Vec<SqlOption>, ParserError> {
        if self.parse_keyword("WITH") {
            self.expect_token(&Token::LParen)?;
            let options = self.parse_comma_separated(|parser| parser.parse_sql_option())?;
            self.expect_token(&Token::RParen)?;
            Ok(options)
        } else {
            match self.peek_token() {
                Some(Token::Word(word)) if word.keyword != "" => self.parse_mysql_table_options(),
                _ => Ok(vec![]),
            }
        }
    }

    pub fn parse_mysql_table_options(&mut self) -> Result<Vec<SqlOption>, ParserError> {
        let mut options: Vec<SqlOption> = vec![];

        loop {
            let _ = self.parse_keyword("DEFAULT");
            match self.peek_token() {
                Some(Token::Word(word)) if word.keyword != "" => {}
                _ => {
                    break;
                }
            }

            let name = self.parse_identifier()?;
            self.expect_token(&Token::Eq)?;
            let value = self.parse_value()?;
            options.push(SqlOption { name, value });
        }

        Ok(options)
    }

    pub fn parse_sql_option(&mut self) -> Result<SqlOption, ParserError> {
        let name = self.parse_identifier()?;
        self.expect_token(&Token::Eq)?;
        let value = self.parse_value()?;
        Ok(SqlOption { name, value })
    }

    /// Parse a literal value (numbers, strings, date/time, booleans)
    fn parse_value(&mut self) -> Result<Value, ParserError> {
        let token = self.next_token();

        if let SQLContextType::Insert(InsertContext::Value(_)) = self.context.context {
            self.execute_value_handler();
        }

        match token {
            Some(t) => match t {
                Token::Word(k) => match k.keyword.as_ref() {
                    "TRUE" => Ok(Value::Boolean(true)),
                    "FALSE" => Ok(Value::Boolean(false)),
                    "NULL" => Ok(Value::Null),
                    "" => Ok(Value::Identifier(Ident {
                        value: k.value,
                        quote_style: None,
                    })),
                    _ => {
                        return parser_err!(format!("No value parser for keyword {}", k.keyword));
                    }
                },
                // The call to n.parse() returns a bigdecimal when the
                // bigdecimal feature is enabled, and is otherwise a no-op
                // (i.e., it returns the input string).
                Token::Number(ref n) => match n.parse() {
                    Ok(n) => Ok(Value::Number(n)),
                    Err(e) => parser_err!(format!("Could not parse '{}' as number: {}", n, e)),
                },
                Token::SingleQuotedString(ref s) => Ok(Value::SingleQuotedString(s.to_string())),
                Token::NationalStringLiteral(ref s) => {
                    Ok(Value::NationalStringLiteral(s.to_string()))
                }
                Token::HexStringLiteral(ref s) => Ok(Value::HexStringLiteral(s.to_string())),
                _ => parser_err!(format!("Unsupported value: {:?}", t)),
            },
            None => parser_err!("Expecting a value, but found EOF"),
        }
    }

    /// Parse an unsigned literal integer/long
    fn parse_literal_uint(&mut self) -> Result<u64, ParserError> {
        match self.next_token() {
            Some(Token::Number(s)) => s.parse::<u64>().map_err(|e| {
                ParserError::ParserError(format!("Could not parse '{}' as u64: {}", s, e))
            }),
            other => self.expected("literal int", other),
        }
    }

    /// Parse a SQL datatype (in the context of a CREATE TABLE statement for example)
    fn parse_data_type(&mut self) -> Result<DataType, ParserError> {
        match self.next_token() {
            Some(Token::Word(k)) => match k.keyword.as_ref() {
                "BOOLEAN" => Ok(DataType::Boolean),
                "FLOAT" => Ok(DataType::Float(self.parse_optional_precision()?)),
                "REAL" => Ok(DataType::Real),
                "DOUBLE" => {
                    let _ = self.parse_keyword("PRECISION");
                    Ok(DataType::Double)
                }
                "SMALLINT" => Ok(DataType::SmallInt),
                "INT" | "INTEGER" => Ok(DataType::Int),
                "BIGINT" => Ok(DataType::BigInt),
                "VARCHAR" => Ok(DataType::Varchar(self.parse_optional_precision()?)),
                "CHAR" | "CHARACTER" => {
                    if self.parse_keyword("VARYING") {
                        Ok(DataType::Varchar(self.parse_optional_precision()?))
                    } else {
                        Ok(DataType::Char(self.parse_optional_precision()?))
                    }
                }
                "UUID" => Ok(DataType::Uuid),
                "DATE" => Ok(DataType::Date),
                "TIMESTAMP" => {
                    // TBD: we throw away "with/without timezone" information
                    if self.parse_keyword("WITH") || self.parse_keyword("WITHOUT") {
                        self.expect_keywords(&["TIME", "ZONE"])?;
                    }
                    Ok(DataType::Timestamp)
                }
                "TIME" => {
                    // TBD: we throw away "with/without timezone" information
                    if self.parse_keyword("WITH") || self.parse_keyword("WITHOUT") {
                        self.expect_keywords(&["TIME", "ZONE"])?;
                    }
                    Ok(DataType::Time)
                }
                // Interval types can be followed by a complicated interval
                // qualifier that we don't currently support. See
                // parse_interval_literal for a taste.
                "INTERVAL" => Ok(DataType::Interval),
                "REGCLASS" => Ok(DataType::Regclass),
                "TEXT" => {
                    if self.consume_token(&Token::LBracket) {
                        // Note: this is postgresql-specific
                        self.expect_token(&Token::RBracket)?;
                        Ok(DataType::Array(Box::new(DataType::Text)))
                    } else {
                        Ok(DataType::Text)
                    }
                }
                "BYTEA" => Ok(DataType::Bytea),
                "NUMERIC" | "DECIMAL" | "DEC" => {
                    let (precision, scale) = self.parse_optional_precision_scale()?;
                    Ok(DataType::Decimal(precision, scale))
                }
                _ => {
                    self.prev_token();
                    let type_name = self.parse_object_name()?;
                    Ok(DataType::Custom(type_name))
                }
            },
            other => self.expected("a data type name", other),
        }
    }

    /// Parse a SQL datatype config (in the context of a CREATE TABLE statement for example)
    fn parse_data_config(&mut self) -> Result<Vec<Value>, ParserError> {
        self.expect_token(&Token::LParen)?;
        let values = self.parse_comma_separated(|parser| parser.parse_value())?;
        self.expect_token(&Token::RParen)?;
        Ok(values)
    }

    /// Parse a possibly qualified, possibly quoted identifier, e.g.
    /// `foo` or `myschema."table"`
    fn parse_object_name(&mut self) -> Result<ObjectName, ParserError> {
        let mut idents = vec![];
        loop {
            idents.push(self.parse_identifier()?);
            if !self.consume_token(&Token::Period) {
                break;
            }
        }
        Ok(ObjectName(idents))
    }

    /// Parse a simple one-word identifier (possibly quoted, possibly a keyword)
    fn parse_identifier(&mut self) -> Result<Ident, ParserError> {
        match self.next_token() {
            Some(Token::Word(w)) => Ok(w.to_ident()),
            unexpected => self.expected("identifier", unexpected),
        }
    }

    /// Parse a parenthesized comma-separated list of unqualified, possibly quoted identifiers
    fn parse_parenthesized_column_list(
        &mut self,
        optional: IsOptional,
    ) -> Result<Vec<Ident>, ParserError> {
        if self.consume_token(&Token::LParen) {
            let cols = self.parse_comma_separated(|parser| parser.parse_identifier())?;
            self.expect_token(&Token::RParen)?;
            Ok(cols)
        } else if optional == Optional {
            Ok(vec![])
        } else {
            let token = self.peek_token();
            self.expected("a list of columns in parentheses", token)
        }
    }

    fn parse_optional_precision(&mut self) -> Result<Option<u64>, ParserError> {
        if self.consume_token(&Token::LParen) {
            let n = self.parse_literal_uint()?;
            self.expect_token(&Token::RParen)?;
            Ok(Some(n))
        } else {
            Ok(None)
        }
    }

    fn parse_optional_precision_scale(
        &mut self,
    ) -> Result<(Option<u64>, Option<u64>), ParserError> {
        if self.consume_token(&Token::LParen) {
            let n = self.parse_literal_uint()?;
            let scale = if self.consume_token(&Token::Comma) {
                Some(self.parse_literal_uint()?)
            } else {
                None
            };
            self.expect_token(&Token::RParen)?;
            Ok((Some(n), scale))
        } else {
            Ok((None, None))
        }
    }

    /// Parse a query expression, i.e. a `SELECT` statement optionally
    /// preceeded with some `WITH` CTE declarations and optionally followed
    /// by `ORDER BY`. Unlike some other parse_... methods, this one doesn't
    /// expect the initial keyword to be already consumed
    fn parse_query(&mut self) -> Result<Query, ParserError> {
        let ctes = vec![];

        let body = self.parse_query_body(0)?;

        let order_by = vec![];

        let limit = None;

        let offset = None;

        let fetch = None;

        Ok(Query {
            ctes,
            body,
            limit,
            order_by,
            offset,
            fetch,
        })
    }

    /// Parse a "query body", which is an expression with roughly the
    /// following grammar:
    /// ```text
    ///   query_body ::= restricted_select | '(' subquery ')' | set_operation
    ///   restricted_select ::= 'SELECT' [expr_list] [ from ] [ where ] [ groupby_having ]
    ///   subquery ::= query_body [ order_by_limit ]
    ///   set_operation ::= query_body { 'UNION' | 'EXCEPT' | 'INTERSECT' } [ 'ALL' ] query_body
    /// ```
    fn parse_query_body(&mut self, _precedence: u8) -> Result<SetExpr, ParserError> {
        // We parse the expression using a Pratt parser, as in `parse_expr()`.
        // Start by parsing a restricted SELECT or a `(subquery)`:
        let expr = if self.parse_keyword("VALUES") {
            SetExpr::Values(self.parse_values()?)
        } else {
            let token = self.peek_token();
            return self.expected("VALUES", token);
        };

        Ok(expr)
    }

    /// Parse an INSERT statement
    fn parse_insert(&mut self) -> Result<Statement, ParserError> {
        if !self.is_after_newline() {
            return Err(ParserError::Ignored);
        }
        self.expect_keyword("INTO")?;
        self.context.started_insert();
        let table_name = self.parse_object_name()?;

        self.context.started_insert_table(format!("{}", table_name));

        let columns = self.parse_parenthesized_column_list(Optional)?;
        let source = Box::new(self.parse_query()?);

        self.context.ended_insert_table();
        self.context.ended_insert();
        Ok(Statement::Insert {
            table_name,
            columns,
            source,
        })
    }

    fn parse_values(&mut self) -> Result<Values, ParserError> {
        let values = self.parse_comma_separated(|parser| {
            parser.expect_token(&Token::LParen)?;
            let mut counter = 0;
            let exprs = parser.parse_comma_separated(|parser| {
                parser.context.started_insert_value(counter);
                counter += 1;
                let value = parser.parse_expr();
                parser.context.ended_insert_value();
                value
            })?;
            parser.expect_token(&Token::RParen)?;
            Ok(exprs)
        })?;
        Ok(Values(values))
    }
}

impl Word {
    fn to_ident(&self) -> Ident {
        Ident {
            value: self.value.clone(),
            quote_style: self.quote_style,
        }
    }
}
