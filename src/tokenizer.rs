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

//! SQL Tokenizer
//!
//! The tokenizer (a.k.a. lexer) converts a string into a sequence of tokens.
//!
//! The tokens then form the input for the parser, which outputs an Abstract Syntax Tree (AST).

use std::io::BufRead;
use std::iter::Peekable;
use utf8_chars::{BufReadCharsExt, Chars};

use super::dialect::keywords::ALL_KEYWORDS;
use super::dialect::Dialect;
use std::collections::VecDeque;
use std::fmt;

/// SQL Token enumeration
#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    /// A keyword (like SELECT) or an optionally quoted SQL identifier
    Word(Word),
    /// An unsigned numeric literal
    Number(String),
    /// A character that could not be tokenized
    Char(char),
    /// Single quoted string: i.e: 'string'
    SingleQuotedString(String),
    /// "National" string literal: i.e: N'string'
    NationalStringLiteral(String),
    /// Hexadecimal string literal: i.e.: X'deadbeef'
    HexStringLiteral(String),
    /// Comma
    Comma,
    /// Whitespace (space, tab, etc)
    Whitespace(Whitespace),
    /// Equality operator `=`
    Eq,
    /// Not Equals operator `<>` (or `!=` in some dialects)
    Neq([char; 2]),
    /// Less Than operator `<`
    Lt,
    /// Greater han operator `>`
    Gt,
    /// Less Than Or Equals operator `<=`
    LtEq,
    /// Greater Than Or Equals operator `>=`
    GtEq,
    /// Plus operator `+`
    Plus,
    /// Minus operator `-`
    Minus,
    /// Multiplication operator `*`
    Mult,
    /// Division operator `/`
    Div,
    /// Modulo Operator `%`
    Mod,
    /// Left parenthesis `(`
    LParen,
    /// Right parenthesis `)`
    RParen,
    /// Period (used for compound identifiers or projections into nested types)
    Period,
    /// Colon `:`
    Colon,
    /// DoubleColon `::` (used for casting in postgresql)
    DoubleColon,
    /// SemiColon `;` used as separator for COPY and payload
    SemiColon,
    /// Backslash `\` used in terminating the COPY payload with `\.`
    Backslash,
    /// Left bracket `[`
    LBracket,
    /// Right bracket `]`
    RBracket,
    /// Ampersand &
    Ampersand,
    /// Left brace `{`
    LBrace,
    /// Right brace `}`
    RBrace,
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Token::Word(ref w) => write!(f, "{}", w),
            Token::Number(ref n) => f.write_str(n),
            Token::Char(ref c) => write!(f, "{}", c),
            Token::SingleQuotedString(ref s) => write!(f, "'{}'", s),
            Token::NationalStringLiteral(ref s) => write!(f, "N'{}'", s),
            Token::HexStringLiteral(ref s) => write!(f, "X'{}'", s),
            Token::Comma => f.write_str(","),
            Token::Whitespace(ws) => write!(f, "{}", ws),
            Token::Eq => f.write_str("="),
            Token::Neq(values) => write!(f, "{}{}", values[0], values[1]),
            Token::Lt => f.write_str("<"),
            Token::Gt => f.write_str(">"),
            Token::LtEq => f.write_str("<="),
            Token::GtEq => f.write_str(">="),
            Token::Plus => f.write_str("+"),
            Token::Minus => f.write_str("-"),
            Token::Mult => f.write_str("*"),
            Token::Div => f.write_str("/"),
            Token::Mod => f.write_str("%"),
            Token::LParen => f.write_str("("),
            Token::RParen => f.write_str(")"),
            Token::Period => f.write_str("."),
            Token::Colon => f.write_str(":"),
            Token::DoubleColon => f.write_str("::"),
            Token::SemiColon => f.write_str(";"),
            Token::Backslash => f.write_str("\\"),
            Token::LBracket => f.write_str("["),
            Token::RBracket => f.write_str("]"),
            Token::Ampersand => f.write_str("&"),
            Token::LBrace => f.write_str("{"),
            Token::RBrace => f.write_str("}"),
        }
    }
}

impl Token {
    pub fn make_keyword(keyword: &str) -> Self {
        Token::make_word(keyword, None)
    }
    pub fn make_word(word: &str, quote_style: Option<char>) -> Self {
        let word_uppercase = word.to_uppercase();
        //TODO: need to reintroduce FnvHashSet at some point .. iterating over keywords is
        // not fast but I want the simplicity for now while I experiment with pluggable
        // dialects
        let is_keyword = quote_style == None && ALL_KEYWORDS.contains(&word_uppercase.as_str());
        Token::Word(Word {
            value: word.to_string(),
            quote_style,
            keyword: if is_keyword {
                word_uppercase
            } else {
                "".to_string()
            },
        })
    }
}

/// A keyword (like SELECT) or an optionally quoted SQL identifier
#[derive(Debug, Clone, PartialEq)]
pub struct Word {
    /// The value of the token, without the enclosing quotes, and with the
    /// escape sequences (if any) processed (TODO: escapes are not handled)
    pub value: String,
    /// An identifier can be "quoted" (&lt;delimited identifier> in ANSI parlance).
    /// The standard and most implementations allow using double quotes for this,
    /// but some implementations support other quoting styles as well (e.g. \[MS SQL])
    pub quote_style: Option<char>,
    /// If the word was not quoted and it matched one of the known keywords,
    /// this will have one of the values from dialect::keywords, otherwise empty
    pub keyword: String,
}

impl fmt::Display for Word {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.quote_style {
            Some(s) if s == '"' || s == '[' || s == '`' => {
                write!(f, "{}{}{}", s, self.value, Word::matching_end_quote(s))
            }
            None => f.write_str(&self.value),
            _ => panic!("Unexpected quote_style!"),
        }
    }
}
impl Word {
    fn matching_end_quote(ch: char) -> char {
        match ch {
            '"' => '"', // ANSI and most dialects
            '[' => ']', // MS SQL
            '`' => '`', // MySQL
            _ => panic!("unexpected quoting style!"),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Whitespace {
    Space,
    Newline,
    Tab,
    SingleLineComment(String),
    MultiLineComment(String),
}

impl fmt::Display for Whitespace {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Whitespace::Space => f.write_str(" "),
            Whitespace::Newline => f.write_str("\n"),
            Whitespace::Tab => f.write_str("\t"),
            Whitespace::SingleLineComment(s) => write!(f, "--{}", s),
            Whitespace::MultiLineComment(s) => write!(f, "/*{}*/", s),
        }
    }
}

/// Tokenizer error
#[derive(Debug, PartialEq)]
pub struct TokenizerError(String);

/// SQL Tokenizer
pub struct Tokenizer<'a> {
    dialect: &'a dyn Dialect,
    pub query: Peekable<Chars<'a, dyn BufRead + 'a>>,
    pub line: u64,
    pub col: u64,
    peeked_tokens: VecDeque<Token>,
}

impl<'a> Tokenizer<'a> {
    /// Create a new SQL tokenizer for the specified SQL statement
    pub fn new(dialect: &'a dyn Dialect, query: &'a mut dyn BufRead) -> Self {
        Self {
            dialect,
            query: query.chars().peekable(),
            line: 1,
            col: 1,
            peeked_tokens: VecDeque::new(),
        }
    }

    pub fn peek_token(&mut self, n: usize) -> Result<Option<Token>, TokenizerError> {
        // We need to have a peeked token at least in case they send us n=0
        if self.peeked_tokens.len() <= n {
            //Peek enough in order to get the one we want. Including 1 token when n=0
            let tokens_to_peek = n - self.peeked_tokens.len() + 1;
            for _ in 0..tokens_to_peek {
                match self.internal_next_token() {
                    Ok(Some(token)) => {
                        self.peeked_tokens.push_back(token);
                    }
                    _ => return Err(TokenizerError("Unexpected EOF.".to_string())),
                }
            }
        }
        Ok(Some(self.peeked_tokens[n].clone()))
    }

    pub fn pushback_token(&mut self, token: Token) {
        self.peeked_tokens.push_front(token);
    }

    /// Get the next token or return None
    pub fn next_token(&mut self) -> Result<Option<Token>, TokenizerError> {
        if let Some(token) = self.peeked_tokens.pop_front() {
            //println!("{:?}", token);
            return Ok(Some(token));
        }

        self.internal_next_token()
        //println!("{:?}", token);
    }

    fn internal_next_token(&mut self) -> Result<Option<Token>, TokenizerError> {
        match self.query.peek() {
            Some(Ok(ch)) => match *ch {
                ' ' => self.consume_and_return(Token::Whitespace(Whitespace::Space)),
                '\t' => self.consume_and_return(Token::Whitespace(Whitespace::Tab)),
                '\n' => self.consume_and_return(Token::Whitespace(Whitespace::Newline)),
                '\r' => {
                    // Emit a single Whitespace::Newline token for \r and \r\n
                    self.query.next();
                    if let Some(Ok('\n')) = self.query.peek() {
                        self.query.next();
                    }
                    Ok(Some(Token::Whitespace(Whitespace::Newline)))
                }
                'N' => {
                    self.query.next(); // consume, to check the next char
                    match self.query.peek() {
                        Some(Ok('\'')) => {
                            // N'...' - a <national character string literal>
                            let s = self.tokenize_single_quoted_string();
                            Ok(Some(Token::NationalStringLiteral(s)))
                        }
                        _ => {
                            // regular identifier starting with an "N"
                            let s = self.tokenize_word('N');
                            Ok(Some(Token::make_word(&s, None)))
                        }
                    }
                }
                // The spec only allows an uppercase 'X' to introduce a hex
                // string, but PostgreSQL, at least, allows a lowercase 'x' too.
                x @ 'x' | x @ 'X' => {
                    self.query.next(); // consume, to check the next char
                    match self.query.peek() {
                        Some(Ok('\'')) => {
                            // X'...' - a <binary string literal>
                            let s = self.tokenize_single_quoted_string();
                            Ok(Some(Token::HexStringLiteral(s)))
                        }
                        _ => {
                            // regular identifier starting with an "X"
                            let s = self.tokenize_word(x);
                            Ok(Some(Token::make_word(&s, None)))
                        }
                    }
                }
                // identifier or keyword
                ch if self.dialect.is_identifier_start(ch) => {
                    self.query.next(); // consume the first char
                    let s = self.tokenize_word(ch);
                    Ok(Some(Token::make_word(&s, None)))
                }
                // string
                '\'' => {
                    let s = self.tokenize_single_quoted_string();
                    Ok(Some(Token::SingleQuotedString(s)))
                }
                // delimited (quoted) identifier
                quote_start if self.dialect.is_delimited_identifier_start(quote_start) => {
                    self.query.next(); // consume the opening quote
                    let quote_end = Word::matching_end_quote(quote_start);
                    let s = self.peeking_take_while(|ch| ch != quote_end);
                    match self.query.next() {
                        Some(Ok(ch)) if ch == quote_end => {
                            Ok(Some(Token::make_word(&s, Some(quote_start))))
                        }
                        _ => Err(TokenizerError(format!(
                            "Expected close delimiter '{}' before EOF.",
                            quote_end
                        ))),
                    }
                }
                // numbers
                '0'..='9' => {
                    // TODO: https://jakewheat.github.io/sql-overview/sql-2011-foundation-grammar.html#unsigned-numeric-literal
                    let s = self.peeking_take_while(|ch| match ch {
                        '0'..='9' | '.' => true,
                        _ => false,
                    });
                    Ok(Some(Token::Number(s)))
                }
                // punctuation
                '(' => self.consume_and_return(Token::LParen),
                ')' => self.consume_and_return(Token::RParen),
                ',' => self.consume_and_return(Token::Comma),
                // operators
                '-' => {
                    self.query.next(); // consume the '-'
                    match self.query.peek() {
                        Some(Ok('-')) => {
                            self.query.next(); // consume the second '-', starting a single-line comment
                            let mut s = self.peeking_take_while(|ch| ch != '\n');
                            if let Some(Ok(ch)) = self.query.next() {
                                assert_eq!(ch, '\n');
                                s.push(ch);
                            }
                            Ok(Some(Token::Whitespace(Whitespace::SingleLineComment(s))))
                        }
                        // a regular '-' operator
                        _ => Ok(Some(Token::Minus)),
                    }
                }
                '/' => {
                    self.query.next(); // consume the '/'
                    match self.query.peek() {
                        Some(Ok('*')) => {
                            self.query.next(); // consume the '*', starting a multi-line comment
                            self.tokenize_multiline_comment()
                        }
                        // a regular '/' operator
                        _ => Ok(Some(Token::Div)),
                    }
                }
                '+' => self.consume_and_return(Token::Plus),
                '*' => self.consume_and_return(Token::Mult),
                '%' => self.consume_and_return(Token::Mod),
                '=' => self.consume_and_return(Token::Eq),
                '.' => self.consume_and_return(Token::Period),
                '!' => {
                    self.query.next(); // consume
                    match self.query.peek() {
                        Some(Ok('=')) => self.consume_and_return(Token::Neq(['!', '='])),
                        _ => Err(TokenizerError(format!(
                            "Tokenizer Error at Line: {}, Col: {}",
                            self.line, self.col
                        ))),
                    }
                }
                '<' => {
                    self.query.next(); // consume
                    match self.query.peek() {
                        Some(Ok('=')) => self.consume_and_return(Token::LtEq),
                        Some(Ok('>')) => self.consume_and_return(Token::Neq(['<', '>'])),
                        _ => Ok(Some(Token::Lt)),
                    }
                }
                '>' => {
                    self.query.next(); // consume
                    match self.query.peek() {
                        Some(Ok('=')) => self.consume_and_return(Token::GtEq),
                        _ => Ok(Some(Token::Gt)),
                    }
                }
                ':' => {
                    self.query.next();
                    match self.query.peek() {
                        Some(Ok(':')) => self.consume_and_return(Token::DoubleColon),
                        _ => Ok(Some(Token::Colon)),
                    }
                }
                ';' => self.consume_and_return(Token::SemiColon),
                '\\' => self.consume_and_return(Token::Backslash),
                '[' => self.consume_and_return(Token::LBracket),
                ']' => self.consume_and_return(Token::RBracket),
                '&' => self.consume_and_return(Token::Ampersand),
                '{' => self.consume_and_return(Token::LBrace),
                '}' => self.consume_and_return(Token::RBrace),
                other => self.consume_and_return(Token::Char(other)),
            },
            _ => Ok(None),
        }
    }

    /// Tokenize an identifier or keyword, after the first char is already consumed.
    fn tokenize_word(&mut self, first_char: char) -> String {
        let mut s = first_char.to_string();
        let dialect = self.dialect;
        s.push_str(&self.peeking_take_while(|ch| dialect.is_identifier_part(ch)));
        s
    }

    /// Read a single quoted string, starting with the opening quote.
    fn tokenize_single_quoted_string(&mut self) -> String {
        //TODO: handle escaped quotes in string
        //TODO: handle newlines in string
        //TODO: handle EOF before terminating quote
        //TODO: handle 'string' <white space> 'string continuation'
        let chars = &mut self.query;
        let mut s = String::new();
        chars.next(); // consume the opening quote
        while let Some(Ok(ch)) = chars.peek() {
            match *ch {
                '\'' => {
                    chars.next(); // consume
                    let escaped_quote = chars
                        .peek()
                        .map(|c| c.as_ref().unwrap() == &'\'')
                        .unwrap_or(false);
                    if escaped_quote {
                        s.push('\'');
                        s.push('\'');
                        chars.next();
                    } else {
                        break;
                    }
                }
                '\\' => {
                    chars.next(); // consume
                    let next_char = chars.peek().unwrap().as_ref().unwrap();
                    if next_char == &'\\'
                        || next_char == &'\''
                        || next_char == &'\"'
                        || next_char == &'n'
                        || next_char == &'t'
                    {
                        s.push('\\');
                        s.push(*next_char);
                        chars.next();
                    } else {
                        break;
                    }
                }
                ch => {
                    chars.next(); // consume
                    s.push(ch);
                }
            }
        }
        s
    }

    fn tokenize_multiline_comment(&mut self) -> Result<Option<Token>, TokenizerError> {
        let mut s = String::new();
        let mut maybe_closing_comment = false;
        // TODO: deal with nested comments
        loop {
            match self.query.next() {
                Some(Ok(ch)) => {
                    if maybe_closing_comment {
                        if ch == '/' {
                            break Ok(Some(Token::Whitespace(Whitespace::MultiLineComment(s))));
                        } else {
                            s.push('*');
                        }
                    }
                    maybe_closing_comment = ch == '*';
                    if !maybe_closing_comment {
                        s.push(ch);
                    }
                }
                _ => {
                    break Err(TokenizerError(
                        "Unexpected EOF while in a multi-line comment".to_string(),
                    ));
                }
            }
        }
    }

    fn consume_and_return(&mut self, t: Token) -> Result<Option<Token>, TokenizerError> {
        self.query.next();
        Ok(Some(t))
    }

    /// Read from `chars` until `predicate` returns `false` or EOF is hit.
    /// Return the characters read as String, and keep the first non-matching
    /// char available as `chars.next()`.
    fn peeking_take_while(&mut self, mut predicate: impl FnMut(char) -> bool) -> String {
        let mut s = String::new();
        while let Some(Ok(ch)) = self.query.peek() {
            let ch = *ch;
            if predicate(ch) {
                self.query.next(); // consume
                s.push(ch);
            } else {
                break;
            }
        }
        s
    }
}
