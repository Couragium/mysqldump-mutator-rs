use sqlparser::dialect::MySqlDialect;
use sqlparser::parser::*;
use sqlparser::tokenizer::{Token, Word};

use std::io::{self, BufReader};
use std::fs::File;

fn main() -> io::Result<()> {
	env_logger::init();

    let f = File::open("tests/migration_example_2.sql")?;
    let mut sql = BufReader::new(f);

    let dialect = MySqlDialect {};


    let _result = Parser::parse_sql(&dialect, &mut sql, &|_context, _token| {
    	//println!("{:?} {}", context, token);
    	Token::Word(Word {value: "42".to_string(), quote_style: None, keyword: "".to_string()})
    }, &|tokens| {
    	for token in tokens {
    		print!("{}", token)
    	}
    });

    //println!("{:?}", result);

    Ok(())
}
