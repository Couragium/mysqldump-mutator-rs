use sqlparser::dialect::MySqlDialect;
use sqlparser::parser::*;
//use sqlparser::tokenizer::{Token, Word};

use std::fs::File;
use std::io::{self, BufReader};

fn main() -> io::Result<()> {
    env_logger::init();

    let f = File::open("tests/migration_example_2.sql")?;
    let mut sql = BufReader::new(f);

    let dialect = MySqlDialect {};

    let (mut count_a, mut count_b) = (0, 0);

    let _result = Parser::parse_sql(
        &dialect,
        &mut sql,
        &mut |_context, token| {
            //println!("{:?} {}", context, token);
            //Token::Word(Word {value: "42".to_string(), quote_style: None, keyword: "".to_string()})
            count_a += 1;
            token
        },
        &mut |tokens| {
            for token in tokens {
                print!("{}", token)
            }
            count_b += 1;
        },
    );

    //println!("{:?}", result);

    //println!("{} {}", count_a, count_b);

    Ok(())
}
