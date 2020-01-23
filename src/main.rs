use sqlparser::dialect::GenericDialect;
use sqlparser::parser::*;

use std::io::{self, BufReader};
use std::fs::File;

fn main() -> io::Result<()> {
    let f = File::open("tests/migration_example.sql")?;
    let mut sql = BufReader::new(f);

    let dialect = GenericDialect {};

    println!("Parsing test file!");

    let _ = Parser::parse_sql(&dialect, &mut sql, &|context, token| {
    	println!("{:?}", context);
    	token
    });

    Ok(())
}
