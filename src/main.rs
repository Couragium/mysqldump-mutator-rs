use sqlparser::Parser;
use sqlparser::Token;

use std::fs::File;
use std::io::{self, BufReader};

fn main() -> io::Result<()> {
    env_logger::init();

    let f = File::open("/home/david/Documents/Omnea/dump_custarea.sql")?;

    let (mut count_a, mut count_b) = (0, 0);

    let result = Parser::parse_mysqldump(
        BufReader::new(f),
        |_context, token| {
            //println!("{:?} {}", context, token);
            Token::new(&format!("Hola{}", count_a), Some('\''));
            //Token::Word(Word {value: "42".to_string(), quote_style: None, keyword: "".to_string()})
            count_a += 1;
            token
        },
        |tokens| {
            for token in tokens {
                print!("{}", token)
            }
            count_b += 1;
        },
    );

    if let Err(result) = result {
        println!("{:?}", result);
    }

    //println!("{:?}", result);

    //println!("{} {}", count_a, count_b);

    Ok(())
}
