use mysqldump_mutator::{Parser/*, Token*/};

use std::fs::File;
use std::io::{self, Write, BufReader, stderr};

fn main() -> io::Result<()> {
    env_logger::init();

    let args: Vec<String> = std::env::args().collect();

    //let (mut count_a, mut count_b) = (0, 0);

    let result = Parser::parse_mysqldump(
        BufReader::new(File::open(&args[1])?),
        |_context, token| {
            //println!("{:?} {}", context, token);
            //Token::new(&format!("REDACTED{}", count_a), Some('\''));
            //count_a += 1;
            token
        },
        |tokens| {
            for token in tokens {
                print!("{}", token)
            }
            //count_b += 1;
        },
    );

    if let Err(result) = result {
        let stderr = stderr();
        let mut handle = stderr.lock();

        handle.write_all(
            format!("\nError found during the file processing: {}\n", result).as_ref(),
        )?;

        println!("{:?}", result);
    }

    //println!("{:?}", result);

    //println!("{} {}", count_a, count_b);

    Ok(())
}
