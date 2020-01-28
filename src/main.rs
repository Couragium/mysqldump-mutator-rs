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
