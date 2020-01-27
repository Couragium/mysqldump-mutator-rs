# MySQL mysqldump stream processor / mutator in Rust

This library is based on another library for parsing SQL. I just took that library, simplified it, change what I needed and adapted it for what I needed in order to parse mysqldump files.

You can check Andy Grove awesome work here: [https://github.com/andygrove/sqlparser-rs](https://github.com/andygrove/sqlparser-rs)

[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](https://opensource.org/licenses/Apache-2.0)

This library can parse a BufRead of a MySQL mysqldump file and it will call a clousure function every time the parser reaches a column or a value. This will allow you to change the content of a backup without parsing the whole file in memory first.

Changes made:

 - The previous parser assumed that had all the tokens already in memory. This ones parses only what it needs and therefore, doesn't needs to load the whole file in order to work.
 - I deleted a lot of code (I would say around 50%). With it, I removed many many features.
 - I added some logic in order to work with BufRead instead of &str
