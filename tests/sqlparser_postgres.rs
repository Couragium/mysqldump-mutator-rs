#![warn(clippy::all)]
//! Test SQL syntax specific to PostgreSQL. The parser based on the
//! generic dialect is also tested (on the inputs it can handle).

use sqlparser::dialect::{GenericSqlDialect, PostgreSqlDialect};
use sqlparser::sqlast::*;
use sqlparser::test_utils::*;

#[test]
fn parse_create_table_with_defaults() {
    let sql = "CREATE TABLE public.customer (
            customer_id integer DEFAULT nextval(public.customer_customer_id_seq),
            store_id smallint NOT NULL,
            first_name character varying(45) NOT NULL,
            last_name character varying(45) COLLATE \"es_ES\" NOT NULL,
            email character varying(50),
            address_id smallint NOT NULL,
            activebool boolean DEFAULT true NOT NULL,
            create_date date DEFAULT now()::text NOT NULL,
            last_update timestamp without time zone DEFAULT now() NOT NULL,
            active integer NOT NULL
    ) WITH (fillfactor = 20, user_catalog_table = true, autovacuum_vacuum_threshold = 100)";
    match pg_and_generic().one_statement_parses_to(sql, "") {
        SQLStatement::SQLCreateTable {
            name,
            columns,
            constraints,
            with_options,
            external: false,
            file_format: None,
            location: None,
        } => {
            assert_eq!("public.customer", name.to_string());
            assert_eq!(
                columns,
                vec![
                    SQLColumnDef {
                        name: "customer_id".into(),
                        data_type: SQLType::Int,
                        collation: None,
                        options: vec![ColumnOptionDef {
                            name: None,
                            option: ColumnOption::Default(
                                pg().verified_expr("nextval(public.customer_customer_id_seq)")
                            )
                        }],
                    },
                    SQLColumnDef {
                        name: "store_id".into(),
                        data_type: SQLType::SmallInt,
                        collation: None,
                        options: vec![ColumnOptionDef {
                            name: None,
                            option: ColumnOption::NotNull,
                        }],
                    },
                    SQLColumnDef {
                        name: "first_name".into(),
                        data_type: SQLType::Varchar(Some(45)),
                        collation: None,
                        options: vec![ColumnOptionDef {
                            name: None,
                            option: ColumnOption::NotNull,
                        }],
                    },
                    SQLColumnDef {
                        name: "last_name".into(),
                        data_type: SQLType::Varchar(Some(45)),
                        collation: Some(SQLObjectName(vec!["\"es_ES\"".into()])),
                        options: vec![ColumnOptionDef {
                            name: None,
                            option: ColumnOption::NotNull,
                        }],
                    },
                    SQLColumnDef {
                        name: "email".into(),
                        data_type: SQLType::Varchar(Some(50)),
                        collation: None,
                        options: vec![],
                    },
                    SQLColumnDef {
                        name: "address_id".into(),
                        data_type: SQLType::SmallInt,
                        collation: None,
                        options: vec![ColumnOptionDef {
                            name: None,
                            option: ColumnOption::NotNull
                        }],
                    },
                    SQLColumnDef {
                        name: "activebool".into(),
                        data_type: SQLType::Boolean,
                        collation: None,
                        options: vec![
                            ColumnOptionDef {
                                name: None,
                                option: ColumnOption::Default(ASTNode::SQLValue(Value::Boolean(
                                    true
                                ))),
                            },
                            ColumnOptionDef {
                                name: None,
                                option: ColumnOption::NotNull,
                            }
                        ],
                    },
                    SQLColumnDef {
                        name: "create_date".into(),
                        data_type: SQLType::Date,
                        collation: None,
                        options: vec![
                            ColumnOptionDef {
                                name: None,
                                option: ColumnOption::Default(
                                    pg().verified_expr("CAST(now() AS text)")
                                )
                            },
                            ColumnOptionDef {
                                name: None,
                                option: ColumnOption::NotNull,
                            }
                        ],
                    },
                    SQLColumnDef {
                        name: "last_update".into(),
                        data_type: SQLType::Timestamp,
                        collation: None,
                        options: vec![
                            ColumnOptionDef {
                                name: None,
                                option: ColumnOption::Default(pg().verified_expr("now()")),
                            },
                            ColumnOptionDef {
                                name: None,
                                option: ColumnOption::NotNull,
                            }
                        ],
                    },
                    SQLColumnDef {
                        name: "active".into(),
                        data_type: SQLType::Int,
                        collation: None,
                        options: vec![ColumnOptionDef {
                            name: None,
                            option: ColumnOption::NotNull
                        }],
                    },
                ]
            );
            assert!(constraints.is_empty());
            assert_eq!(
                with_options,
                vec![
                    SQLOption {
                        name: "fillfactor".into(),
                        value: Value::Long(20)
                    },
                    SQLOption {
                        name: "user_catalog_table".into(),
                        value: Value::Boolean(true)
                    },
                    SQLOption {
                        name: "autovacuum_vacuum_threshold".into(),
                        value: Value::Long(100)
                    },
                ]
            );
        }
        _ => unreachable!(),
    }
}

#[test]
fn parse_create_table_from_pg_dump() {
    let sql = "CREATE TABLE public.customer (
            customer_id integer DEFAULT nextval('public.customer_customer_id_seq'::regclass) NOT NULL,
            store_id smallint NOT NULL,
            first_name character varying(45) NOT NULL,
            last_name character varying(45) NOT NULL,
            info text[],
            address_id smallint NOT NULL,
            activebool boolean DEFAULT true NOT NULL,
            create_date date DEFAULT now()::date NOT NULL,
            create_date1 date DEFAULT 'now'::text::date NOT NULL,
            last_update timestamp without time zone DEFAULT now(),
            release_year public.year,
            active integer
        )";
    pg().one_statement_parses_to(sql, "CREATE TABLE public.customer (\
            customer_id int DEFAULT nextval(CAST('public.customer_customer_id_seq' AS regclass)) NOT NULL, \
            store_id smallint NOT NULL, \
            first_name character varying(45) NOT NULL, \
            last_name character varying(45) NOT NULL, \
            info text[], \
            address_id smallint NOT NULL, \
            activebool boolean DEFAULT true NOT NULL, \
            create_date date DEFAULT CAST(now() AS date) NOT NULL, \
            create_date1 date DEFAULT CAST(CAST('now' AS text) AS date) NOT NULL, \
            last_update timestamp DEFAULT now(), \
            release_year public.year, \
            active int\
        )");
}

#[test]
fn parse_create_table_with_inherit() {
    let sql = "\
               CREATE TABLE bazaar.settings (\
               settings_id uuid PRIMARY KEY DEFAULT uuid_generate_v4() NOT NULL, \
               user_id uuid UNIQUE, \
               value text[], \
               use_metric boolean DEFAULT true\
               )";
    pg().verified_stmt(sql);
}

#[test]
fn parse_copy_example() {
    let sql = r#"COPY public.actor (actor_id, first_name, last_name, last_update, value) FROM stdin;
1	PENELOPE	GUINESS	2006-02-15 09:34:33 0.11111
2	NICK	WAHLBERG	2006-02-15 09:34:33 0.22222
3	ED	CHASE	2006-02-15 09:34:33 0.312323
4	JENNIFER	DAVIS	2006-02-15 09:34:33 0.3232
5	JOHNNY	LOLLOBRIGIDA	2006-02-15 09:34:33 1.343
6	BETTE	NICHOLSON	2006-02-15 09:34:33 5.0
7	GRACE	MOSTEL	2006-02-15 09:34:33 6.0
8	MATTHEW	JOHANSSON	2006-02-15 09:34:33 7.0
9	JOE	SWANK	2006-02-15 09:34:33 8.0
10	CHRISTIAN	GABLE	2006-02-15 09:34:33 9.1
11	ZERO	CAGE	2006-02-15 09:34:33 10.001
12	KARL	BERRY	2017-11-02 19:15:42.308637+08 11.001
A Fateful Reflection of a Waitress And a Boat who must Discover a Sumo Wrestler in Ancient China
Kwara & Kogi
{"Deleted Scenes","Behind the Scenes"}
'awe':5 'awe-inspir':4 'barbarella':1 'cat':13 'conquer':16 'dog':18 'feminist':10 'inspir':6 'monasteri':21 'must':15 'stori':7 'streetcar':2
PHP	₱ USD $
\N  Some other value
\\."#;
    let ast = pg_and_generic().one_statement_parses_to(sql, "");
    println!("{:#?}", ast);
    //assert_eq!(sql, ast.to_string());
}

fn pg() -> TestedDialects {
    TestedDialects {
        dialects: vec![Box::new(PostgreSqlDialect {})],
    }
}

fn pg_and_generic() -> TestedDialects {
    TestedDialects {
        dialects: vec![
            Box::new(PostgreSqlDialect {}),
            Box::new(GenericSqlDialect {}),
        ],
    }
}
