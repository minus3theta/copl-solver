#[macro_use]
extern crate combine;
extern crate combine_language;
use combine::{satisfy, Parser, Stream, ParseResult, many1, from_str, parser};
use combine::parser::char::{alpha_num, letter, string, digit};
use combine_language::{LanguageEnv, LanguageDef, Identifier};

#[derive(Debug, PartialEq)]
pub enum Expr {
  Bool(bool),
  Int(i64),
  Ident(String),
  Plus(Box<Expr>, Box<Expr>),
  Minus(Box<Expr>, Box<Expr>),
  Times(Box<Expr>, Box<Expr>),
  Lt(Box<Expr>, Box<Expr>),
  If(Box<Expr>, Box<Expr>, Box<Expr>),
  Let(String, Box<Expr>, Box<Expr>),
  Fun(String, Box<Expr>),
  App(Box<Expr>, Box<Expr>),
  LetRec(String, String, Box<Expr>, Box<Expr>),
  Nil,
  Cons(Box<Expr>, Box<Expr>),
  Match(Box<Expr>, Box<Expr>, String, String, Box<Expr>),
}

fn calc_expr_env<'a, I>() -> LanguageEnv<'a, I>
  where
    I: 'a,
    I: Stream<Item=char>,
    <I as combine::StreamOnce>::Error: combine::ParseError<char, <I as combine::StreamOnce>::Range, <I as combine::StreamOnce>::Position>
{
  LanguageEnv::new(LanguageDef {
    ident: Identifier {
      start: letter(),
      rest: alpha_num(),
      reserved: ["if", "then", "else", "let", "rec", "in", "fun", "match", "with"]
        .iter()
        .map(|x| (*x).into())
        .collect(),
    },
    op: Identifier {
      start: satisfy(|c| "+-*<".chars().any(|x| x == c)),
      rest: satisfy(|c| "+-*<".chars().any(|x| x == c)),
      reserved: ["+", "-", "*", "<"].iter().map(|x| (*x).into()).collect()
    },
    comment_start: string("/*").map(|_| ()),
    comment_end: string("*/").map(|_| ()),
    comment_line: string("//").map(|_| ()),
  })
}

fn calc_env_env<'a, I>() -> LanguageEnv<'a, I>
  where
    I: 'a,
    I: Stream<Item=char>,
    <I as combine::StreamOnce>::Error: combine::ParseError<char, <I as combine::StreamOnce>::Range, <I as combine::StreamOnce>::Position>
{
  LanguageEnv::new(LanguageDef {
    ident: Identifier {
      start: letter(),
      rest: alpha_num(),
      reserved: Vec::new(),
    },
    op: Identifier {
      start: satisfy(|c| ",=".chars().any(|x| x == c)),
      rest: satisfy(|c| ",=".chars().any(|x| x == c)),
      reserved: [",", "="].iter().map(|x| (*x).into()).collect()
    },
    comment_start: string("/*").map(|_| ()),
    comment_end: string("*/").map(|_| ()),
    comment_line: string("//").map(|_| ()),
  })
}

fn expr<I>(mut input: I) -> ParseResult<Box<Expr>, I>
  where
    I: Stream<Item=char>,
    <I as combine::StreamOnce>::Error: combine::ParseError<char, <I as combine::StreamOnce>::Range, <I as combine::StreamOnce>::Position>
{
  let expr_env = calc_expr_env();
  let mut integer = expr_env.integer().map(|x| Box::new(Expr::Int(x)));
  integer.parse_stream(&mut input)
}

fn main() {
}
