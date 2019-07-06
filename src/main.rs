#[macro_use]
extern crate combine;
extern crate combine_language;

use combine::parser::char::{alpha_num, letter, string};
use combine::{parser, satisfy, ParseError, Parser, Stream};
use combine_language::{expression_parser, Assoc, Fixity, Identifier, LanguageDef, LanguageEnv};

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

#[derive(Debug, PartialEq)]
pub enum Op {
  Plus,
  Minus,
  Aster,
  Cons,
  Langle,
}

fn calc_expr_env<'a, I>() -> LanguageEnv<'a, I>
where
  I: 'a,
  I: Stream<Item = char>,
  <I as combine::StreamOnce>::Error: combine::ParseError<
    char,
    <I as combine::StreamOnce>::Range,
    <I as combine::StreamOnce>::Position,
  >,
{
  LanguageEnv::new(LanguageDef {
    ident: Identifier {
      start: letter(),
      rest: alpha_num(),
      reserved: [
        "true", "false", "if", "then", "else", "let", "rec", "in", "fun", "match", "with",
      ]
      .iter()
      .map(|x| (*x).into())
      .collect(),
    },
    op: Identifier {
      start: satisfy(|c| "+-*<:".chars().any(|x| x == c)),
      rest: satisfy(|c| "+-*<:".chars().any(|x| x == c)),
      reserved: ["+", "-", "*", "<", "::"]
        .iter()
        .map(|x| (*x).into())
        .collect(),
    },
    comment_start: string("/*").map(|_| ()),
    comment_end: string("*/").map(|_| ()),
    comment_line: string("//").map(|_| ()),
  })
}

parser! {
  fn expr_parser[I]()(I) -> Expr
  where [
    I: Stream<Item = char>,
    I::Error: ParseError<char, I::Range, I::Position>,
    <I::Error as ParseError<I::Item, I::Range, I::Position>>::StreamError:
      From<::std::num::ParseIntError>,
  ]
  {
    choice!(
      expression_parser(term_parser(calc_expr_env()), op_parser(calc_expr_env()), op)
    )
  }
}

parser! {
  fn term_parser['a, I](expr_env: LanguageEnv<'a, I>)(I) -> Expr
  where [
    I: Stream<Item = char>,
    I::Error: ParseError<char, I::Range, I::Position>,
    <I::Error as ParseError<I::Item, I::Range, I::Position>>::StreamError:
      From<::std::num::ParseIntError>,
  ]
  {
    choice!(
      expr_env.reserved("true").map(|_| Expr::Bool(true)),
      expr_env.reserved("false").map(|_| Expr::Bool(false)),
      expr_env.integer().map(|x| Expr::Int(x)),
      expr_env.identifier().map(|x| Expr::Ident(x)),
      expr_env.parens(expr_parser())
    )
  }
}

parser! {
  fn op_parser['a, I](expr_env: LanguageEnv<'a, I>)(I) -> (Op, Assoc)
  where [
    I: Stream<Item = char>,
    I::Error: ParseError<char, I::Range, I::Position>,
    <I::Error as ParseError<I::Item, I::Range, I::Position>>::StreamError:
      From<::std::num::ParseIntError>,
  ]
  {
    choice! (
      expr_env.reserved_op("+").map(|_| (Op::Plus, Assoc { precedence: 6, fixity: Fixity::Left})),
      expr_env.reserved_op("-").map(|_| (Op::Minus, Assoc { precedence: 6, fixity: Fixity::Left})),
      expr_env.reserved_op("*").map(|_| (Op::Aster, Assoc { precedence: 7, fixity: Fixity::Left})),
      expr_env.reserved_op("<").map(|_| (Op::Plus, Assoc { precedence: 4, fixity: Fixity::Left})),
      expr_env.reserved_op("::").map(|_| (Op::Cons, Assoc { precedence: 5, fixity: Fixity::Right}))
    )
  }
}

fn op(l: Expr, o: Op, r: Expr) -> Expr {
  use Expr::*;
  match o {
    Op::Plus => Plus(Box::new(l), Box::new(r)),
    Op::Minus => Minus(Box::new(l), Box::new(r)),
    Op::Aster => Times(Box::new(l), Box::new(r)),
    Op::Cons => Cons(Box::new(l), Box::new(r)),
    Op::Langle => Lt(Box::new(l), Box::new(r)),
  }
}

fn main() {
  let mut input = String::new();
  std::io::stdin().read_line(&mut input).unwrap();
  let input: &str = &input;
  println!("{:?}", expr_parser().easy_parse(input));
}
