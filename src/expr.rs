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

pub fn calc_expr_env<'a, I>() -> LanguageEnv<'a, I>
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
  pub fn expr_parser['a, I](_expr_env: LanguageEnv<'a, I>)(I) -> Expr
  where [
    I: Stream<Item = char>,
    I::Error: ParseError<char, I::Range, I::Position>,
    <I::Error as ParseError<I::Item, I::Range, I::Position>>::StreamError:
      From<::std::num::ParseIntError>,
  ]
  {
    expression_parser(term_parser(calc_expr_env()), op_parser(calc_expr_env()), op)
  }
}

parser! {
  fn if_parser['a, I](expr_env: LanguageEnv<'a, I>)(I) -> Expr
  where [
    I: Stream<Item = char>,
    I::Error: ParseError<char, I::Range, I::Position>,
    <I::Error as ParseError<I::Item, I::Range, I::Position>>::StreamError:
      From<::std::num::ParseIntError>,
  ]
  {
    (
      expr_env.reserved("if").with(expr_parser(calc_expr_env())),
      expr_env.reserved("then").with(expr_parser(calc_expr_env())),
      expr_env.reserved("else").with(expr_parser(calc_expr_env()))
    ).map(|(p, t, f)| ite(p, t, f))
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
      if_parser(calc_expr_env()),
      expr_env.reserved("true").map(|_| Expr::Bool(true)),
      expr_env.reserved("false").map(|_| Expr::Bool(false)),
      expr_env.integer().map(|x| Expr::Int(x)),
      expr_env.identifier().map(|x| Expr::Ident(x)),
      expr_env.parens(expr_parser(calc_expr_env()))
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
      expr_env.reserved_op("<").map(|_| (Op::Langle, Assoc { precedence: 4, fixity: Fixity::Left})),
      expr_env.reserved_op("::").map(|_| (Op::Cons, Assoc { precedence: 5, fixity: Fixity::Right}))
    )
  }
}

fn op(l: Expr, o: Op, r: Expr) -> Expr {
  use self::Expr::*;
  match o {
    Op::Plus => Plus(Box::new(l), Box::new(r)),
    Op::Minus => Minus(Box::new(l), Box::new(r)),
    Op::Aster => Times(Box::new(l), Box::new(r)),
    Op::Cons => Cons(Box::new(l), Box::new(r)),
    Op::Langle => Lt(Box::new(l), Box::new(r)),
  }
}

pub fn plus(l: Expr, r: Expr) -> Expr {
  Expr::Plus(Box::new(l), Box::new(r))
}

pub fn minus(l: Expr, r: Expr) -> Expr {
  Expr::Minus(Box::new(l), Box::new(r))
}

pub fn times(l: Expr, r: Expr) -> Expr {
  Expr::Times(Box::new(l), Box::new(r))
}

pub fn lt(l: Expr, r: Expr) -> Expr {
  Expr::Lt(Box::new(l), Box::new(r))
}

pub fn cons(l: Expr, r: Expr) -> Expr {
  Expr::Cons(Box::new(l), Box::new(r))
}

pub fn ite(p: Expr, t: Expr, f: Expr) -> Expr {
  Expr::If(Box::new(p), Box::new(t), Box::new(f))
}

#[derive(Debug, PartialEq)]
pub enum Value {
  VBool(bool),
  VInt(i64),
  VCons(Box<Value>, Box<Value>),
  VNil,
}

parser! {
  pub fn value_parser['a, I](expr_env: LanguageEnv<'a, I>)(I) -> Value
  where [
    I: Stream<Item = char>,
    I::Error: ParseError<char, I::Range, I::Position>,
    <I::Error as ParseError<I::Item, I::Range, I::Position>>::StreamError:
      From<::std::num::ParseIntError>,
  ]
  {
    choice!(
      expr_env.reserved("true").map(|_| Value::VBool(true)),
      expr_env.reserved("false").map(|_| Value::VBool(false)),
      expr_env.integer().map(Value::VInt)
    )
  }
}

#[cfg(test)]
mod test {
  use super::Expr::*;
  use super::*;
  #[test]
  fn parse_expr1() {
    let s = "1 + 2 * 3 - 4";
    assert_eq!(
      expr_parser(calc_expr_env()).easy_parse(s),
      Ok((minus(plus(Int(1), times(Int(2), Int(3))), Int(4)), ""))
    )
  }
  #[test]
  fn parse_ident() {
    let s = "foo";
    assert_eq!(
      expr_parser(calc_expr_env()).easy_parse(s),
      Ok((Ident("foo".to_owned()), ""))
    )
  }
  #[test]
  fn parse_if1() {
    let s = "if 1 < 2 then 1 + 2 else 3 * 4";
    assert_eq!(
      expr_parser(calc_expr_env()).easy_parse(s),
      Ok((
        ite(
          lt(Int(1), Int(2)),
          plus(Int(1), Int(2)),
          times(Int(3), Int(4))
        ),
        ""
      ))
    )
  }
  #[test]
  fn parse_if2() {
    let s = "1 + if true then 1 else 3";
    assert_eq!(
      expr_parser(calc_expr_env()).easy_parse(s),
      Ok((plus(Int(1), ite(Bool(true), Int(1), Int(3))), ""))
    )
  }
  #[test]
  fn parse_if3() {
    let s = "1 + if 1 < 2 then 1 + 2 else 3 * 4";
    assert_eq!(
      expr_parser(calc_expr_env()).easy_parse(s),
      Ok((
        plus(
          Int(1),
          ite(
            lt(Int(1), Int(2)),
            plus(Int(1), Int(2)),
            times(Int(3), Int(4))
          )
        ),
        ""
      ))
    )
  }
  #[test]
  fn parse_value_bool() {
    let s = "true";
    assert_eq!(
      value_parser(calc_expr_env()).easy_parse(s),
      Ok((Value::VBool(true), ""))
    )
  }
  #[test]
  fn parse_value_int() {
    let s = "42";
    assert_eq!(
      value_parser(calc_expr_env()).easy_parse(s),
      Ok((Value::VInt(42), ""))
    )
  }
}
