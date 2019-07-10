use combine::parser::char::{alpha_num, letter, string};
use combine::{
  attempt, char::spaces, optional, parser, satisfy, sep_by, token, tokens, ParseError, Parser,
  Stream,
};
use combine_language::{expression_parser, Assoc, Fixity, Identifier, LanguageDef, LanguageEnv};

#[derive(Debug, PartialEq, Clone)]
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

#[derive(Debug, PartialEq, Clone)]
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
        "true", "false", "if", "then", "else", "let", "rec", "in", "fun", "match", "with", "evalto",
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
  pub fn expr_parser[I]()(I) -> Expr
  where [
    I: Stream<Item = char>,
    I::Error: ParseError<char, I::Range, I::Position>,
    <I::Error as ParseError<I::Item, I::Range, I::Position>>::StreamError:
      From<::std::num::ParseIntError>,
  ]
  {
    expression_parser(app_parser(), op_parser(calc_expr_env()), op)
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
      expr_env.reserved("if").with(expr_parser()),
      expr_env.reserved("then").with(expr_parser()),
      expr_env.reserved("else").with(expr_parser())
    ).map(|(p, t, f)| ite(p, t, f))
  }
}

parser! {
  fn let_parser['a, I](expr_env: LanguageEnv<'a, I>)(I) -> Expr
  where [
    I: Stream<Item = char>,
    I::Error: ParseError<char, I::Range, I::Position>,
    <I::Error as ParseError<I::Item, I::Range, I::Position>>::StreamError:
      From<::std::num::ParseIntError>,
  ]
  {
    (
      expr_env.reserved("let").with(expr_env.identifier()),
      (spaces(), token('='), spaces()).with(expr_parser()),
      expr_env.reserved("in").with(expr_parser())
    ).map(|(var, def, body)| let_in(var, def, body))
  }
}

parser! {
  pub fn fun_parser['a, I](expr_env: LanguageEnv<'a, I>)(I) -> (String, Expr)
  where [
    I: Stream<Item = char>,
    I::Error: ParseError<char, I::Range, I::Position>,
    <I::Error as ParseError<I::Item, I::Range, I::Position>>::StreamError:
      From<::std::num::ParseIntError>,
  ]
  {
    (
      (spaces(), expr_env.reserved("fun"), spaces()).with(expr_env.identifier()),
      (spaces(), tokens(|l, r| l == r, "->".into(), "->".chars()),spaces())
        .with(expr_parser()).skip(spaces())
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
      if_parser(calc_expr_env()),
      let_parser(calc_expr_env()),
      fun_parser(calc_expr_env()).map(|(var, body)| fun(var, body)),
      expr_env.reserved("true").map(|_| Expr::Bool(true)),
      expr_env.reserved("false").map(|_| Expr::Bool(false)),
      (optional(token('-').skip(spaces())), expr_env.integer()).map(|(neg, x)| Expr::Int(
        match neg {
          None => x,
          Some(_) => -x,
        })
      ),
      expr_env.identifier().map(Expr::Ident),
      expr_env.parens(expr_parser())
    )
  }
}

parser! {
  fn app_parser[I]()(I) -> Expr
  where [
    I: Stream<Item = char>,
    I::Error: ParseError<char, I::Range, I::Position>,
    <I::Error as ParseError<I::Item, I::Range, I::Position>>::StreamError:
      From<::std::num::ParseIntError>,
  ]
  {
    (spaces().with(term_parser(calc_expr_env())).skip(spaces()), app_rest_parser()).map(|(mut f, v)| {
      for e in v.into_iter().rev() {
        f = app(f, e);
      }
      f
    })
  }
}

parser! {
  fn app_rest_parser[I]()(I) -> Vec<Expr>
  where [
    I: Stream<Item = char>,
    I::Error: ParseError<char, I::Range, I::Position>,
    <I::Error as ParseError<I::Item, I::Range, I::Position>>::StreamError:
      From<::std::num::ParseIntError>,
  ]
  {
    optional((app_arg_parser(calc_expr_env()).skip(spaces()), app_rest_parser())).map(|opt| {
      match opt {
        Some((e, mut v)) => {
          v.push(e);
          v
        }
        None => vec![],
      }
    })
  }
}

parser! {
  fn app_arg_parser['a, I](expr_env: LanguageEnv<'a, I>)(I) -> Expr
  where [
    I: Stream<Item = char>,
    I::Error: ParseError<char, I::Range, I::Position>,
    <I::Error as ParseError<I::Item, I::Range, I::Position>>::StreamError:
      From<::std::num::ParseIntError>,
  ]
  {
    choice!(
      if_parser(calc_expr_env()),
      let_parser(calc_expr_env()),
      fun_parser(calc_expr_env()).map(|(var, body)| fun(var, body)),
      expr_env.reserved("true").map(|_| Expr::Bool(true)),
      expr_env.reserved("false").map(|_| Expr::Bool(false)),
      expr_env.integer().map(Expr::Int),
      expr_env.parens(expr_parser()),
      attempt(expr_env.identifier().map(Expr::Ident))
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

pub fn let_in(var: String, def: Expr, body: Expr) -> Expr {
  Expr::Let(var, Box::new(def), Box::new(body))
}

pub fn app(f: Expr, x: Expr) -> Expr {
  Expr::App(Box::new(f), Box::new(x))
}

pub fn fun(var: String, body: Expr) -> Expr {
  Expr::Fun(var, Box::new(body))
}

#[derive(Debug, PartialEq, Clone)]
pub enum Value {
  VBool(bool),
  VInt(i64),
  VClosure { env: Env, var: String, expr: Expr },
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
      (
        expr_env.parens(env_parser()),
        expr_env.brackets(fun_parser(calc_expr_env()))
      ).map(|(env, (var, expr))| Value::VClosure { env, var, expr }),
      (optional(token('-').skip(spaces())), expr_env.integer()).map(|(neg, x)| Value::VInt(
        match neg {
          None => x,
          Some(_) => -x,
        })
      )
    )
  }
}

#[derive(Debug, PartialEq, Clone)]
pub struct EnvPair {
  pub var: String,
  pub value: Value,
}

pub fn env_pair(var: String, value: Value) -> EnvPair {
  EnvPair { var, value }
}

#[derive(Debug, PartialEq, Clone)]
pub struct Env(pub Vec<EnvPair>);

parser! {
  pub fn env_pair_parser['a, I](expr_env: LanguageEnv<'a, I>)(I) -> EnvPair
  where [
    I: Stream<Item = char>,
    I::Error: ParseError<char, I::Range, I::Position>,
    <I::Error as ParseError<I::Item, I::Range, I::Position>>::StreamError:
      From<::std::num::ParseIntError>,
  ]
  {
    (
      expr_env.identifier().skip(spaces()).skip(token('=')).skip(spaces()),
      value_parser(calc_expr_env())
    ).map(|(s, v)| env_pair(s, v))
  }
}

parser! {
  pub fn env_parser[I]()(I) -> Env
  where [
    I: Stream<Item = char>,
    I::Error: ParseError<char, I::Range, I::Position>,
    <I::Error as ParseError<I::Item, I::Range, I::Position>>::StreamError:
      From<::std::num::ParseIntError>,
  ]
  {
    sep_by(env_pair_parser(calc_expr_env()), (spaces(), token(','), spaces())).map(Env)
  }
}

use std::fmt;

impl fmt::Display for Expr {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    use self::Expr::*;
    match self {
      Bool(b) => b.fmt(f),
      Int(i) => i.fmt(f),
      Ident(s) => s.fmt(f),
      Plus(l, r) => write!(f, "({} + {})", l, r),
      Minus(l, r) => write!(f, "({} - {})", l, r),
      Times(l, r) => write!(f, "({} * {})", l, r),
      Lt(l, r) => write!(f, "({} < {})", l, r),
      If(ep, et, ef) => write!(f, "(if {} then {} else {})", ep, et, ef),
      Let(s, d, b) => write!(f, "(let {} = {} in {})", s, d, b),
      Fun(_, _) => unimplemented!(),
      App(_, _) => unimplemented!(),
      LetRec(_, _, _, _) => unimplemented!(),
      Nil => write!(f, "[]"),
      Cons(_, _) => unimplemented!(),
      Match(_, _, _, _, _) => unimplemented!(),
    }
  }
}

impl fmt::Display for Value {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    use self::Value::*;
    match self {
      VBool(b) => b.fmt(f),
      VInt(i) => i.fmt(f),
      VClosure { env, var, expr } => write!(f, "({})[fun {} -> {}]", env, var, expr),
      VNil => write!(f, "[]"),
      VCons(_, _) => unimplemented!(),
    }
  }
}

impl fmt::Display for Env {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    let env = &self.0;
    for (i, EnvPair { var, value }) in env.iter().enumerate() {
      write!(f, "{} = {}", var, value)?;
      if i < env.len() - 1 {
        write!(f, ", ")?;
      } else {
        write!(f, " ")?;
      }
    }
    Ok(())
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
      expr_parser().easy_parse(s),
      Ok((minus(plus(Int(1), times(Int(2), Int(3))), Int(4)), ""))
    )
  }
  #[test]
  fn parse_expr2() {
    let s = " 1 + 2 * 3 - 4";
    assert_eq!(
      expr_parser().easy_parse(s),
      Ok((minus(plus(Int(1), times(Int(2), Int(3))), Int(4)), ""))
    )
  }
  #[test]
  fn parse_ident() {
    let s = "foo";
    assert_eq!(
      expr_parser().easy_parse(s),
      Ok((Ident("foo".to_owned()), ""))
    )
  }
  #[test]
  fn parse_bool() {
    let s = "true";
    assert_eq!(expr_parser().easy_parse(s), Ok((Bool(true), "")))
  }
  #[test]
  fn parse_negative_int() {
    let s = "-42";
    assert_eq!(expr_parser().easy_parse(s), Ok((Int(-42), "")))
  }
  #[test]
  fn parse_if1() {
    let s = "if 1 < 2 then 1 + 2 else 3 * 4";
    assert_eq!(
      expr_parser().easy_parse(s),
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
      expr_parser().easy_parse(s),
      Ok((plus(Int(1), ite(Bool(true), Int(1), Int(3))), ""))
    )
  }
  #[test]
  fn parse_if3() {
    let s = "1 + if 1 < 2 then 1 + 2 else 3 * 4";
    assert_eq!(
      expr_parser().easy_parse(s),
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
  #[test]
  fn parse_value_negative_int() {
    let s = "-42";
    assert_eq!(
      value_parser(calc_expr_env()).easy_parse(s),
      Ok((Value::VInt(-42), ""))
    )
  }
  #[test]
  fn parse_let1() {
    let s = "let x = 1 in x + 2";
    assert_eq!(
      expr_parser().easy_parse(s),
      Ok((
        let_in("x".to_owned(), Int(1), plus(Ident("x".to_owned()), Int(2))),
        ""
      ))
    )
  }
  #[test]
  fn parse_value_closure() {
    use self::Value::*;
    let s = "(y=2)[fun x -> x + y]";
    assert_eq!(
      value_parser(calc_expr_env()).easy_parse(s),
      Ok((
        VClosure {
          env: Env(vec![env_pair("y".to_owned(), VInt(2))]),
          var: "x".to_owned(),
          expr: plus(Ident("x".to_owned()), Ident("y".to_owned()))
        },
        ""
      ))
    )
  }
  #[test]
  fn parse_apply() {
    let s = "f 1 2";
    assert_eq!(
      expr_parser().easy_parse(s),
      Ok((app(app(Ident("f".to_owned()), Int(1)), Int(2)), ""))
    )
  }
  #[test]
  fn parse_fun() {
    let s = "fun x -> x + 1";
    assert_eq!(
      expr_parser().easy_parse(s),
      Ok((fun("x".to_owned(), plus(Ident("x".to_owned()), Int(1))), ""))
    )
  }
  #[test]
  fn parse_apply_app_parser() {
    let s = "f 1 2";
    assert_eq!(
      app_parser().easy_parse(s),
      Ok((app(app(Ident("f".to_owned()), Int(1)), Int(2)), ""))
    )
  }
  #[test]
  fn parse_int_app_parser() {
    let s = "1";
    assert_eq!(app_parser().easy_parse(s), Ok((Int(1), "")))
  }
  #[test]
  fn parse_if0_app_parser() {
    let s = "if true then 1 else 2";
    assert_eq!(
      app_parser().easy_parse(s),
      Ok((ite(Bool(true), Int(1), Int(2)), ""))
    )
  }
  #[test]
  fn parse_if1_app_parser() {
    let s = "if 1 < 2 then 1 + 2 else 3 * 4";
    assert_eq!(
      app_parser().easy_parse(s),
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
  fn parse_if0_if_parser() {
    let s = "if true then 1 else 2";
    assert_eq!(
      if_parser(calc_expr_env()).easy_parse(s),
      Ok((ite(Bool(true), Int(1), Int(2)), ""))
    )
  }
  #[test]
  fn parse_if1_term_parser() {
    let s = "if 1 < 2 then 1 + 2 else 3 * 4";
    assert_eq!(
      term_parser(calc_expr_env()).easy_parse(s),
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
  fn parse_reserved_app_rest_parser() {
    let s = "then";
    assert_eq!(app_rest_parser().easy_parse(s), Ok((vec![], "then")))
  }
}
