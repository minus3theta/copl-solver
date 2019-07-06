use combine::parser::char::spaces;
use combine::{parser, ParseError, Stream, tokens};
use expr::*;

#[derive(Debug, PartialEq)]
pub struct Judgement {
  expr: Expr,
  value: Value,
}

parser! {
  pub fn judgement_parser[I]()(I) -> Judgement
  where [
    I: Stream<Item = char>,
    I::Error: ParseError<char, I::Range, I::Position>,
    <I::Error as ParseError<I::Item, I::Range, I::Position>>::StreamError:
      From<::std::num::ParseIntError>,
  ]
  {
    (
      expr_parser(calc_expr_env()).skip((
        spaces(),
        tokens(|l, r| l == r, "evalto".into(), "evalto".chars()),
        spaces()
      )),
      value_parser(calc_expr_env())
    ).map(|(e, v)| {
      Judgement { expr: e, value: v }
    })
  }
}

pub fn judgement(expr: Expr, value: Value) -> Judgement {
  Judgement { expr, value }
}

#[derive(Debug, PartialEq)]
pub enum BProof {
  BPlus(Value, Value, Value),
  BMinus(Value, Value, Value),
  BTimes(Value, Value, Value),
  BLt(Value, Value, Value),
}

#[derive(Debug, PartialEq)]
pub enum EProof {
  EInt(Expr, Value),
  EBool(Expr, Value),
  EIfT(Expr, Value, Box<EProof>, Box<EProof>),
  EIfF(Expr, Value, Box<EProof>, Box<EProof>),
  EMinus(Expr, Value)
}

pub fn prove(expr: Expr) -> EProof {
  use self::Expr::*;
  use self::Value::*;
  use self::EProof::*;
  match expr {
    Bool(b) => EBool(Bool(b), VBool(b)),
    _ => unimplemented!()
  }
}

#[cfg(test)]
mod test {
  use super::*;
  use self::EProof::*;
  use super::super::expr::{Expr::*, Value::*};
  use combine::Parser;
  #[test]
  fn parse_judgement1() {
    let s = "1 + 2 evalto 3";
    assert_eq!(
      judgement_parser().easy_parse(s),
      Ok((judgement(plus(Int(1), Int(2)), VInt(3)), ""))
    )
  }
  #[test]
  fn prove_bool() {
    assert_eq!(prove(Bool(true)), EBool(Bool(true), VBool(true)))
  }
}
