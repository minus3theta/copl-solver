use combine::parser::char::spaces;
use combine::{parser, ParseError, Stream, tokens};
use expr::*;

#[derive(Debug, PartialEq)]
pub struct Judgement {
  pub expr: Expr,
  pub value: Value,
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
pub enum BProofKind {
  BPlus(Value, Value),
  BMinus(Value, Value),
  BTimes(Value, Value),
  BLt(Value, Value),
}

#[derive(Debug, PartialEq)]
pub struct BProof(Value, BProofKind);

fn b_plus<'a>(l: &'a Value, r: &'a Value) -> BProof {
  use self::Value::VInt;
  if let (VInt(l), VInt(r)) = (l, r) {
    BProof(VInt(l + r), BProofKind::BPlus(VInt(*l), VInt(*r)))
  } else {
    panic!("Type error")
  }
}

#[derive(Debug, PartialEq)]
pub enum EProofKind<'a> {
  EInt,
  EBool,
  EIfT(Box<EProof<'a>>, Box<EProof<'a>>),
  EIfF(Box<EProof<'a>>, Box<EProof<'a>>),
  EPlus(Box<EProof<'a>>, Box<EProof<'a>>, Box<BProof>),
  EMinus,
  ETimes,
  ELt,
}

#[derive(Debug, PartialEq)]
pub struct EProof<'a>(&'a Expr, Value, EProofKind<'a>);

pub fn prove<'a>(expr: &'a Expr) -> EProof<'a> {
  use self::Expr::*;
  use self::Value::*;
  use self::EProofKind::*;
  match expr {
    Int(i) => EProof(expr, VInt(*i), EInt),
    Bool(b) => EProof(expr, VBool(*b), EBool),
    // Plus(l, r) => {
    //   let EProof(_el, vl, pl) = prove(l.as_ref());
    //   let EProof(_er, vr, pr) = prove(r.as_ref());
    //   let BProof(vb, pb) = b_plus(&vl, &vr);
    //   EProof(expr, vb.clone(), EPlus(Box::new(pl), Box::new(pr), Box::new(pb)))
    // }
    _ => unimplemented!()
  }
}

use std::fmt;

impl<'a> EProof<'a> {
  fn print(&self, f: &mut fmt::Formatter, offset: usize) -> fmt::Result {
    use self::EProofKind::*;
    match self {
      EProof(e, v, EInt) => write!(f, "{}{} evalto {} by E-Int {{}}", " ".repeat(offset), e, v),
      EProof(e, v, EBool) => write!(f, "{}{} evalto {} by E-Bool {{}}", " ".repeat(offset), e, v),
      _ => unimplemented!()
    }
  }
}

impl<'a> fmt::Display for EProof<'a> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    self.print(f, 0)
  }
}

#[cfg(test)]
mod test {
  use super::*;
  use self::EProofKind::*;
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
    assert_eq!(prove(&Bool(true)), EProof(&Bool(true), VBool(true), EBool))
  }
}
