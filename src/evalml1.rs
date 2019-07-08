use combine::parser::char::spaces;
use combine::{parser, tokens, ParseError, Stream};
use expr::*;
use std::fmt;

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

impl BProof {
  fn print(&self, f: &mut fmt::Formatter, offset: usize) -> fmt::Result {
    use self::BProofKind::*;
    match self {
      BProof(v, BPlus(l, r)) => write!(
        f,
        "{}{} plus {} is {} by B-Plus {{}}",
        " ".repeat(offset),
        l,
        r,
        v
      ),
      _ => unimplemented!(),
    }
  }
}

impl fmt::Display for BProof {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    self.print(f, 0)
  }
}

#[derive(Debug, PartialEq)]
pub enum EProofKind<'a> {
  EInt,
  EBool,
  EIfT(Box<EProof<'a>>, Box<EProof<'a>>),
  EIfF(Box<EProof<'a>>, Box<EProof<'a>>),
  EPlus(Box<EProof<'a>>, Box<EProof<'a>>, Box<BProof>),
  EMinus(Box<EProof<'a>>, Box<EProof<'a>>, Box<BProof>),
  ETimes(Box<EProof<'a>>, Box<EProof<'a>>, Box<BProof>),
  ELt(Box<EProof<'a>>, Box<EProof<'a>>, Box<BProof>),
}

#[derive(Debug, PartialEq)]
pub struct EProof<'a>(&'a Expr, Value, EProofKind<'a>);

pub fn prove<'a>(expr: &'a Expr) -> EProof<'a> {
  use self::EProofKind::*;
  use self::Expr::*;
  use self::Value::*;

  match expr {
    Int(i) => EProof(expr, VInt(*i), EInt),
    Bool(b) => EProof(expr, VBool(*b), EBool),
    Plus(l, r) => {
      let pl = prove(l.as_ref());
      let pr = prove(r.as_ref());
      let pb = b_plus(&pl.1, &pr.1);
      EProof(
        expr,
        pb.0.clone(),
        EPlus(Box::new(pl), Box::new(pr), Box::new(pb)),
      )
    }
    _ => unimplemented!(),
  }
}

impl<'a> EProof<'a> {
  fn print(&self, f: &mut fmt::Formatter, offset: usize) -> fmt::Result {
    use self::EProofKind::*;
    let print_binop =
      |f: &mut fmt::Formatter, rule: &str, l: &EProof, r: &EProof, b: &BProof| -> fmt::Result {
        write!(
          f,
          "{}{} evalto {} by {} {{\n",
          " ".repeat(offset),
          self.0,
          self.1,
          rule
        )?;
        l.print(f, offset + 2)?;
        write!(f, ";\n")?;
        r.print(f, offset + 2)?;
        write!(f, ";\n")?;
        b.print(f, offset + 2)?;
        write!(f, "\n{}}}", " ".repeat(offset))
      };
    match self {
      EProof(e, v, EInt) => write!(f, "{}{} evalto {} by E-Int {{}}", " ".repeat(offset), e, v),
      EProof(e, v, EBool) => write!(f, "{}{} evalto {} by E-Bool {{}}", " ".repeat(offset), e, v),
      EProof(_, _, EPlus(l, r, b)) => print_binop(f, "E-Plus", l.as_ref(), r.as_ref(), b),
      EProof(_, _, EMinus(l, r, b)) => print_binop(f, "E-Minus", l.as_ref(), r.as_ref(), b),
      EProof(_, _, ETimes(l, r, b)) => print_binop(f, "E-Times", l.as_ref(), r.as_ref(), b),
      EProof(_, _, ELt(l, r, b)) => print_binop(f, "E-Lt", l.as_ref(), r.as_ref(), b),
      _ => unimplemented!(),
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
  use self::BProofKind::*;
  use self::EProofKind::*;
  use super::super::expr::{Expr::*, Value::*};
  use super::*;
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
  #[test]
  fn prove_plus() {
    let e = plus(Int(3), Int(5));
    assert_eq!(
      prove(&e),
      EProof(
        &e,
        VInt(8),
        EPlus(
          Box::new(EProof(&Int(3), VInt(3), EInt)),
          Box::new(EProof(&Int(5), VInt(5), EInt)),
          Box::new(BProof(VInt(8), BPlus(VInt(3), VInt(5))))
        )
      )
    )
  }
}
