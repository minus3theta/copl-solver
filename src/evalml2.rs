use combine::parser::char::spaces;
use combine::{parser, tokens, ParseError, Stream};
use expr::*;
use std::fmt;

#[derive(Debug, PartialEq)]
pub struct Judgement {
  pub env: Env,
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
      env_parser().skip((
        spaces(),
        tokens(|l, r| l == r, "|-".into(), "|-".chars()),
        spaces(),
      )),
      expr_parser(calc_expr_env()).skip((
        spaces(),
        tokens(|l, r| l == r, "evalto".into(), "evalto".chars()),
        spaces()
      )),
      value_parser(calc_expr_env())
    ).map(|(env, e, v)| {
      Judgement { env, expr: e, value: v }
    })
  }
}

pub fn judgement(env: Env, expr: Expr, value: Value) -> Judgement {
  Judgement { env, expr, value }
}

#[derive(Debug, PartialEq)]
pub enum BProofKind {
  BPlus(Value, Value),
  BMinus(Value, Value),
  BTimes(Value, Value),
  BLt(Value, Value),
}

#[derive(Debug, PartialEq)]
pub struct BProof {
  value: Value,
  kind: BProofKind,
}

fn b_proof(value: Value, kind: BProofKind) -> BProof {
  BProof { value, kind }
}

fn b_plus(l: &Value, r: &Value) -> BProof {
  use self::Value::VInt;
  if let (VInt(l), VInt(r)) = (l, r) {
    b_proof(VInt(l + r), BProofKind::BPlus(VInt(*l), VInt(*r)))
  } else {
    panic!("Type error")
  }
}

fn b_minus(l: &Value, r: &Value) -> BProof {
  use self::Value::VInt;
  if let (VInt(l), VInt(r)) = (l, r) {
    b_proof(VInt(l - r), BProofKind::BMinus(VInt(*l), VInt(*r)))
  } else {
    panic!("Type error")
  }
}

fn b_times(l: &Value, r: &Value) -> BProof {
  use self::Value::VInt;
  if let (VInt(l), VInt(r)) = (l, r) {
    b_proof(VInt(l * r), BProofKind::BTimes(VInt(*l), VInt(*r)))
  } else {
    panic!("Type error")
  }
}

fn b_lt(l: &Value, r: &Value) -> BProof {
  use self::Value::{VBool, VInt};
  if let (VInt(l), VInt(r)) = (l, r) {
    b_proof(VBool(l < r), BProofKind::BLt(VInt(*l), VInt(*r)))
  } else {
    panic!("Type error")
  }
}

impl BProof {
  fn print(&self, f: &mut fmt::Formatter, offset: usize) -> fmt::Result {
    use self::BProofKind::*;
    let print_binop = |f: &mut fmt::Formatter,
                       op: &str,
                       rule: &str,
                       l: &Value,
                       r: &Value,
                       v: &Value|
     -> fmt::Result {
      write!(
        f,
        "{}{} {} {} is {} by {} {{}}",
        " ".repeat(offset),
        l,
        op,
        r,
        v,
        rule
      )
    };
    match self {
      BProof {
        value,
        kind: BPlus(l, r),
      } => print_binop(f, "plus", "B-Plus", l, r, value),
      BProof {
        value,
        kind: BMinus(l, r),
      } => print_binop(f, "minus", "B-Minus", l, r, value),
      BProof {
        value,
        kind: BTimes(l, r),
      } => print_binop(f, "times", "B-Times", l, r, value),
      BProof {
        value,
        kind: BLt(l, r),
      } => print_binop(f, "less than", "B-Lt", l, r, value),
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
pub struct EProof<'a> {
  env: Env,
  expr: &'a Expr,
  value: Value,
  kind: EProofKind<'a>,
}

fn e_proof<'a>(env: Env, expr: &'a Expr, value: Value, kind: EProofKind<'a>) -> EProof<'a> {
  EProof {
    env,
    expr,
    value,
    kind,
  }
}

fn prove_binop<'a, 'l, 'r>(
  env: Env,
  expr: &'a Expr,
  l: &'l Expr,
  r: &'r Expr,
  b_prover: impl Fn(&Value, &Value) -> BProof,
  constructor: impl Fn(Box<EProof<'l>>, Box<EProof<'r>>, Box<BProof>) -> EProofKind<'a>,
) -> EProof<'a> {
  let pl = prove(env.clone(), l);
  let pr = prove(env.clone(), r);
  let pb = b_prover(&pl.value, &pr.value);
  e_proof(
    env,
    expr,
    pb.value.clone(),
    constructor(Box::new(pl), Box::new(pr), Box::new(pb)),
  )
}

pub fn prove<'a>(env: Env, expr: &'a Expr) -> EProof<'a> {
  use self::EProofKind::*;
  use self::Expr::*;
  use self::Value::*;

  match expr {
    Int(i) => e_proof(env, expr, VInt(*i), EInt),
    Bool(b) => e_proof(env, expr, VBool(*b), EBool),
    Plus(l, r) => prove_binop(env, expr, l.as_ref(), r.as_ref(), b_plus, EPlus),
    Minus(l, r) => prove_binop(env, expr, l.as_ref(), r.as_ref(), b_minus, EMinus),
    Times(l, r) => prove_binop(env, expr, l.as_ref(), r.as_ref(), b_times, ETimes),
    Lt(l, r) => prove_binop(env, expr, l.as_ref(), r.as_ref(), b_lt, ELt),
    If(p, t, f) => {
      let pp = prove(env.clone(), p.as_ref());
      match pp.value {
        VBool(true) => {
          let pt = prove(env.clone(), t.as_ref());
          e_proof(
            env,
            expr,
            pt.value.clone(),
            EIfT(Box::new(pp), Box::new(pt)),
          )
        }
        VBool(false) => {
          let pf = prove(env.clone(), f.as_ref());
          e_proof(
            env,
            expr,
            pf.value.clone(),
            EIfF(Box::new(pp), Box::new(pf)),
          )
        }
        _ => panic!("Type error"),
      }
    }
    _ => panic!("Unsupported expression"),
  }
}

impl<'a> EProof<'a> {
  fn print(&self, f: &mut fmt::Formatter, offset: usize) -> fmt::Result {
    use self::EProofKind::*;
    let print_binop =
      |f: &mut fmt::Formatter, rule: &str, l: &EProof, r: &EProof, b: &BProof| -> fmt::Result {
        write!(
          f,
          "{}{} |- {} evalto {} by {} {{\n",
          " ".repeat(offset),
          self.env,
          self.expr,
          self.value,
          rule
        )?;
        l.print(f, offset + 2)?;
        write!(f, ";\n")?;
        r.print(f, offset + 2)?;
        write!(f, ";\n")?;
        b.print(f, offset + 2)?;
        write!(f, "\n{}}}", " ".repeat(offset))
      };
    match &self.kind {
      EInt => write!(
        f,
        "{}{} |- {} evalto {} by E-Int {{}}",
        " ".repeat(offset),
        self.env,
        self.expr,
        self.value
      ),
      EBool => write!(
        f,
        "{}{} |- {} evalto {} by E-Bool {{}}",
        " ".repeat(offset),
        self.env,
        self.expr,
        self.value
      ),
      EPlus(l, r, b) => print_binop(f, "E-Plus", l.as_ref(), r.as_ref(), b.as_ref()),
      EMinus(l, r, b) => print_binop(f, "E-Minus", l.as_ref(), r.as_ref(), b.as_ref()),
      ETimes(l, r, b) => print_binop(f, "E-Times", l.as_ref(), r.as_ref(), b.as_ref()),
      ELt(l, r, b) => print_binop(f, "E-Lt", l.as_ref(), r.as_ref(), b.as_ref()),
      EIfT(pp, pt) => {
        write!(
          f,
          "{}{} |- {} evalto {} by E-IfT {{\n",
          " ".repeat(offset),
          self.env,
          self.expr,
          self.value,
        )?;
        pp.print(f, offset + 2)?;
        write!(f, ";\n")?;
        pt.print(f, offset + 2)?;
        write!(f, "\n{}}}", " ".repeat(offset))
      }
      EIfF(pp, pf) => {
        write!(
          f,
          "{}{} |- {} evalto {} by E-IfF {{\n",
          " ".repeat(offset),
          self.env,
          self.expr,
          self.value,
        )?;
        pp.print(f, offset + 2)?;
        write!(f, ";\n")?;
        pf.print(f, offset + 2)?;
        write!(f, "\n{}}}", " ".repeat(offset))
      }
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
  use super::super::expr::{Expr::*, Value::*};
  use super::*;
  use combine::Parser;
  #[test]
  fn parse_judgement1() {
    let s = "x = 3, y = 2 |- x evalto 3";
    assert_eq!(
      judgement_parser().easy_parse(s),
      Ok((
        judgement(
          Env(vec![
            env_pair("x".to_owned(), VInt(3)),
            env_pair("y".to_owned(), VInt(2))
          ]),
          Ident("x".to_owned()),
          VInt(3)
        ),
        ""
      ))
    )
  }
}
