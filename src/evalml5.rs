use combine::{parser, ParseError, Stream};
use combine_language::LanguageEnv;
use expr::*;
use std::fmt;

#[derive(Debug, PartialEq)]
pub struct Judgement {
  pub env: Env,
  pub expr: Expr,
  pub value: Value,
}

parser! {
  pub fn judgement_parser['a, I](expr_env: LanguageEnv<'a, I>)(I) -> Judgement
  where [
    I: Stream<Item = char>,
    I::Error: ParseError<char, I::Range, I::Position>,
    <I::Error as ParseError<I::Item, I::Range, I::Position>>::StreamError:
      From<::std::num::ParseIntError>,
  ]
  {
    (
      env_parser().skip(expr_env.reserved("|-")),
      expr_parser().skip(expr_env.reserved("evalto")),
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
pub enum EProofKind {
  EInt,
  EBool,
  EIfT(Box<EProof>, Box<EProof>),
  EIfF(Box<EProof>, Box<EProof>),
  EPlus(Box<EProof>, Box<EProof>, Box<BProof>),
  EMinus(Box<EProof>, Box<EProof>, Box<BProof>),
  ETimes(Box<EProof>, Box<EProof>, Box<BProof>),
  ELt(Box<EProof>, Box<EProof>, Box<BProof>),
  EVar,
  ELet(Box<EProof>, Box<EProof>),
  EFun,
  EApp(Box<EProof>, Box<EProof>, Box<EProof>),
  ELetRec(Box<EProof>),
  EAppRec(Box<EProof>, Box<EProof>, Box<EProof>),
  ENil,
  ECons(Box<EProof>, Box<EProof>),
  EMatchM1(Box<EProof>, Box<MProof>, Box<EProof>),
  EMatchM2(Box<EProof>, Box<MProof>, Box<EProof>),
  EMatchN(Box<EProof>, Box<NMProof>, Box<EProof>),
}

#[derive(Debug, PartialEq)]
pub struct EProof {
  env: Env,
  expr: Expr,
  value: Value,
  kind: EProofKind,
}

fn e_proof(env: Env, expr: Expr, value: Value, kind: EProofKind) -> EProof {
  EProof {
    env,
    expr,
    value,
    kind,
  }
}

fn prove_binop(
  env: Env,
  expr: Expr,
  l: Expr,
  r: Expr,
  b_prover: impl Fn(&Value, &Value) -> BProof,
  constructor: impl Fn(Box<EProof>, Box<EProof>, Box<BProof>) -> EProofKind,
) -> EProof {
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

pub fn prove(env: Env, expr: Expr) -> EProof {
  use self::EProofKind::*;
  use self::Expr::*;
  use self::Value::*;

  match expr.clone() {
    Int(i) => e_proof(env, expr, VInt(i), EInt),
    Bool(b) => e_proof(env, expr, VBool(b), EBool),
    Plus(l, r) => prove_binop(env, expr, *l, *r, b_plus, EPlus),
    Minus(l, r) => prove_binop(env, expr, *l, *r, b_minus, EMinus),
    Times(l, r) => prove_binop(env, expr, *l, *r, b_times, ETimes),
    Lt(l, r) => prove_binop(env, expr, *l, *r, b_lt, ELt),
    If(p, t, f) => {
      let pp = prove(env.clone(), *p);
      match pp.value {
        VBool(true) => {
          let pt = prove(env.clone(), *t);
          e_proof(
            env,
            expr,
            pt.value.clone(),
            EIfT(Box::new(pp), Box::new(pt)),
          )
        }
        VBool(false) => {
          let pf = prove(env.clone(), *f);
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
    Ident(x) => {
      if let Some(EnvPair { value, .. }) = env
        .0
        .clone()
        .into_iter()
        .rev()
        .find(|EnvPair { var, .. }| *var == x)
      {
        e_proof(env, expr, value, EVar)
      } else {
        panic!("Undefined variable")
      }
    }
    Let(var, def, body) => {
      let pdef = prove(env.clone(), *def);
      let mut next_env = env.clone();
      next_env.0.push(EnvPair {
        var: var.clone(),
        value: pdef.value.clone(),
      });
      let pbody = prove(next_env, *body);
      e_proof(
        env,
        expr,
        pbody.value.clone(),
        ELet(Box::new(pdef), Box::new(pbody)),
      )
    }
    Fun(var, body) => {
      let env2 = env.clone();
      e_proof(
        env,
        expr,
        VClosure {
          env: env2,
          var: var.to_owned(),
          expr: *body,
        },
        EFun,
      )
    }
    App(l, r) => {
      let pl = prove(env.clone(), *l);
      let pr = prove(env.clone(), *r);
      match pl.value.clone() {
        VClosure {
          env: mut env_cl,
          var,
          expr: body,
        } => {
          env_cl.0.push(env_pair(var, pr.value.clone()));
          let p_cl = prove(env_cl, body);
          e_proof(
            env,
            expr,
            p_cl.value.clone(),
            EApp(Box::new(pl), Box::new(pr), Box::new(p_cl)),
          )
        }
        VRec {
          env: mut env_cl,
          var,
          arg,
          expr: body,
        } => {
          env_cl.0.push(env_pair(var, pl.value.clone()));
          env_cl.0.push(env_pair(arg, pr.value.clone()));
          let p_cl = prove(env_cl, body);
          e_proof(
            env,
            expr,
            p_cl.value.clone(),
            EAppRec(Box::new(pl), Box::new(pr), Box::new(p_cl)),
          )
        }
        _ => panic!("Type error: not a closure"),
      }
    }
    LetRec(var, arg, def, body) => {
      let closure = VRec {
        env: env.clone(),
        var: var.clone(),
        arg,
        expr: *def,
      };
      let mut next_env = env.clone();
      next_env.0.push(EnvPair {
        var,
        value: closure,
      });
      let p = prove(next_env, *body);
      e_proof(env, expr, p.value.clone(), ELetRec(Box::new(p)))
    }
    Nil => e_proof(env, expr, VNil, ENil),
    Cons(l, r) => {
      let pl = prove(env.clone(), *l);
      let pr = prove(env.clone(), *r);
      e_proof(
        env,
        expr,
        v_cons(pl.value.clone(), pr.value.clone()),
        ECons(Box::new(pl), Box::new(pr)),
      )
    }
    Match(_, _) => unimplemented!(),
  }
}

impl EProof {
  fn print(&self, f: &mut fmt::Formatter, offset: usize) -> fmt::Result {
    use self::EProofKind::*;
    let print_binop =
      |f: &mut fmt::Formatter, rule: &str, l: &EProof, r: &EProof, b: &BProof| -> fmt::Result {
        write!(
          f,
          "{}{}|- {} evalto {} by {} {{\n",
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
        "{}{}|- {} evalto {} by E-Int {{}}",
        " ".repeat(offset),
        self.env,
        self.expr,
        self.value
      ),
      EBool => write!(
        f,
        "{}{}|- {} evalto {} by E-Bool {{}}",
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
          "{}{}|- {} evalto {} by E-IfT {{\n",
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
          "{}{}|- {} evalto {} by E-IfF {{\n",
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
      EVar => write!(
        f,
        "{}{}|- {} evalto {} by E-Var {{}}",
        " ".repeat(offset),
        self.env,
        self.expr,
        self.value
      ),
      ELet(pdef, pbody) => {
        write!(
          f,
          "{}{}|- {} evalto {} by E-Let {{\n",
          " ".repeat(offset),
          self.env,
          self.expr,
          self.value,
        )?;
        pdef.print(f, offset + 2)?;
        write!(f, ";\n")?;
        pbody.print(f, offset + 2)?;
        write!(f, "\n{}}}", " ".repeat(offset))
      }
      EFun => write!(
        f,
        "{}{}|- {} evalto {} by E-Fun {{}}",
        " ".repeat(offset),
        self.env,
        self.expr,
        self.value
      ),
      EApp(pl, pr, pcl) => {
        write!(
          f,
          "{}{}|- {} evalto {} by E-App {{\n",
          " ".repeat(offset),
          self.env,
          self.expr,
          self.value,
        )?;
        pl.print(f, offset + 2)?;
        write!(f, ";\n")?;
        pr.print(f, offset + 2)?;
        write!(f, ";\n")?;
        pcl.print(f, offset + 2)?;
        write!(f, "\n{}}}", " ".repeat(offset))
      }
      ELetRec(p) => {
        write!(
          f,
          "{}{}|- {} evalto {} by E-LetRec {{\n",
          " ".repeat(offset),
          self.env,
          self.expr,
          self.value,
        )?;
        p.print(f, offset + 2)?;
        write!(f, "\n{}}}", " ".repeat(offset))
      }
      EAppRec(pl, pr, pcl) => {
        write!(
          f,
          "{}{}|- {} evalto {} by E-AppRec {{\n",
          " ".repeat(offset),
          self.env,
          self.expr,
          self.value,
        )?;
        pl.print(f, offset + 2)?;
        write!(f, ";\n")?;
        pr.print(f, offset + 2)?;
        write!(f, ";\n")?;
        pcl.print(f, offset + 2)?;
        write!(f, "\n{}}}", " ".repeat(offset))
      }
      ENil => write!(
        f,
        "{}{}|- {} evalto {} by E-Nil {{}}",
        " ".repeat(offset),
        self.env,
        self.expr,
        self.value
      ),
      ECons(pl, pr) => {
        write!(
          f,
          "{}{}|- {} evalto {} by E-Cons {{\n",
          " ".repeat(offset),
          self.env,
          self.expr,
          self.value,
        )?;
        pl.print(f, offset + 2)?;
        write!(f, ";\n")?;
        pr.print(f, offset + 2)?;
        write!(f, "\n{}}}", " ".repeat(offset))
      }
      EMatchM1(p1, m, p2) => {
        write!(
          f,
          "{}{}|- {} evalto {} by E-MatchM1 {{\n",
          " ".repeat(offset),
          self.env,
          self.expr,
          self.value,
        )?;
        p1.print(f, offset + 2)?;
        write!(f, ";\n")?;
        m.print(f, offset + 2)?;
        write!(f, ";\n")?;
        p2.print(f, offset + 2)?;
        write!(f, "\n{}}}", " ".repeat(offset))
      }
      EMatchM2(p1, m, p2) => {
        write!(
          f,
          "{}{}|- {} evalto {} by E-MatchM2 {{\n",
          " ".repeat(offset),
          self.env,
          self.expr,
          self.value,
        )?;
        p1.print(f, offset + 2)?;
        write!(f, ";\n")?;
        m.print(f, offset + 2)?;
        write!(f, ";\n")?;
        p2.print(f, offset + 2)?;
        write!(f, "\n{}}}", " ".repeat(offset))
      }
      EMatchN(p1, n, p2) => {
        write!(
          f,
          "{}{}|- {} evalto {} by E-MatchM1 {{\n",
          " ".repeat(offset),
          self.env,
          self.expr,
          self.value,
        )?;
        p1.print(f, offset + 2)?;
        write!(f, ";\n")?;
        n.print(f, offset + 2)?;
        write!(f, ";\n")?;
        p2.print(f, offset + 2)?;
        write!(f, "\n{}}}", " ".repeat(offset))
      }
    }
  }
}

impl fmt::Display for EProof {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    self.print(f, 0)
  }
}

#[derive(Debug, PartialEq, Clone)]
pub struct MProof {
  pattern: Pattern,
  value: Value,
  env: Env,
  kind: MProofKind,
}

fn m_proof(pattern: Pattern, value: Value, env: Env, kind: MProofKind) -> MProof {
  MProof {
    pattern,
    value,
    env,
    kind,
  }
}

#[derive(Debug, PartialEq, Clone)]
pub enum MProofKind {
  MVar,
  MNil,
  MCons(Box<MProof>, Box<MProof>),
  MWild,
}

impl MProof {
  fn print(&self, f: &mut fmt::Formatter, offset: usize) -> fmt::Result {
    use self::MProofKind::*;
    match &self.kind {
      MVar => write!(
        f,
        "{}{} matches {} when ({}) by M-Var {{}}",
        " ".repeat(offset),
        self.pattern,
        self.value,
        self.env
      ),
      MNil => write!(
        f,
        "{}{} matches {} when ({}) by M-Nil {{}}",
        " ".repeat(offset),
        self.pattern,
        self.value,
        self.env
      ),
      MCons(l, r) => {
        write!(
          f,
          "{}{} matches {} when ({}) by M-Cons {{\n",
          " ".repeat(offset),
          self.pattern,
          self.value,
          self.env
        )?;
        l.print(f, offset + 2)?;
        write!(f, ";\n")?;
        r.print(f, offset + 2)?;
        write!(f, "\n{}}}", " ".repeat(offset))
      }
      MWild => write!(
        f,
        "{}{} matches {} when ({}) by M-Wild {{}}",
        " ".repeat(offset),
        self.pattern,
        self.value,
        self.env
      ),
    }
  }
}

impl fmt::Display for MProof {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    self.print(f, 0)
  }
}

#[derive(Debug, PartialEq, Clone)]
pub struct NMProof {
  pattern: Pattern,
  value: Value,
  kind: NMProofKind,
}

fn nm_proof(pattern: Pattern, value: Value, kind: NMProofKind) -> NMProof {
  NMProof {
    pattern,
    value,
    kind,
  }
}

#[derive(Debug, PartialEq, Clone)]
pub enum NMProofKind {
  NMConsNil,
  NMNilCons,
  NMConsConsL(Box<NMProof>),
  NMConsConsR(Box<NMProof>),
}

impl NMProof {
  fn print(&self, f: &mut fmt::Formatter, offset: usize) -> fmt::Result {
    use self::NMProofKind::*;
    match &self.kind {
      NMConsNil => write!(
        f,
        "{}{} doesn't match {} by NM-ConsNil {{}}",
        " ".repeat(offset),
        self.pattern,
        self.value,
      ),
      NMNilCons => write!(
        f,
        "{}{} doesn't match {} by NM-NilCons {{}}",
        " ".repeat(offset),
        self.pattern,
        self.value,
      ),
      NMConsConsL(p) => {
        write!(
          f,
          "{}{} doesn't match {} by NM-ConsConsL {{\n",
          " ".repeat(offset),
          self.pattern,
          self.value,
        )?;
        p.print(f, offset + 2)?;
        write!(f, "\n{}}}", " ".repeat(offset))
      }
      NMConsConsR(p) => {
        write!(
          f,
          "{}{} doesn't match {} by NM-ConsConsR {{\n",
          " ".repeat(offset),
          self.pattern,
          self.value,
        )?;
        p.print(f, offset + 2)?;
        write!(f, "\n{}}}", " ".repeat(offset))
      }
    }
  }
}

impl fmt::Display for NMProof {
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
      judgement_parser(calc_expr_env()).easy_parse(s),
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
  #[test]
  fn parse_judgement2() {
    let s = "|- 1 + 2 evalto 3";
    assert_eq!(
      judgement_parser(calc_expr_env()).easy_parse(s),
      Ok((judgement(Env(vec![]), plus(Int(1), Int(2)), VInt(3)), ""))
    )
  }
  #[test]
  fn parse_judgement3() {
    let s = "|- fun x -> x + 1 evalto ()[fun x -> x + 1]";
    assert_eq!(
      judgement_parser(calc_expr_env()).easy_parse(s),
      Ok((
        judgement(
          Env(vec![]),
          fun("x".to_owned(), plus(Ident("x".to_owned()), Int(1))),
          VClosure {
            env: Env(vec![]),
            var: "x".to_owned(),
            expr: plus(Ident("x".to_owned()), Int(1))
          }
        ),
        ""
      ))
    )
  }
}
