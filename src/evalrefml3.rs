use combine::{optional, parser, ParseError, Stream};
use combine_language::LanguageEnv;
use expr::*;
use std::fmt;

#[derive(Debug, PartialEq)]
pub struct Judgement {
  pub pre_store: Store,
  pub env: Env,
  pub expr: Expr,
  pub value: Value,
  pub post_store: Store,
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
      optional(store_parser(calc_expr_env()).skip(expr_env.reserved("/"))).map(|opt| {
        opt.unwrap_or(Store::new())
      }),
      env_parser().skip(expr_env.reserved("|-")),
      expr_parser().skip(expr_env.reserved("evalto")),
      value_parser(calc_expr_env()),
      optional(expr_env.reserved("/").with(store_parser(calc_expr_env()))).map(|opt| {
        opt.unwrap_or(Store::new())
      })
    ).map(|(pre_store, env, expr, value, post_store)| {
      Judgement { pre_store, env, expr, value, post_store }
    })
  }
}

pub fn judgement(
  pre_store: Store,
  env: Env,
  expr: Expr,
  value: Value,
  post_store: Store,
) -> Judgement {
  Judgement {
    pre_store,
    env,
    expr,
    value,
    post_store,
  }
}

impl fmt::Display for Judgement {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(
      f,
      "{}/ {} |- {} evalto {} / {}",
      self.pre_store, self.env, self.expr, self.value, self.post_store
    )
  }
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
      } => print_binop(f, "times", "B-Mult", l, r, value),
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
  ERef(Box<EProof>),
  EDeref(Box<EProof>),
  EAssign(Box<EProof>, Box<EProof>),
}

impl EProofKind {
  fn extract(&self) -> (&str, Vec<&EProof>) {
    use evalrefml3::EProofKind::*;
    match self {
      EInt => ("E-Int", Vec::new()),
      EBool => ("E-Bool", Vec::new()),
      EIfT(l, r) => ("E-IfT", vec![l, r]),
      EIfF(l, r) => ("E-IfF", vec![l, r]),
      EVar => ("E-Var", Vec::new()),
      ELet(l, r) => ("E-Let", vec![l, r]),
      EFun => ("E-Fun", Vec::new()),
      EApp(p1, p2, p3) => ("E-App", vec![p1, p2, p3]),
      ELetRec(p) => ("E-LetRec", vec![p]),
      EAppRec(p1, p2, p3) => ("E-AppRec", vec![p1, p2, p3]),
      ERef(p) => ("E-Ref", vec![p]),
      EDeref(p) => ("E-Deref", vec![p]),
      EAssign(l, r) => ("E-Assign", vec![l, r]),
      _ => panic!("Illegal argument"),
    }
  }
}

#[derive(Debug, PartialEq)]
pub struct EProof {
  pre_store: Store,
  env: Env,
  expr: Expr,
  value: Value,
  post_store: Store,
  kind: EProofKind,
}

fn e_proof(
  pre_store: Store,
  env: Env,
  expr: Expr,
  value: Value,
  post_store: Store,
  kind: EProofKind,
) -> EProof {
  EProof {
    pre_store,
    env,
    expr,
    value,
    post_store,
    kind,
  }
}

fn prove_binop(
  pre_store: Store,
  env: Env,
  expr: Expr,
  l: Expr,
  r: Expr,
  locs: &mut Vec<Loc>,
  b_prover: impl Fn(&Value, &Value) -> BProof,
  constructor: impl Fn(Box<EProof>, Box<EProof>, Box<BProof>) -> EProofKind,
) -> EProof {
  let pl = prove(pre_store.clone(), env.clone(), l, locs);
  let pr = prove(pl.post_store.clone(), env.clone(), r, locs);
  let pb = b_prover(&pl.value, &pr.value);
  e_proof(
    pre_store,
    env,
    expr,
    pb.value.clone(),
    pr.post_store.clone(),
    constructor(Box::new(pl), Box::new(pr), Box::new(pb)),
  )
}

pub fn prove(pre_store: Store, env: Env, expr: Expr, locs: &mut Vec<Loc>) -> EProof {
  use self::EProofKind::*;
  use self::Expr::*;
  use self::Value::*;

  match expr.clone() {
    Int(i) => e_proof(pre_store.clone(), env, expr, VInt(i), pre_store, EInt),
    Bool(b) => e_proof(pre_store.clone(), env, expr, VBool(b), pre_store, EBool),
    Plus(l, r) => prove_binop(pre_store, env, expr, *l, *r, locs, b_plus, EPlus),
    Minus(l, r) => prove_binop(pre_store, env, expr, *l, *r, locs, b_minus, EMinus),
    Times(l, r) => prove_binop(pre_store, env, expr, *l, *r, locs, b_times, ETimes),
    Lt(l, r) => prove_binop(pre_store, env, expr, *l, *r, locs, b_lt, ELt),
    If(p, t, f) => {
      let pp = prove(pre_store.clone(), env.clone(), *p, locs);
      match pp.value {
        VBool(true) => {
          let pt = prove(pp.post_store.clone(), env.clone(), *t, locs);
          e_proof(
            pre_store,
            env,
            expr,
            pt.value.clone(),
            pt.post_store.clone(),
            EIfT(Box::new(pp), Box::new(pt)),
          )
        }
        VBool(false) => {
          let pf = prove(pp.post_store.clone(), env.clone(), *f, locs);
          e_proof(
            pre_store,
            env,
            expr,
            pf.value.clone(),
            pf.post_store.clone(),
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
        e_proof(pre_store.clone(), env, expr, value, pre_store, EVar)
      } else {
        panic!("Undefined variable")
      }
    }
    Let(var, def, body) => {
      let pdef = prove(pre_store.clone(), env.clone(), *def, locs);
      let mut next_env = env.clone();
      next_env.0.push(EnvPair {
        var: var.clone(),
        value: pdef.value.clone(),
      });
      let pbody = prove(pdef.post_store.clone(), next_env, *body, locs);
      e_proof(
        pre_store,
        env,
        expr,
        pbody.value.clone(),
        pbody.post_store.clone(),
        ELet(Box::new(pdef), Box::new(pbody)),
      )
    }
    Fun(var, body) => {
      let env2 = env.clone();
      e_proof(
        pre_store.clone(),
        env,
        expr,
        VClosure {
          env: env2,
          var: var.to_owned(),
          expr: *body,
        },
        pre_store,
        EFun,
      )
    }
    App(l, r) => {
      let pl = prove(pre_store.clone(), env.clone(), *l, locs);
      let pr = prove(pl.post_store.clone(), env.clone(), *r, locs);
      match pl.value.clone() {
        VClosure {
          env: mut env_cl,
          var,
          expr: body,
        } => {
          env_cl.0.push(env_pair(var, pr.value.clone()));
          let p_cl = prove(pr.post_store.clone(), env_cl, body, locs);
          e_proof(
            pre_store,
            env,
            expr,
            p_cl.value.clone(),
            p_cl.post_store.clone(),
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
          let p_cl = prove(pr.post_store.clone(), env_cl, body, locs);
          e_proof(
            pre_store.clone(),
            env,
            expr,
            p_cl.value.clone(),
            p_cl.post_store.clone(),
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
      let p = prove(pre_store.clone(), next_env, *body, locs);
      e_proof(
        pre_store,
        env,
        expr,
        p.value.clone(),
        p.post_store.clone(),
        ELetRec(Box::new(p)),
      )
    }
    Ref(e) => {
      let p = prove(pre_store.clone(), env.clone(), *e, locs);
      let loc = locs.pop().unwrap();
      let mut post_store = p.post_store.clone();
      post_store.push(loc.clone(), p.value.clone());
      e_proof(
        pre_store,
        env,
        expr,
        VLoc { loc },
        post_store,
        ERef(Box::new(p)),
      )
    }
    Deref(e) => {
      let p = prove(pre_store.clone(), env.clone(), *e, locs);
      match p.value.clone() {
        VLoc { loc } => match p.post_store.find(loc) {
          Some(v) => e_proof(
            pre_store,
            env,
            expr,
            v,
            p.post_store.clone(),
            EDeref(Box::new(p)),
          ),
          None => panic!("Undefined reference"),
        },
        _ => panic!("Not a reference"),
      }
    }
    Assign(l, r) => {
      let pl = prove(pre_store.clone(), env.clone(), *l, locs);
      let loc = if let VLoc { loc } = pl.value.clone() {
        loc
      } else {
        panic!("Not a reference");
      };
      let pr = prove(pl.post_store.clone(), env.clone(), *r, locs);
      let mut post_store = pr.post_store.clone();
      post_store.replace(loc, pr.value.clone());
      e_proof(
        pre_store,
        env,
        expr,
        pr.value.clone(),
        post_store,
        EAssign(Box::new(pl), Box::new(pr)),
      )
    }
    _ => panic!("Unsupported expression"),
  }
}

impl EProof {
  fn print(&self, f: &mut fmt::Formatter, offset: usize) -> fmt::Result {
    use self::EProofKind::*;
    let print_binop =
      |f: &mut fmt::Formatter, rule: &str, l: &EProof, r: &EProof, b: &BProof| -> fmt::Result {
        write!(
          f,
          "{}{}{}{}|- {} evalto {} {}{}by {} {{\n",
          " ".repeat(offset),
          self.pre_store,
          self.pre_store.separator(),
          self.env,
          self.expr,
          self.value,
          self.post_store.separator(),
          self.post_store,
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
      EPlus(l, r, b) => print_binop(f, "E-Plus", l.as_ref(), r.as_ref(), b.as_ref()),
      EMinus(l, r, b) => print_binop(f, "E-Minus", l.as_ref(), r.as_ref(), b.as_ref()),
      ETimes(l, r, b) => print_binop(f, "E-Mult", l.as_ref(), r.as_ref(), b.as_ref()),
      ELt(l, r, b) => print_binop(f, "E-Lt", l.as_ref(), r.as_ref(), b.as_ref()),
      k => {
        let (rule, proofs) = k.extract();
        write!(
          f,
          "{}{}{}{}|- {} evalto {} {}{}by {} ",
          " ".repeat(offset),
          self.pre_store,
          self.pre_store.separator(),
          self.env,
          self.expr,
          self.value,
          self.post_store.separator(),
          self.post_store,
          rule
        )?;
        let n = proofs.len();
        if n == 0 {
          return write!(f, "{{}}");
        }
        write!(f, "{{\n")?;
        for (i, p) in proofs.iter().enumerate() {
          p.print(f, offset + 2)?;
          if i == n - 1 {
            write!(f, "\n")?;
          } else {
            write!(f, ";\n")?;
          }
        }
        write!(f, "{}}}", " ".repeat(offset))
      }
    }
  }
}

impl fmt::Display for EProof {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    self.print(f, 0)
  }
}

#[cfg(test)]
mod test {
  use super::super::expr::{store, store_pair, Expr::*, Value::*};
  use super::*;
  use combine::Parser;
  #[test]
  fn parse_store() {
    let s = "@l1 = 1, @l2 = true";
    assert_eq!(
      store_parser(calc_expr_env()).easy_parse(s),
      Ok((
        store(vec![
          store_pair("l1".to_owned(), VInt(1)),
          store_pair("l2".to_owned(), VBool(true)),
        ]),
        ""
      ))
    )
  }
  #[test]
  fn parse_ref() {
    let s = "! ref x";
    assert_eq!(
      expr_parser().easy_parse(s),
      Ok((Deref(Box::new(Ref(Box::new(Ident("x".to_owned()))))), ""))
    )
  }
  #[test]
  fn parse_ref2() {
    let s = "!ref x";
    assert_eq!(
      expr_parser().easy_parse(s),
      Ok((Deref(Box::new(Ref(Box::new(Ident("x".to_owned()))))), ""))
    )
  }
}
