use combine::{many, optional, parser, sep_by, ParseError, Stream};
use combine_language::LanguageEnv;
use expr::*;
use std::fmt;

#[derive(Debug, PartialEq, Clone)]
pub struct TypeJudgement {
  pub env: TypeEnv,
  pub expr: Expr,
  pub typ: Type,
}

parser! {
  pub fn judgement_parser['a, I](expr_env: LanguageEnv<'a, I>)(I) -> TypeJudgement
  where [
    I: Stream<Item = char>,
    I::Error: ParseError<char, I::Range, I::Position>,
    <I::Error as ParseError<I::Item, I::Range, I::Position>>::StreamError:
      From<::std::num::ParseIntError>,
  ]
  {
    (
      type_env_parser(calc_expr_env()).skip(expr_env.reserved("|-")),
      expr_parser().skip(expr_env.reserved(":")),
      type_parser(calc_expr_env())
    ).map(|(env, expr, typ)| {
      TypeJudgement { env, expr, typ }
    })
  }
}

#[derive(Debug, PartialEq, Clone)]
pub enum Type {
  TBool,
  TInt,
  TFun(Box<Type>, Box<Type>),
  TList(Box<Type>),
}

#[derive(Debug, PartialEq, Clone)]
pub struct TypeEnv(Vec<(String, Type)>);

impl TypeEnv {
  pub fn new() -> Self {
    Self(Vec::new())
  }
  pub fn push(&mut self, var: String, typ: Type) {
    self.0.push((var, typ));
  }
}

parser! {
  pub fn type_atom_parser['a, I](expr_env: LanguageEnv<'a, I>)(I) -> Type
  where [
    I: Stream<Item = char>,
    I::Error: ParseError<char, I::Range, I::Position>,
    <I::Error as ParseError<I::Item, I::Range, I::Position>>::StreamError:
      From<::std::num::ParseIntError>,
  ]
  {
    choice!(
      expr_env.reserved("bool").map(|_| Type::TBool),
      expr_env.reserved("int").map(|_| Type::TInt),
      expr_env.parens(type_parser(calc_expr_env()))
    )
  }
}

parser! {
  pub fn type_term_parser['a, I](expr_env: LanguageEnv<'a, I>)(I) -> Type
  where [
    I: Stream<Item = char>,
    I::Error: ParseError<char, I::Range, I::Position>,
    <I::Error as ParseError<I::Item, I::Range, I::Position>>::StreamError:
      From<::std::num::ParseIntError>,
  ]
  {
    (
      type_atom_parser(calc_expr_env()),
      many::<Vec<_>, _>(expr_env.reserved("list"))
    ).map(|(mut t, v)| {
      for _ in 0 .. v.len() {
        t = Type::TList(Box::new(t));
      }
      t
    })
  }
}

parser! {
  pub fn type_parser['a, I](expr_env: LanguageEnv<'a, I>)(I) -> Type
  where [
    I: Stream<Item = char>,
    I::Error: ParseError<char, I::Range, I::Position>,
    <I::Error as ParseError<I::Item, I::Range, I::Position>>::StreamError:
      From<::std::num::ParseIntError>,
  ]
  {
    (
      type_term_parser(calc_expr_env()),
      optional(expr_env.reserved("->").with(type_parser(calc_expr_env())))
    ).map(|(l, r)| match r {
      None => l,
      Some(r) => Type::TFun(Box::new(l), Box::new(r)),
    })
  }
}

parser! {
  pub fn type_env_pair_parser['a, I](expr_env: LanguageEnv<'a, I>)(I) -> (String, Type)
  where [
    I: Stream<Item = char>,
    I::Error: ParseError<char, I::Range, I::Position>,
    <I::Error as ParseError<I::Item, I::Range, I::Position>>::StreamError:
      From<::std::num::ParseIntError>,
  ]
  {
    (
      expr_env.identifier(),
      expr_env.reserved(":").with(type_parser(calc_expr_env()))
    )
  }
}

parser! {
  pub fn type_env_parser['a, I](expr_env: LanguageEnv<'a, I>)(I) -> TypeEnv
  where [
    I: Stream<Item = char>,
    I::Error: ParseError<char, I::Range, I::Position>,
    <I::Error as ParseError<I::Item, I::Range, I::Position>>::StreamError:
      From<::std::num::ParseIntError>,
  ]
  {
    sep_by(type_env_pair_parser(calc_expr_env()), expr_env.reserved(",")).map(TypeEnv)
  }
}

impl fmt::Display for Type {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    use self::Type::*;
    match self {
      TBool => write!(f, "bool"),
      TInt => write!(f, "int"),
      TFun(l, r) => write!(f, "({} -> {})", l, r),
      TList(t) => write!(f, "{} list", t),
    }
  }
}

impl fmt::Display for TypeEnv {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    let env = &self.0;
    for (i, (var, typ)) in env.iter().enumerate() {
      write!(f, "{} : {}", var, typ)?;
      if i < env.len() - 1 {
        write!(f, ", ")?;
      } else {
        write!(f, " ")?;
      }
    }
    Ok(())
  }
}

#[derive(Debug, PartialEq, Clone)]
pub struct TProof {
  pub env: TypeEnv,
  pub expr: Expr,
  pub typ: Type,
  pub kind: TProofKind,
}

#[derive(Debug, PartialEq, Clone)]
pub enum TProofKind {
  TPInt,
  TPBool,
  TPIf(Box<TProof>, Box<TProof>, Box<TProof>),
  TPPlus(Box<TProof>, Box<TProof>),
  TPMinus(Box<TProof>, Box<TProof>),
  TPTimes(Box<TProof>, Box<TProof>),
  TPLt(Box<TProof>, Box<TProof>),
  TPVar,
  TPLet(Box<TProof>, Box<TProof>),
  TPFun(Box<TProof>),
  TPApp(Box<TProof>, Box<TProof>),
  TPLetRec(Box<TProof>, Box<TProof>),
  TPNil,
  TPCons(Box<TProof>, Box<TProof>),
  TPMatch(Box<TProof>, Box<TProof>, Box<TProof>),
}

pub fn prove(env: TypeEnv, expr: Expr, typ: Option<Type>) -> TProof {
  use self::Expr::*;
  use self::TProofKind::*;
  use self::Type::*;
  match expr.clone() {
    Int(_) => {
      if let Some(typ) = typ {
        assert_eq!(typ, TInt);
      }
      TProof {
        env,
        expr,
        typ: TInt,
        kind: TPInt,
      }
    }
    Bool(_) => {
      if let Some(typ) = typ {
        assert_eq!(typ, TBool);
      }
      TProof {
        env,
        expr,
        typ: TBool,
        kind: TPBool,
      }
    }
    If(p, t, f) => {
      let tp = prove(env.clone(), *p, Some(TBool));
      let tt = prove(env.clone(), *t, typ.clone());
      let tf = prove(env.clone(), *f, typ.clone());
      assert_eq!(tt.typ, tf.typ);
      TProof {
        env,
        expr,
        typ: tt.typ.clone(),
        kind: TPIf(Box::new(tp), Box::new(tt), Box::new(tf)),
      }
    }
    Plus(l, r) => {
      if let Some(typ) = typ {
        assert_eq!(typ, TInt);
      }
      let tl = prove(env.clone(), *l, Some(TInt));
      let tr = prove(env.clone(), *r, Some(TInt));
      TProof {
        env,
        expr,
        typ: TInt,
        kind: TPPlus(Box::new(tl), Box::new(tr)),
      }
    }
    Minus(l, r) => {
      if let Some(typ) = typ {
        assert_eq!(typ, TInt);
      }
      let tl = prove(env.clone(), *l, Some(TInt));
      let tr = prove(env.clone(), *r, Some(TInt));
      TProof {
        env,
        expr,
        typ: TInt,
        kind: TPMinus(Box::new(tl), Box::new(tr)),
      }
    }
    Times(l, r) => {
      if let Some(typ) = typ {
        assert_eq!(typ, TInt);
      }
      let tl = prove(env.clone(), *l, Some(TInt));
      let tr = prove(env.clone(), *r, Some(TInt));
      TProof {
        env,
        expr,
        typ: TInt,
        kind: TPTimes(Box::new(tl), Box::new(tr)),
      }
    }
    Lt(l, r) => {
      if let Some(typ) = typ {
        assert_eq!(typ, TBool);
      }
      let tl = prove(env.clone(), *l, Some(TInt));
      let tr = prove(env.clone(), *r, Some(TInt));
      TProof {
        env,
        expr,
        typ: TBool,
        kind: TPLt(Box::new(tl), Box::new(tr)),
      }
    }
    Ident(x) => {
      if let Some((_, t)) = env.0.clone().into_iter().rev().find(|(var, _)| *var == x) {
        if let Some(typ) = typ {
          assert_eq!(typ, t);
        }
        TProof {
          env,
          expr,
          typ: t,
          kind: TPVar,
        }
      } else {
        panic!("Undefined variable")
      }
    }
    Let(var, def, body) => {
      let td = prove(env.clone(), *def, None);
      let mut next_env = env.clone();
      next_env.push(var, td.typ.clone());
      let tb = prove(next_env, *body, typ.clone());
      if let Some(typ) = typ {
        assert_eq!(typ, tb.typ);
      }
      TProof {
        env,
        expr,
        typ: tb.typ.clone(),
        kind: TPLet(Box::new(td), Box::new(tb)),
      }
    }
    Fun(var, body) => {
      if let Some(TFun(l, r)) = typ {
        let mut next_env = env.clone();
        next_env.push(var, *l.clone());
        let t = prove(next_env, *body, Some(*r.clone()));
        TProof {
          env,
          expr,
          typ: TFun(l, r),
          kind: TPFun(Box::new(t)),
        }
      } else {
        panic!("Cannot decide type of function")
      }
    }
    _ => unimplemented!(),
  }
}

impl TProof {
  fn print(&self, f: &mut fmt::Formatter, offset: usize) -> fmt::Result {
    let (rule, proofs) = Self::extract(&self.kind);
    write!(
      f,
      "{}{}|- {} : {} by {} ",
      " ".repeat(offset),
      self.env,
      self.expr,
      self.typ,
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
  fn extract(kind: &TProofKind) -> (&str, Vec<&TProof>) {
    use self::TProofKind::*;
    match kind {
      TPInt => ("T-Int", Vec::new()),
      TPBool => ("T-Bool", Vec::new()),
      TPIf(p, t, f) => ("T-If", vec![p, t, f]),
      TPPlus(l, r) => ("T-Plus", vec![l, r]),
      TPMinus(l, r) => ("T-Minus", vec![l, r]),
      TPTimes(l, r) => ("T-Times", vec![l, r]),
      TPLt(l, r) => ("T-Lt", vec![l, r]),
      TPVar => ("T-Var", Vec::new()),
      TPLet(d, b) => ("T-Let", vec![d, b]),
      TPFun(f) => ("T-Fun", vec![f]),
      _ => unimplemented!(),
    }
  }
}

impl fmt::Display for TProof {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    self.print(f, 0)
  }
}

#[cfg(test)]
mod test {
  use super::super::expr::Expr::*;
  use super::Type::*;
  use super::*;
  use combine::Parser;
  #[test]
  fn parse_type_int() {
    let s = "int";
    assert_eq!(type_parser(calc_expr_env()).easy_parse(s), Ok((TInt, "")))
  }
  #[test]
  fn parse_type_list() {
    let s = "bool list list";
    assert_eq!(
      type_parser(calc_expr_env()).easy_parse(s),
      Ok((TList(Box::new(TList(Box::new(TBool)))), ""))
    )
  }
  #[test]
  fn parse_type_fun() {
    let s = "bool -> int -> int";
    assert_eq!(
      type_parser(calc_expr_env()).easy_parse(s),
      Ok((
        TFun(
          Box::new(TBool),
          Box::new(TFun(Box::new(TInt), Box::new(TInt)))
        ),
        ""
      ))
    )
  }
  #[test]
  fn parse_type_list_fun() {
    let s = "(bool -> int) list";
    assert_eq!(
      type_parser(calc_expr_env()).easy_parse(s),
      Ok((TList(Box::new(TFun(Box::new(TBool), Box::new(TInt)))), ""))
    )
  }
  #[test]
  fn parse_type_fun_list() {
    let s = "int list -> bool list";
    assert_eq!(
      type_parser(calc_expr_env()).easy_parse(s),
      Ok((
        TFun(
          Box::new(TList(Box::new(TInt))),
          Box::new(TList(Box::new(TBool)))
        ),
        ""
      ))
    )
  }
  #[test]
  fn parse_type_judge() {
    let s = "|- 3 + 5 : int";
    assert_eq!(
      judgement_parser(calc_expr_env()).easy_parse(s),
      Ok((
        TypeJudgement {
          env: TypeEnv::new(),
          expr: plus(Int(3), Int(5)),
          typ: TInt
        },
        ""
      ))
    )
  }
}
