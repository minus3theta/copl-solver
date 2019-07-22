use combine::{many, optional, parser, sep_by, ParseError, Stream};
use combine_language::LanguageEnv;
use expr::*;

use std::collections::HashMap;
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

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct TypeVar(usize);

#[derive(Debug, PartialEq, Clone)]
pub struct TypeVarFactory {
  current: usize,
}

impl TypeVarFactory {
  pub fn new() -> Self {
    Self { current: 0 }
  }
  pub fn get(&mut self) -> TypeVar {
    let ret = TypeVar(self.current);
    self.current += 1;
    ret
  }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Type {
  TVar(TypeVar),
  TBool,
  TInt,
  TFun(Box<Type>, Box<Type>),
  TList(Box<Type>),
}

#[derive(Debug, PartialEq, Clone)]
pub struct TypeEnv(Vec<(String, Type)>);

#[derive(Debug, PartialEq, Clone)]
pub struct TypeScheme {
  pub scheme: Vec<TypeVar>,
  pub typ: Type,
}

impl TypeEnv {
  pub fn new() -> Self {
    Self(Vec::new())
  }
  pub fn push(&mut self, var: String, typ: Type) {
    self.0.push((var, typ));
  }
}

#[derive(Debug, PartialEq, Clone)]
pub struct TypeSubst(HashMap<TypeVar, Type>);

impl TypeSubst {
  pub fn new() -> Self {
    Self(HashMap::new())
  }
  pub fn substitute(&self, typ: &Type) -> Type {
    use self::Type::*;
    match typ {
      TVar(x) => match self.0.get(x) {
        None => TVar(x.clone()),
        Some(t) => t.clone(),
      },
      TBool => TBool,
      TInt => TInt,
      TFun(l, r) => TFun(
        Box::new(self.substitute(l.as_ref())),
        Box::new(self.substitute(r.as_ref())),
      ),
      TList(x) => TList(Box::new(self.substitute(x.as_ref()))),
    }
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

impl fmt::Display for TypeVar {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    if self.0 < 26 {
      write!(f, "'{}", char::from(self.0 as u8))
    } else {
      write!(f, "'{}", self.0)
    }
  }
}

impl fmt::Display for Type {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    use self::Type::*;
    match self {
      TVar(v) => write!(f, "{}", v),
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

pub fn prove(env: TypeEnv, expr: Expr, fac: &mut TypeVarFactory) -> (TypeSubst, TProof) {
  use self::Expr::*;
  use self::TProofKind::*;
  use self::Type::*;
  match expr.clone() {
    Int(_) => (
      TypeSubst::new(),
      TProof {
        env,
        expr,
        typ: TInt,
        kind: TPInt,
      },
    ),
    Bool(_) => (
      TypeSubst::new(),
      TProof {
        env,
        expr,
        typ: TBool,
        kind: TPBool,
      },
    ),
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
  #[test]
  fn type_substitute() {
    let mut sub = TypeSubst::new();
    sub.0.insert(TypeVar(0), TInt);
    assert_eq!(
      sub.substitute(&TFun(
        Box::new(TBool),
        Box::new(TList(Box::new(TVar(TypeVar(0)))))
      )),
      TFun(Box::new(TBool), Box::new(TList(Box::new(TInt))))
    )
  }
}
