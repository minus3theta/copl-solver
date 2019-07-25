use combine::parser::char::{lower, spaces};
use combine::{attempt, many, optional, parser, sep_by, token, ParseError, Stream};
use combine_language::LanguageEnv;
use expr::*;
use std::collections::{HashMap, HashSet};
use std::fmt;

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct TypeJudgement {
  pub env: TypeEnv,
  pub expr: Expr,
  pub typ: Type,
}

impl TypeJudgement {
  pub fn prove(self) -> Result<TProof, &'static str> {
    let used_tv = self
      .typ
      .ftv()
      .iter()
      .chain(self.env.ftv().iter())
      .map(|v| v.0)
      .max()
      .map(|x| x + 1);
    let mut fac = TypeVarFactory::new(used_tv.unwrap_or(0));
    let (subst, proof) = prove(self.env, self.expr, &mut fac)?;
    let mut formula: TypeFormula = subst.into();
    formula.push(self.typ, proof.typ.clone());
    let subst = formula.unify()?;
    Ok(subst.subst_tproof(proof))
  }
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

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub struct TypeVar(usize);

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct TypeVarFactory {
  current: usize,
}

impl TypeVarFactory {
  pub fn new(start: usize) -> Self {
    Self { current: start }
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

impl Type {
  pub fn is_free(&self, v: &TypeVar) -> bool {
    use self::Type::*;
    match self {
      TVar(x) => x == v,
      TBool | TInt => false,
      TFun(l, r) => l.is_free(v) || r.is_free(v),
      TList(t) => t.is_free(v),
    }
  }
  pub fn ftv(&self) -> HashSet<TypeVar> {
    use self::Type::*;
    match self {
      TVar(x) => [*x].iter().cloned().collect(),
      TBool | TInt => HashSet::new(),
      TFun(l, r) => l.ftv().union(&r.ftv()).cloned().collect(),
      TList(l) => l.ftv(),
    }
  }
  pub fn closure(self, env: &TypeEnv) -> TypeScheme {
    let scheme = self.ftv().into_iter().filter(|v| !env.is_free(v)).collect();
    TypeScheme { scheme, typ: self }
  }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct TypeScheme {
  pub scheme: Vec<TypeVar>,
  pub typ: Type,
}

impl TypeScheme {
  pub fn simple(typ: Type) -> Self {
    Self {
      scheme: Vec::new(),
      typ,
    }
  }
  pub fn is_free(&self, v: &TypeVar) -> bool {
    self.typ.is_free(v) && self.scheme.iter().all(|x| x != v)
  }
  pub fn ftv(&self) -> HashSet<TypeVar> {
    self
      .typ
      .ftv()
      .iter()
      .cloned()
      .filter(|v| self.is_free(v))
      .collect()
  }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct TypeEnv(Vec<(String, TypeScheme)>);

impl TypeEnv {
  pub fn new() -> Self {
    Self(Vec::new())
  }
  pub fn push(&mut self, var: String, typ: TypeScheme) {
    self.0.push((var, typ));
  }
  pub fn find<'a>(&'a self, var: &String) -> Option<&'a TypeScheme> {
    self.0.iter().rev().find(|(v, _)| v == var).map(|(_, t)| t)
  }
  pub fn is_free(&self, v: &TypeVar) -> bool {
    self.0.iter().any(|(_, t)| t.is_free(v))
  }
  pub fn ftv(&self) -> HashSet<TypeVar> {
    self
      .0
      .iter()
      .flat_map(|(_, t)| t.ftv().into_iter())
      .collect()
  }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct TypeSubst(HashMap<TypeVar, Type>);

impl TypeSubst {
  pub fn new() -> Self {
    Self(HashMap::new())
  }
  pub fn push(&mut self, typ: Type, var: TypeVar) {
    self.0.insert(var, typ);
  }
  pub fn singleton(typ: Type, var: TypeVar) -> Self {
    Self([(var, typ)].iter().cloned().collect())
  }
  pub fn subst_type(&self, typ: &Type) -> Type {
    use self::Type::*;
    match typ {
      TVar(x) => match self.0.get(x) {
        None => TVar(x.clone()),
        Some(t) => t.clone(),
      },
      TBool => TBool,
      TInt => TInt,
      TFun(l, r) => TFun(
        Box::new(self.subst_type(l.as_ref())),
        Box::new(self.subst_type(r.as_ref())),
      ),
      TList(x) => TList(Box::new(self.subst_type(x.as_ref()))),
    }
  }
  pub fn subst_type_scheme(&self, ts: &TypeScheme, fac: &mut TypeVarFactory) -> TypeScheme {
    let mut pre_subst = TypeSubst::new();
    let mut vs = Vec::new();
    for v in &ts.scheme {
      let new_var = fac.get();
      pre_subst.push(Type::TVar(new_var), *v);
      vs.push(new_var);
    }
    let pre_typ = pre_subst.subst_type(&ts.typ);
    let typ = self.subst_type(&pre_typ);
    TypeScheme { scheme: vs, typ }
  }
  pub fn subst_type_scheme_simple(&self, ts: &TypeScheme) -> TypeScheme {
    let subst = TypeSubst(
      self
        .0
        .clone()
        .into_iter()
        .filter(|(tv, _)| ts.is_free(tv))
        .collect(),
    );
    let typ = subst.subst_type(&ts.typ);
    TypeScheme {
      scheme: ts.scheme.clone(),
      typ,
    }
  }
  pub fn subst_type_env(&self, env: TypeEnv, fac: &mut TypeVarFactory) -> TypeEnv {
    TypeEnv(
      env
        .0
        .into_iter()
        .map(|(x, t)| (x, self.subst_type_scheme(&t, fac)))
        .collect(),
    )
  }
  pub fn subst_type_env_simple(&self, env: TypeEnv) -> TypeEnv {
    TypeEnv(
      env
        .0
        .into_iter()
        .map(|(x, t)| (x, self.subst_type_scheme_simple(&t)))
        .collect(),
    )
  }
  pub fn subst_type_formula(&self, fm: TypeFormula) -> TypeFormula {
    TypeFormula(
      fm.0
        .into_iter()
        .map(|(t1, t2)| (self.subst_type(&t1), self.subst_type(&t2)))
        .collect(),
    )
  }
  pub fn subst_tproof_box(&self, proof: Box<TProof>) -> Box<TProof> {
    Box::new(self.subst_tproof(*proof))
  }
  pub fn subst_tproof(&self, proof: TProof) -> TProof {
    use self::TProofKind::*;
    let TProof {
      env,
      expr,
      typ,
      kind,
    } = proof;
    TProof {
      env: self.subst_type_env_simple(env),
      expr,
      typ: self.subst_type(&typ),
      kind: match kind {
        TPIf(p, t, f) => TPIf(
          self.subst_tproof_box(p),
          self.subst_tproof_box(t),
          self.subst_tproof_box(f),
        ),
        TPPlus(l, r) => TPPlus(self.subst_tproof_box(l), self.subst_tproof_box(r)),
        TPMinus(l, r) => TPMinus(self.subst_tproof_box(l), self.subst_tproof_box(r)),
        TPTimes(l, r) => TPTimes(self.subst_tproof_box(l), self.subst_tproof_box(r)),
        TPLt(l, r) => TPLt(self.subst_tproof_box(l), self.subst_tproof_box(r)),
        TPLet(l, r) => TPLet(self.subst_tproof_box(l), self.subst_tproof_box(r)),
        TPFun(e) => TPFun(self.subst_tproof_box(e)),
        TPApp(l, r) => TPApp(self.subst_tproof_box(l), self.subst_tproof_box(r)),
        TPLetRec(l, r) => TPLetRec(self.subst_tproof_box(l), self.subst_tproof_box(r)),
        TPCons(l, r) => TPCons(self.subst_tproof_box(l), self.subst_tproof_box(r)),
        TPMatch(e1, e2, e3) => TPMatch(
          self.subst_tproof_box(e1),
          self.subst_tproof_box(e2),
          self.subst_tproof_box(e3),
        ),
        k => k,
      },
    }
  }
  pub fn compose(&mut self, typ: &Type, var: TypeVar) {
    let t = self.subst_type(typ);
    self.push(t, var);
  }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct TypeFormula(Vec<(Type, Type)>);

impl From<TypeSubst> for TypeFormula {
  fn from(subst: TypeSubst) -> Self {
    let vec = subst
      .0
      .into_iter()
      .map(|(v, t)| (Type::TVar(v), t))
      .collect();
    TypeFormula(vec)
  }
}

impl TypeFormula {
  pub fn push(&mut self, t1: Type, t2: Type) -> &mut Self {
    self.0.push((t1, t2));
    self
  }
  pub fn unify(mut self) -> Result<TypeSubst, &'static str> {
    use self::Type::*;
    match self.0.pop() {
      None => Ok(TypeSubst::new()),
      Some((t1, t2)) => {
        if t1 == t2 {
          return self.unify();
        }
        match (t1, t2) {
          (TVar(v), t) | (t, TVar(v)) => {
            if t.is_free(&v) {
              Err("Not a free variable")
            } else {
              let s1 = TypeSubst::singleton(t.clone(), v.clone());
              let mut s2 = s1.subst_type_formula(self).unify()?;
              s2.compose(&t, v);
              Ok(s2)
            }
          }
          (TFun(a1, b1), TFun(a2, b2)) => {
            self.push(*a1, *a2).push(*b1, *b2);
            self.unify()
          }
          (TList(t1), TList(t2)) => {
            self.push(*t1, *t2);
            self.unify()
          }
          _ => Err("Type mismatch"),
        }
      }
    }
  }
  pub fn append(&mut self, other: &mut Self) {
    self.0.append(&mut other.0);
  }
}

parser! {
  pub fn typevar_parser[I]()(I) -> TypeVar
  where [
    I: Stream<Item = char>,
    I::Error: ParseError<char, I::Range, I::Position>,
    <I::Error as ParseError<I::Item, I::Range, I::Position>>::StreamError:
      From<::std::num::ParseIntError>,
  ]
  {
    token('\'').with(lower()).map(|c| TypeVar(c as usize - 'a' as usize))
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
      typevar_parser().map(Type::TVar).skip(spaces()),
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
  pub fn typescheme_parser['a, I](expr_env: LanguageEnv<'a, I>)(I) -> TypeScheme
  where [
    I: Stream<Item = char>,
    I::Error: ParseError<char, I::Range, I::Position>,
    <I::Error as ParseError<I::Item, I::Range, I::Position>>::StreamError:
      From<::std::num::ParseIntError>,
  ]
  {
    (
      optional(attempt(sep_by(typevar_parser(), spaces()).skip(expr_env.reserved(".")))),
      type_parser(calc_expr_env())
    ).map(|(v, t)| TypeScheme { scheme: v.unwrap_or(Vec::new()), typ: t })
  }
}

parser! {
  pub fn type_env_pair_parser['a, I](expr_env: LanguageEnv<'a, I>)(I) -> (String, TypeScheme)
  where [
    I: Stream<Item = char>,
    I::Error: ParseError<char, I::Range, I::Position>,
    <I::Error as ParseError<I::Item, I::Range, I::Position>>::StreamError:
      From<::std::num::ParseIntError>,
  ]
  {
    (
      expr_env.identifier(),
      expr_env.reserved(":").with(typescheme_parser(calc_expr_env()))
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
      write!(f, "'{}", char::from('a' as u8 + self.0 as u8))
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

impl fmt::Display for TypeScheme {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    use self::Type::*;
    let n = self.scheme.len();
    for (i, v) in self.scheme.iter().enumerate() {
      if i == n - 1 {
        write!(f, "{}.", v)?;
      } else {
        write!(f, "{} ", v)?;
      }
    }
    match &self.typ {
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

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct TProof {
  pub env: TypeEnv,
  pub expr: Expr,
  pub typ: Type,
  pub kind: TProofKind,
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
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

fn prove_binop(
  env: TypeEnv,
  expr: Expr,
  l: Box<Expr>,
  r: Box<Expr>,
  fac: &mut TypeVarFactory,
  op: Op,
) -> Result<(TypeSubst, TProof), &'static str> {
  use self::Op::*;
  use self::TProofKind::*;
  use self::Type::{TBool, TInt};
  let (sl, pl) = prove(env.clone(), *l, fac)?;
  let (sr, pr) = prove(env.clone(), *r, fac)?;
  let mut fm: TypeFormula = sl.into();
  fm.append(&mut sr.into());
  fm.push(pl.typ.clone(), TInt);
  fm.push(pr.typ.clone(), TInt);
  let s = fm.unify()?;
  Ok((
    s,
    TProof {
      env,
      expr,
      typ: match op {
        Langle => TBool,
        _ => TInt,
      },
      kind: match op {
        Plus => TPPlus(Box::new(pl), Box::new(pr)),
        Minus => TPMinus(Box::new(pl), Box::new(pr)),
        Aster => TPTimes(Box::new(pl), Box::new(pr)),
        Langle => TPLt(Box::new(pl), Box::new(pr)),
        _ => panic!("Invalid argument"),
      },
    },
  ))
}

pub fn prove(
  env: TypeEnv,
  expr: Expr,
  fac: &mut TypeVarFactory,
) -> Result<(TypeSubst, TProof), &'static str> {
  use self::Expr::*;
  use self::TProofKind::*;
  use self::Type::*;
  match expr.clone() {
    Int(_) => Ok((
      TypeSubst::new(),
      TProof {
        env,
        expr,
        typ: TInt,
        kind: TPInt,
      },
    )),
    Bool(_) => Ok((
      TypeSubst::new(),
      TProof {
        env,
        expr,
        typ: TBool,
        kind: TPBool,
      },
    )),
    Ident(x) => {
      let s = TypeSubst::new();
      let typ = match env.find(&x) {
        None => {
          return Err("Undefined variable");
        }
        Some(ref ts) => s.subst_type_scheme(ts, fac).typ,
      };
      Ok((
        s,
        TProof {
          env,
          expr,
          typ,
          kind: TPVar,
        },
      ))
    }
    Fun(var, body) => {
      let alpha = fac.get();
      let mut next_env = env.clone();
      next_env.push(var, TypeScheme::simple(TVar(alpha.clone())));
      let (s, p) = prove(next_env, *body, fac)?;
      let t = s.subst_type(&TVar(alpha));
      Ok((
        s,
        TProof {
          env,
          expr,
          typ: TFun(Box::new(t), Box::new(p.typ.clone())),
          kind: TPFun(Box::new(p)),
        },
      ))
    }
    Plus(l, r) => prove_binop(env, expr, l, r, fac, self::Op::Plus),
    Minus(l, r) => prove_binop(env, expr, l, r, fac, self::Op::Minus),
    Times(l, r) => prove_binop(env, expr, l, r, fac, self::Op::Aster),
    Lt(l, r) => prove_binop(env, expr, l, r, fac, self::Op::Langle),
    If(p, t, f) => {
      let (sp, pp) = prove(env.clone(), *p, fac)?;
      let (st, pt) = prove(env.clone(), *t, fac)?;
      let (sf, pf) = prove(env.clone(), *f, fac)?;
      let mut fm: TypeFormula = sp.into();
      fm.append(&mut st.into());
      fm.append(&mut sf.into());
      fm.push(pp.typ.clone(), TBool);
      fm.push(pt.typ.clone(), pf.typ.clone());
      let s = fm.unify()?;
      let typ = s.subst_type(&pt.typ);
      Ok((
        s,
        TProof {
          env,
          expr,
          typ,
          kind: TPIf(Box::new(pp), Box::new(pt), Box::new(pf)),
        },
      ))
    }
    Let(var, def, body) => {
      let (sdef, pdef) = prove(env.clone(), *def, fac)?;
      let ts = pdef
        .typ
        .clone()
        .closure(&sdef.subst_type_env(env.clone(), fac));
      let mut next_env = env.clone();
      next_env.push(var, ts);
      let (sbody, pbody) = prove(next_env, *body, fac)?;
      let mut fm: TypeFormula = sdef.into();
      fm.append(&mut sbody.into());
      let s = fm.unify()?;
      let typ = s.subst_type(&pbody.typ);
      Ok((
        s,
        TProof {
          env,
          expr,
          typ,
          kind: TPLet(Box::new(pdef), Box::new(pbody)),
        },
      ))
    }
    App(l, r) => {
      let (sl, pl) = prove(env.clone(), *l, fac)?;
      let (sr, pr) = prove(env.clone(), *r, fac)?;
      let alpha = fac.get();
      let mut fm: TypeFormula = sl.into();
      fm.append(&mut sr.into());
      fm.push(
        pl.typ.clone(),
        TFun(Box::new(pr.typ.clone()), Box::new(TVar(alpha.clone()))),
      );
      let s = fm.unify()?;
      let typ = s.subst_type(&TVar(alpha));
      Ok((
        s,
        TProof {
          env,
          expr,
          typ,
          kind: TPApp(Box::new(pl), Box::new(pr)),
        },
      ))
    }
    Nil => {
      let alpha = fac.get();
      Ok((
        TypeSubst::new(),
        TProof {
          env,
          expr,
          typ: TList(Box::new(TVar(alpha))),
          kind: TPNil,
        },
      ))
    }
    Cons(l, r) => {
      let (sl, pl) = prove(env.clone(), *l, fac)?;
      let (sr, pr) = prove(env.clone(), *r, fac)?;
      let mut fm: TypeFormula = sl.into();
      fm.append(&mut sr.into());
      fm.push(TList(Box::new(pl.typ.clone())), pr.typ.clone());
      let s = fm.unify()?;
      let typ = s.subst_type(&pr.typ);
      Ok((
        s,
        TProof {
          env,
          expr,
          typ,
          kind: TPCons(Box::new(pl), Box::new(pr)),
        },
      ))
    }
    // LetRec(x, y, def, body) => {
    //   let alpha = fac.get();
    //   let beta = fac.get();
    //   let mut def_env = env.clone();
    //   def_env.push(x.clone(), TVar(alpha));
    //   def_env.push(y, TVar(beta));
    //   let (sdef, pdef) = prove(def_env, *def, fac)?;
    //   let mut body_env = env.clone();
    //   body_env.push(x, TVar(alpha));
    //   let (sbody, pbody) = prove(body_env, *body, fac)?;
    //   let mut fm: TypeFormula = sdef.into();
    //   fm.append(&mut sbody.into());
    //   fm.push(
    //     TVar(alpha),
    //     TFun(Box::new(TVar(beta)), Box::new(pdef.typ.clone())),
    //   );
    //   let s = fm.unify()?;
    //   let typ = s.subst_type(&pbody.typ);
    //   Ok((
    //     s,
    //     TProof {
    //       env,
    //       expr,
    //       typ,
    //       kind: TPLetRec(Box::new(pdef), Box::new(pbody)),
    //     },
    //   ))
    // }
    // Match2(target, bnil, vcar, vcdr, bcons) => {
    //   let (starget, ptarget) = prove(env.clone(), *target, fac)?;
    //   let (snil, pnil) = prove(env.clone(), *bnil, fac)?;
    //   let alpha = fac.get();
    //   let mut cons_env = env.clone();
    //   cons_env.push(vcar, TVar(alpha));
    //   cons_env.push(vcdr, TList(Box::new(TVar(alpha))));
    //   let (scons, pcons) = prove(cons_env, *bcons, fac)?;
    //   let mut fm: TypeFormula = starget.into();
    //   fm.append(&mut snil.into());
    //   fm.append(&mut scons.into());
    //   fm.push(ptarget.typ.clone(), TList(Box::new(TVar(alpha))));
    //   fm.push(pnil.typ.clone(), pcons.typ.clone());
    //   let s = fm.unify()?;
    //   let typ = s.subst_type(&pnil.typ);
    //   Ok((
    //     s,
    //     TProof {
    //       env,
    //       expr,
    //       typ,
    //       kind: TPMatch(Box::new(ptarget), Box::new(pnil), Box::new(pcons)),
    //     },
    //   ))
    // }
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
      TPFun(f) => ("T-Abs", vec![f]),
      TPApp(l, r) => ("T-App", vec![l, r]),
      TPNil => ("T-Nil", Vec::new()),
      TPCons(l, r) => ("T-Cons", vec![l, r]),
      TPLetRec(d, b) => ("T-LetRec", vec![d, b]),
      TPMatch(t, n, c) => ("T-Match", vec![t, n, c]),
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
      sub.subst_type(&TFun(
        Box::new(TBool),
        Box::new(TList(Box::new(TVar(TypeVar(0)))))
      )),
      TFun(Box::new(TBool), Box::new(TList(Box::new(TInt))))
    )
  }
  #[test]
  fn parse_typevar() {
    let s = "'a";
    assert_eq!(
      type_parser(calc_expr_env()).easy_parse(s),
      Ok((TVar(TypeVar(0)), ""))
    )
  }
  #[test]
  fn parse_typescheme() {
    let s = "'a 'b 'c.'a";
    assert_eq!(
      typescheme_parser(calc_expr_env()).easy_parse(s),
      Ok((
        TypeScheme {
          scheme: vec![TypeVar(0), TypeVar(1), TypeVar(2)],
          typ: TVar(TypeVar(0)),
        },
        ""
      ))
    )
  }
  #[test]
  fn parse_typescheme_fun() {
    let s = "int list -> bool list";
    assert_eq!(
      typescheme_parser(calc_expr_env()).easy_parse(s),
      Ok((
        TypeScheme {
          scheme: Vec::new(),
          typ: TFun(
            Box::new(TList(Box::new(TInt))),
            Box::new(TList(Box::new(TBool)))
          ),
        },
        ""
      ))
    )
  }
}