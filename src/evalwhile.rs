use combine::parser::char::{alpha_num, letter, string};
use combine::{optional, parser, satisfy, sep_by, ParseError, Parser, Stream};
use combine_language::{expression_parser, Assoc, Fixity, Identifier, LanguageDef, LanguageEnv};
use std::fmt;

type Var = String;
type Value = i64;
type BValue = bool;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub enum Aop {
  Plus,
  Minus,
  Times,
}

impl fmt::Display for Aop {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    use self::Aop::*;
    match self {
      Plus => write!(f, "+"),
      Minus => write!(f, "-"),
      Times => write!(f, "*"),
    }
  }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub enum AExp {
  AInt(Value),
  AVar(Var),
  AOp(Aop, Box<AExp>, Box<AExp>),
}

impl fmt::Display for AExp {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    use self::AExp::*;
    match self {
      AInt(i) => write!(f, "{}", i),
      AVar(x) => write!(f, "{}", x),
      AOp(op, l, r) => write!(f, "({} {} {})", l, op, r),
    }
  }
}

pub fn plus(l: AExp, r: AExp) -> AExp {
  AExp::AOp(Aop::Plus, Box::new(l), Box::new(r))
}

pub fn minus(l: AExp, r: AExp) -> AExp {
  AExp::AOp(Aop::Minus, Box::new(l), Box::new(r))
}

pub fn times(l: AExp, r: AExp) -> AExp {
  AExp::AOp(Aop::Times, Box::new(l), Box::new(r))
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub enum Lop {
  And,
  Or,
}

impl fmt::Display for Lop {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    use self::Lop::*;
    match self {
      And => write!(f, "&&"),
      Or => write!(f, "||"),
    }
  }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub enum Comp {
  Less,
  Equal,
  LessEqual,
}

impl fmt::Display for Comp {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    use self::Comp::*;
    match self {
      Less => write!(f, "<"),
      Equal => write!(f, "="),
      LessEqual => write!(f, "<="),
    }
  }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub enum BExp {
  BBool(BValue),
  BNot(Box<BExp>),
  BLop(Lop, Box<BExp>, Box<BExp>),
  BComp(Comp, Box<AExp>, Box<AExp>),
}

impl fmt::Display for BExp {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    use self::BExp::*;
    match self {
      BBool(b) => write!(f, "{}", b),
      BNot(e) => write!(f, "! {}", e),
      BLop(op, l, r) => write!(f, "({} {} {})", l, op, r),
      BComp(op, l, r) => write!(f, "({} {} {})", l, op, r),
    }
  }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct StorePair {
  pub var: Var,
  pub value: Value,
}

impl fmt::Display for StorePair {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "{} = {}", self.var, self.value)
  }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct Store(Vec<StorePair>);

impl Store {
  pub fn replace(&mut self, v: &Var, val: Value) {
    for &mut StorePair {
      ref var,
      ref mut value,
    } in self.0.iter_mut().rev()
    {
      if var == v {
        *value = val;
        return;
      }
    }
  }
}

impl fmt::Display for Store {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    let store = &self.0;
    for (i, sp) in store.iter().enumerate() {
      write!(f, "{}", sp)?;
      if i < store.len() - 1 {
        write!(f, ", ")?;
      } else {
        write!(f, " ")?;
      }
    }
    Ok(())
  }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub enum Com {
  Skip,
  Assign(Var, Box<AExp>),
  Succ(Box<Com>, Box<Com>),
  If(Box<BExp>, Box<Com>, Box<Com>),
  While(Box<BExp>, Box<Com>),
}

impl fmt::Display for Com {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    use self::Com::*;
    match self {
      Skip => write!(f, "skip"),
      Assign(x, a) => write!(f, "{} := {}", x, a),
      Succ(l, r) => write!(f, "{}; {}", l, r),
      If(b, l, r) => write!(f, "if {} then {} else {}", b, l, r),
      While(b, c) => write!(f, "while ({}) do {}", b, c),
    }
  }
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
        "true", "false", "if", "then", "else", "skip", "while", "do", "changes", "to", ";", ":=",
      ]
      .iter()
      .map(|x| (*x).into())
      .collect(),
    },
    op: Identifier {
      start: satisfy(|c| "+-*<=&|".chars().any(|x| x == c)),
      rest: satisfy(|c| "+-*<=&|".chars().any(|x| x == c)),
      reserved: ["+", "-", "*", "<", "=", "<=", "&&", "||"]
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
  fn storepair_parser['a, I](expr_env: LanguageEnv<'a, I>)(I) -> StorePair
  where [
    I: Stream<Item = char>,
    I::Error: ParseError<char, I::Range, I::Position>,
    <I::Error as ParseError<I::Item, I::Range, I::Position>>::StreamError:
      From<::std::num::ParseIntError>,
  ]
  {
    (
      expr_env.identifier().skip(expr_env.reserved("=")),
      expr_env.integer()
    ).map(|(var, value)| StorePair {var, value})
  }
}

parser! {
  pub fn store_parser['a, I](expr_env: LanguageEnv<'a, I>)(I) -> Store
  where [
    I: Stream<Item = char>,
    I::Error: ParseError<char, I::Range, I::Position>,
    <I::Error as ParseError<I::Item, I::Range, I::Position>>::StreamError:
      From<::std::num::ParseIntError>,
  ]
  {
    sep_by(storepair_parser(calc_expr_env()), expr_env.reserved(",")).map(Store)
  }
}

parser! {
  pub fn aexp_parser[I]()(I) -> AExp
  where [
    I: Stream<Item = char>,
    I::Error: ParseError<char, I::Range, I::Position>,
    <I::Error as ParseError<I::Item, I::Range, I::Position>>::StreamError:
      From<::std::num::ParseIntError>,
  ]
  {
    expression_parser(aexp_atom_parser(calc_expr_env()), aop_parser(calc_expr_env()), aop)
  }
}

parser! {
  fn aexp_atom_parser['a, I](expr_env: LanguageEnv<'a, I>)(I) -> AExp
  where [
    I: Stream<Item = char>,
    I::Error: ParseError<char, I::Range, I::Position>,
    <I::Error as ParseError<I::Item, I::Range, I::Position>>::StreamError:
      From<::std::num::ParseIntError>,
  ]
  {
    choice!(
      expr_env.integer().map(AExp::AInt),
      expr_env.identifier().map(AExp::AVar),
      expr_env.parens(aexp_parser())
    )
  }
}

parser! {
  fn aop_parser['a, I](expr_env: LanguageEnv<'a, I>)(I) -> (Aop, Assoc)
  where [
    I: Stream<Item = char>,
    I::Error: ParseError<char, I::Range, I::Position>,
    <I::Error as ParseError<I::Item, I::Range, I::Position>>::StreamError:
      From<::std::num::ParseIntError>,
  ]
  {
    choice!(
      expr_env.reserved_op("*").map(|_| (Aop::Times, Assoc { precedence: 7, fixity: Fixity::Left })),
      expr_env.reserved_op("+").map(|_| (Aop::Plus, Assoc { precedence: 6, fixity: Fixity::Left })),
      expr_env.reserved_op("-").map(|_| (Aop::Minus, Assoc { precedence: 6, fixity: Fixity::Left }))
    )
  }
}

fn aop(l: AExp, o: Aop, r: AExp) -> AExp {
  AExp::AOp(o, Box::new(l), Box::new(r))
}

parser! {
  pub fn bexp_parser[I]()(I) -> BExp
  where [
    I: Stream<Item = char>,
    I::Error: ParseError<char, I::Range, I::Position>,
    <I::Error as ParseError<I::Item, I::Range, I::Position>>::StreamError:
      From<::std::num::ParseIntError>,
  ]
  {
    expression_parser(bexp_atom_parser(calc_expr_env()), lop_parser(calc_expr_env()), lop)
  }
}

parser! {
  fn bexp_atom_parser['a, I](expr_env: LanguageEnv<'a, I>)(I) -> BExp
  where [
    I: Stream<Item = char>,
    I::Error: ParseError<char, I::Range, I::Position>,
    <I::Error as ParseError<I::Item, I::Range, I::Position>>::StreamError:
      From<::std::num::ParseIntError>,
  ]
  {
    choice!(
      expr_env.reserved("true").map(|_| BExp::BBool(true)),
      expr_env.reserved("false").map(|_| BExp::BBool(false)),
      expr_env.reserved("!").with(bexp_atom_parser(calc_expr_env())).map(|e| BExp::BNot(Box::new(e))),
      expr_env.parens(bexp_parser()),
      bexp_comp_parser()
    )
  }
}

parser! {
  fn lop_parser['a, I](expr_env: LanguageEnv<'a, I>)(I) -> (Lop, Assoc)
  where [
    I: Stream<Item = char>,
    I::Error: ParseError<char, I::Range, I::Position>,
    <I::Error as ParseError<I::Item, I::Range, I::Position>>::StreamError:
      From<::std::num::ParseIntError>,
  ]
  {
    choice!(
      expr_env.reserved_op("&&").map(|_| (Lop::And, Assoc { precedence: 7, fixity: Fixity::Left })),
      expr_env.reserved_op("||").map(|_| (Lop::Or, Assoc { precedence: 6, fixity: Fixity::Left }))
    )
  }
}

fn lop(l: BExp, o: Lop, r: BExp) -> BExp {
  BExp::BLop(o, Box::new(l), Box::new(r))
}

parser! {
  fn bexp_comp_parser[I]()(I) -> BExp
  where [
    I: Stream<Item = char>,
    I::Error: ParseError<char, I::Range, I::Position>,
    <I::Error as ParseError<I::Item, I::Range, I::Position>>::StreamError:
      From<::std::num::ParseIntError>,
  ]
  {
    (
      aexp_parser(),
      comp_parser(calc_expr_env()),
      aexp_parser()
    ).map(|(l, o, r)| BExp::BComp(o, Box::new(l), Box::new(r)))
  }
}

parser! {
  fn comp_parser['a, I](expr_env: LanguageEnv<'a, I>)(I) -> Comp
  where [
    I: Stream<Item = char>,
    I::Error: ParseError<char, I::Range, I::Position>,
    <I::Error as ParseError<I::Item, I::Range, I::Position>>::StreamError:
      From<::std::num::ParseIntError>,
  ]
  {
    choice!(
      expr_env.reserved_op("<").map(|_| Comp::Less),
      expr_env.reserved_op("=").map(|_| Comp::Equal),
      expr_env.reserved_op("<=").map(|_| Comp::LessEqual)
    )
  }
}

parser! {
  fn com_parser['a, I](expr_env: LanguageEnv<'a, I>)(I) -> Com
  where [
    I: Stream<Item = char>,
    I::Error: ParseError<char, I::Range, I::Position>,
    <I::Error as ParseError<I::Item, I::Range, I::Position>>::StreamError:
      From<::std::num::ParseIntError>,
  ]
  {
    (
      com_atom_parser(calc_expr_env()),
      optional(expr_env.reserved(";").with(com_parser(calc_expr_env())))
    ).map(|(l, r)| {
      match r {
        None => l,
        Some(r) => Com::Succ(Box::new(l), Box::new(r)),
      }
    })
  }
}

parser! {
  fn com_atom_parser['a, I](expr_env: LanguageEnv<'a, I>)(I) -> Com
  where [
    I: Stream<Item = char>,
    I::Error: ParseError<char, I::Range, I::Position>,
    <I::Error as ParseError<I::Item, I::Range, I::Position>>::StreamError:
      From<::std::num::ParseIntError>,
  ]
  {
    choice!(
      expr_env.reserved("skip").map(|_| Com::Skip),
      (
        expr_env.identifier().skip(expr_env.reserved(":=")),
        aexp_parser()
      ).map(|(x, a)| Com::Assign(x, Box::new(a))),
      (
        expr_env.reserved("if").with(bexp_parser()),
        expr_env.reserved("then").with(com_parser(calc_expr_env())),
        expr_env.reserved("else").with(com_parser(calc_expr_env()))
      ).map(|(p, l, r)| Com::If(Box::new(p), Box::new(l), Box::new(r))),
      (
        expr_env.reserved("while").with(expr_env.parens(bexp_parser())),
        expr_env.reserved("do").with(com_parser(calc_expr_env()))
      ).map(|(b, c)| Com::While(Box::new(b), Box::new(c)))
    )
  }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct Judgement {
  pub com: Com,
  pub pre_store: Store,
  pub post_store: Store,
}

impl fmt::Display for Judgement {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(
      f,
      "{} changes {}to {}",
      self.com, self.pre_store, self.post_store
    )
  }
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
      com_parser(calc_expr_env()).skip(expr_env.reserved("changes")),
      store_parser(calc_expr_env()).skip(expr_env.reserved("to")),
      store_parser(calc_expr_env())
    ).map(|(com, pre_store, post_store)| Judgement { com, pre_store, post_store })
  }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub enum Proof<'a> {
  A(&'a AProof),
  B(&'a BProof),
  C(&'a CProof),
}

impl<'a> Proof<'a> {
  fn print(&self, f: &mut fmt::Formatter, offset: usize) -> fmt::Result {
    use self::Proof::*;
    match self {
      A(a) => unimplemented!(),
      B(b) => unimplemented!(),
      C(c) => c.print(f, offset),
    }
  }
  fn print_proofs(proofs: &Vec<Proof<'a>>, f: &mut fmt::Formatter, offset: usize) -> fmt::Result {
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
    Ok(())
  }
}

impl<'a> fmt::Display for Proof<'a> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    self.print(f, 0)
  }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub enum AProofKind {
  AConst,
  AVar,
  APlus(Box<AProof>, Box<AProof>),
  AMinus(Box<AProof>, Box<AProof>),
  ATimes(Box<AProof>, Box<AProof>),
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct AProof {
  pub store: Store,
  pub aexp: AExp,
  pub value: Value,
  pub kind: AProofKind,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub enum BProofKind {
  BConst,
  BNot(Box<BProof>),
  BAnd(Box<BProof>, Box<BProof>),
  BOr(Box<BProof>, Box<BProof>),
  BLt(Box<AProof>, Box<AProof>),
  BEq(Box<AProof>, Box<AProof>),
  BLe(Box<AProof>, Box<AProof>),
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct BProof {
  pub store: Store,
  pub bexp: BExp,
  pub value: BValue,
  pub kind: BProofKind,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub enum CProofKind {
  CSkip,
  CAssign(Box<AProof>),
  CSeq(Box<CProof>, Box<CProof>),
  CIfT(Box<BProof>, Box<CProof>),
  CIfF(Box<BProof>, Box<CProof>),
  CWhileT(Box<BProof>, Box<CProof>, Box<CProof>),
  CWhileF(Box<BProof>),
}

impl CProofKind {
  fn extract<'a>(&'a self) -> (&str, Vec<Proof<'a>>) {
    use self::CProofKind::*;
    use self::Proof::*;
    match self {
      CSkip => ("C-Skip", Vec::new()),
      CAssign(a) => ("C-Assign", vec![A(a)]),
      _ => unimplemented!(),
    }
  }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct CProof {
  pub com: Com,
  pub pre_store: Store,
  pub post_store: Store,
  pub kind: CProofKind,
}

impl CProof {
  fn print(&self, f: &mut fmt::Formatter, offset: usize) -> fmt::Result {
    let (rule, proofs) = self.kind.extract();
    write!(
      f,
      "{}{} changes {}to {}by {} ",
      " ".repeat(offset),
      self.com,
      self.pre_store,
      self.post_store,
      rule
    )?;
    Proof::print_proofs(&proofs, f, offset)?;
    write!(f, "{}}}", " ".repeat(offset))
  }
}

impl fmt::Display for CProof {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    self.print(f, 0)
  }
}

pub fn prove_com(com: Com, store: Store) -> CProof {
  use self::CProofKind::*;
  use self::Com::*;
  match com.clone() {
    Skip => CProof {
      com,
      pre_store: store.clone(),
      post_store: store,
      kind: CSkip,
    },
    _ => unimplemented!(),
  }
}

#[cfg(test)]
mod test {
  use super::AExp::*;
  use super::*;
  #[test]
  fn parse_store() {
    let s = "x = 1, y = 0";
    assert_eq!(
      store_parser(calc_expr_env()).easy_parse(s),
      Ok((
        Store(vec![
          StorePair {
            var: "x".to_owned(),
            value: 1
          },
          StorePair {
            var: "y".to_owned(),
            value: 0
          },
        ]),
        ""
      ))
    )
  }
  #[test]
  fn parse_aexp1() {
    let s = "x + 2 * y";
    assert_eq!(
      aexp_parser().easy_parse(s),
      Ok((
        plus(AVar("x".to_owned()), times(AInt(2), AVar("y".to_owned()))),
        ""
      ))
    )
  }
}
