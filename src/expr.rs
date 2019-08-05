use combine::parser::char::{alpha_num, letter, string};
use combine::{
  attempt, char::spaces, optional, parser, satisfy, sep_by, token, ParseError, Parser, Stream,
};
use combine_language::{expression_parser, Assoc, Fixity, Identifier, LanguageDef, LanguageEnv};

#[derive(Debug, PartialEq, Clone)]
pub enum Expr {
  Bool(bool),
  Int(i64),
  Ident(String),
  Plus(Box<Expr>, Box<Expr>),
  Minus(Box<Expr>, Box<Expr>),
  Times(Box<Expr>, Box<Expr>),
  Lt(Box<Expr>, Box<Expr>),
  If(Box<Expr>, Box<Expr>, Box<Expr>),
  Let(String, Box<Expr>, Box<Expr>),
  Fun(String, Box<Expr>),
  App(Box<Expr>, Box<Expr>),
  LetRec(String, String, Box<Expr>, Box<Expr>),
  Nil,
  Cons(Box<Expr>, Box<Expr>),
  Match(Box<Expr>, Box<Clause>),
  Ref(Box<Expr>),
  Deref(Box<Expr>),
  Assign(Box<Expr>, Box<Expr>),
}

#[derive(Debug, PartialEq, Clone)]
pub enum Op {
  Plus,
  Minus,
  Aster,
  Cons,
  Langle,
  ColEq,
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
      rest: alpha_num().or(token('\'')),
      reserved: [
        "true", "false", "if", "then", "else", "let", "rec", "in", "fun", "match", "with",
        "evalto", "[]", "->", "|-", "|", "_", "=", ",", "ref", "/",
      ]
      .iter()
      .map(|x| (*x).into())
      .collect(),
    },
    op: Identifier {
      start: satisfy(|c| "+-*<:=".chars().any(|x| x == c)),
      rest: satisfy(|c| "+-*<:=".chars().any(|x| x == c)),
      reserved: ["+", "-", "*", "<", "::", ":="]
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
  pub fn expr_parser[I]()(I) -> Expr
  where [
    I: Stream<Item = char>,
    I::Error: ParseError<char, I::Range, I::Position>,
    <I::Error as ParseError<I::Item, I::Range, I::Position>>::StreamError:
      From<::std::num::ParseIntError>,
  ]
  {
    expression_parser(app_parser(), op_parser(calc_expr_env()), op)
  }
}

parser! {
  fn if_parser['a, I](expr_env: LanguageEnv<'a, I>)(I) -> Expr
  where [
    I: Stream<Item = char>,
    I::Error: ParseError<char, I::Range, I::Position>,
    <I::Error as ParseError<I::Item, I::Range, I::Position>>::StreamError:
      From<::std::num::ParseIntError>,
  ]
  {
    (
      expr_env.reserved("if").with(expr_parser()),
      expr_env.reserved("then").with(expr_parser()),
      expr_env.reserved("else").with(expr_parser())
    ).map(|(p, t, f)| ite(p, t, f))
  }
}

parser! {
  fn let_parser['a, I](expr_env: LanguageEnv<'a, I>)(I) -> Expr
  where [
    I: Stream<Item = char>,
    I::Error: ParseError<char, I::Range, I::Position>,
    <I::Error as ParseError<I::Item, I::Range, I::Position>>::StreamError:
      From<::std::num::ParseIntError>,
  ]
  {
    expr_env.reserved("let")
    .with(
      (
        expr_env.reserved("rec").with(expr_env.identifier()),
        (spaces(), token('='), spaces()).with(fun_parser(calc_expr_env())),
        expr_env.reserved("in").with(expr_parser())
      ).map(|(var, (arg, def), body)| let_rec(var, arg, def, body))
      .or(
        (
          expr_env.identifier(),
          (spaces(), token('='), spaces()).with(expr_parser()),
          expr_env.reserved("in").with(expr_parser())
        ).map(|(var, def, body)| let_in(var, def, body))
      )
    )
  }
}

parser! {
  pub fn fun_parser['a, I](expr_env: LanguageEnv<'a, I>)(I) -> (String, Expr)
  where [
    I: Stream<Item = char>,
    I::Error: ParseError<char, I::Range, I::Position>,
    <I::Error as ParseError<I::Item, I::Range, I::Position>>::StreamError:
      From<::std::num::ParseIntError>,
  ]
  {
    (
      expr_env.reserved("fun").with(expr_env.identifier()),
      expr_env.reserved("->").with(expr_parser())
    )
  }
}

parser! {
  pub fn match_parser['a, I](expr_env: LanguageEnv<'a, I>)(I) -> Expr
  where [
    I: Stream<Item = char>,
    I::Error: ParseError<char, I::Range, I::Position>,
    <I::Error as ParseError<I::Item, I::Range, I::Position>>::StreamError:
      From<::std::num::ParseIntError>,
  ]
  {
    (
      expr_env.reserved("match").with(expr_parser()),
      expr_env.reserved("with").with(clause_parser(calc_expr_env()))
    ).map(|(e, c)| Expr::Match(Box::new(e), Box::new(c)))
  }
}

parser! {
  fn term_parser['a, I](expr_env: LanguageEnv<'a, I>)(I) -> Expr
  where [
    I: Stream<Item = char>,
    I::Error: ParseError<char, I::Range, I::Position>,
    <I::Error as ParseError<I::Item, I::Range, I::Position>>::StreamError:
      From<::std::num::ParseIntError>,
  ]
  {
    choice!(
      if_parser(calc_expr_env()),
      let_parser(calc_expr_env()),
      fun_parser(calc_expr_env()).map(|(var, body)| fun(var, body)),
      match_parser(calc_expr_env()),
      expr_env.reserved("true").map(|_| Expr::Bool(true)),
      expr_env.reserved("false").map(|_| Expr::Bool(false)),
      expr_env.reserved("[]").map(|_| Expr::Nil),
      (optional(token('-').skip(spaces())), expr_env.integer()).map(|(neg, x)| Expr::Int(
        match neg {
          None => x,
          Some(_) => -x,
        })
      ),
      expr_env.reserved("ref").with(term_parser(calc_expr_env())).map(|e| Expr::Ref(Box::new(e))),
      token('!').with(spaces()).with(term_parser(calc_expr_env())).map(|e| Expr::Deref(Box::new(e))),
      expr_env.identifier().map(Expr::Ident),
      expr_env.parens(expr_parser())
    )
  }
}

parser! {
  fn app_parser[I]()(I) -> Expr
  where [
    I: Stream<Item = char>,
    I::Error: ParseError<char, I::Range, I::Position>,
    <I::Error as ParseError<I::Item, I::Range, I::Position>>::StreamError:
      From<::std::num::ParseIntError>,
  ]
  {
    (spaces().with(term_parser(calc_expr_env())).skip(spaces()), app_rest_parser()).map(|(mut f, v)| {
      for e in v.into_iter().rev() {
        f = app(f, e);
      }
      f
    })
  }
}

parser! {
  fn app_rest_parser[I]()(I) -> Vec<Expr>
  where [
    I: Stream<Item = char>,
    I::Error: ParseError<char, I::Range, I::Position>,
    <I::Error as ParseError<I::Item, I::Range, I::Position>>::StreamError:
      From<::std::num::ParseIntError>,
  ]
  {
    optional((app_arg_parser(calc_expr_env()).skip(spaces()), app_rest_parser())).map(|opt| {
      match opt {
        Some((e, mut v)) => {
          v.push(e);
          v
        }
        None => vec![],
      }
    })
  }
}

parser! {
  fn app_arg_parser['a, I](expr_env: LanguageEnv<'a, I>)(I) -> Expr
  where [
    I: Stream<Item = char>,
    I::Error: ParseError<char, I::Range, I::Position>,
    <I::Error as ParseError<I::Item, I::Range, I::Position>>::StreamError:
      From<::std::num::ParseIntError>,
  ]
  {
    choice!(
      if_parser(calc_expr_env()),
      let_parser(calc_expr_env()),
      fun_parser(calc_expr_env()).map(|(var, body)| fun(var, body)),
      match_parser(calc_expr_env()),
      expr_env.reserved("true").map(|_| Expr::Bool(true)),
      expr_env.reserved("false").map(|_| Expr::Bool(false)),
      expr_env.reserved("[]").map(|_| Expr::Nil),
      expr_env.integer().map(Expr::Int),
      expr_env.parens(expr_parser()),
      attempt(expr_env.identifier().map(Expr::Ident))
    )
  }
}

parser! {
  fn op_parser['a, I](expr_env: LanguageEnv<'a, I>)(I) -> (Op, Assoc)
  where [
    I: Stream<Item = char>,
    I::Error: ParseError<char, I::Range, I::Position>,
    <I::Error as ParseError<I::Item, I::Range, I::Position>>::StreamError:
      From<::std::num::ParseIntError>,
  ]
  {
    choice! (
      expr_env.reserved_op("+").map(|_| (Op::Plus, Assoc { precedence: 6, fixity: Fixity::Left})),
      expr_env.reserved_op("-").map(|_| (Op::Minus, Assoc { precedence: 6, fixity: Fixity::Left})),
      expr_env.reserved_op("*").map(|_| (Op::Aster, Assoc { precedence: 7, fixity: Fixity::Left})),
      expr_env.reserved_op("<").map(|_| (Op::Langle, Assoc { precedence: 4, fixity: Fixity::Left})),
      expr_env.reserved_op("::").map(|_| (Op::Cons, Assoc { precedence: 5, fixity: Fixity::Right})),
      expr_env.reserved_op(":=").map(|_| (Op::ColEq, Assoc { precedence: 3, fixity: Fixity::Right}))
    )
  }
}

fn op(l: Expr, o: Op, r: Expr) -> Expr {
  use self::Expr::*;
  match o {
    Op::Plus => Plus(Box::new(l), Box::new(r)),
    Op::Minus => Minus(Box::new(l), Box::new(r)),
    Op::Aster => Times(Box::new(l), Box::new(r)),
    Op::Cons => Cons(Box::new(l), Box::new(r)),
    Op::Langle => Lt(Box::new(l), Box::new(r)),
    Op::ColEq => Assign(Box::new(l), Box::new(r)),
  }
}

pub fn plus(l: Expr, r: Expr) -> Expr {
  Expr::Plus(Box::new(l), Box::new(r))
}

pub fn minus(l: Expr, r: Expr) -> Expr {
  Expr::Minus(Box::new(l), Box::new(r))
}

pub fn times(l: Expr, r: Expr) -> Expr {
  Expr::Times(Box::new(l), Box::new(r))
}

pub fn lt(l: Expr, r: Expr) -> Expr {
  Expr::Lt(Box::new(l), Box::new(r))
}

pub fn cons(l: Expr, r: Expr) -> Expr {
  Expr::Cons(Box::new(l), Box::new(r))
}

pub fn ite(p: Expr, t: Expr, f: Expr) -> Expr {
  Expr::If(Box::new(p), Box::new(t), Box::new(f))
}

pub fn let_in(var: String, def: Expr, body: Expr) -> Expr {
  Expr::Let(var, Box::new(def), Box::new(body))
}

pub fn let_rec(var: String, arg: String, def: Expr, body: Expr) -> Expr {
  Expr::LetRec(var, arg, Box::new(def), Box::new(body))
}

pub fn app(f: Expr, x: Expr) -> Expr {
  Expr::App(Box::new(f), Box::new(x))
}

pub fn fun(var: String, body: Expr) -> Expr {
  Expr::Fun(var, Box::new(body))
}

#[derive(Debug, PartialEq, Clone)]
pub struct Loc {
  pub name: String,
}

impl fmt::Display for Loc {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "@{}", self.name)
  }
}

#[derive(Debug, PartialEq, Clone)]
pub struct StorePair {
  pub loc: Loc,
  pub value: Value,
}

pub fn store_pair(name: String, value: Value) -> StorePair {
  StorePair {
    loc: Loc { name },
    value,
  }
}

impl fmt::Display for StorePair {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "{} = {}", self.loc, self.value)
  }
}

#[derive(Debug, PartialEq, Clone)]
pub struct Store(Vec<StorePair>);

pub fn store(sp: Vec<StorePair>) -> Store {
  Store(sp)
}

impl Store {
  pub fn new() -> Store {
    Store(Vec::new())
  }
  pub fn push(&mut self, loc: Loc, value: Value) {
    self.0.push(StorePair { loc, value });
  }
  pub fn find(&self, l: Loc) -> Option<Value> {
    if let Some(StorePair { value, .. }) = self
      .0
      .clone()
      .into_iter()
      .rev()
      .find(|StorePair { loc, .. }| *loc == l)
    {
      Some(value)
    } else {
      None
    }
  }
  pub fn replace(&mut self, l: Loc, v: Value) {
    for &mut StorePair {
      ref loc,
      ref mut value,
    } in self.0.iter_mut().rev()
    {
      if *loc == l {
        *value = v;
        return;
      }
    }
  }
  pub fn separator(&self) -> &str {
    if self.0.is_empty() {
      ""
    } else {
      "/ "
    }
  }
}

impl fmt::Display for Store {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    let st = &self.0;
    for (i, sp) in st.iter().enumerate() {
      write!(f, "{}", sp)?;
      if i < st.len() - 1 {
        write!(f, ", ")?;
      } else {
        write!(f, " ")?;
      }
    }
    Ok(())
  }
}

parser! {
  pub fn loc_parser['a, I](expr_env: LanguageEnv<'a, I>)(I) -> Loc
  where [
    I: Stream<Item = char>,
    I::Error: ParseError<char, I::Range, I::Position>,
    <I::Error as ParseError<I::Item, I::Range, I::Position>>::StreamError:
      From<::std::num::ParseIntError>,
  ]
  {
    token('@').with(expr_env.identifier()).map(|name| Loc { name })
  }
}

parser! {
  pub fn storepair_parser['a, I](expr_env: LanguageEnv<'a, I>)(I) -> StorePair
  where [
    I: Stream<Item = char>,
    I::Error: ParseError<char, I::Range, I::Position>,
    <I::Error as ParseError<I::Item, I::Range, I::Position>>::StreamError:
      From<::std::num::ParseIntError>,
  ]
  {
    (
      loc_parser(calc_expr_env()),
      expr_env.reserved("=").with(value_parser(calc_expr_env())),
    ).map(|(loc, value)| StorePair { loc, value })
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

#[derive(Debug, PartialEq, Clone)]
pub enum Value {
  VBool(bool),
  VInt(i64),
  VClosure {
    env: Env,
    var: String,
    expr: Expr,
  },
  VRec {
    env: Env,
    var: String,
    arg: String,
    expr: Expr,
  },
  VCons(Box<Value>, Box<Value>),
  VNil,
  VLoc {
    loc: Loc,
  },
}

pub fn v_cons(l: Value, r: Value) -> Value {
  Value::VCons(Box::new(l), Box::new(r))
}

parser! {
  pub fn value_parser['a, I](expr_env: LanguageEnv<'a, I>)(I) -> Value
  where [
    I: Stream<Item = char>,
    I::Error: ParseError<char, I::Range, I::Position>,
    <I::Error as ParseError<I::Item, I::Range, I::Position>>::StreamError:
      From<::std::num::ParseIntError>,
  ]
  {
    (
      value_atom_parser(calc_expr_env()),
      optional(expr_env.reserved_op("::").with(value_parser(calc_expr_env())))
    ).map(|(l, r)| {
      match r {
        None => l,
        Some(r) => v_cons(l, r),
      }
    })
  }
}

parser! {
  pub fn value_atom_parser['a, I](expr_env: LanguageEnv<'a, I>)(I) -> Value
  where [
    I: Stream<Item = char>,
    I::Error: ParseError<char, I::Range, I::Position>,
    <I::Error as ParseError<I::Item, I::Range, I::Position>>::StreamError:
      From<::std::num::ParseIntError>,
  ]
  {
    choice!(
      expr_env.reserved("true").map(|_| Value::VBool(true)),
      expr_env.reserved("false").map(|_| Value::VBool(false)),
      expr_env.reserved("[]").map(|_| Value::VNil),
      attempt((
        expr_env.parens(env_parser()),
        expr_env.brackets(fun_parser(calc_expr_env()))
      ).map(|(env, (var, expr))| Value::VClosure { env, var, expr })),
      loc_parser(calc_expr_env()).map(|loc| Value::VLoc { loc }),
      expr_env.parens(value_parser(calc_expr_env())),
      (optional(token('-').skip(spaces())), expr_env.integer()).map(|(neg, x)| Value::VInt(
        match neg {
          None => x,
          Some(_) => -x,
        })
      )
    )
  }
}

#[derive(Debug, PartialEq, Clone)]
pub struct EnvPair {
  pub var: String,
  pub value: Value,
}

pub fn env_pair(var: String, value: Value) -> EnvPair {
  EnvPair { var, value }
}

#[derive(Debug, PartialEq, Clone)]
pub struct Env(pub Vec<EnvPair>);

impl Env {
  pub fn new() -> Self {
    Env(Vec::new())
  }

  pub fn merge(&self, other: &Self) -> Self {
    let mut v = self.0.clone();
    v.append(&mut other.0.clone());
    Env(v)
  }
}

parser! {
  pub fn env_pair_parser['a, I](expr_env: LanguageEnv<'a, I>)(I) -> EnvPair
  where [
    I: Stream<Item = char>,
    I::Error: ParseError<char, I::Range, I::Position>,
    <I::Error as ParseError<I::Item, I::Range, I::Position>>::StreamError:
      From<::std::num::ParseIntError>,
  ]
  {
    (
      expr_env.identifier().skip(spaces()).skip(token('=')).skip(spaces()),
      value_parser(calc_expr_env())
    ).map(|(s, v)| env_pair(s, v))
  }
}

parser! {
  pub fn env_parser[I]()(I) -> Env
  where [
    I: Stream<Item = char>,
    I::Error: ParseError<char, I::Range, I::Position>,
    <I::Error as ParseError<I::Item, I::Range, I::Position>>::StreamError:
      From<::std::num::ParseIntError>,
  ]
  {
    sep_by(env_pair_parser(calc_expr_env()), (spaces(), token(','), spaces())).map(Env)
  }
}

#[derive(Debug, PartialEq, Clone)]
pub enum Pattern {
  PVar(String),
  PNil,
  PCons(Box<Pattern>, Box<Pattern>),
  PWild,
}

pub fn p_cons(l: Pattern, r: Pattern) -> Pattern {
  Pattern::PCons(Box::new(l), Box::new(r))
}

parser! {
  pub fn pattern_atom_parser['a, I](expr_env: LanguageEnv<'a, I>)(I) -> Pattern
  where [
    I: Stream<Item = char>,
    I::Error: ParseError<char, I::Range, I::Position>,
    <I::Error as ParseError<I::Item, I::Range, I::Position>>::StreamError:
      From<::std::num::ParseIntError>,
  ]
  {
    choice!(
      expr_env.identifier().map(|x| Pattern::PVar(x)),
      expr_env.reserved("[]").map(|_| Pattern::PNil),
      expr_env.reserved("_").map(|_| Pattern::PWild),
      expr_env.parens(pattern_parser(calc_expr_env()))
    )
  }
}

parser! {
  pub fn pattern_parser['a, I](expr_env: LanguageEnv<'a, I>)(I) -> Pattern
  where [
    I: Stream<Item = char>,
    I::Error: ParseError<char, I::Range, I::Position>,
    <I::Error as ParseError<I::Item, I::Range, I::Position>>::StreamError:
      From<::std::num::ParseIntError>,
  ]
  {
    (
      pattern_atom_parser(calc_expr_env()),
      optional(expr_env.reserved_op("::").with(pattern_parser(calc_expr_env())))
    ).map(|(l, r)| {
      match r {
        None => l,
        Some(r) => p_cons(l, r)
      }
    })
  }
}

#[derive(Debug, PartialEq, Clone)]
pub struct Clause {
  pub pattern: Pattern,
  pub expr: Expr,
  pub next: Option<Box<Clause>>,
}

parser! {
  pub fn clause_parser['a, I](expr_env: LanguageEnv<'a, I>)(I) -> Clause
  where [
    I: Stream<Item = char>,
    I::Error: ParseError<char, I::Range, I::Position>,
    <I::Error as ParseError<I::Item, I::Range, I::Position>>::StreamError:
      From<::std::num::ParseIntError>,
  ]
  {
    (
      pattern_parser(calc_expr_env()),
      expr_env.reserved("->").with(expr_parser()),
      optional(expr_env.reserved("|").with(clause_parser(calc_expr_env())))
    ).map(|(pattern, expr, next)| {
      Clause {
        pattern,
        expr,
        next: next.map(Box::new)
      }
    })
  }
}


use std::fmt;

impl fmt::Display for Expr {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    use self::Expr::*;
    match self {
      Bool(b) => b.fmt(f),
      Int(i) => i.fmt(f),
      Ident(s) => s.fmt(f),
      Plus(l, r) => write!(f, "({} + {})", l, r),
      Minus(l, r) => write!(f, "({} - {})", l, r),
      Times(l, r) => write!(f, "({} * {})", l, r),
      Lt(l, r) => write!(f, "({} < {})", l, r),
      If(ep, et, ef) => write!(f, "(if {} then {} else {})", ep, et, ef),
      Let(s, d, b) => write!(f, "(let {} = {} in {})", s, d, b),
      Fun(x, e) => write!(f, "(fun {} -> {})", x, e),
      App(l, r) => write!(f, "({} {})", l, r),
      LetRec(x, y, d, b) => write!(f, "(let rec {} = fun {} -> {} in {})", x, y, d, b),
      Nil => write!(f, "[]"),
      Cons(l, r) => write!(f, "({} :: {})", l, r),
      Match(e, c) => write!(f, "(match {} with {})", e, c),
      Ref(e) => write!(f, "(ref {})", e),
      Deref(e) => write!(f, "! {}", e),
      Assign(l, r) => write!(f, "({} := {})", l, r),
    }
  }
}

impl fmt::Display for Value {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    use self::Value::*;
    match self {
      VBool(b) => b.fmt(f),
      VInt(i) => i.fmt(f),
      VClosure { env, var, expr } => write!(f, "({})[fun {} -> {}]", env, var, expr),
      VRec {
        env,
        var,
        arg,
        expr,
      } => write!(f, "({})[rec {} = fun {} -> {}]", env, var, arg, expr),
      VNil => write!(f, "[]"),
      VCons(l, r) => write!(f, "({} :: {})", l, r),
      VLoc { loc } => write!(f, "{}", loc),
    }
  }
}

impl fmt::Display for Env {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    let env = &self.0;
    for (i, EnvPair { var, value }) in env.iter().enumerate() {
      write!(f, "{} = {}", var, value)?;
      if i < env.len() - 1 {
        write!(f, ", ")?;
      } else {
        write!(f, " ")?;
      }
    }
    Ok(())
  }
}

impl fmt::Display for Pattern {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    use expr::Pattern::*;
    match self {
      PVar(x) => write!(f, "{}", x),
      PNil => write!(f, "[]"),
      PCons(l, r) => write!(f, "({} :: {})", *l, *r),
      PWild => write!(f, "_"),
    }
  }
}

impl fmt::Display for Clause {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "{} -> {}", self.pattern, self.expr)?;
    if let Some(ref next) = self.next {
      write!(f, " | {}", next)?;
    }
    Ok(())
  }
}

#[cfg(test)]
mod test {
  use super::Expr::*;
  use super::Value::*;
  use super::*;
  #[test]
  fn parse_expr1() {
    let s = "1 + 2 * 3 - 4";
    assert_eq!(
      expr_parser().easy_parse(s),
      Ok((minus(plus(Int(1), times(Int(2), Int(3))), Int(4)), ""))
    )
  }
  #[test]
  fn parse_expr2() {
    let s = " 1 + 2 * 3 - 4";
    assert_eq!(
      expr_parser().easy_parse(s),
      Ok((minus(plus(Int(1), times(Int(2), Int(3))), Int(4)), ""))
    )
  }
  #[test]
  fn parse_ident() {
    let s = "foo";
    assert_eq!(
      expr_parser().easy_parse(s),
      Ok((Ident("foo".to_owned()), ""))
    )
  }
  #[test]
  fn parse_bool() {
    let s = "true";
    assert_eq!(expr_parser().easy_parse(s), Ok((Bool(true), "")))
  }
  #[test]
  fn parse_negative_int() {
    let s = "-42";
    assert_eq!(expr_parser().easy_parse(s), Ok((Int(-42), "")))
  }
  #[test]
  fn parse_if1() {
    let s = "if 1 < 2 then 1 + 2 else 3 * 4";
    assert_eq!(
      expr_parser().easy_parse(s),
      Ok((
        ite(
          lt(Int(1), Int(2)),
          plus(Int(1), Int(2)),
          times(Int(3), Int(4))
        ),
        ""
      ))
    )
  }
  #[test]
  fn parse_if2() {
    let s = "1 + if true then 1 else 3";
    assert_eq!(
      expr_parser().easy_parse(s),
      Ok((plus(Int(1), ite(Bool(true), Int(1), Int(3))), ""))
    )
  }
  #[test]
  fn parse_if3() {
    let s = "1 + if 1 < 2 then 1 + 2 else 3 * 4";
    assert_eq!(
      expr_parser().easy_parse(s),
      Ok((
        plus(
          Int(1),
          ite(
            lt(Int(1), Int(2)),
            plus(Int(1), Int(2)),
            times(Int(3), Int(4))
          )
        ),
        ""
      ))
    )
  }
  #[test]
  fn parse_value_bool() {
    let s = "true";
    assert_eq!(
      value_parser(calc_expr_env()).easy_parse(s),
      Ok((Value::VBool(true), ""))
    )
  }
  #[test]
  fn parse_value_int() {
    let s = "42";
    assert_eq!(
      value_parser(calc_expr_env()).easy_parse(s),
      Ok((Value::VInt(42), ""))
    )
  }
  #[test]
  fn parse_value_negative_int() {
    let s = "-42";
    assert_eq!(
      value_parser(calc_expr_env()).easy_parse(s),
      Ok((Value::VInt(-42), ""))
    )
  }
  #[test]
  fn parse_let1() {
    let s = "let x = 1 in x + 2";
    assert_eq!(
      expr_parser().easy_parse(s),
      Ok((
        let_in("x".to_owned(), Int(1), plus(Ident("x".to_owned()), Int(2))),
        ""
      ))
    )
  }
  #[test]
  fn parse_value_closure() {
    use self::Value::*;
    let s = "(y=2)[fun x -> x + y]";
    assert_eq!(
      value_parser(calc_expr_env()).easy_parse(s),
      Ok((
        VClosure {
          env: Env(vec![env_pair("y".to_owned(), VInt(2))]),
          var: "x".to_owned(),
          expr: plus(Ident("x".to_owned()), Ident("y".to_owned()))
        },
        ""
      ))
    )
  }
  #[test]
  fn parse_apply() {
    let s = "f 1 2";
    assert_eq!(
      expr_parser().easy_parse(s),
      Ok((app(app(Ident("f".to_owned()), Int(1)), Int(2)), ""))
    )
  }
  #[test]
  fn parse_fun() {
    let s = "fun x -> x + 1";
    assert_eq!(
      expr_parser().easy_parse(s),
      Ok((fun("x".to_owned(), plus(Ident("x".to_owned()), Int(1))), ""))
    )
  }
  #[test]
  fn parse_apply_app_parser() {
    let s = "f 1 2";
    assert_eq!(
      app_parser().easy_parse(s),
      Ok((app(app(Ident("f".to_owned()), Int(1)), Int(2)), ""))
    )
  }
  #[test]
  fn parse_int_app_parser() {
    let s = "1";
    assert_eq!(app_parser().easy_parse(s), Ok((Int(1), "")))
  }
  #[test]
  fn parse_if0_app_parser() {
    let s = "if true then 1 else 2";
    assert_eq!(
      app_parser().easy_parse(s),
      Ok((ite(Bool(true), Int(1), Int(2)), ""))
    )
  }
  #[test]
  fn parse_if1_app_parser() {
    let s = "if 1 < 2 then 1 + 2 else 3 * 4";
    assert_eq!(
      app_parser().easy_parse(s),
      Ok((
        ite(
          lt(Int(1), Int(2)),
          plus(Int(1), Int(2)),
          times(Int(3), Int(4))
        ),
        ""
      ))
    )
  }
  #[test]
  fn parse_if0_if_parser() {
    let s = "if true then 1 else 2";
    assert_eq!(
      if_parser(calc_expr_env()).easy_parse(s),
      Ok((ite(Bool(true), Int(1), Int(2)), ""))
    )
  }
  #[test]
  fn parse_if1_term_parser() {
    let s = "if 1 < 2 then 1 + 2 else 3 * 4";
    assert_eq!(
      term_parser(calc_expr_env()).easy_parse(s),
      Ok((
        ite(
          lt(Int(1), Int(2)),
          plus(Int(1), Int(2)),
          times(Int(3), Int(4))
        ),
        ""
      ))
    )
  }
  #[test]
  fn parse_reserved_app_rest_parser() {
    let s = "then";
    assert_eq!(app_rest_parser().easy_parse(s), Ok((vec![], "then")))
  }
  #[test]
  fn parse_letrec() {
    let s = "let rec f = fun x -> x in f 1";
    assert_eq!(
      expr_parser().easy_parse(s),
      Ok((
        let_rec(
          "f".to_owned(),
          "x".to_owned(),
          Ident("x".to_owned()),
          app(Ident("f".to_owned()), Int(1))
        ),
        ""
      ))
    )
  }
  #[test]
  fn parse_cons() {
    let s = "1 + 2 :: 3 :: []";
    assert_eq!(
      expr_parser().easy_parse(s),
      Ok((cons(plus(Int(1), Int(2)), cons(Int(3), Nil)), ""))
    )
  }
  #[test]
  fn parse_value_cons() {
    let s = "1 :: 3 :: []";
    assert_eq!(
      value_parser(calc_expr_env()).easy_parse(s),
      Ok((v_cons(VInt(1), v_cons(VInt(3), VNil)), ""))
    )
  }
  #[test]
  fn parse_match() {
    use expr::Pattern::*;
    let s = "match x with [] -> 0 | a :: b -> a";
    assert_eq!(
      expr_parser().easy_parse(s),
      Ok((
        Match(
          Box::new(Ident("x".to_owned())),
          Box::new(Clause {
            pattern: PNil,
            expr: Int(0),
            next: Some(Box::new(Clause {
              pattern: p_cons(PVar("a".to_owned()), PVar("b".to_owned())),
              expr: Ident("a".to_owned()),
              next: None
            }))
          })
        ),
        ""
      ))
    )
  }
  #[test]
  fn parse_pattern_cons() {
    use expr::Pattern::*;
    let s = "x :: _ :: []";
    assert_eq!(
      pattern_parser(calc_expr_env()).easy_parse(s),
      Ok((p_cons(PVar("x".to_owned()), p_cons(PWild, PNil)), ""))
    )
  }
  #[test]
  fn parse_pattern_nest() {
    use expr::Pattern::*;
    let s = "(x :: []) :: y";
    assert_eq!(
      pattern_parser(calc_expr_env()).easy_parse(s),
      Ok((
        p_cons(p_cons(PVar("x".to_owned()), PNil), PVar("y".to_owned())),
        ""
      ))
    )
  }
  #[test]
  fn parse_clause() {
    use expr::Pattern::*;
    let s = "[] -> 1 | _ :: _ -> 2";
    assert_eq!(
      clause_parser(calc_expr_env()).easy_parse(s),
      Ok((
        Clause {
          pattern: PNil,
          expr: Int(1),
          next: Some(Box::new(Clause {
            pattern: p_cons(PWild, PWild),
            expr: Int(2),
            next: None
          }))
        },
        ""
      ))
    )
  }
}
