#![recursion_limit = "256"]
pub mod expr;
pub mod typingml4;
#[macro_use]
extern crate combine;
extern crate combine_language;

use combine::Parser;
use std::io::prelude::Read;

fn main() {
  let mut input = String::new();
  std::io::stdin().read_to_string(&mut input).unwrap();
  let input: &str = &input;
  let judge = typingml4::judgement_parser(expr::calc_expr_env())
    .easy_parse(input)
    .unwrap()
    .0;
  let proof = typingml4::prove(judge.env, judge.expr, &mut typingml4::TypeVarFactory::new());
  println!("{}", proof.1);
}
