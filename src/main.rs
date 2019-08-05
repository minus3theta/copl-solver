#![recursion_limit = "256"]
pub mod evalrefml3;
pub mod expr;
#[macro_use]
extern crate combine;
extern crate combine_language;

use combine::Parser;
use std::io::prelude::Read;

fn main() {
  let mut input = String::new();
  std::io::stdin().read_to_string(&mut input).unwrap();
  let input: &str = &input;
  let judge = evalrefml3::judgement_parser(expr::calc_expr_env())
    .easy_parse(input)
    .unwrap()
    .0;
  let mut locs = judge.post_store.locs();
  let proof = evalrefml3::prove(judge.pre_store, judge.env, judge.expr, &mut locs);
  println!("{}", proof);
}
