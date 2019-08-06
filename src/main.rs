#![recursion_limit = "256"]
pub mod evalwhile;
#[macro_use]
extern crate combine;
extern crate combine_language;

use combine::Parser;
use std::io::prelude::Read;

fn main() {
  let mut input = String::new();
  std::io::stdin().read_to_string(&mut input).unwrap();
  let input: &str = &input;
  let judge = evalwhile::judgement_parser(evalwhile::calc_expr_env())
    .easy_parse(input)
    .unwrap()
    .0;
  let proof = evalwhile::prove_com(judge.com, judge.pre_store);
  println!("{}", proof);
}
