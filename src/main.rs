
pub mod evalml1;
pub mod evalml2;
pub mod evalml3;
pub mod expr;
#[macro_use]
extern crate combine;
extern crate combine_language;

use combine::Parser;

fn main() {
  let mut input = String::new();
  std::io::stdin().read_line(&mut input).unwrap();
  let input: &str = &input;
  let judge = evalml2::judgement_parser().easy_parse(input).unwrap().0;
  let proof = evalml2::prove(judge.env, &judge.expr);
  println!("{}", proof);
}
