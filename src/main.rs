pub mod expr;
pub mod evalml1;

#[macro_use]
extern crate combine;
extern crate combine_language;

use combine::Parser;

fn main() {
  let mut input = String::new();
  std::io::stdin().read_line(&mut input).unwrap();
  let input: &str = &input;
  println!(
    "{:?}",
    evalml1::judgement_parser().easy_parse(input)
  );
}
