pub mod expr;

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
    expr::expr_parser(expr::calc_expr_env()).easy_parse(input)
  );
}
