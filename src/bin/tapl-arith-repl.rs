extern crate tapl;

use std::io;
use std::io::Write;

use tapl::tapl::arith;

fn main() {
    let mut input = String::new();
    loop {
        print!("In: ");
        io::stdout().flush().unwrap();
        io::stdin().read_line(&mut input).expect("failed to read line");
        input.trim();
        match arith::run(&input) {
            Ok(s) => println!("Out: {}", s),
            _ => println!("Error: Failed to run"),
        }
        input.clear();
    }
}
