use std::{env, process};

// use rucc::tokenizer::Tokenizer;

fn main() {
    let args: Vec<String> = env::args().collect();

    if args.len() != 2 {
        eprintln!("{}: invalid number of arguments", args.len());
        process::exit(1);
    }

    let input = &args[1];

    println!("  .global main");
    println!("main:");
    println!("  mov ${}, %rax", input);
    println!("  ret");
}
