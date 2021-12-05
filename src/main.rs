use std::{env, process};
use rucc::tokenizer::Tokenizer;
use rucc::parser::Parser;
use rucc::codegen::CodeGenerator;

fn main() {
    let args: Vec<String> = env::args().collect();

    if args.len() != 2 {
        eprintln!("{}: invalid number of arguments", args.len());
        process::exit(1);
    }

    let input = &args[1];

    let mut parser = Parser::new(input);
    let prog = parser.parse().unwrap();
    let mut codegen = CodeGenerator::new();
    codegen.gen(&prog);
}
