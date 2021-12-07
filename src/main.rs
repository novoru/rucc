use std::{env, process};
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
    let mut prog = parser.parse().unwrap();
    dbg!(&prog);
    let mut codegen = CodeGenerator::new(parser.scope);
    codegen.gen(&mut prog);
}
