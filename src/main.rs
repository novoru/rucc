use std::{env, process};
use std::io::stdin;
use std::io::Read;
use std::fs::read_to_string;
use rucc::parser::Parser;
use rucc::codegen::CodeGenerator;

fn main() {
    let args: Vec<String> = env::args().collect();

    if args.len() != 2 {
        eprintln!("{}: invalid number of arguments", args.len());
        process::exit(1);
    }

    let path = &args[1];
    let mut buf = Vec::new();

    let input = if path == "-" {
        stdin().lock().read_to_end(&mut buf).unwrap();
        std::str::from_utf8(&buf).unwrap().to_string()
    } else {
        read_to_string(path).unwrap()
    };

    let mut parser = Parser::new(&input);
    let mut prog = parser.parse().unwrap();
    let mut codegen = CodeGenerator::new();
    codegen.gen(&mut prog);
}
