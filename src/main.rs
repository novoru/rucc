use std::{env, process};
use std::io::{ Read, Write, stdin };
use std::fs::read_to_string;
use rucc::parser::Parser;
use rucc::codegen::CodeGenerator;

#[derive(Debug)]
struct Opt {
    input_path: Option<String>,
    opt_o:      Option<String>,
}

fn usage(status: i32) {
    eprintln!("rucc [ -o <path> ] <file>");
    process::exit(status);
}

fn parse_args(args: Vec<String>) -> Opt {
    let mut oflag = false;
    let mut opt_o = None;
    let mut input_path = None;

    for (_, arg) in args.iter().skip(1).enumerate() {
        if oflag {
            opt_o = Some(arg.clone());
            oflag = false;
            continue;
        }

        if arg == "--help" {
            usage(0);
        }

        if arg == "-o" {
            oflag = true;
            continue;
        }

        input_path = Some(arg.clone());
    }

    if input_path == None {
        eprintln!("no input files");
        process::exit(1);
    }

    Opt {
        input_path,
        opt_o,
    }
}

fn open_file(path: String) -> String {
    if path == "" || path == "-" {
        let mut buf = Vec::new();
        stdin().lock().read_to_end(&mut buf).unwrap();
        return std::str::from_utf8(&buf).unwrap().to_string();
    }

    read_to_string(path).unwrap()
}

fn main() {
    let args: Vec<String> = env::args().collect();

    let opt = parse_args(args);

    let path = opt.input_path.unwrap();
    let input = open_file(path.to_string());

    let mut parser = Parser::new(&input);
    let mut prog = parser.parse().unwrap();

    let output: Box<dyn Write> = if let Some(output_file) = opt.opt_o {
        Box::new(std::fs::File::create(output_file).unwrap())
    } else {
        Box::new(std::io::stdout())
    };

    let mut codegen = CodeGenerator::new(output);
    codegen.gen(&mut prog);
}
