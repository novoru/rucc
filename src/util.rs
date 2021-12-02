use std::process;

pub fn error(s: &str) {
    eprintln!("{}", s);
    process::exit(1);
}