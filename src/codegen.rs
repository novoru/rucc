use crate::parser::Node;

pub fn codegen(&node: Node) {
    println!("  .global main");
    println!("main:");

    gen_expr();

    println!("  ret");
}