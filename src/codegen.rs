use crate::parser::Node;

pub struct CodeGenerator {
    depth:  u32,
}

impl CodeGenerator {
    pub fn new() -> Self {
        CodeGenerator {
            depth:  0,
        }
    }

    fn push(&mut self, ) {
        println!("  push %rax");
        self.depth += 1;
    }

    fn pop(&mut self, arg: &str) {
        println!("  pop {}", arg);
        self.depth -= 1;
    }

    fn gen_expr(&mut self, node: &Node) {
        match node {
            Node::Num (val) => println!("  mov ${}, %rax", val),
            Node::Add { lhs, rhs }  =>  {
                self.gen_expr(rhs);
                self.push();
                self.gen_expr(lhs);
                self.pop("%rdi");
                println!("  add %rdi, %rax");
            },
            Node::Sub { lhs, rhs }  =>  {
                self.gen_expr(rhs);
                self.push();
                self.gen_expr(lhs);
                self.pop("%rdi");
                println!("  sub %rdi, %rax");
            },
            Node::Mul { lhs, rhs }  =>  {
                self.gen_expr(rhs);
                self.push();
                self.gen_expr(lhs);
                self.pop("%rdi");
                println!("  imul %rdi, %rax");
            },
            Node::Div { lhs, rhs }  =>  {
                self.gen_expr(rhs);
                self.push();
                self.gen_expr(lhs);
                self.pop("%rdi");
                println!("  cqo");
                println!("  idiv %rdi");
            },
        }
    }

    pub fn gen(&mut self, node: &Node) {
        self.depth = 0;

        println!("  .global main");
        println!("main:");

        self.gen_expr(node);

        println!("  ret");
        assert!(self.depth==0);
    }
}

#[test]
fn test_codegen() {
    use crate::tokenizer::Tokenizer;
    use crate::parser::Parser;

    let mut tokenizer = Tokenizer::new("12+42*(3-9)");
    tokenizer.tokenize();
    let mut parser = Parser::new(&mut tokenizer);
    let prog = parser.parse().unwrap();
    let mut codegen = CodeGenerator::new();
    codegen.gen(&prog);
}