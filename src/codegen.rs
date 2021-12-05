use std::rc::Rc;
use std::cell::RefCell;
use crate::util::error;
use crate::parser::{ Node, Scope };

pub struct CodeGenerator {
    scope:  Rc<RefCell<Scope>>,
    count:  u32,
}

impl CodeGenerator {
    pub fn new(scope: Rc<RefCell<Scope>>) -> Self {

        CodeGenerator {
            scope:  Rc::clone(&scope),
            count:  1,
        }
    }

    fn count(&mut self) -> u32 {
        let c = self.count;
        self.count += 1;
        c
    }

    fn push(&mut self, ) {
        println!("  push %rax");
    }

    fn pop(&mut self, arg: &str) {
        println!("  pop {}", arg);
    }

    // Compute the absolute address of a given node.
    // It's an error if a given node does not reside in memory.
    fn gen_addr(&mut self, node: &Node) {
        match node {
            Node::Var(name)     =>  {
                for obj in &self.scope.borrow_mut().objs {
                    if obj.0 == name {
                        println!("  lea {}(%rbp), %rax", -obj.1.offset);
                        return;
                    }
                }
            },
            Node::Deref(expr)   =>  {
                self.gen_expr(expr);
            },
            _   =>  error("not an lvalue"),
        }
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
            Node::Neg (node)    =>   {
                self.gen_expr(node);
                println!("  neg %rax");
            },
            Node::Eq { lhs, rhs }   =>  {
                self.gen_expr(rhs);
                self.push();
                self.gen_expr(lhs);
                self.pop("%rdi");
                println!("  cmp %rdi, %rax");
                println!("  sete %al");
                println!("  movzb %al, %rax");
            },
            Node::Ne { lhs, rhs }   =>  {
                self.gen_expr(rhs);
                self.push();
                self.gen_expr(lhs);
                self.pop("%rdi");
                println!("  cmp %rdi, %rax");
                println!("  setne %al");
                println!("  movzb %al, %rax");
            },
            Node::Lt { lhs, rhs }   =>  {
                self.gen_expr(rhs);
                self.push();
                self.gen_expr(lhs);
                self.pop("%rdi");
                println!("  cmp %rdi, %rax");
                println!("  setl %al");
                println!("  movzb %al, %rax");
            },
            Node::Le { lhs, rhs }   =>  {
                self.gen_expr(rhs);
                self.push();
                self.gen_expr(lhs);
                self.pop("%rdi");
                println!("  cmp %rdi, %rax");
                println!("  setle %al");
                println!("  movzb %al, %rax");
            },
            Node::Deref (expr)  =>  {
                self.gen_expr(expr);
                println!("  mov (%rax), %rax");
            },
            Node::Addr (expr)   =>  {
                self.gen_addr(expr);
            },
            Node::Assign { lhs, rhs }   =>  {
                self.gen_addr(lhs);
                self.push();
                self.gen_expr(rhs);
                self.pop("%rdi");
                println!("  mov %rax, (%rdi)");
            },
            Node::Var (_)   =>  {
                self.gen_addr(node);
                println!("  mov (%rax), %rax");
            },
            _   =>  error("invalid node"),
        }
    }

    fn gen_stmt(&mut self, node: &Node) {
        match node {
            Node::If { cond, then, els }    =>  {
                let c = self.count();

                self.gen_expr(cond);
                println!("  cmp $0, %rax");
                println!("  je  .L.else.{}", c);
                self.gen_stmt(then);
                println!("  jmp .L.end.{}", c);
                println!(".L.else.{}:", c);
                if let Some(stmt) = els {
                    self.gen_stmt(stmt);
                };
                println!(".L.end.{}:", c);
            },
            Node::For { init, cond, inc, body } =>  {
                let c = self.count();

                if let Some(stmt) = init {
                    self.gen_stmt(stmt);
                }
                println!(".L.begin.{}:", c);

                if let Some(expr) = cond {
                    self.gen_expr(expr);
                    println!("  cmp $0, %rax");
                    println!("  je .L.end.{}", c);
                }

                self.gen_stmt(body);

                if let Some(expr) = inc {
                    self.gen_expr(expr);
                }

                println!("  jmp .L.begin.{}", c);
                println!(".L.end.{}:", c);
            },
            Node::Block (body)  =>  {
                for stmt in body {
                    self.gen_stmt(stmt);
                }
            },
            Node::Return (expr) =>  {
                self.gen_expr(expr);
                println!("  jmp .L.return");
            },
            Node::ExprStmt(expr) => {
                self.gen_expr(&expr);
            }
            _   => error(&format!("invalid statement: {:?}", node)),
        }
    }

    fn gen_func(&mut self, func: &Node) {
        match func {
            Node::Function { body, locals }  =>  {
                println!("  sub ${}, %rsp", locals.borrow().stack_size);
                for stmt in body {
                    self.gen_stmt(&stmt);
                }
            },
            _   =>  error(&format!("not function: {:?}", &func)),
        }
    }

    fn gen_prog(&mut self, prog: &mut Node) {
        match prog {
            Node::Program(ref mut funcs) =>  {
                let func = &funcs[0];
                self.gen_func(func);
            },
            _   =>  error(&format!("not program: {:?}", prog)),
        }
    }

    pub fn gen(&mut self, prog: &mut Node) {
        println!("  .global main");
        println!("main:");

        // Prologue
        println!("  push %rbp");
        println!("  mov %rsp, %rbp");

        self.gen_prog(prog);

        println!(".L.return:");
        println!("  mov %rbp, %rsp");
        println!("  pop %rbp");
        println!("  ret");
    }
}