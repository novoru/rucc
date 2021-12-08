use std::rc::Rc;
use crate::util::error;
use crate::parser::Node;

static ARGREG: &'static [&str] = &["%rdi", "%rsi", "%rdx", "%rcx", "%r8", "%r9"];

pub struct CodeGenerator {
    cur_func:   Option<Rc<Node>>,
    count:      u32,
}

impl CodeGenerator {
    pub fn new() -> Self {

        CodeGenerator {
            cur_func:   None,
            count:      1,
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
            Node::Var { name, ty:_ }    =>  {
                if let Some(func) = &self.cur_func {
                    if let Node::Function { locals,..} = &**func {
                        for obj in &locals.borrow().objs {
                            if obj.0 == name {
                                println!("  lea {}(%rbp), %rax", -(obj.1.offset as i32));
                                return;
                            }
                        }
                    }
                }
            },
            Node::Deref (expr)   =>  {
                self.gen_expr(expr);
            },
            _   =>  error("not an lvalue"),
        }
    }

    fn gen_expr(&mut self, node: &Node) {
        match node {
            Node::Num (val)   => println!("  mov ${}, %rax", val),
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
            Node::Neg (expr)    =>   {
                self.gen_expr(expr);
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
            Node::Var {..}   =>  {
                self.gen_addr(node);
                println!("  mov (%rax), %rax");
            },
            Node::FuncCall { name, args } =>  {
                for arg in args {
                    self.gen_expr(arg);
                    self.push();
                }

                for i in (0..args.len()).rev() {
                    self.pop(ARGREG[i]);
                }

                println!("  mov $0, %rax");
                println!("  call {}", name);
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
            Node::Block (stmts)  =>  {
                for stmt in stmts {
                    self.gen_stmt(stmt);
                }
            },
            Node::Return (expr) =>  {
                self.gen_expr(expr);
                if let Some(func) = &self.cur_func {
                    if let Node::Function{ name, .. } = &**func {
                        println!("  jmp .L.return.{}", name);
                    }
                }
            },
            Node::ExprStmt (expr) => {
                self.gen_expr(&expr);
            }
            _   => error(&format!("invalid statement: {:?}", node)),
        }
    }

    fn gen_func(&mut self, func: &Node) {
        self.cur_func = Some(Rc::new(func.clone()));
        println!("  .global main");
        match func {
            Node::Function { name, body, locals, ret_ty:_ }  =>  {
                println!("{}:", name);
                
                // Prologue
                println!("  push %rbp");

                println!("  mov %rsp, %rbp");
                println!("  sub ${}, %rsp", locals.borrow().stack_size);
                
                // Emit code
                for stmt in body {
                    self.gen_stmt(&stmt);
                }
                
                // Epilogue
                println!(".L.return.{}:", name);
                println!("  mov %rbp, %rsp");
                println!("  pop %rbp");
                println!("  ret");
            },
            _   =>  error(&format!("not function: {:?}", &func)),
        }
    }

    fn gen_prog(&mut self, prog: &mut Node) {
        match prog {
            Node::Program (ref mut funcs ) =>  {
                for func in funcs {
                    self.gen_func(func);
                }
            },
            _   =>  error(&format!("not program: {:?}", prog)),
        }
    }

    pub fn gen(&mut self, prog: &mut Node) {
        self.gen_prog(prog);
    }
}