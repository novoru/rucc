use std::rc::Rc;
use crate::util::error;
use crate::parser::{ Node, Obj };
use crate::ty::Type;

static ARGREG8: &'static [&str] = &[
    "%dil", "%sil", "%dl", "%cl", "%r8b", "%r9b"
];

static ARGREG64: &'static [&str] = &[
    "%rdi", "%rsi", "%rdx", "%rcx", "%r8", "%r9"
];

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

    fn push(&self, ) {
        println!("  push %rax");
    }

    fn pop(&self, arg: &str) {
        println!("  pop {}", arg);
    }
    
    // Load a value from where %rax is pointing to.
    fn load(&self, ty: &Type) {
        if let Type::Array { .. } = ty {
            return;
        }

        if ty.get_size() == 1 {
            println!("  movsbq (%rax), %rax");
        } else {
            println!("  mov (%rax), %rax");
        }
    }

    fn store(&self, ty: &Type) {
        self.pop("%rdi");

        if ty.get_size() == 1 {
            println!("  mov %al, (%rdi)");
        } else {
            println!("  mov %rax, (%rdi)");
        }
    }

    // Compute the absolute address of a given node.
    // It's an error if a given node does not reside in memory.
    fn gen_addr(&mut self, node: &Node) {
        match node {
            Node::Var { name, ty:_ }    =>  {
                if let Some(func) = &self.cur_func {
                    if let Node::Function { locals,.. } = &**func {
                        for obj in &locals.borrow().objs {
                            if &obj.ty.get_name().unwrap() == name {
                                println!("  lea {}(%rbp), %rax", -(obj.offset as i32));
                                return;
                            }
                        }

                        if let Some(scope) = &locals.borrow().parent {
                            for var in &scope.borrow().objs {
                                if &var.ty.get_name().unwrap() == name {
                                    if scope.borrow().parent == None {
                                        println!("  lea {}(%rip), %rax", var.ty.get_name().unwrap());
                                        return;
                                    } else {
                                        println!("  lea {}(%rbp), %rax", -(var.offset as i32));
                                        return;
                                    }
                                }
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
                self.load(&node.get_type());
            },
            Node::Addr (expr)   =>  {
                self.gen_addr(expr);
            },
            Node::Assign { lhs, rhs }   =>  {
                self.gen_addr(lhs);
                self.push();
                self.gen_expr(rhs);
                self.store(&node.get_type());
            },
            Node::Var { ty, .. }    =>  {
                self.gen_addr(node);
                self.load(&ty);
            },
            Node::FuncCall { name, args } =>  {
                for arg in args {
                    self.gen_expr(arg);
                    self.push();
                }

                for i in (0..args.len()).rev() {
                    self.pop(ARGREG64[i]);
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
        match func {
            Node::Function { name, params, body, locals, .. }  =>  {
                println!("  .globl {}", name);
                println!("  .text");
                println!("{}:", name);
                
                // Prologue
                println!("  push %rbp");

                println!("  mov %rsp, %rbp");
                println!("  sub ${}, %rsp", locals.borrow().stack_size);
                
                // Save passed-by-register arguments to the stack
                let mut i = 0;
                for param in &params.objs {
                    if param.ty.get_size() == 1 {
                        println!("  mov {}, {}(%rbp)", ARGREG8[i], -(param.offset as i32));
                    } else {
                        println!("  mov {}, {}(%rbp)", ARGREG64[i], -(param.offset as i32));
                    }
                    i += 1;
                }

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

    fn emit_data(&self, objs: &Vec<Obj>) {
        for var in objs {
            println!("  .data");
            println!("  .globl {}", var.ty.get_name().unwrap());
            println!("{}:", var.ty.get_name().unwrap());

            if let Some(init_data) = &var.init_data {
                for ch in init_data {
                    println!("  .byte {}", *ch as u32);
                }
            } else {
                println!("  .zero {}", var.ty.get_size());
            }
        }
    }

    fn gen_prog(&mut self, prog: &mut Node) {
        match prog {
            Node::Program {data, ref mut text}  =>  {
                self.emit_data(&data.borrow().objs);
                for func in text {
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