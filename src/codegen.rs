use std::rc::Rc;
use std::io::Write;
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
    output:     Box<dyn Write>,
}

impl CodeGenerator {
    pub fn new(output: Box<dyn Write>) -> Self {

        CodeGenerator {
            cur_func:   None,
            count:      1,
            output:     output,
        }
    }

    fn count(&mut self) -> u32 {
        let c = self.count;
        self.count += 1;
        c
    }

    fn push(&mut self, ) {
        writeln!(self.output, "  push %rax").unwrap();
    }

    fn pop(&mut self, arg: &str) {
        writeln!(self.output, "  pop {}", arg).unwrap();
    }
    
    // Load a value from where %rax is pointing to.
    fn load(&mut self, ty: &Type) {
        if let Type::Array { .. } = ty {
            return;
        }

        if ty.get_size() == 1 {
            writeln!(self.output, "  movsbq (%rax), %rax").unwrap();
        } else {
            writeln!(self.output, "  mov (%rax), %rax").unwrap();
        }
    }

    fn store(&mut self, ty: &Type) {
        self.pop("%rdi");

        if ty.get_size() == 1 {
            writeln!(self.output, "  mov %al, (%rdi)").unwrap();
        } else {
            writeln!(self.output, "  mov %rax, (%rdi)").unwrap();
        }
    }

    // Compute the absolute address of a given node.
    // It's an error if a given node does not reside in memory.
    fn gen_addr(&mut self, node: &Node) {
        match node {
            Node::Var { obj, .. }  =>  {
                if obj.is_local {
                    writeln!(self.output, "  lea {}(%rbp), %rax", -(obj.offset as i32)).unwrap();
                } else {
                    writeln!(self.output, "  lea {}(%rip), %rax", obj.ty.get_name().unwrap()).unwrap();
                }
                return;
            },
            Node::Deref (expr, ..)  =>  {
                self.gen_expr(expr);
            },
            Node::Comma { lhs, rhs, .. }    =>  {
                self.gen_expr(lhs);
                self.gen_addr(rhs);
            },
            _   =>  node.get_token().error("not an lvalue"),
        }
    }

    fn gen_expr(&mut self, node: &Node) {
        match node {
            Node::Num (val, ..)         => writeln!(self.output, "  mov ${}, %rax", val).unwrap(),
            Node::Add { lhs, rhs, .. }  =>  {
                self.gen_expr(rhs);
                self.push();
                self.gen_expr(lhs);
                self.pop("%rdi");
                writeln!(self.output, "  add %rdi, %rax").unwrap();
            },
            Node::Sub { lhs, rhs, .. }  =>  {
                self.gen_expr(rhs);
                self.push();
                self.gen_expr(lhs);
                self.pop("%rdi");
                writeln!(self.output, "  sub %rdi, %rax").unwrap();
            },
            Node::Mul { lhs, rhs, .. }  =>  {
                self.gen_expr(rhs);
                self.push();
                self.gen_expr(lhs);
                self.pop("%rdi");
                writeln!(self.output, "  imul %rdi, %rax").unwrap();
            },
            Node::Div { lhs, rhs, .. }  =>  {
                self.gen_expr(rhs);
                self.push();
                self.gen_expr(lhs);
                self.pop("%rdi");
                writeln!(self.output, "  cqo").unwrap();
                writeln!(self.output, "  idiv %rdi").unwrap();
            },
            Node::Neg (expr, ..)    =>   {
                self.gen_expr(expr);
                writeln!(self.output, "  neg %rax").unwrap();
            },
            Node::Eq { lhs, rhs, .. }   =>  {
                self.gen_expr(rhs);
                self.push();
                self.gen_expr(lhs);
                self.pop("%rdi");
                writeln!(self.output, "  cmp %rdi, %rax").unwrap();
                writeln!(self.output, "  sete %al").unwrap();
                writeln!(self.output, "  movzb %al, %rax").unwrap();
            },
            Node::Ne { lhs, rhs, .. }   =>  {
                self.gen_expr(rhs);
                self.push();
                self.gen_expr(lhs);
                self.pop("%rdi");
                writeln!(self.output, "  cmp %rdi, %rax").unwrap();
                writeln!(self.output, "  setne %al").unwrap();
                writeln!(self.output, "  movzb %al, %rax").unwrap();
            },
            Node::Lt { lhs, rhs, .. }   =>  {
                self.gen_expr(rhs);
                self.push();
                self.gen_expr(lhs);
                self.pop("%rdi");
                writeln!(self.output, "  cmp %rdi, %rax").unwrap();
                writeln!(self.output, "  setl %al").unwrap();
                writeln!(self.output, "  movzb %al, %rax").unwrap();
            },
            Node::Le { lhs, rhs, .. }   =>  {
                self.gen_expr(rhs);
                self.push();
                self.gen_expr(lhs);
                self.pop("%rdi");
                writeln!(self.output, "  cmp %rdi, %rax").unwrap();
                writeln!(self.output, "  setle %al").unwrap();
                writeln!(self.output, "  movzb %al, %rax").unwrap();
            },
            Node::Deref (expr, ..)  =>  {
                self.gen_expr(expr);
                self.load(&node.get_type());
            },
            Node::Addr (expr, ..)   =>  {
                self.gen_addr(expr);
            },
            Node::Assign { lhs, rhs, .. }   =>  {
                self.gen_addr(lhs);
                self.push();
                self.gen_expr(rhs);
                self.store(&node.get_type());
            },
            Node::Var { ty, .. }    =>  {
                self.gen_addr(node);
                self.load(&ty);
            },
            Node::StmtExpr (body, ..)   =>  {
                self.gen_stmt(body);
            },
            Node::Comma { lhs, rhs, .. }    =>  {
                self.gen_expr(lhs);
                self.gen_expr(rhs);
            },
            Node::FuncCall { name, args, .. } =>  {
                for arg in args {
                    self.gen_expr(arg);
                    self.push();
                }

                for i in (0..args.len()).rev() {
                    self.pop(ARGREG64[i]);
                }

                writeln!(self.output, "  mov $0, %rax").unwrap();
                writeln!(self.output, "  call {}", name).unwrap();
            },
            _   =>  node.get_token().error("invalid node"),
        }
    }

    fn gen_stmt(&mut self, node: &Node) {
        match node {
            Node::If { cond, then, els, .. }    =>  {
                let c = self.count();

                self.gen_expr(cond);
                writeln!(self.output, "  cmp $0, %rax").unwrap();
                writeln!(self.output, "  je  .L.else.{}", c).unwrap();
                self.gen_stmt(then);
                writeln!(self.output, "  jmp .L.end.{}", c).unwrap();
                writeln!(self.output, ".L.else.{}:", c).unwrap();
                if let Some(stmt) = els {
                    self.gen_stmt(stmt);
                };
                writeln!(self.output, ".L.end.{}:", c).unwrap();
            },
            Node::For { init, cond, inc, body, .. } =>  {
                let c = self.count();

                if let Some(stmt) = init {
                    self.gen_stmt(stmt);
                }
                writeln!(self.output, ".L.begin.{}:", c).unwrap();

                if let Some(expr) = cond {
                    self.gen_expr(expr);
                    writeln!(self.output, "  cmp $0, %rax").unwrap();
                    writeln!(self.output, "  je .L.end.{}", c).unwrap();
                }

                self.gen_stmt(body);

                if let Some(expr) = inc {
                    self.gen_expr(expr);
                }

                writeln!(self.output, "  jmp .L.begin.{}", c).unwrap();
                writeln!(self.output, ".L.end.{}:", c).unwrap();
            },
            Node::Block (stmts, ..) =>  {
                for stmt in stmts {
                    self.gen_stmt(stmt);
                }
            },
            Node::Return (expr, ..) =>  {
                self.gen_expr(expr);
                if let Some(func) = &self.cur_func {
                    if let Node::Function{ name, .. } = &**func {
                        writeln!(self.output, "  jmp .L.return.{}", name).unwrap();
                    }
                }
            },
            Node::ExprStmt (expr, ..)   => {
                self.gen_expr(&expr);
            }
            _   => node.get_token().error("invalid statement"),
        }
    }

    fn gen_func(&mut self, func: &Node) {
        self.cur_func = Some(Rc::new(func.clone()));
        match func {
            Node::Function { name, params, body, locals, .. }  =>  {
                writeln!(self.output, "  .globl {}", name).unwrap();
                writeln!(self.output, "  .text").unwrap();
                writeln!(self.output, "{}:", name).unwrap();
                
                // Prologue
                writeln!(self.output, "  push %rbp").unwrap();

                writeln!(self.output, "  mov %rsp, %rbp").unwrap();
                writeln!(self.output, "  sub ${}, %rsp", locals.borrow().stack_size).unwrap();
                
                // Save passed-by-register arguments to the stack
                let mut i = 0;
                for param in &params.objs {
                    if param.ty.get_size() == 1 {
                        writeln!(self.output, "  mov {}, {}(%rbp)", ARGREG8[i], -(param.offset as i32)).unwrap();
                    } else {
                        writeln!(self.output, "  mov {}, {}(%rbp)", ARGREG64[i], -(param.offset as i32)).unwrap();
                    }
                    i += 1;
                }

                // Emit code
                for stmt in body {
                    self.gen_stmt(&stmt);
                }
                
                // Epilogue
                writeln!(self.output, ".L.return.{}:", name).unwrap();
                writeln!(self.output, "  mov %rbp, %rsp").unwrap();
                writeln!(self.output, "  pop %rbp").unwrap();
                writeln!(self.output, "  ret").unwrap();
            },
            _   =>  func.get_token().error("not function"),
        }
    }

    fn emit_data(&mut self, objs: &Vec<Obj>) {
        for var in objs {
            writeln!(self.output, "  .data").unwrap();
            writeln!(self.output, "  .globl {}", var.ty.get_name().unwrap()).unwrap();
            writeln!(self.output, "{}:", var.ty.get_name().unwrap()).unwrap();

            if let Some(init_data) = &var.init_data {
                for ch in init_data {
                    writeln!(self.output, "  .byte {}", *ch as u32).unwrap();
                }
            } else {
                writeln!(self.output, "  .zero {}", var.ty.get_size()).unwrap();
            }
        }
    }

    fn gen_prog(&mut self, prog: &mut Node) {
        match prog {
            Node::Program { data, ref mut text, .. }    =>  {
                self.emit_data(&data.borrow().objs);
                for func in text {
                    self.gen_func(func);
                }
            },
            _   =>  prog.get_token().error("not program"),
        }
    }

    pub fn gen(&mut self, prog: &mut Node) {
        self.gen_prog(prog);
    }
}