use std::rc::Rc;
use std::io::Write;
use std::cell::RefCell;

use crate::node::Node;
use crate::obj::Obj;
use crate::ty::{ Type, TypeKind };

static ARGREG8: &'static [&str] = &[
    "%dil", "%sil", "%dl", "%cl", "%r8b", "%r9b"
];

static ARGREG16: &'static [&str] = &[
    "%di", "%si", "%dx", "%cx", "%r8w", "%r9w"
];

static ARGREG32: &'static [&str] = &[
    "%edi", "%esi", "%edx", "%ecx", "%r8d", "%r9d"
];

static ARGREG64: &'static [&str] = &[
    "%rdi", "%rsi", "%rdx", "%rcx", "%r8", "%r9"
];

#[derive(Debug, Copy, Clone)]
enum TypeId {
    I8 = 0,
    I16,
    I32,
    I64,
}

fn get_type_id(ty: Rc<RefCell<Type>>) -> TypeId {
    match ty.borrow().kind {
        TypeKind::Char  =>  TypeId::I8,
        TypeKind::Short =>  TypeId::I16,
        TypeKind::Int   =>  TypeId::I32,
        _               =>  TypeId::I64,
    }
}

// The table for type casts
static I32I8: &'static str  = "movsbl %al, %eax";
static I32I16: &'static str = "movswl %ax, %eax";
static I32I64: &'static str = "cltq";

static CAST_TABLE: [[Option<&'static str>; 4]; 4] = [
  [None,        None,           None, Some(I32I64)],    // i8
  [Some(I32I8), None,           None, Some(I32I64)],    // i16
  [Some(I32I8), Some(I32I16),   None, Some(I32I64)],    // i32
  [Some(I32I8), Some(I32I16),   None, None],            // i64
];

fn reg_name(lhs: &Node) -> (String, String) {
    if lhs.get_type().borrow().kind == TypeKind::Long || lhs.get_type().borrow().base.is_some() {
        ("%rax".to_string(), "%rdi".to_string())
    } else {
        ("%eax".to_string(), "%edi".to_string())
    }
}

pub struct CodeGenerator {
    cur_func:   Option<Rc<Node>>,
    count:      u64,
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

    fn count(&mut self) -> u64 {
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
    fn load(&mut self, ty: Rc<RefCell<Type>>) {
        match ty.borrow().kind {
            TypeKind::Array     |
            TypeKind::Struct    |
            TypeKind::Union     => return,
            _   =>  (),
        }

        match ty.borrow().size {
            1   =>  writeln!(self.output, "  movsbl (%rax), %eax").unwrap(),
            2   =>  writeln!(self.output, "  movswl (%rax), %eax").unwrap(),
            4   =>  writeln!(self.output, "  movsxd (%rax), %rax").unwrap(),
            _   =>  writeln!(self.output, "  mov (%rax), %rax").unwrap(),
        }
    }

    fn store(&mut self, ty: Rc<RefCell<Type>>) {
        self.pop("%rdi");

        match ty.borrow().kind {
            TypeKind::Struct    |
            TypeKind::Union     => {
                for i in 0..ty.borrow().size {
                    writeln!(self.output, "  mov {}(%rax), %r8b", i).unwrap();
                    writeln!(self.output, "  mov %r8b, {}(%rdi)", i).unwrap();
                }
                return;
            },
            _   =>  (),
        }

        match ty.borrow().size {
            1   =>  writeln!(self.output, "  mov %al, (%rdi)").unwrap(),
            2   =>  writeln!(self.output, "  mov %ax, (%rdi)").unwrap(),
            4   =>  writeln!(self.output, "  mov %eax, (%rdi)").unwrap(),
            _   =>  writeln!(self.output, "  mov %rax, (%rdi)").unwrap(),
        }
    }

    fn cast(&mut self, from: Rc<RefCell<Type>>, to: Rc<RefCell<Type>>) {
        if to.borrow().kind == TypeKind::Void {
            return;
        }

        if to.borrow().kind == TypeKind::Bool {
            self.cmp_zero(from);
            writeln!(self.output, "  setne %al").unwrap();
            writeln!(self.output, "  movzx %al, %rax").unwrap();
            return;
        }
    
        let t1 = get_type_id(from);
        let t2 = get_type_id(to);
        
        if let Some(conv) = CAST_TABLE[t1 as usize][t2 as usize] {
            writeln!(self.output, "  {}", conv).unwrap();
        }
    }

    fn cmp_zero(&mut self, ty: Rc<RefCell<Type>>) {
        if ty.borrow().is_num() && ty.borrow().size <= 4 {
            writeln!(self.output, "  cmp $0, %eax").unwrap();
        } else {
            writeln!(self.output, "  cmp $0, %rax").unwrap();
        }
    }

    // Compute the absolute address of a given node.
    // It's an error if a given node does not reside in memory.
    fn gen_addr(&mut self, node: &Node) {
        match node {
            Node::Var { obj, .. }  =>  {
                if obj.borrow().is_local {
                    writeln!(self.output, "  lea {}(%rbp), %rax", -(obj.borrow().offset as i64)).unwrap();
                } else {
                    writeln!(self.output, "  lea {}(%rip), %rax", obj.borrow().ty.borrow().name.as_ref().unwrap().literal).unwrap();
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
            Node::Member{ base, member, .. } =>  {
                self.gen_addr(base);
                writeln!(self.output, "  add ${}, %rax", member.offset).unwrap();
            },
            _   =>  node.get_token().error("not an lvalue"),
        }
    }

    fn gen_expr(&mut self, node: &Node) {
        match node {
            Node::Num (val, ..)         => writeln!(self.output, "  mov ${}, %rax", val).unwrap(),
            Node::Add { lhs, rhs, .. }  =>  {
                let (ax, di) = reg_name(lhs);
                self.gen_expr(rhs);
                self.push();
                self.gen_expr(lhs);
                self.pop("%rdi");
                writeln!(self.output, "  add {}, {}", &di, &ax).unwrap();
            },
            Node::Sub { lhs, rhs, .. }  =>  {
                let (ax, di) = reg_name(lhs);
                self.gen_expr(rhs);
                self.push();
                self.gen_expr(lhs);
                self.pop("%rdi");
                writeln!(self.output, "  sub {}, {}", &di, &ax).unwrap();
            },
            Node::Mul { lhs, rhs, .. }  =>  {
                let (ax, di) = reg_name(lhs);
                self.gen_expr(rhs);
                self.push();
                self.gen_expr(lhs);
                self.pop("%rdi");
                writeln!(self.output, "  imul {}, {}", &di, &ax).unwrap();
            },
            Node::Div { lhs, rhs, .. }  =>  {
                let (_, di) = reg_name(lhs);
                self.gen_expr(rhs);
                self.push();
                self.gen_expr(lhs);
                self.pop("%rdi");
                if lhs.get_type().borrow().size == 8 {
                    writeln!(self.output, "  cqo").unwrap();
                } else {
                    writeln!(self.output, "  cdq").unwrap();
                }
                writeln!(self.output, "  idiv {}", di).unwrap();
            },
            Node::Mod { lhs, rhs, .. }  =>  {
                let (_, di) = reg_name(lhs);
                self.gen_expr(rhs);
                self.push();
                self.gen_expr(lhs);
                self.pop("%rdi");
                if lhs.get_type().borrow().size == 8 {
                    writeln!(self.output, "  cqo").unwrap();
                } else {
                    writeln!(self.output, "  cdq").unwrap();
                }
                writeln!(self.output, "  idiv {}", di).unwrap();
                writeln!(self.output, "  mov %rdx, %rax").unwrap();
            },
            Node::Neg (expr, ..)    =>   {
                self.gen_expr(expr);
                writeln!(self.output, "  neg %rax").unwrap();
            },
            Node::BitAnd { lhs, rhs, .. }  =>  {
                self.gen_expr(rhs);
                self.push();
                self.gen_expr(lhs);
                self.pop("%rdi");
                writeln!(self.output, "  and %rdi, %rax").unwrap();
            },
            Node::BitOr { lhs, rhs, .. }  =>  {
                self.gen_expr(rhs);
                self.push();
                self.gen_expr(lhs);
                self.pop("%rdi");
                writeln!(self.output, "  or %rdi, %rax").unwrap();
            },
            Node::BitXor { lhs, rhs, .. }  =>  {
                self.gen_expr(rhs);
                self.push();
                self.gen_expr(lhs);
                self.pop("%rdi");
                writeln!(self.output, "  xor %rdi, %rax").unwrap();
            },
            Node::Eq { lhs, rhs, .. }   =>  {
                let (ax, di) = reg_name(lhs);
                self.gen_expr(rhs);
                self.push();
                self.gen_expr(lhs);
                self.pop("%rdi");
                writeln!(self.output, "  cmp {}, {}", di, ax).unwrap();
                writeln!(self.output, "  sete %al").unwrap();
                writeln!(self.output, "  movzb %al, %rax").unwrap();
            },
            Node::Ne { lhs, rhs, .. }   =>  {
                let (ax, di) = reg_name(lhs);
                self.gen_expr(rhs);
                self.push();
                self.gen_expr(lhs);
                self.pop("%rdi");
                writeln!(self.output, "  cmp {}, {}", di, ax).unwrap();
                writeln!(self.output, "  setne %al").unwrap();
                writeln!(self.output, "  movzb %al, %rax").unwrap();
            },
            Node::Lt { lhs, rhs, .. }   =>  {
                let (ax, di) = reg_name(lhs);
                self.gen_expr(rhs);
                self.push();
                self.gen_expr(lhs);
                self.pop("%rdi");
                writeln!(self.output, "  cmp {}, {}", di, ax).unwrap();
                writeln!(self.output, "  setl %al").unwrap();
                writeln!(self.output, "  movzb %al, %rax").unwrap();
            },
            Node::Le { lhs, rhs, .. }   =>  {
                let (ax, di) = reg_name(lhs);
                self.gen_expr(rhs);
                self.push();
                self.gen_expr(lhs);
                self.pop("%rdi");
                writeln!(self.output, "  cmp {}, {}", di, ax).unwrap();
                writeln!(self.output, "  setle %al").unwrap();
                writeln!(self.output, "  movzb %al, %rax").unwrap();
            },
            Node::Deref (expr, ..)  =>  {
                self.gen_expr(expr);
                self.load(node.get_type());
            },
            Node::Not (expr, ..)    =>  {
                self.gen_expr(expr);
                writeln!(self.output, "  cmp $0, %rax").unwrap();
                writeln!(self.output, "  sete %al").unwrap();
                writeln!(self.output, "  movzx %al, %rax").unwrap();
            }
            Node::BitNot (expr, ..) =>  {
                self.gen_expr(expr);
                writeln!(self.output, "  not %rax").unwrap();
            },
            Node::Addr (expr, ..)   =>  {
                self.gen_addr(expr);
            },
            Node::Assign { lhs, rhs, .. }   =>  {
                self.gen_addr(lhs);
                self.push();
                self.gen_expr(rhs);
                self.store(node.get_type());
            },
            Node::Var { ty, .. }    =>  {
                self.gen_addr(node);
                self.load(Rc::clone(ty));
            },
            Node::Member { .. } =>  {
                self.gen_addr(node);
                self.load(node.get_type());
            },
            Node::StmtExpr (body, ..)   =>  {
                self.gen_stmt(body);
            },
            Node::Comma { lhs, rhs, .. }    =>  {
                self.gen_expr(lhs);
                self.gen_expr(rhs);
            },
            Node::Cast { expr, .. } =>  {
                self.gen_expr(expr);
                self.cast(expr.get_type(), node.get_type());
            },
            Node::LogAnd { lhs, rhs, ..}    =>  {
                let c = self.count();
                self.gen_expr(lhs);
                writeln!(self.output, "  cmp $0, %rax").unwrap();
                writeln!(self.output, "  je .L.false.{}", c).unwrap();
                self.gen_expr(rhs);
                writeln!(self.output, "  cmp $0, %rax").unwrap();
                writeln!(self.output, "  je .L.false.{}", c).unwrap();
                writeln!(self.output, "  mov $1, %rax").unwrap();
                writeln!(self.output, "  jmp .L.end.{}", c).unwrap();
                writeln!(self.output, ".L.false.{}:", c).unwrap();
                writeln!(self.output, "  mov $0, %rax").unwrap();
                writeln!(self.output, ".L.end.{}:", c).unwrap();
            },
            Node::LogOr { lhs, rhs, ..}    =>  {
                let c = self.count();
                self.gen_expr(lhs);
                writeln!(self.output, "  cmp $0, %rax").unwrap();
                writeln!(self.output, "  jne .L.true.{}", c).unwrap();
                self.gen_expr(rhs);
                writeln!(self.output, "  cmp $0, %rax").unwrap();
                writeln!(self.output, "  jne .L.true.{}", c).unwrap();
                writeln!(self.output, "  mov $0, %rax").unwrap();
                writeln!(self.output, "  jmp .L.end.{}", c).unwrap();
                writeln!(self.output, ".L.true.{}:", c).unwrap();
                writeln!(self.output, "  mov $1, %rax").unwrap();
                writeln!(self.output, ".L.end.{}:", c).unwrap();
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
            Node::Goto { unique_label, .. } =>  {
                writeln!(self.output, "  jmp {}", unique_label.as_ref().unwrap()).unwrap();
            },
            Node::Label { stmt, unique_label, .. } =>   {
                writeln!(self.output, "{}:", unique_label).unwrap();
                self.gen_stmt(stmt);
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

    fn store_gp(&mut self, r: usize, offset: i64, sz: u64) {
        match sz {
            1   =>  writeln!(self.output, "  mov {}, {}(%rbp)", ARGREG8[r], -offset).unwrap(),
            2   =>  writeln!(self.output, "  mov {}, {}(%rbp)", ARGREG16[r], -offset).unwrap(),
            4   =>  writeln!(self.output, "  mov {}, {}(%rbp)", ARGREG32[r], -offset).unwrap(), 
            8   =>  writeln!(self.output, "  mov {}, {}(%rbp)", ARGREG64[r], -offset).unwrap(),
            _   =>  panic!("internal error"),
        }
    }

    fn gen_func(&mut self, func: &Node) {
        self.cur_func = Some(Rc::new(func.clone()));
        match func {
            Node::Function { name, params, body, locals, is_static, .. }  =>  {

                if *is_static {
                    writeln!(self.output, "  .local {}", name).unwrap();
                } else {
                    writeln!(self.output, "  .globl {}", name).unwrap();
                }
                writeln!(self.output, "  .text").unwrap();
                writeln!(self.output, "{}:", name).unwrap();
                
                // Prologue
                writeln!(self.output, "  push %rbp").unwrap();

                writeln!(self.output, "  mov %rsp, %rbp").unwrap();
                writeln!(self.output, "  sub ${}, %rsp", locals.borrow().stack_size).unwrap();
                
                // Save passed-by-register arguments to the stack
                for (i, param) in params.objs.iter().enumerate() {
                    self.store_gp(i, param.borrow().offset as i64, param.borrow().ty.borrow().size);
                }

                // Emit code
                self.gen_stmt(body);
                
                // Epilogue
                writeln!(self.output, ".L.return.{}:", name).unwrap();
                writeln!(self.output, "  mov %rbp, %rsp").unwrap();
                writeln!(self.output, "  pop %rbp").unwrap();
                writeln!(self.output, "  ret").unwrap();
            },
            _   =>  func.get_token().error("not function"),
        }
    }

    fn emit_data(&mut self, objs: &Vec<Rc<RefCell<Obj>>>) {
        for var in objs {
            if var.borrow().ty.borrow().kind == TypeKind::Function {
                continue;
            }

            writeln!(self.output, "  .data").unwrap();
            writeln!(self.output, "  .globl {}", var.borrow().name).unwrap();
            writeln!(self.output, "{}:", var.borrow().name).unwrap();

            if let Some(init_data) = &var.borrow().init_data {
                for ch in init_data {
                    writeln!(self.output, "  .byte {}", *ch as u64).unwrap();
                }
            } else {
                writeln!(self.output, "  .zero {}", var.borrow().ty.borrow().size).unwrap();
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