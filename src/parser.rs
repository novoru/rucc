use std::rc::Rc;
use std::cell::RefCell;
use crate::tokenizer::{ TokenKind, Tokenizer };
use crate::ty::*;

// Ast node type
#[derive(Debug, Clone, PartialEq)]
pub enum Node {
    Add         { lhs: Box<Node>, rhs: Box<Node> },     // +
    Sub         { lhs: Box<Node>, rhs: Box<Node> },     // -
    Mul         { lhs: Box<Node>, rhs: Box<Node> },     // *
    Div         { lhs: Box<Node>, rhs: Box<Node> },     // /
    Neg         ( Box<Node> ),                          // unary -
    Eq          { lhs: Box<Node>, rhs: Box<Node> },     // ==
    Ne          { lhs: Box<Node>, rhs: Box<Node> },     // !=
    Lt          { lhs: Box<Node>, rhs: Box<Node> },     // <
    Le          { lhs: Box<Node>, rhs: Box<Node> },     // <=
    Assign      { lhs: Box<Node>, rhs: Box<Node> },     // =
    Addr        ( Box<Node> ),                          // unary &
    Deref       ( Box<Node> ),                          // unary *
    Return      ( Box<Node> ),                          // "return"
    If          {                                       // "if"
                    cond:   Box<Node>,
                    then:   Box<Node>,
                    els:    Option<Box<Node>>,
                },
    For         {                                       // "for" of "while"
                    init:   Option<Box<Node>>,
                    cond:   Option<Box<Node>>,
                    inc:    Option<Box<Node>>,
                    body:   Box<Node>,
                },
    Block       ( Vec<Box<Node>> ),                     // { ... }
    ExprStmt    ( Box<Node> ),                          // Expression statement
    Var         { name: String, ty: Type },             // Variable
    FuncCall    { name: String, args: Vec<Box<Node>> }, // Function call
    Function    {                                       // Function definition
                    name:   String,
                    params: Rc<RefCell<Scope>>,
                    body:   Vec<Box<Node>>,
                    locals: Rc<RefCell<Scope>>,
                    ret_ty: Option<Type>,
                },
    Program     ( Vec<Box<Node>> ),                     // Program
    Num         ( u32 ),                                // Integer
}

impl Node {
    pub fn get_type(&mut self) -> Type {
        match self {
            Node::Add { lhs, .. }   =>  lhs.get_type(),
            Node::Sub { lhs, rhs }  =>  {
                // ptr - ptr, which returns how many elements are between the two.
                if lhs.get_type().is_ptr() && rhs.get_type().is_ptr() {
                    ty_int(None)
                } else {
                    lhs.get_type()
                }
            },
            Node::Mul { lhs, .. }   |
            Node::Div { lhs, .. }   =>  lhs.get_type(),
            Node::Neg (expr)    =>  expr.get_type(),
            Node::Eq { .. } |
            Node::Ne { .. } |
            Node::Lt { .. } |
            Node::Le { .. } =>   ty_int(None),
            Node::Assign { lhs, .. }    =>  lhs.get_type(),
            Node::Addr (expr)   =>  {
                Type::Ptr{ name: None, base: Box::new(expr.get_type()), size: 8 }
            },
            Node::Deref (expr)  =>  {
                if let Type::Ptr{ name:_, base, size:_ } = expr.get_type() {
                    *base
                } else {
                    panic!("invalid pointer dereference")
                }
            },
            Node::Var { name:_, ty }    =>  ty.clone(),
            Node::FuncCall { .. }       |
            Node::Num (..)              =>  ty_int(None),
            _   =>  panic!("not an expression: {:?}", &self),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Obj {
    pub offset: u32,
    pub ty:     Type,
}

#[derive(Debug, PartialEq)]
pub struct Scope {
    parent:     Option<Rc<RefCell<Scope>>>,
    pub objs:   Vec<Obj>,
    pub stack_size: u32,
}

impl Scope {
    fn align_to(&self, n: u32, align: u32) -> u32 {
        (n + align - 1) / align * align
    }

    pub fn add_var(&mut self, ty: &Type) {
        let mut offset = ty.get_size();
        for obj in &mut self.objs {
            obj.offset += ty.get_size();
            offset += obj.ty.get_size();
        }
        let obj = Obj { offset: 8, ty: ty.clone() };
        self.objs.push(obj);
        self.stack_size = self.align_to(offset, 16);
    }

    pub fn find_var(&self, name: &str) -> Option<&Obj> {
        for obj in &self.objs {
            if obj.ty.get_name().unwrap() == name {
                return Some(&obj)
            }
        }
        None
    }

    pub fn add_parent(&mut self, parent: &Rc<RefCell<Scope>>) {
        self.parent = Some(Rc::clone(parent));
    }
}

#[derive(Debug)]
pub struct Parser {
    pub scope:      Rc<RefCell<Scope>>,
    tokenizer:      Tokenizer,
}

impl Parser {
    pub fn new(input: &str) -> Self {
        let mut tokenizer = Tokenizer::new(input);
        tokenizer.tokenize();

        Parser {
            scope: Rc::new(RefCell::new( Scope {
                parent: None, objs: Vec::new(), stack_size: 0,
            })),
            tokenizer:  tokenizer,
        }
    }

    fn new_lvar(&mut self, ty: &Type) {
        (*self.scope).borrow_mut().add_var(ty);
    }

    fn new_param_lvars(&mut self, params: &Vec<Type>) {
        for param in params {
            self.new_lvar(param);
        }
    }

    fn get_ident(&self) -> String {
        let token = self.tokenizer.cur_token();
        if token.kind != TokenKind::Ident {
            self.tokenizer.error_tok(token, "expected an identifier");
        }
        token.literal.to_string()
    }

    // declspec = "int"
    fn declspec(&mut self) -> Type {
        self.tokenizer.skip("int");
        ty_int(None)
    }

    // type-suffix = ("(" func-params? ")")?
    // func-params = param ("," param)*
    // param       = declspec declarator
    fn type_suffix(&mut self, ty: Type) -> Type {
        let ty = ty.clone();
        let token = self.tokenizer.cur_token().clone();

        if self.tokenizer.peek_token("(") {
            self.tokenizer.next_token();
            self.tokenizer.next_token();

            let mut params = Vec::new();

            while !self.tokenizer.consume(")") {
                if params.len() != 0 {
                    self.tokenizer.skip(",");
                }

                let basety = self.declspec();
                let ty = self.declarator(basety);
                params.push(ty);
            }

            self.new_param_lvars(&params);

            return Type::Function {
                name:   Some(token.literal.to_string()),
                params: Some(params),
                ret_ty: Box::new(ty),
            };
        }
        self.tokenizer.next_token();

        ty
    }

    // declarator = "*" ident type-suffix
    fn declarator(&mut self, ty: Type) -> Type {
        let mut ty = ty.clone();
        while self.tokenizer.consume("*") {
            ty = Type::Ptr {
                name: None,
                base: Box::new(ty),
                size: 8,
            };
        }
         
        let token = self.tokenizer.cur_token().clone();
        if token.kind != TokenKind::Ident {
            self.tokenizer.error_tok(&token, "expected a variable name");
        }
        ty.set_name(token.literal.to_string());
        ty = self.type_suffix(ty);

        ty
    }

    // declaration = declspec (declarator ("=" expr)? ("," declarator ("=" expr)?)*)? ";"
    fn declaration(&mut self) -> Option<Node> {
        let basety = self.declspec();
        let mut decls = Vec::new();

        let mut i = 0;

        while !self.tokenizer.consume(";") {
            if i > 0 {
                self.tokenizer.skip(",");
            }
            i += 1;

            let ty = self.declarator(basety.clone());
            let name = ty.get_name().unwrap();
            self.new_lvar(&ty);

            if !self.tokenizer.consume("=") {
                continue;
            }

            let lhs = Node::Var{ name, ty };
            let rhs = self.assign().unwrap();
            let node = Node::Assign {
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            };
            decls.push(Box::new(Node::ExprStmt(Box::new(node))));
        }

        Some(Node::Block(decls))
    }

    // stmt = "return" expr ";"
    //      | "if" "(" expr ")" stmt ("else" stmt)?
    //      | "for" "(" expr-stmt expr? ";" expr?  ")" stmt
    //      | "while" "(" expr ")" stmt
    //      | "{" compound-stmt
    //      | expr-stmt
    fn stmt(&mut self) -> Option<Node> {
        if self.tokenizer.consume("return") {
            let node = Node::Return(Box::new(self.expr().unwrap()));
            self.tokenizer.skip(";");
            return Some(node);
        }

        if self.tokenizer.consume("if") {
            self.tokenizer.skip("(");
            let cond = Box::new(self.expr().unwrap());
            self.tokenizer.skip(")");
            let then = Box::new(self.stmt().unwrap());
            
            let els = if self.tokenizer.consume("else") {
                Some(Box::new(self.stmt().unwrap()))
            } else {
                None
            };

            return Some(Node::If { cond, then, els });
        }

        if self.tokenizer.consume("for") {
            self.tokenizer.skip("(");

            let init = if !self.tokenizer.consume(";") {
                Some(Box::new(self.expr_stmt().unwrap()))
            } else {
                None
            };

            let cond = if !self.tokenizer.cur_token().equal(";") {
                Some(Box::new(self.expr().unwrap()))
            } else {
                None
            };

            self.tokenizer.skip(";");

            let inc = if !self.tokenizer.cur_token().equal(")") {
                Some(Box::new(self.expr().unwrap()))
            } else {
                None
            };

            self.tokenizer.skip(")");

            let body = Box::new(self.stmt().unwrap());

            return Some(Node::For { init, cond, inc, body })
        }

        if self.tokenizer.consume("while") {
            self.tokenizer.skip("(");
            let cond = if !self.tokenizer.cur_token().equal(")") {
                Some(Box::new(self.expr().unwrap()))
            } else {
                None
            };

            self.tokenizer.skip(")");

            let body = Box::new(self.stmt().unwrap());

            return Some(Node::For { init: None, cond: cond, inc: None, body: body });
        }

        if self.tokenizer.consume("{") {
            return self.compound_stmt();
        }

        self.expr_stmt()
    }

    // compound-stmt = (declaration | stmt)* "}"
    fn compound_stmt(&mut self) -> Option<Node> {
        let mut stmts = Vec::new();

        while !self.tokenizer.consume("}") {
            if self.tokenizer.cur_token().equal("int") {
                stmts.push(Box::new(self.declaration().unwrap()))
            } else {
                stmts.push(Box::new(self.stmt().unwrap()));
            }
        }

        return Some(Node::Block(stmts))
    }

    // expr = assign
    fn expr(&mut self) -> Option<Node> {
        self.assign()
    }

    // assign = equality ("=" assign)?
    fn assign(&mut self) -> Option<Node> {
        let mut node = self.equality().unwrap();

        if self.tokenizer.consume("=") {
            node = Node::Assign {
                lhs: Box::new(node),
                rhs: Box::new(self.assign().unwrap()),
            };
        }

        Some(node)
    }

    // expr-stmt = expr? ";"
    fn expr_stmt(&mut self) -> Option<Node> {
        if self.tokenizer.consume(";") {
            return Some(Node::Block(Vec::new()));
        }

        let node = Node::ExprStmt(Box::new(self.expr().unwrap()));
        self.tokenizer.skip(";");

        Some(node)
    }

    // equality = relational ("==" relational | "!=" relational)*
    fn equality(&mut self) -> Option<Node> {
        let mut node = self.relational().unwrap();

        loop {
            if self.tokenizer.consume("==") {
                node = Node::Eq {
                    lhs: Box::new(node),
                    rhs: Box::new(self.relational().unwrap()),
                };
                continue;
            }
            
            if self.tokenizer.consume("!=") {
                node = Node::Ne {
                    lhs: Box::new(node),
                    rhs: Box::new(self.relational().unwrap()),
                };
                continue;
            }
            
            return Some(node);
        }
    }

    // relational = add ("<" add | "<=" add | ">" add | ">=" add)*
    fn relational(&mut self) -> Option<Node> {
        let mut node = self.add().unwrap();

        loop {
            if self.tokenizer.consume("<") {
                node = Node::Lt {
                    lhs: Box::new(node),
                    rhs: Box::new(self.add().unwrap()),
                };
                continue;
            }
            
            if self.tokenizer.consume("<=") {
                node = Node::Le {
                    lhs: Box::new(node),
                    rhs: Box::new(self.add().unwrap()),
                };
                continue;
            }
            
            if self.tokenizer.consume(">") {
                node = Node::Lt {
                    lhs: Box::new(self.add().unwrap()),
                    rhs: Box::new(node),
                };
                continue;
            }
            
            if self.tokenizer.consume(">=") {
                node = Node::Le {
                    lhs: Box::new(self.add().unwrap()),
                    rhs: Box::new(node),
                };
                continue;
            }

            return Some(node);
        }
    }

    // In C, `+` operator is overloaded to perform the pointer arithmetic.
    // If p is a pointer, p+n adds not n but sizeof(*p)*n to the value of p,
    // so that p+n points to the location n elements (not bytes) ahead of p.
    // In other words, we need to scale an integer value before adding to a
    // pointer value. This function takes care of the scaling.
    // add = mul ("+" mul | "-" mul)*
    fn add(&mut self) -> Option<Node> {
        let mut node = self.mul().unwrap();

        loop {
            if self.tokenizer.consume("+") {
                let mut rhs = self.mul().unwrap();

                // num + num
                if node.get_type().is_integer() && rhs.get_type().is_integer() {
                    node = Node::Add {
                        lhs: Box::new(node),
                        rhs: Box::new(rhs),
                    };

                    continue;
                }

                if node.get_type().is_ptr() && rhs.get_type().is_ptr() {
                    self.tokenizer.error_tok(
                        self.tokenizer.cur_token(),
                        "invalid operands"
                    );
                }

                // Canonicalize `num + ptr` to `ptr + num`.
                if !node.get_type().is_ptr() && rhs.get_type().is_ptr() {
                    let tmp = node;
                    node = rhs;
                    rhs = tmp;
                }

                rhs = Node::Mul {
                    lhs: Box::new(rhs),
                    rhs: Box::new(Node::Num(8)),
                };
                node = Node::Add {
                    lhs: Box::new(node),
                    rhs: Box::new(rhs),
                };

                continue;
            }
            
            if self.tokenizer.consume("-") {
                let mut rhs = self.mul().unwrap();

                // num - num
                if node.get_type().is_integer() && rhs.get_type().is_integer() {
                    node = Node::Sub {
                        lhs: Box::new(node),
                        rhs: Box::new(rhs),
                    };

                    continue;
                }

                // ptr - num
                if node.get_type().is_ptr() && rhs.get_type().is_integer() {
                    rhs = Node::Mul {
                        lhs: Box::new(rhs),
                        rhs: Box::new(Node::Num(8)),
                    };
                    node = Node::Sub {
                        lhs: Box::new(node),
                        rhs: Box::new(rhs),
                    };

                    continue;
                }

                // ptr - ptr, which returns how many elements are between the two.
                if node.get_type().is_ptr() && rhs.get_type().is_ptr() {
                    node = Node::Sub {
                        lhs: Box::new(node),
                        rhs: Box::new(rhs),
                    };
                    node = Node::Div {
                        lhs: Box::new(node),
                        rhs: Box::new(Node::Num(8)),
                    };

                    continue;
                }

                self.tokenizer.error_tok(
                    self.tokenizer.cur_token(),
                    "invalid operands"
                );
            }

            return Some(node);
        }
    }

    // funcall = ident "(" (assign ("," assign)*)? ")"
    fn funcall(&mut self) -> Option<Node> {
        let mut args = Vec::new();
        let name = self.get_ident();

        self.tokenizer.next_token();
        self.tokenizer.next_token();

        let mut i = 0;
        while !self.tokenizer.consume(")") {
            if i > 0 {
                self.tokenizer.skip(",");
            }
            args.push(Box::new(self.assign().unwrap()));
            i += 1;
        }

        Some(Node::FuncCall { name, args })
    }

    // primary = "(" expr ")" | ident args? | num
    // args = "(" ")"
    fn primary(&mut self) -> Option<Node> {
        if self.tokenizer.consume("(") {
            let node = self.expr().unwrap();
            self.tokenizer.skip(")");
            return Some(node);
        }

        let token = self.tokenizer.cur_token().clone();

        if token.kind == TokenKind::Ident {
            // Function call
            if self.tokenizer.peek_token("(") {
                return self.funcall();
            }

            let name = token.literal.clone();
            self.tokenizer.next_token().unwrap();

            // Variable
            let ty = if let Some(obj) = self.scope.borrow().find_var(&name) {
                obj.ty.clone()
            } else {
                self.tokenizer.error_tok(&token, "undefined variable");
                panic!()
            };

            return Some(Node::Var{ name, ty: ty });
        }

        if token.kind == TokenKind::Num {
            let node = Node::Num(token.val.unwrap());
            self.tokenizer.next_token();
            return Some(node);
        }

        self.tokenizer.error_tok(
            self.tokenizer.cur_token(),
            &format!("expected an expression: {:?}", self.tokenizer.cur_token()),
        );
        
        None
    }

    // mul = unary ("*" unary | "/" unary)*
    fn mul(&mut self) -> Option<Node> {
        let mut node = self.unary().unwrap();
        
        loop {
            if self.tokenizer.consume("*") {
                node = Node::Mul {
                    lhs: Box::new(node),
                    rhs: Box::new(self.unary().unwrap()),
                };
                continue;
            }
            
            if self.tokenizer.consume("/") {
                node = Node::Div {
                    lhs: Box::new(node),
                    rhs: Box::new(self.unary().unwrap()),
                };
                continue;
            }

            return Some(node);
        }
    }

    // unary = ("+" | "-" | "*" | "&") unary
    //       | primary
    fn unary(&mut self) -> Option<Node> {
        if self.tokenizer.consume("+") {
            return self.unary();
        }

        if self.tokenizer.consume("-") {
            return Some(Node::Neg(Box::new(self.unary().unwrap())));
        }

        if self.tokenizer.consume("&") {
            return Some(Node::Addr(Box::new(self.unary().unwrap())));
        }
        
        if self.tokenizer.consume("*") {
            return Some(Node::Deref(Box::new(self.unary().unwrap())));
        }

        self.primary()
    }

    // function-definition = declspec declarator "{" compound-stmt
    fn function(&mut self) -> Option<Node> {
        let locals = Rc::new(RefCell::new( Scope {
            parent:     None,
            objs:       Vec::new(),
            stack_size: 0,
        }));
        self.scope = Rc::clone(&locals);

        let basety = self.declspec();
        let ty = self.declarator(basety.clone());
        let name = ty.get_name().unwrap();

        let params = Rc::clone(&self.scope);

        self.tokenizer.skip("{");
        let mut body = Vec::new();
        body.push(Box::new(self.compound_stmt().unwrap()));

        Some(Node::Function {
            name:   name,
            params: params,
            body:   body,
            locals: Rc::clone(&self.scope),
            ret_ty: Some(ty),
        })
    }
 
    // program = function-definition*
    pub fn parse(&mut self) -> Option<Node> {
        let mut prog = Vec::new();

        while self.tokenizer.cur_token().kind != TokenKind::Eof {
            prog.push(Box::new(self.function().unwrap()));
        }

        Some(Node::Program(prog))
    }
}