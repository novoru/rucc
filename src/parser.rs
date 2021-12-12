use std::rc::Rc;
use std::cell::RefCell;
use crate::tokenizer::{ Token, TokenKind, Tokenizer };
use crate::ty::*;

// Ast node type
#[derive(Debug, Clone, PartialEq)]
pub enum Node {
    Add         { lhs: Box<Node>, rhs: Box<Node>, token: Token },     // +
    Sub         { lhs: Box<Node>, rhs: Box<Node>, token: Token },     // -
    Mul         { lhs: Box<Node>, rhs: Box<Node>, token: Token },     // *
    Div         { lhs: Box<Node>, rhs: Box<Node>, token: Token },     // /
    Neg         ( Box<Node>, Token ),                   // unary -
    Eq          { lhs: Box<Node>, rhs: Box<Node>, token: Token },     // ==
    Ne          { lhs: Box<Node>, rhs: Box<Node>, token: Token },     // !=
    Lt          { lhs: Box<Node>, rhs: Box<Node>, token: Token },     // <
    Le          { lhs: Box<Node>, rhs: Box<Node>, token: Token },     // <=
    Assign      { lhs: Box<Node>, rhs: Box<Node>, token: Token },     // =
    Addr        ( Box<Node>, Token ),                   // unary &
    Deref       ( Box<Node>, Token ),                   // unary *
    Return      ( Box<Node>, Token ),                   // "return"
    If          {                                       // "if"
        cond:   Box<Node>,
        then:   Box<Node>,
        els:    Option<Box<Node>>,
        token:  Token,
    },
    For         {                                       // "for" of "while"
        init:   Option<Box<Node>>,
        cond:   Option<Box<Node>>,
        inc:    Option<Box<Node>>,
        body:   Box<Node>,
        token:  Token,
    },
    Block       ( Vec<Box<Node>>, Token ),              // { ... }
    ExprStmt    ( Box<Node>, Token ),                   // Expression statement
    StmtExpr    ( Box<Node>, Token ),                   // Statement Expression
    Var         { name: String, ty: Type, token: Token },             // Variable
    FuncCall    { name: String, args: Vec<Box<Node>>, token: Token }, // Function call
    Function    {                                       // Function definition
        name:   String,
        params: Scope,
        body:   Vec<Box<Node>>,
        locals: Rc<RefCell<Scope>>,
        ret_ty: Option<Type>,
        token:  Token,
    },
    Program     {                                       // Program
        data: Rc<RefCell<Scope>>,
        text: Vec<Box<Node>>,
        token:  Token,
    },
    Num         ( u32, Token ),                         // Integer
}

impl Node {
    pub fn get_type(&self) -> Type {
        match self {
            Node::Add { lhs, .. }       =>  lhs.get_type(),
            Node::Sub { lhs, rhs, .. }  =>  {
                // ptr - ptr, which returns how many elements are between the two.
                if lhs.get_type().is_ptr() && rhs.get_type().is_ptr() {
                    ty_int(None)
                } else {
                    lhs.get_type()
                }
            },
            Node::Mul { lhs, .. }   |
            Node::Div { lhs, .. }   =>  lhs.get_type(),
            Node::Neg (expr, ..)    =>  expr.get_type(),
            Node::Eq { .. }         |
            Node::Ne { .. }         |
            Node::Lt { .. }         |
            Node::Le { .. }         =>   ty_int(None),
            Node::Assign { lhs, .. }    =>  {
                let ty = lhs.get_type();
                if let Type::Array { .. } = ty {
                    self.get_token().error("not an lvalue");
                }

                ty
            }
            Node::Addr (expr, ..)   =>  {
                let ty = expr.get_type();
                match ty {
                    Type::Array { base, .. }    =>  {
                        Type::Ptr{ name: None, base: Box::new(*base.clone()), size: 8 }
                    },
                    _   =>  Type::Ptr{ name: None, base: Box::new(ty.clone()), size: 8 },
                }
                
            },
            Node::Deref (expr, ..)  =>  {
                let ty = expr.get_type();
                match ty {
                    Type::Ptr   { base, .. }    |
                    Type::Array { base, .. }    =>  *base,
                    _   =>  panic!("invalid pointer dereference"),
                }
            },
            Node::ExprStmt (expr, ..)   => expr.get_type(),
            Node::StmtExpr (body, ..)   => {
                if let Node::Block (stmts, ..)  = &**body {
                    if let Some(expr)   = stmts.last() {
                        return expr.get_type();
                    }
                }
                panic!("statement expression returning void is not supported");
            },
            Node::Var { ty, .. }        =>  ty.clone(),
            Node::FuncCall { .. }       |
            Node::Num (..)              =>  ty_int(None),
            _   =>  panic!("not an expression: {:?}", &self),
        }
    }

    pub fn get_token(&self) -> &Token {
        match self {
            Node::Add       { token, .. }   |
            Node::Sub       { token, .. }   |
            Node::Mul       { token, .. }   |
            Node::Div       { token, .. }   |
            Node::Neg       ( .., token )   |
            Node::Eq        { token, .. }   |
            Node::Ne        { token, .. }   |
            Node::Lt        { token, .. }   |
            Node::Le        { token, .. }   |
            Node::Assign    { token, .. }   |
            Node::Addr      ( .., token )   |
            Node::Deref     ( .., token )   |
            Node::Return    ( .., token )   |
            Node::If        { token, .. }   |
            Node::For       { token, .. }   |
            Node::Block     ( .., token )   |
            Node::ExprStmt  ( .., token )   |
            Node::StmtExpr  ( .., token )   |
            Node::Var       { token, .. }   |
            Node::FuncCall  { token, .. }   |
            Node::Function  { token, .. }   |
            Node::Program   { token, .. }   |
            Node::Num       ( .., token )   =>  token,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Obj {
    pub offset:     u32,
    pub ty:         Type,
    pub init_data:  Option<Vec<char>> // Global variable
}

#[derive(Debug, Clone, PartialEq)]
pub struct Scope {
    pub parent:     Option<Rc<RefCell<Scope>>>,
    pub objs:       Vec<Obj>,
    pub stack_size: u32,
}

impl Scope {
    fn align_to(&self, n: u32, align: u32) -> u32 {
        (n + align - 1) / align * align
    }

    pub fn add_var(&mut self, ty: &Type, init_data: Option<Vec<char>>) -> Obj {
        let mut offset = ty.get_size();
        for obj in &mut self.objs {
            obj.offset += ty.get_size();
            offset += obj.ty.get_size();
        }
        let size = ty.get_size();
        let obj = Obj { offset: size, ty: ty.clone(), init_data: init_data };
        self.objs.push(obj.clone());
        self.stack_size = self.align_to(offset, 16);

        obj
    }

    pub fn find_var(&self, name: &str) -> Option<Obj> {
        for obj in &self.objs {
            if obj.ty.get_name().unwrap() == name {
                return Some(obj.clone())
            }
        }

        if let Some(scope) = &self.parent {
            return scope.borrow().find_var(name);
        }

        None
    }

    pub fn add_parent(&mut self, parent: &Rc<RefCell<Scope>>) {
        self.parent = Some(Rc::clone(parent));
    }
}

#[derive(Debug)]
pub struct Parser {
    id:             u32,
    global:         Rc<RefCell<Scope>>,
    pub scope:      Rc<RefCell<Scope>>,
    tokenizer:      Tokenizer,
}

impl Parser {
    pub fn new(input: &str) -> Self {
        let mut tokenizer = Tokenizer::new(input);
        tokenizer.tokenize();

        Parser {
            id: 0,
            global: Rc::new(RefCell::new( Scope {
                parent: None, objs: Vec::new(), stack_size: 0,
            })),
            scope: Rc::new(RefCell::new( Scope {
                parent: None, objs: Vec::new(), stack_size: 0,
            })),
            tokenizer:  tokenizer,
        }
    }

    fn new_lvar(&mut self, ty: &Type) {
        (*self.scope).borrow_mut().add_var(ty, None);
    }

    fn new_param_lvars(&mut self, params: &Vec<Type>) {
        for param in params {
            self.new_lvar(param);
        }
    }

    fn new_unique_name(&mut self) -> String {
        let s = format!(".L..{}", self.id);
        self.id += 1;

        s
    }

    fn new_anon_gvar(&mut self, s: String, ty: Type) -> Obj {
        let mut ty = ty.clone();
        ty.set_name(self.new_unique_name());
        self.global.borrow_mut().add_var(&ty, Some(s.chars().collect()))
    }

    fn new_string_literal(&mut self, s: String, ty: Type) -> Obj {
        self.new_anon_gvar(s, ty)
    }

    fn get_ident(&self) -> String {
        let token = self.tokenizer.cur_token();
        if token.kind != TokenKind::Ident {
            token.error("expected an identifier");
        }
        token.literal.to_string()
    }

    // declspec = "char" | "int"
    fn declspec(&mut self) -> Type {
        if self.tokenizer.consume("char") {
            return ty_char(None);
        }

        self.tokenizer.skip("int");
        ty_int(None)
    }

    // func-params = (param ("," param)*)? ")"
    // param       = declspec declarator
    fn func_params(&mut self, ty: Type) -> Type {
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

        Type::Function {
            name:   ty.get_name(),
            params: Some(params),
            ret_ty: Box::new(ty),
        }
    }

    // type-suffix = "(" func-pramas
    //             | "[" num "]" type-suffix
    //             | ε
    fn type_suffix(&mut self, ty: Type) -> Type {
        let mut ty = ty.clone();

        if self.tokenizer.peek_token("(") {
            return self.func_params(ty);
        }

        if self.tokenizer.peek_token("[") {
            self.tokenizer.next_token();
            self.tokenizer.next_token();
            let token = self.tokenizer.cur_token().clone();
            let sz = if let Some(val) = self.tokenizer.next_token().unwrap().val {
                val
            } else {
                token.error("expected a number");
                panic!();
            };
            self.tokenizer.skip("]");
            ty = self.type_suffix(ty.clone());

            return Type::Array {
                name:   ty.get_name(),
                base:   Box::new(ty.clone()),
                size:   ty.get_size()*sz,
                len:    sz,
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
                base: Box::new(ty.clone()),
                size: ty.get_size(),
            };
        }
         
        let token = self.tokenizer.cur_token().clone();
        if token.kind != TokenKind::Ident {
            token.error("expected a variable name");
        }
        ty.set_name(token.literal.to_string());
        ty = self.type_suffix(ty);

        ty
    }

    // declaration = declspec (declarator ("=" expr)? ("," declarator ("=" expr)?)*)? ";"
    fn declaration(&mut self) -> Option<Node> {
        let tok_ty = self.tokenizer.cur_token().clone();
        let basety = self.declspec();
        let mut decls = Vec::new();

        let mut i = 0;

        while !self.tokenizer.consume(";") {
            if i > 0 {
                self.tokenizer.skip(",");
            }
            i += 1;

            let tok_lhs = self.tokenizer.cur_token().clone();
            let ty = self.declarator(basety.clone());
            let name = ty.get_name().unwrap();
            self.new_lvar(&ty);

            if !self.tokenizer.consume("=") {
                continue;
            }

            let lhs = Node::Var {
                name,
                ty,
                token: tok_lhs.clone(),
            };

            let rhs = self.assign().unwrap();
            let node = Node::Assign {
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
                token: tok_lhs.clone(),
            };
            decls.push(Box::new(Node::ExprStmt(
                Box::new(node),
                tok_lhs.clone(),
            )));
        }

        Some(Node::Block(
            decls,
            tok_ty,
        ))
    }

    fn is_typename(&self, token: &Token) -> bool {
       token.equal("char") || token.equal("int")
    }

    // stmt = "return" expr ";"
    //      | "if" "(" expr ")" stmt ("else" stmt)?
    //      | "for" "(" expr-stmt expr? ";" expr?  ")" stmt
    //      | "while" "(" expr ")" stmt
    //      | compound-stmt
    //      | expr-stmt
    fn stmt(&mut self) -> Option<Node> {
        let token = self.tokenizer.cur_token().clone();
        if self.tokenizer.consume("return") {
            let node = Node::Return(
                Box::new(self.expr().unwrap()),
                token,
            );
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

            return Some(Node::If {
                cond,
                then,
                els,
                token,
             });
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

            return Some(Node::For {
                init,
                cond,
                inc,
                body,
                token,
             })
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

            return Some(Node::For {
                init: None,
                cond,
                inc: None,
                body,
                token,
             });
        }

        if token.equal("{") {
            return self.compound_stmt();
        }

        self.expr_stmt()
    }

    // compound-stmt = "{" (declaration | stmt)* "}"
    fn compound_stmt(&mut self) -> Option<Node> {
        let token = self.tokenizer.cur_token().clone();
        self.tokenizer.skip("{");
        let mut stmts = Vec::new();

        while !self.tokenizer.consume("}") {
            if self.is_typename(&self.tokenizer.cur_token()) {
                stmts.push(Box::new(self.declaration().unwrap()))
            } else {
                stmts.push(Box::new(self.stmt().unwrap()));
            }
        }

        return Some(Node::Block(stmts, token))
    }

    // expr = assign
    fn expr(&mut self) -> Option<Node> {
        self.assign()
    }

    // assign = equality ("=" assign)?
    fn assign(&mut self) -> Option<Node> {
        let token = self.tokenizer.cur_token().clone();
        let mut node = self.equality().unwrap();

        if self.tokenizer.consume("=") {
            node = Node::Assign {
                lhs: Box::new(node),
                rhs: Box::new(self.assign().unwrap()),
                token,
            };
        }

        Some(node)
    }

    // expr-stmt = expr? ";"
    fn expr_stmt(&mut self) -> Option<Node> {
        if self.tokenizer.consume(";") {
            return Some(Node::Block(
                Vec::new(),
                self.tokenizer.cur_token().clone(),
            ));
        }

        let tok_expr = self.tokenizer.cur_token().clone();
        let node = Node::ExprStmt(
            Box::new(self.expr().unwrap()),
            tok_expr,
        );
        self.tokenizer.skip(";");

        Some(node)
    }

    // equality = relational ("==" relational | "!=" relational)*
    fn equality(&mut self) -> Option<Node> {
        let mut node = self.relational().unwrap();

        loop {
            let token = self.tokenizer.cur_token().clone();
            if self.tokenizer.consume("==") {
                node = Node::Eq {
                    lhs: Box::new(node),
                    rhs: Box::new(self.relational().unwrap()),
                    token,
                };
                continue;
            }
            
            if self.tokenizer.consume("!=") {
                node = Node::Ne {
                    lhs: Box::new(node),
                    rhs: Box::new(self.relational().unwrap()),
                    token,
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
            let token = self.tokenizer.cur_token().clone();
            if self.tokenizer.consume("<") {
                node = Node::Lt {
                    lhs: Box::new(node),
                    rhs: Box::new(self.add().unwrap()),
                    token,
                };
                continue;
            }
            
            if self.tokenizer.consume("<=") {
                node = Node::Le {
                    lhs: Box::new(node),
                    rhs: Box::new(self.add().unwrap()),
                    token,
                };
                continue;
            }
            
            if self.tokenizer.consume(">") {
                node = Node::Lt {
                    lhs: Box::new(self.add().unwrap()),
                    rhs: Box::new(node),
                    token,
                };
                continue;
            }
            
            if self.tokenizer.consume(">=") {
                node = Node::Le {
                    lhs: Box::new(self.add().unwrap()),
                    rhs: Box::new(node),
                    token,
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
    fn new_add(&mut self, mut lhs: Node, mut rhs: Node, token: Token) -> Option<Node> {
        // num + num
        if lhs.get_type().is_num() && rhs.get_type().is_num() {
            return  Some(Node::Add {
                lhs: Box::new(lhs.clone()),
                rhs: Box::new(rhs),
                token,
            });
        }

        if lhs.get_type().is_ptr() && rhs.get_type().is_ptr() {
            token.error("invalid operands");
        }

        // Canonicalize `num + ptr` to `ptr + num`.
        if !lhs.get_type().is_ptr() && rhs.get_type().is_ptr() {
            let tmp = lhs;
            lhs = rhs;
            rhs = tmp;
        }

        rhs = Node::Mul {
            lhs: Box::new(rhs.clone()),
            rhs: Box::new(Node::Num(
                lhs.get_type().get_base().get_size(),
                rhs.clone().get_token().clone(),
            )),
            token: rhs.get_token().clone(),
        };
        return Some(Node::Add {
            lhs: Box::new(lhs.clone()),
            rhs: Box::new(rhs),
            token,
        });
    }

    fn new_sub(&mut self, mut lhs: Node, mut rhs: Node, token: Token) -> Option<Node> {
        // num - num
        if lhs.get_type().is_num() && rhs.get_type().is_num() {
            return Some(Node::Sub {
                lhs: Box::new(lhs.clone()),
                rhs: Box::new(rhs),
                token,
            });
        }

        // ptr - num
        if lhs.get_type().is_ptr() && rhs.get_type().is_num() {
            rhs = Node::Mul {
                lhs: Box::new(rhs.clone()),
                rhs: Box::new(Node::Num(
                    lhs.get_type().get_size(),
                    rhs.clone().get_token().clone(),
                )),
                token: rhs.get_token().clone(),
            };
            return Some(Node::Sub {
                lhs: Box::new(lhs.clone()),
                rhs: Box::new(rhs),
                token,
            });
        }

        // ptr - ptr, which returns how many elements are between the two.
        if lhs.get_type().is_ptr() && rhs.get_type().is_ptr() {
            lhs = Node::Sub {
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
                token: token.clone(),
            };
            return Some(Node::Div {
                lhs: Box::new(lhs.clone()),
                rhs: Box::new(Node::Num(
                    lhs.get_type().get_size(),
                    self.tokenizer.cur_token().clone(),
                )),
                token,
            });
        }
        token.error("invalid operands");

        None
    }

    // add = mul ("+" mul | "-" mul)*
    fn add(&mut self) -> Option<Node> {
        let mut node = self.mul().unwrap();

        loop {
            let token = self.tokenizer.cur_token().clone();
            if self.tokenizer.consume("+") {
                let rhs = self.mul().unwrap().clone();
                node = self.new_add(node, rhs, token).unwrap();
                continue;
            }
            
            if self.tokenizer.consume("-") {
                let rhs = self.mul().unwrap().clone();
                node = self.new_sub(node, rhs, token).unwrap();
                continue;
            }

            return Some(node);
        }
    }

    // funcall = ident "(" (assign ("," assign)*)? ")"
    fn funcall(&mut self) -> Option<Node> {
        let mut args = Vec::new();
        let token = self.tokenizer.cur_token().clone();
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

        Some(Node::FuncCall {
            name,
            args,
            token,
        })
    }

    // primary = "(" "{" compound-stmt "}" ")"
    //         | "(" expr ")"
    //         | "sizeof" unary
    //         | ident args?
    //         | str
    //         | num
    fn primary(&mut self) -> Option<Node> {
        if self.tokenizer.cur_token().equal("(") && self.tokenizer.peek_token("{") {
            let token = self.tokenizer.cur_token().clone();
            self.tokenizer.next_token();
            let node = Node::StmtExpr(
                Box::new(self.compound_stmt().unwrap()),
                token,
            );

            self.tokenizer.skip(")");
            return Some(node);
        }

        if self.tokenizer.consume("(") {
            let node = self.expr().unwrap();
            self.tokenizer.skip(")");
            return Some(node);
        }

        let token = self.tokenizer.cur_token().clone();

        if self.tokenizer.consume("sizeof") {
            let node = self.unary().unwrap();
            return Some(Node::Num(
                node.get_type().get_size(),
                token,
            ));
        }

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
                token.error("undefined variable");
                panic!()
            };

            return Some(Node::Var{
                name,
                ty,
                token,
            });
        }

        if token.kind == TokenKind::Str {
            let var = self.new_string_literal(token.literal.clone(), token.ty.clone().unwrap());
            self.tokenizer.next_token();
            let ty = token.clone().ty.unwrap();
            return Some(Node::Var {
                name:   var.ty.get_name().unwrap(),
                ty:     ty,
                token,
            })
        }

        if token.kind == TokenKind::Num {
            let node = Node::Num(
                token.val.unwrap(),
                token,
            );
            self.tokenizer.next_token();
            return Some(node);
        }

        token.error("expected an expression");
        
        None
    }

    // mul = unary ("*" unary | "/" unary)*
    fn mul(&mut self) -> Option<Node> {
        let mut node = self.unary().unwrap();
        
        loop {
            let token = self.tokenizer.cur_token().clone();
            if self.tokenizer.consume("*") {
                node = Node::Mul {
                    lhs: Box::new(node),
                    rhs: Box::new(self.unary().unwrap()),
                    token,
                };
                continue;
            }
            
            if self.tokenizer.consume("/") {
                node = Node::Div {
                    lhs: Box::new(node),
                    rhs: Box::new(self.unary().unwrap()),
                    token,
                };
                continue;
            }

            return Some(node);
        }
    }

    // unary = ("+" | "-" | "*" | "&") unary
    //       | postfix
    fn unary(&mut self) -> Option<Node> {
        let token = self.tokenizer.cur_token().clone();
        if self.tokenizer.consume("+") {
            return self.unary();
        }

        if self.tokenizer.consume("-") {
            return Some(Node::Neg(
                Box::new(self.unary().unwrap()),
                token,
            ));
        }

        if self.tokenizer.consume("&") {
            return Some(Node::Addr(
                Box::new(self.unary().unwrap()),
                token,
            ));
        }
        
        if self.tokenizer.consume("*") {
            return Some(Node::Deref(
                Box::new(self.unary().unwrap()),
                token,
            ));
        }

        self.postfix()
    }

    // postfix = primary ("[" expr "]")*
    fn postfix(&mut self) -> Option<Node> {
        let mut node = self.primary().unwrap();

        while self.tokenizer.consume("[") {
            // x[y] is short for *(x+y)
            let token = self.tokenizer.cur_token().clone();
            let idx = self.expr().unwrap();
            self.tokenizer.skip("]");
            node = Node::Deref(
                Box::new(self.new_add(node, idx, token.clone()).unwrap()),
                token,
            );
        }

        Some(node)
    }

    // function-definition = declspec declarator compound-stmt
    fn function(&mut self, basety: Type) -> Option<Node> {
        let locals = Rc::new(RefCell::new( Scope {
            parent:     Some(Rc::clone(&self.global)),
            objs:       Vec::new(),
            stack_size: 0,
        }));
        self.scope = Rc::clone(&locals);

        let token = self.tokenizer.cur_token().clone();
        let ty = self.declarator(basety.clone());
        let name = ty.get_name().unwrap();

        let params = Scope {
            parent: None,
            objs:   self.scope.borrow().objs.clone(),
            stack_size: 0,
        };

        let mut body = Vec::new();
        body.push(Box::new(self.compound_stmt().unwrap()));

        Some(Node::Function {
            name,
            params,
            body,
            locals: Rc::clone(&self.scope),
            ret_ty: Some(ty),
            token,
        })
    }

    fn global_variables(&mut self, basety: Type) {
        let mut first = true;

        while !self.tokenizer.consume(";") {
            if !first {
                self.tokenizer.skip(",");
            }
            first = false;

            let ty = self.declarator(basety.clone());
            self.global.borrow_mut().add_var(&ty, None);
        }
    }
 
    fn is_function(&mut self) -> bool {
        if self.tokenizer.cur_token().equal(";") {
            return false;
        }

        let idx = self.tokenizer.idx;
        if let Type::Function {..} = self.declarator(ty_int(None)) {
            self.tokenizer.idx = idx;
            true
        } else {
            self.tokenizer.idx = idx;
            false
        }
    }

    // program = (function-definition | global-variable)*
    pub fn parse(&mut self) -> Option<Node> {
        let token = self.tokenizer.cur_token().clone();
        let mut prog = Vec::new();

        while self.tokenizer.cur_token().kind != TokenKind::Eof {
            let basety = self.declspec();

            if self.is_function() {
                prog.push(Box::new(self.function(basety).unwrap()));
                continue;
            }
            self.global_variables(basety);
        }

        Some(Node::Program {
            data:   Rc::clone(&self.global),
            text:   prog,
            token,
        })
    }
}