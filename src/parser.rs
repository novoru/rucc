use std::rc::Rc;
use std::cell::RefCell;
use std::collections::HashMap;
use crate::tokenizer::{ Token, TokenKind, Tokenizer };
use crate::ty::*;

static KW: &'static [&str] = &[
    "void", "char", "short", "int", "long", "struct", "union", "typedef"
];

const VOID:     u16 = 1 << 0;
const CHAR:     u16 = 1 << 2;
const SHORT:    u16 = 1 << 4;
const INT:      u16 = 1 << 6;
const LONG:     u16 = 1 << 8;
const OTHER:    u16 = 1 << 10;

// Ast node type
#[derive(Debug, Clone, PartialEq)]
pub enum Node {
    Add         { lhs: Box<Node>, rhs: Box<Node>, token: Token },   // +
    Sub         { lhs: Box<Node>, rhs: Box<Node>, token: Token },   // -
    Mul         { lhs: Box<Node>, rhs: Box<Node>, token: Token },   // *
    Div         { lhs: Box<Node>, rhs: Box<Node>, token: Token },   // /
    Neg         ( Box<Node>, Token ),                               // unary -
    Eq          { lhs: Box<Node>, rhs: Box<Node>, token: Token },   // ==
    Ne          { lhs: Box<Node>, rhs: Box<Node>, token: Token },   // !=
    Lt          { lhs: Box<Node>, rhs: Box<Node>, token: Token },   // <
    Le          { lhs: Box<Node>, rhs: Box<Node>, token: Token },   // <=
    Assign      { lhs: Box<Node>, rhs: Box<Node>, token: Token },   // =
    Comma       { lhs: Box<Node>, rhs: Box<Node>, token: Token },   // ,
    Member      {
        base:   Box<Node>,
        member: Member,
        token:  Token,
    },
    Addr        ( Box<Node>, Token ),                               // unary &
    Deref       ( Box<Node>, Token ),                               // unary *
    Return      ( Box<Node>, Token ),                               // "return"
    If          {                                                   // "if"
        cond:   Box<Node>,
        then:   Box<Node>,
        els:    Option<Box<Node>>,
        token:  Token,
    },
    For         {                                                   // "for" of "while"
        init:   Option<Box<Node>>,
        cond:   Option<Box<Node>>,
        inc:    Option<Box<Node>>,
        body:   Box<Node>,
        token:  Token,
    },
    Block       ( Vec<Box<Node>>, Token ),                          // { ... }
    ExprStmt    ( Box<Node>, Token ),                               // Expression statement
    StmtExpr    ( Box<Node>, Token ),                               // Statement Expression
    Var         {                                                   // Variable
        name: String,
        ty: Type,
        token: Token,
        obj: Rc<RefCell<Obj>>
    },
    FuncCall    {                                                   // Function call
        name: String,
        args: Vec<Box<Node>>,
        token: Token
    },
    Function    {                                                   // Function definition
        name:   String,
        params: Env,
        body:   Vec<Box<Node>>,
        locals: Rc<RefCell<Env>>,
        ret_ty: Option<Type>,
        token:  Token,
    },
    Program     {                                                   // Program
        data: Rc<RefCell<Env>>,
        text: Vec<Box<Node>>,
        token:  Token,
    },
    Num         ( u64, Token ),                                     // Integer
    Cast        {
        expr:   Box<Node>,
        ty:     Type,
        token:  Token,
    }
}

impl Node {
    pub fn get_type(&self) -> Type {
        match self {
            Node::Add { lhs, .. }       =>  lhs.get_type(),
            Node::Sub { lhs, rhs, .. }  =>  {
                // ptr - ptr, which returns how many elements are between the two.
                if lhs.get_type().is_ptr() && rhs.get_type().is_ptr() {
                    new_int(None)
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
            Node::Le { .. }         =>   new_long(None),
            Node::Assign { lhs, .. }    =>  {
                let ty = lhs.get_type();
                if ty.kind == TypeKind::Array {
                    self.get_token().error("not an lvalue");
                }

                ty
            }
            Node::Comma { rhs, .. }     =>  rhs.get_type(),
            Node::Member { member, ..}    =>  member.ty.clone(),
            Node::Addr (expr, ..)       =>  {
                let ty = expr.get_type();
                match ty.kind {
                    TypeKind::Array =>  {
                        new_ptr(None, Some(Box::new(*ty.base.unwrap().clone())))
                    },
                    _   =>  new_ptr(None, Some(Box::new(ty.clone()))),
                }
                
            },
            Node::Deref (expr, ..)  =>  {
                let ty = expr.get_type();
                match ty.kind {
                    TypeKind::Ptr       |
                    TypeKind::Array     =>  *ty.base.unwrap(),
                    TypeKind::Void      =>  self.get_token().error("deferencing a void pointer"),
                    _   =>  self.get_token().error("invalid pointer dereference"),
                }
            },
            Node::ExprStmt (expr, ..)   => expr.get_type(),
            Node::StmtExpr (body, ..)   => {
                if let Node::Block (stmts, ..)  = &**body {
                    if let Some(expr)   = stmts.last() {
                        return expr.get_type();
                    }
                }
                self.get_token().error("statement expression returning void is not supported");
            },
            Node::Var { ty, .. }        =>  ty.clone(),
            Node::FuncCall { .. }       |
            Node::Num (..)              =>  new_long(None),
            Node::Cast { ty, .. }       =>  ty.clone(),
            _   =>  {
                self.get_token().error("not an expression");
            },
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
            Node::Comma     { token, .. }   |
            Node::Member    { token, .. }   |
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
            Node::Num       ( .., token )   |
            Node::Cast      { token, .. }   =>  token,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Obj {
    pub offset:     u64,
    pub ty:         Type,
    pub is_local:   bool,
    pub init_data:  Option<Vec<char>> // Global variable
}

#[derive(Debug, Clone, PartialEq)]
pub struct Env {
    pub parent:     Option<Rc<RefCell<Env>>>,
    pub objs:       Vec<Rc<RefCell<Obj>>>,   // variables
    pub stack_size: u64,
}

fn align_to(n: u64, align: u64) -> u64 {
    (n + align - 1) / align * align
}

impl Env {

    pub fn add_var(&mut self, ty: &Type, init_data: Option<Vec<char>>, token: &Token, is_local: bool, scope: &Scope) -> Rc<RefCell<Obj>> {
        if scope.find_svar(&ty.name.as_ref().unwrap().literal) != None {
            token.error(&format!("redefinition of '{}'", &ty.name.as_ref().unwrap().literal));
        }

        let mut offset = ty.size;
        for obj in &mut self.objs {
            obj.borrow_mut().offset += ty.size;
            offset += obj.borrow().ty.size;
        }
        
        let obj = Rc::new(RefCell::new( Obj {
            offset: ty.size,
            ty:     ty.clone(),
            init_data, is_local
        }));
        self.objs.push(Rc::clone(&obj));
        self.stack_size = align_to(offset, 16);

        obj
    }

    // find variable from local and global
    pub fn find_var(&self, name: &str) -> Option<Rc<RefCell<Obj>>> {
        for obj in self.objs.iter().rev() {
            if obj.borrow().ty.name.as_ref().unwrap().literal == name {
                return Some(Rc::clone(obj))
            }
        }

        if let Some(scope) = &self.parent {
            return scope.borrow().find_var(name);
        }

        None
    }
    
    // find variable from local
    pub fn find_lvar(&self, name: &str) -> Option<Rc<RefCell<Obj>>> {
        for obj in &self.objs {
            if obj.borrow().ty.name.as_ref().unwrap().literal == name {
                return Some(Rc::clone(obj))
            }
        }

        None
    }

    pub fn add_parent(&mut self, parent: &Rc<RefCell<Env>>) {
        self.parent = Some(Rc::clone(parent));
    }
}

#[derive(Debug)]
pub struct Scope {
    parent:     Option<Rc<RefCell<Scope>>>,
    objs:       Vec<Rc<RefCell<Obj>>>,
    tags:       HashMap<String, Type>,      // struct tags or union tags
    typedefs:   HashMap<String, Type>,      // typedef
}

impl Scope {
    pub fn find_lvar(&self, name: &str) -> Option<Rc<RefCell<Obj>>> {
        for obj in &self.objs {
            if obj.borrow().ty.name.as_ref().unwrap().literal == name {
                return Some(Rc::clone(obj));
            }
        }

        if let Some(parent) = &self.parent {
            return parent.borrow().find_lvar(name);
        }

        None
    }

    // find variable from scope
    pub fn find_svar(&self, name: &str) -> Option<Rc<RefCell<Obj>>> {
        for obj in &self.objs {
            if obj.borrow().ty.name.as_ref().unwrap().literal == name {
                return Some(Rc::clone(obj));
            }
        }

        None
    }

    fn find_tag(&self, name: String) -> Option<Type> {
        if let Some(tag) = self.tags.get(&name) {
            Some(tag.clone())
        } else {
            None
        }
    }

    fn find_typedef(&self, name: String) -> Option<Type> {
        if let Some(typedef) = self.typedefs.get(&name) {
            return Some(typedef.clone());
        }

        if let Some(parent) = &self.parent {
            return parent.borrow().find_typedef(name);
        }

        None
    }
}

#[derive(Debug)]
struct VarAttr {
    token:      Option<Token>,
    is_typedef: bool,
}

#[derive(Debug)]
pub struct Parser {
    tokenizer:      Tokenizer,
    id:             u64,
    global:         Rc<RefCell<Env>>,
    pub local:      Rc<RefCell<Env>>,
    scope:          Rc<RefCell<Scope>>,
}

impl Parser {
    pub fn new(input: &str) -> Self {
        let mut tokenizer = Tokenizer::new(input);
        tokenizer.tokenize();

        Parser {
            tokenizer:  tokenizer,
            id:     0,
            global: Rc::new(RefCell::new( Env {
                parent: None,
                objs:   Vec::new(),
                stack_size: 0,
            })),
            local:  Rc::new(RefCell::new( Env {
                parent: None,
                objs:   Vec::new(),
                stack_size: 0,
            })),
            scope:  Rc::new(RefCell::new( Scope {
                parent:     None,
                objs:       Vec::new(),
                tags:       HashMap::new(),
                typedefs:   HashMap::new(),
            })),
        }
    }

    fn enter_scope(&mut self) {
        self.scope = Rc::new(RefCell::new( Scope {
            parent:     Some(Rc::clone(&self.scope)),
            objs:       Vec::new(),
            tags:       HashMap::new(),
            typedefs:   HashMap::new(),
        }));
    }

    fn leave_scope(&mut self) {
        if let Some(parent) = &self.scope.clone().borrow().parent {
            self.scope = Rc::clone(&parent);
        };
    }

    fn push_scope(&mut self, obj: Rc<RefCell<Obj>>) {
        self.scope.borrow_mut().objs.push(Rc::clone(&obj));
    }

    fn push_tag_scope(&mut self, name: &str, tag: Type) {
        self.scope.borrow_mut().tags.insert(name.to_string(), tag);
    }

    fn push_typedef_scope(&mut self, name: &str, typedef: Type) {
        self.scope.borrow_mut().typedefs.insert(name.to_string(), typedef);
    }

    fn new_lvar(&mut self, ty: &Type, token: &Token) -> Rc<RefCell<Obj>> {
        let obj = (*self.local).borrow_mut().add_var(ty, None, token, true, &self.scope.borrow());
        self.push_scope(Rc::clone(&obj));

        obj
    }

    fn new_gvar(&mut self, ty: &Type, token: &Token) -> Rc<RefCell<Obj>> {
        let obj = self.global.borrow_mut().add_var(&ty, None, &token, false, &self.scope.borrow());
        self.push_scope(Rc::clone(&obj));

        obj
    }

    fn new_param_lvars(&mut self, params: &Vec<Type>) {
        for param in params {
            if self.scope.borrow().find_lvar(&param.name.as_ref().unwrap().literal) != None {
                param.name.as_ref().unwrap().error(&format!("redefinition of '{}'", &param.name.as_ref().unwrap().literal));
            }
            self.new_lvar(param, &param.name.as_ref().unwrap());
        }
    }

    fn new_unique_name(&mut self) -> String {
        let s = format!(".L..{}", self.id);
        self.id += 1;

        s
    }

    fn new_anon_gvar(&mut self, token: Token, ty: Type) -> Rc<RefCell<Obj>> {
        let mut ty = ty.clone();
        ty.name = Some(Rc::new(Token::new(
            TokenKind::Ident,
            0,
            &self.new_unique_name(),
            "".to_string(),
            0,
            0,
        )));
        let obj = self.global.borrow_mut().add_var(
            &ty,
            Some(token.literal.chars().collect()),
            &token,
            false,
            &self.scope.borrow()
        );
        self.push_scope(Rc::clone(&obj));

        obj
    }

    fn new_string_literal(&mut self, token: Token, ty: Type) -> Rc<RefCell<Obj>> {
        self.new_anon_gvar(token, ty)
    }

    fn get_ident(&self) -> String {
        let token = self.tokenizer.cur_token();
        if token.kind != TokenKind::Ident {
            token.error("expected an identifier");
        }
        token.literal.to_string()
    }

    // declspec = ("void" | "char" | "shoht" | "int" | "long" | 
    //          | struct-decl | union-decl | typedef-name)+
    fn declspec(&mut self, attr: &mut Option<VarAttr>) -> Type {
        let mut ty = new_int(None);
        let mut counter = 0;

        while self.is_typename(&self.tokenizer.cur_token()) {
            if self.tokenizer.consume("typedef") {
                if let Some(ref mut attr) = attr {
                    attr.token = Some(self.tokenizer.cur_token().clone());
                    attr.is_typedef = true;
                } else {
                    self.tokenizer.cur_token()
                        .error("storage class specifier is not allowed in this context");
                }
                continue;
            }

            let ty2 = self.scope.borrow()
                .find_typedef(self.tokenizer.cur_token().literal.clone());

            let token = self.tokenizer.cur_token().clone();
            if token.equal("struct") || token.equal("union") || ty2.is_some() {
                if counter > 0 {
                    break;
                }

                if self.tokenizer.consume("struct") {
                    ty = self.struct_decl();
                    counter += OTHER;
                    continue;
                } else if self.tokenizer.consume("union") {
                    ty = self.union_decl();
                    counter += OTHER;
                    continue;
                } else if ty2.is_some() {
                    self.tokenizer.next_token();
                    ty = ty2.unwrap();
                    counter += OTHER;
                    continue;
                }
            }
            

            if self.tokenizer.consume("void") {
                counter += VOID;
            } else if self.tokenizer.consume("char") {
                counter += CHAR;
            } else if self.tokenizer.consume("short") {
                counter += SHORT;
            } else if self.tokenizer.consume("int") {
                counter += INT;
            } else if self.tokenizer.consume("long") {
                counter += LONG;
            }

            match counter {
                _ if counter == VOID                =>  ty = new_void(None),
                _ if counter == CHAR                =>  ty = new_char(None),
                _ if counter == SHORT               =>  ty = new_short(None),
                _ if counter == SHORT + INT         =>  ty = new_short(None),
                _ if counter == INT                 =>  ty = new_int(None),
                _ if counter == LONG                =>  ty = new_long(None),
                _ if counter == LONG + INT          =>  ty = new_long(None),
                _ if counter == LONG + LONG         =>  ty = new_long(None),
                _ if counter == LONG + LONG + INT   =>  ty = new_long(None),
                _   =>  self.tokenizer.cur_token().error("invalid type"),
            }
        }

        ty
    }

    // func-params = (param ("," param)*)? ")"
    // param       = declspec declarator
    fn func_params(&mut self, ty: Type) -> Type {
        let mut params = Vec::new();
        while !self.tokenizer.consume(")") {
            if params.len() != 0 {
                self.tokenizer.skip(",");
            }

            let basety = self.declspec(&mut None);
            let ty = self.declarator(basety);
            params.push(ty);
        }

        new_function (
            Some(Rc::clone(&ty.name.as_ref().unwrap())),
            params,
            Some(Box::new(ty)),
        )
    }

    // type-suffix = "(" func-pramas
    //             | "[" num "]" type-suffix
    //             | ε
    fn type_suffix(&mut self, mut ty: Type) -> Type {
        if self.tokenizer.consume("(") {
            return self.func_params(ty);
        }

        if self.tokenizer.consume("[") {
            let token = self.tokenizer.cur_token().clone();
            let sz = if let Some(val) = self.tokenizer.next_token().unwrap().val {
                val
            } else {
                token.error("expected a number");
            };
            self.tokenizer.skip("]");
            ty = self.type_suffix(ty.clone());

            return new_array (
                ty.clone().name,
                Some(Box::new(ty.clone())),
                ty.clone().size*sz,
                sz,
                ty.align,
            );
        }

        ty
    }

    // declarator = "*"* ("(" ident ")" | "(" declarator ")" | ident) type-suffix
    fn declarator(&mut self, mut ty: Type) -> Type {
        while self.tokenizer.consume("*") {
            ty = new_ptr (
                None,
                Some(Box::new(ty.clone())),
            );
        }

        if self.tokenizer.consume("(") {
            let start = self.tokenizer.idx;
            self.declarator(ty.clone());
            self.tokenizer.skip(")");
            ty = self.type_suffix(ty.clone());
            let end = self.tokenizer.idx;
            self.tokenizer.idx = start;
            ty = self.declarator(ty.clone());
            self.tokenizer.idx = end;

            return ty;
        }
         
        let token = self.tokenizer.cur_token().clone();
        if token.kind != TokenKind::Ident {
            token.error("expected a variable name");
        }

        ty.name = Some(Rc::new(token));
        self.tokenizer.next_token();
        ty = self.type_suffix(ty);

        ty
    }

    // abstract-declarator = "*"* ("(" abstract-declarator ")")? type-suffix
    fn abstract_declarator(&mut self, mut ty: Type) -> Type {
        while self.tokenizer.consume("*") {
            ty = new_ptr(None, Some(Box::new(ty)));
        }

        if self.tokenizer.consume("(") {
            let start = self.tokenizer.idx;
            self.abstract_declarator(ty.clone());

            self.tokenizer.skip(")");

            let end = self.tokenizer.idx;
            ty = self.type_suffix(ty);

            self.tokenizer.idx = start;
            ty = self.abstract_declarator(ty);

            self.tokenizer.idx = end;
            self.type_suffix(ty.clone());
            
            return ty;
        }

        return self.type_suffix(ty);
    }

    // type-name = declspec abstract-declarator
    fn typename(&mut self) -> Type {
        let ty = self.declspec(&mut None);
        return self.abstract_declarator(ty);
    }

    // declaration = declspec (declarator ("=" expr)? ("," declarator ("=" expr)?)*)? ";"
    fn declaration(&mut self, basety: Type) -> Node {
        let token = self.tokenizer.cur_token().clone();
        let mut decls = Vec::new();

        let mut i = 0;

        while !self.tokenizer.consume(";") {
            if i > 0 {
                self.tokenizer.skip(",");
            }
            i += 1;

            let tok_lhs = self.tokenizer.cur_token().clone();
            let ty = self.declarator(basety.clone());

            if ty.kind == TypeKind::Void {
                ty.name.unwrap().error("variable declared void");
            }

            let name = ty.name.as_ref().unwrap().literal.clone();
            let obj = Rc::clone(&self.new_lvar(&ty, &tok_lhs));

            if !self.tokenizer.consume("=") {
                continue;
            }

            let lhs = Node::Var {
                name,
                ty,
                token:  tok_lhs.clone(),
                obj:    Rc::clone(&obj),
            };

            let rhs = self.assign();
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

        Node::Block(
            decls,
            token,
        )
    }

    fn is_typename(&self, token: &Token) -> bool {
        for kw in KW.iter() {
            if token.equal(kw) {
                return true;
            }
        }

        self.scope.borrow().find_typedef(token.literal.clone()).is_some()
    }

    // stmt = "return" expr ";"
    //      | "if" "(" expr ")" stmt ("else" stmt)?
    //      | "for" "(" expr-stmt expr? ";" expr?  ")" stmt
    //      | "while" "(" expr ")" stmt
    //      | compound-stmt
    //      | expr-stmt
    fn stmt(&mut self) -> Node {
        let token = self.tokenizer.cur_token().clone();
        if self.tokenizer.consume("return") {
            let node = Node::Return(
                Box::new(self.expr()),
                token,
            );
            self.tokenizer.skip(";");
            return node;
        }

        if self.tokenizer.consume("if") {
            self.tokenizer.skip("(");
            let cond = Box::new(self.expr());
            self.tokenizer.skip(")");
            let then = Box::new(self.stmt());
            
            let els = if self.tokenizer.consume("else") {
                Some(Box::new(self.stmt()))
            } else {
                None
            };

            return Node::If {
                cond,
                then,
                els,
                token,
             };
        }

        if self.tokenizer.consume("for") {
            self.tokenizer.skip("(");

            let init = if !self.tokenizer.consume(";") {
                Some(Box::new(self.expr_stmt()))
            } else {
                None
            };

            let cond = if !self.tokenizer.cur_token().equal(";") {
                Some(Box::new(self.expr()))
            } else {
                None
            };

            self.tokenizer.skip(";");

            let inc = if !self.tokenizer.cur_token().equal(")") {
                Some(Box::new(self.expr()))
            } else {
                None
            };

            self.tokenizer.skip(")");

            let body = Box::new(self.stmt());

            return Node::For {
                init,
                cond,
                inc,
                body,
                token,
             }
        }

        if self.tokenizer.consume("while") {
            self.tokenizer.skip("(");
            let cond = if !self.tokenizer.cur_token().equal(")") {
                Some(Box::new(self.expr()))
            } else {
                None
            };

            self.tokenizer.skip(")");

            let body = Box::new(self.stmt());

            return Node::For {
                init: None,
                cond,
                inc: None,
                body,
                token,
             };
        }

        if token.equal("{") {
            return self.compound_stmt();
        }

        self.expr_stmt()
    }

    // compound-stmt = "{" (typedef | declaration | stmt)* "}"
    fn compound_stmt(&mut self) -> Node {
        let token = self.tokenizer.cur_token().clone();
        self.tokenizer.skip("{");
        let mut stmts = Vec::new();
        self.enter_scope();

        while !self.tokenizer.consume("}") {
            if self.is_typename(&self.tokenizer.cur_token()) {
                let token = self.tokenizer.cur_token().clone();
                let mut attr = Some(VarAttr {
                    token:      Some(token),
                    is_typedef: false,
                });
                let basety = self.declspec(&mut attr);

                if attr.unwrap().is_typedef {
                    self.parse_typedef(basety);
                    continue;
                }
                
                stmts.push(Box::new(self.declaration(basety)))
            } else {
                stmts.push(Box::new(self.stmt()));
            }
        }

        self.leave_scope();

        return Node::Block(stmts, token)
    }

    // expr = assign ("," expr)?
    fn expr(&mut self) -> Node {
        let node = self.assign();
        let token = self.tokenizer.cur_token().clone();

        if self.tokenizer.consume(",") {
            return Node::Comma {
                lhs:    Box::new(node),
                rhs:    Box::new(self.expr()),
                token:  token.clone(),
            };
        }

        node
    }

    // assign = equality ("=" assign)?
    fn assign(&mut self) -> Node {
        let token = self.tokenizer.cur_token().clone();
        let mut node = self.equality();

        if self.tokenizer.consume("=") {
            node = Node::Assign {
                lhs: Box::new(node),
                rhs: Box::new(self.assign()),
                token,
            };
        }

        node
    }

    // expr-stmt = expr? ";"
    fn expr_stmt(&mut self) -> Node {
        if self.tokenizer.consume(";") {
            return Node::Block(
                Vec::new(),
                self.tokenizer.cur_token().clone(),
            );
        }

        let tok_expr = self.tokenizer.cur_token().clone();
        let node = Node::ExprStmt(
            Box::new(self.expr()),
            tok_expr,
        );
        self.tokenizer.skip(";");

        node
    }

    // equality = relational ("==" relational | "!=" relational)*
    fn equality(&mut self) -> Node {
        let mut node = self.relational();

        loop {
            let token = self.tokenizer.cur_token().clone();
            if self.tokenizer.consume("==") {
                node = Node::Eq {
                    lhs: Box::new(node),
                    rhs: Box::new(self.relational()),
                    token,
                };
                continue;
            }
            
            if self.tokenizer.consume("!=") {
                node = Node::Ne {
                    lhs: Box::new(node),
                    rhs: Box::new(self.relational()),
                    token,
                };
                continue;
            }
            
            return node;
        }
    }

    // relational = add ("<" add | "<=" add | ">" add | ">=" add)*
    fn relational(&mut self) -> Node {
        let mut node = self.add();

        loop {
            let token = self.tokenizer.cur_token().clone();
            if self.tokenizer.consume("<") {
                node = Node::Lt {
                    lhs: Box::new(node),
                    rhs: Box::new(self.add()),
                    token,
                };
                continue;
            }
            
            if self.tokenizer.consume("<=") {
                node = Node::Le {
                    lhs: Box::new(node),
                    rhs: Box::new(self.add()),
                    token,
                };
                continue;
            }
            
            if self.tokenizer.consume(">") {
                node = Node::Lt {
                    lhs: Box::new(self.add()),
                    rhs: Box::new(node),
                    token,
                };
                continue;
            }
            
            if self.tokenizer.consume(">=") {
                node = Node::Le {
                    lhs: Box::new(self.add()),
                    rhs: Box::new(node),
                    token,
                };
                continue;
            }

            return node;
        }
    }

    // In C, `+` operator is overloaded to perform the pointer arithmetic.
    // If p is a pointer, p+n adds not n but sizeof(*p)*n to the value of p,
    // so that p+n points to the location n elements (not bytes) ahead of p.
    // In other words, we need to scale an integer value before adding to a
    // pointer value. This function takes care of the scaling.
    fn new_add(&mut self, mut lhs: Node, mut rhs: Node, token: Token) -> Node {
        // num + num
        if lhs.get_type().is_num() && rhs.get_type().is_num() {
            return  Node::Add {
                lhs: Box::new(lhs.clone()),
                rhs: Box::new(rhs),
                token,
            };
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
                lhs.get_type().base.unwrap().size,
                rhs.clone().get_token().clone(),
            )),
            token: rhs.get_token().clone(),
        };
        return Node::Add {
            lhs: Box::new(lhs.clone()),
            rhs: Box::new(rhs),
            token,
        };
    }

    fn new_sub(&mut self, mut lhs: Node, mut rhs: Node, token: Token) -> Node {
        // num - num
        if lhs.get_type().is_num() && rhs.get_type().is_num() {
            return Node::Sub {
                lhs: Box::new(lhs.clone()),
                rhs: Box::new(rhs),
                token,
            };
        }

        // ptr - num
        if lhs.get_type().is_ptr() && rhs.get_type().is_num() {
            rhs = Node::Mul {
                lhs: Box::new(rhs.clone()),
                rhs: Box::new(Node::Num(
                    lhs.get_type().base.unwrap().size,
                    rhs.clone().get_token().clone(),
                )),
                token: rhs.get_token().clone(),
            };
            return Node::Sub {
                lhs: Box::new(lhs.clone()),
                rhs: Box::new(rhs),
                token,
            };
        }

        // ptr - ptr, which returns how many elements are between the two.
        if lhs.get_type().is_ptr() && rhs.get_type().is_ptr() {
            lhs = Node::Sub {
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
                token: token.clone(),
            };
            return Node::Div {
                lhs: Box::new(lhs.clone()),
                rhs: Box::new(Node::Num(
                    lhs.get_type().size,
                    self.tokenizer.cur_token().clone(),
                )),
                token,
            };
        }
        token.error("invalid operands");
    }

    // add = mul ("+" mul | "-" mul)*
    fn add(&mut self) -> Node {
        let mut node = self.mul();

        loop {
            let token = self.tokenizer.cur_token().clone();
            if self.tokenizer.consume("+") {
                let rhs = self.mul().clone();
                node = self.new_add(node, rhs, token);
                continue;
            }
            
            if self.tokenizer.consume("-") {
                let rhs = self.mul().clone();
                node = self.new_sub(node, rhs, token);
                continue;
            }

            return node;
        }
    }

    // funcall = ident "(" (assign ("," assign)*)? ")"
    fn funcall(&mut self) -> Node {
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
            args.push(Box::new(self.assign()));
            i += 1;
        }

        Node::FuncCall {
            name,
            args,
            token,
        }
    }

    // primary = "(" "{" compound-stmt "}" ")"
    //         | "(" expr ")"
    //         | "sizeof" "(" type-name ")"
    //         | "sizeof" unary
    //         | ident args?
    //         | str
    //         | num
    fn primary(&mut self) -> Node {
        if self.tokenizer.cur_token().equal("(") &&
        self.tokenizer.peek_token().equal("{") {
            let token = self.tokenizer.cur_token().clone();
            self.tokenizer.next_token();
            let node = Node::StmtExpr(
                Box::new(self.compound_stmt()),
                token,
            );

            self.tokenizer.skip(")");
            return node;
        }

        if self.tokenizer.consume("(") {
            let node = self.expr();
            self.tokenizer.skip(")");
            return node;
        }

        let token = self.tokenizer.cur_token().clone();

        if self.tokenizer.consume("sizeof") {
            if self.tokenizer.cur_token().equal("(") &&
               self.is_typename(&self.tokenizer.peek_token()) {
                self.tokenizer.next_token();
                let token = self.tokenizer.cur_token().clone();
                let ty = self.typename();
                self.tokenizer.skip(")");

                return Node::Num(
                    ty.size,
                    token,
                );
            }
            else {
                let node = self.unary();
                return Node::Num(
                    node.get_type().size,
                    token,
                );
            }
        }

        if token.kind == TokenKind::Ident {
            // Function call
            if self.tokenizer.peek_token().equal("(") {
                return self.funcall();
            }

            let name = token.literal.clone();
            self.tokenizer.next_token().unwrap();

            // Variable
            let obj = if let Some(obj) = self.scope.borrow().find_lvar(&name) {
                obj
            } else {
                token.error("undefined variable");
            };

            return Node::Var{
                name,
                ty:     obj.borrow().ty.clone(),
                token,
                obj:    Rc::clone(&obj),
            };
        }

        if token.kind == TokenKind::Str {
            let var = self.new_string_literal(
                token.clone(), *token.ty.clone().unwrap()
            );
            self.tokenizer.next_token();
            let ty = token.clone().ty.unwrap();
            return Node::Var {
                name:   var.borrow().ty.name.as_ref().unwrap().literal.clone(),
                ty:     *ty,
                token,
                obj:    Rc::clone(&var),
            };
        }

        if token.kind == TokenKind::Num {
            let node = Node::Num(
                token.val.unwrap(),
                token,
            );
            self.tokenizer.next_token();
            return node;
        }

        token.error("expected an expression");
    }

    // mul = cast ("*" cast | "/" cast)*
    fn mul(&mut self) -> Node {
        let mut node = self.cast();
        
        loop {
            let token = self.tokenizer.cur_token().clone();
            if self.tokenizer.consume("*") {
                node = Node::Mul {
                    lhs: Box::new(node),
                    rhs: Box::new(self.cast()),
                    token,
                };
                continue;
            }
            
            if self.tokenizer.consume("/") {
                node = Node::Div {
                    lhs: Box::new(node),
                    rhs: Box::new(self.cast()),
                    token,
                };
                continue;
            }

            return node;
        }
    }

    // cast = "(" type-name ")" cast | unary
    fn cast(&mut self) -> Node {
        let idx = self.tokenizer.idx;
        if self.tokenizer.consume("(") {
            let token = self.tokenizer.cur_token().clone();
            if self.is_typename(&token) {
                let ty = self.typename();
                self.tokenizer.skip(")");
                let node = Node::Cast {
                    expr:   Box::new(self.cast()),
                    token,
                    ty:     ty.clone(),
                };

                return node;
            }
        }

        self.tokenizer.idx = idx;
        return self.unary();
    }

    // unary = ("+" | "-" | "*" | "&") cast
    //       | postfix
    fn unary(&mut self) -> Node {
        let token = self.tokenizer.cur_token().clone();
        if self.tokenizer.consume("+") {
            return self.cast();
        }

        if self.tokenizer.consume("-") {
            return Node::Neg(
                Box::new(self.cast()),
                token,
            );
        }

        if self.tokenizer.consume("&") {
            return Node::Addr(
                Box::new(self.cast()),
                token,
            );
        }
        
        if self.tokenizer.consume("*") {
            return Node::Deref(
                Box::new(self.cast()),
                token,
            );
        }

        self.postfix()
    }

    // struct-members = (declspec declarator ("," declarator)* ";")*
    fn struct_members(&mut self) -> Vec<Box<Member>> {
        let mut members = Vec::new();

        while !self.tokenizer.cur_token().equal("}") {
            let basety = self.declspec(&mut None);
            let mut i = 0;

            while !self.tokenizer.consume(";") {
                if i > 0 {
                    self.tokenizer.skip(",");
                }
                let ty = self.declarator(basety.clone());
                members.push(Box::new(Member {
                    ty:     ty.clone(),
                    name:   ty.name.as_ref().unwrap().literal.clone(),
                    offset: 0,
                }));
                i += 1;
            }
        }
        self.tokenizer.next_token();

        members

    }

    // struct-decl = ident? "{" struct-members
    fn struct_decl(&mut self) -> Type {

        // Read a struct tag.
        let mut tag = None;
        if self.tokenizer.cur_token().kind == TokenKind::Ident {
            tag = Some(self.tokenizer.cur_token().clone());
            self.tokenizer.next_token();
        }

        if tag != None && !self.tokenizer.cur_token().equal("{") {
            let ty = self.scope.borrow().find_tag(
                tag.as_ref().unwrap().literal.clone()
            );
            if ty == None {
                if let Some(token) = tag {
                    token.error("unknown struct type");
                }
            }
            return ty.unwrap();
        }

        self.tokenizer.next_token();

        // Construct a struct object.
        let mut ty = new_struct (
            None,
            self.struct_members(),
        );

        // Assign offsets within the struct to member.
        let mut offset = 0;
        for member in ty.members.iter_mut() {
            offset = align_to(offset, member.ty.align);
            member.offset = offset;
            offset += member.ty.size;

            if ty.align < member.ty.align {
                ty.align = member.ty.align;
            }
        }
        ty.size = align_to(offset, ty.align);

        if tag.is_some() {
            self.push_tag_scope(&tag.unwrap().literal, ty.clone());
        }

        ty
    }

    // union-decl = ident? "{" struct-members
    fn union_decl(&mut self) -> Type {

        // Read a struct tag.
        let mut tag = None;
        if self.tokenizer.cur_token().kind == TokenKind::Ident {
            tag = Some(self.tokenizer.cur_token().clone());
            self.tokenizer.next_token();
        }

        if tag != None && !self.tokenizer.cur_token().equal("{") {
            let ty = self.scope.borrow().find_tag(
                tag.as_ref().unwrap().literal.clone()
            );
            if ty == None {
                if let Some(token) = tag {
                    token.error("unknown union type");
                }
            }
            return ty.unwrap();
        }

        self.tokenizer.next_token();

        // Construct a union object.
        let mut ty = new_union(
            None,
            self.struct_members(),
        );

        // Assign offsets within the struct to member.
        for member in ty.members.iter_mut() {
            if ty.align < member.ty.align {
                ty.align = member.ty.align;
            }
            if ty.size < member.ty.size {
                ty.size = member.ty.size;
            }
        }
        ty.size = align_to(ty.size, ty.align);

        if tag != None {
            self.push_tag_scope(&tag.unwrap().literal, ty.clone());
        }

        ty
    }

    fn get_struct_member(&self, ty: &Type) -> Member {
        let token = self.tokenizer.cur_token();

        match ty.kind {
            TypeKind::Struct    |
            TypeKind::Union     =>  {
                for member in &ty.members {
                    if member.name == token.literal {
                        return *member.clone();
                    }
                }
                token.error("no such member");
            },
            _   => {
                token.error("no such member");
            },
        }
    }

    fn struct_ref(&mut self, lhs: &Node) -> Node {
        let token = self.tokenizer.cur_token();

        match lhs.get_type().kind {
            TypeKind::Struct    |
            TypeKind::Union     => (),
            _   =>{
                lhs.get_token().error("not a struct nor union");
            },
        }

        let node = Node::Member {
            base:   Box::new(lhs.clone()),
            member: self.get_struct_member(&lhs.get_type()),
            token:  token.clone(),
        };

        node        
    }

    // postfix = primary ("[" expr "]" | "." ident | "->" ident)*
    fn postfix(&mut self) -> Node {
        let mut node = self.primary();

        loop {
            if self.tokenizer.consume("[") {
                let token = self.tokenizer.cur_token().clone();
                let idx = self.expr();
                self.tokenizer.skip("]");
                node = Node::Deref(
                    Box::new(self.new_add(node, idx, token.clone())),
                    token,
                );
                continue;
            }

            if self.tokenizer.consume(".") {
                node = self.struct_ref(&node);
                self.tokenizer.next_token();
                continue;
            }

            if self.tokenizer.consume("->") {
                let token = self.tokenizer.cur_token().clone();
                node = Node::Deref(
                    Box::new(node),
                    token,
                );
                node = self.struct_ref(&node);
                self.tokenizer.next_token();
                continue;
            };

            return node;
        }
    }

    fn parse_typedef(&mut self, basety: Type) {
        let mut first = true;

        while !self.tokenizer.consume(";") {
            if !first {
                self.tokenizer.skip(",");
            }
            first = false;

            let ty = self.declarator(basety.clone());
            self.push_typedef_scope(
                &ty.name.as_ref().unwrap().literal, ty.clone()
            );
        }
    }

    // function-definition = declspec declarator compound-stmt
    fn function(&mut self, basety: Type) -> Option<Node> {
        let locals = Rc::new(RefCell::new( Env {
            parent:     Some(Rc::clone(&self.global)),
            objs:       Vec::new(),
            stack_size: 0,
        }));
        self.local = Rc::clone(&locals);

        let token = self.tokenizer.cur_token().clone();
        let mut ty = self.declarator(basety.clone());
        ty.is_definition = !self.tokenizer.consume(";");
        let name = ty.name.as_ref().unwrap().literal.clone();

        if !ty.is_definition {
            return None;
        }

        self.enter_scope();
        self.new_param_lvars(&ty.params);

        let params = Env {
            parent: None,
            objs:   self.local.borrow().objs.clone(),
            stack_size: 0,
        };

        let mut body = Vec::new();
        body.push(Box::new(self.compound_stmt()));

        self.leave_scope();
        Some(Node::Function {
            name,
            params,
            body,
            locals: Rc::clone(&self.local),
            ret_ty: Some(ty),
            token,
        })
    }

    fn global_variables(&mut self, basety: Type) {
        let token = self.tokenizer.cur_token().clone();
        let mut first = true;

        while !self.tokenizer.consume(";") {
            if !first {
                self.tokenizer.skip(",");
            }
            first = false;

            let ty = self.declarator(basety.clone());
            self.new_gvar(&ty, &token);
        }
    }
 
    // function = "*"* ident "(" func-params ")"
    fn is_function(&mut self) -> bool {
        if self.tokenizer.cur_token().equal(";") {
            return false;
        }

        let idx = self.tokenizer.idx;

        while self.tokenizer.consume("*") {
        };

        if self.tokenizer.cur_token().kind != TokenKind::Ident {
            self.tokenizer.idx = idx;
            return false;
        }

        self.tokenizer.next_token();

        if !self.tokenizer.cur_token().equal("(") {
            self.tokenizer.idx = idx;
            return false;
        }

        self.tokenizer.next_token();

        self.func_params_dummy();

        self.tokenizer.idx = idx;
        true
    }

    // func-params  = (param ("," param)*)?
    // param        = declspec declarator
    fn func_params_dummy(&mut self) {
        let mut params = Vec::new();
        while !self.tokenizer.consume(")") {
            if params.len() != 0 {
                self.tokenizer.skip(",");
            }

            let basety = self.declspec(&mut None);
            let ty = self.declarator(basety);
            let token = self.tokenizer.cur_token().clone();
            params.push((ty, token));
        }
    }

    // program = (typedef | function-definition | global-variable)*
    pub fn parse(&mut self) -> Node {
        let token = self.tokenizer.cur_token().clone();
        let mut prog = Vec::new();
        self.enter_scope();

        while self.tokenizer.cur_token().kind != TokenKind::Eof {
            let mut attr = Some(VarAttr {
                token:      None,
                is_typedef: false,
            });
            let basety = self.declspec(&mut attr);

            if self.is_function() {
                if let Some(func) = self.function(basety.clone()) {
                    prog.push(Box::new(func));
                }
                continue;
            }

            if attr.unwrap().is_typedef {
                self.parse_typedef(basety);
                continue;
            }

            self.global_variables(basety);
        }

        self.leave_scope();

        Node::Program {
            data:   Rc::clone(&self.global),
            text:   prog,
            token,
        }
    }
}