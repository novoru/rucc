use std::rc::Rc;
use std::cell::RefCell;
use std::collections::HashMap;
use crate::tokenizer::{ Token, TokenKind, Tokenizer };
use crate::ty::*;
use crate::obj::*;
use crate::env::{ Env, align_to, };
use crate::scope::Scope;
use crate::node::Node;

static KW: &'static [&str] = &[
    "void", "_Bool", "char", "short", "int", "long",
    "struct", "union", "typedef", "enum", "static",
];

const VOID:     u16 = 1 << 0;
const BOOL:     u16 = 1 << 2;
const CHAR:     u16 = 1 << 4;
const SHORT:    u16 = 1 << 6;
const INT:      u16 = 1 << 8;
const LONG:     u16 = 1 << 10;
const OTHER:    u16 = 1 << 12;

#[derive(Debug)]
struct VarAttr {
    token:      Option<Token>,
    is_typedef: bool,
    is_static:  bool,
}

#[derive(Debug)]
pub struct Parser {
    tokenizer:      Tokenizer,
    id:             u64,
    global:         Rc<RefCell<Env>>,
    pub local:      Rc<RefCell<Env>>,
    scope:          Rc<RefCell<Scope>>,
    current_fn:     Option<Rc<RefCell<Type>>>,

    // Lists of all goto labels in the curent function.
    labels:         Vec<Node>,

    brk_label:      Option<String>,
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
            current_fn: None,

            labels:     Vec::new(),
            brk_label:  None,
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

    fn push_tag_scope(&mut self, name: &str, tag: Rc<RefCell<Type>>) {
        self.scope.borrow_mut().tags.insert(name.to_string(), Rc::clone(&tag));
    }

    fn push_typedef_scope(&mut self, name: &str, typedef: Rc<RefCell<Type>>) {
        self.scope.borrow_mut().typedefs.insert(name.to_string(), typedef);
    }

    fn new_lvar(&mut self, ty: Rc<RefCell<Type>>, token: &Token) -> Rc<RefCell<Obj>> {
        let obj = (*self.local).borrow_mut().add_var(ty, None, token, true, &self.scope.borrow());
        self.push_scope(Rc::clone(&obj));

        obj
    }

    fn new_gvar(&mut self, ty: Rc<RefCell<Type>>, token: &Token) -> Rc<RefCell<Obj>> {
        let obj = self.global.borrow_mut().add_var(ty, None, token, false, &self.scope.borrow());
        self.push_scope(Rc::clone(&obj));

        obj
    }

    fn new_param_lvars(&mut self, params: &Vec<Rc<RefCell<Type>>>) {
        for param in params {
            if self.scope.borrow().find_lvar(&param.borrow().name.as_ref().unwrap().literal).is_some() {
                param.borrow().name.as_ref().unwrap().error(&format!("redefinition of '{}'", &param.borrow().name.as_ref().unwrap().literal));
            }
            self.new_lvar(Rc::clone(&param), &param.borrow().name.as_ref().unwrap());
        }
    }

    fn new_unique_name(&mut self) -> String {
        let s = format!(".L..{}", self.id);
        self.id += 1;

        s
    }

    fn new_anon_gvar(&mut self, token: Token, ty: Rc<RefCell<Type>>) -> Rc<RefCell<Obj>> {
        let ty = ty.clone();
        let name = self.new_unique_name();
        ty.borrow_mut().name = Some(Rc::new(Token::new(
            TokenKind::Ident,
            0,
            &name.clone(),
            "".to_string(),
            0,
            0,
        )));

        let obj = self.global.borrow_mut().add_var(
            ty.clone(),
            Some(token.literal.chars().collect()),
            &ty.borrow().name.as_ref().unwrap(),
            false,
            &self.scope.borrow()
        );
        self.push_scope(Rc::clone(&obj));

        obj
    }

    fn new_string_literal(&mut self, token: Token, ty: Rc<RefCell<Type>>) -> Rc<RefCell<Obj>> {
        self.new_anon_gvar(token, ty)
    }

    fn get_ident(&self) -> String {
        let token = self.tokenizer.cur_token();
        if token.kind != TokenKind::Ident {
            token.error("expected an identifier");
        }
        token.literal.to_string()
    }

    // declspec = ("void" | "_Bool" | "char" | "shoht" | "int" | "long" | 
    //          | "typedef" | "static"
    //          | struct-decl | union-decl | typedef-name
    //          | enum-specifier)+
    fn declspec(&mut self, attr: &mut Option<VarAttr>) -> Rc<RefCell<Type>> {
        let mut ty = Rc::new(RefCell::new(ty_int(None)));
        let mut counter = 0;

        while self.is_typename(&self.tokenizer.cur_token()) {
            // Handle storage class specifiers.
            let specifier = self.tokenizer.cur_token();
            if specifier.equal("typedef") || specifier.equal("static") {
                if let Some(ref mut attr) = attr {
                    attr.token = Some(self.tokenizer.cur_token().clone());

                    if specifier.equal("typedef") {
                        attr.is_typedef = true;
                    } else {
                        attr.is_static = true;
                    }
    
                    if attr.is_typedef && attr.is_static {
                        specifier.error("typedef and static may not be used together");
                    }
                } else {
                    self.tokenizer.cur_token()
                        .error("storage class specifier is not allowed in this context");
                }
                
                self.tokenizer.next_token();

                continue;
            }

            let ty2 = self.scope.borrow()
                .find_typedef(self.tokenizer.cur_token().literal.clone());

            let token = self.tokenizer.cur_token().clone();
            if token.equal("struct") || token.equal("union") || token.equal("enum") | ty2.is_some() {
                if counter > 0 {
                    break;
                }

                if self.tokenizer.consume("struct") {
                    ty = self.struct_decl();
                } else if self.tokenizer.consume("union") {
                    ty = self.union_decl();
                } else if self.tokenizer.consume("enum") {
                    ty = self.enum_specifier();
                } else if ty2.is_some() {
                    self.tokenizer.next_token();
                    ty = ty2.unwrap();
                }

                counter += OTHER;
                continue;
            }

            if self.tokenizer.consume("void") {
                counter += VOID;
            } else if self.tokenizer.consume("_Bool") {
                counter += BOOL;
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
                _ if counter == VOID                =>  ty = Rc::new(RefCell::new(ty_void(None))),
                _ if counter == BOOL                =>  ty = Rc::new(RefCell::new(ty_bool(None))),
                _ if counter == CHAR                =>  ty = Rc::new(RefCell::new(ty_char(None))),
                _ if counter == SHORT               =>  ty = Rc::new(RefCell::new(ty_short(None))),
                _ if counter == SHORT + INT         =>  ty = Rc::new(RefCell::new(ty_short(None))),
                _ if counter == INT                 =>  ty = Rc::new(RefCell::new(ty_int(None))),
                _ if counter == LONG                =>  ty = Rc::new(RefCell::new(ty_long(None))),
                _ if counter == LONG + INT          =>  ty = Rc::new(RefCell::new(ty_long(None))),
                _ if counter == LONG + LONG         =>  ty = Rc::new(RefCell::new(ty_long(None))),
                _ if counter == LONG + LONG + INT   =>  ty = Rc::new(RefCell::new(ty_long(None))),
                _   =>  self.tokenizer.cur_token().error("invalid type"),
            }
        }

        ty
    }

    // func-params = (param ("," param)*)? ")"
    // param       = declspec declarator
    fn func_params(&mut self, ty: Rc<RefCell<Type>>) -> Rc<RefCell<Type>> {
        let mut params = Vec::new();
        while !self.tokenizer.consume(")") {
            if params.len() != 0 {
                self.tokenizer.skip(",");
            }

            let mut ty2 = Rc::clone(&self.declspec(&mut None));
            ty2 =  Rc::clone(&self.declarator(Rc::clone(&ty2)));
            let name = ty2.borrow().name.as_ref().unwrap().clone();

            if ty2.borrow().kind == TypeKind::Array {
                let base = Rc::clone(&ty2.borrow().base.as_ref().unwrap());
                ty2 = Rc::new(RefCell::new(ty_ptr(
                    Some(name),
                    Some(base),
                )));
            }

            params.push(ty2);
        }

        Rc::new(RefCell::new(ty_function (
            Some(Rc::clone(&ty.borrow().name.as_ref().unwrap())),
            params,
            Some(Rc::clone(&ty)),
        )))
    }

    // array-dimensions = num? "]" type-suffix
    fn array_dimensions(&mut self, mut ty: Rc<RefCell<Type>>) -> Rc<RefCell<Type>> {
        if self.tokenizer.consume("]") {
            ty = Rc::clone(&self.type_suffix(ty));
            return Rc::new(RefCell::new(ty_array(
                ty.borrow().name.clone(),
                Some(Rc::clone(&ty)),
                0,
                0,
                ty.borrow().align,
            )));
        }

        let sz = self.tokenizer.cur_token().get_number();
        self.tokenizer.next_token();
        self.tokenizer.skip("]");
        ty = Rc::clone(&self.type_suffix(ty.clone()));
        
        return Rc::new(RefCell::new(ty_array (
            ty.borrow().name.clone(),
            Some(Rc::clone(&ty)),
            ty.borrow().size*sz,
            sz,
            ty.borrow().align,
        )));
    }

    // type-suffix = "(" func-pramas
    //             | "[" array-dimenstions
    //             | ε
    fn type_suffix(&mut self, ty: Rc<RefCell<Type>>) -> Rc<RefCell<Type>> {
        if self.tokenizer.consume("(") {
            return self.func_params(ty);
        }

        if self.tokenizer.consume("[") {
            return self.array_dimensions(ty);
        }

        ty
    }

    // declarator = "*"* ("(" ident ")" | "(" declarator ")" | ident) type-suffix
    fn declarator(&mut self, mut ty: Rc<RefCell<Type>>) -> Rc<RefCell<Type>> {
        while self.tokenizer.consume("*") {
            ty = Rc::new(RefCell::new(ty_ptr (
                None,
                Some(ty),
            )));
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

        ty.borrow_mut().name = Some(Rc::new(token));
        self.tokenizer.next_token();
        ty = self.type_suffix(ty);

        ty
    }

    // abstract-declarator = "*"* ("(" abstract-declarator ")")? type-suffix
    fn abstract_declarator(&mut self, mut ty: Rc<RefCell<Type>>) -> Rc<RefCell<Type>> {
        while self.tokenizer.consume("*") {
            ty = Rc::new(RefCell::new(ty_ptr(None, Some(ty))));
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
    fn typename(&mut self) -> Rc<RefCell<Type>> {
        let ty = self.declspec(&mut None);
        return self.abstract_declarator(ty);
    }

    // enum-specifier = ident? "{" enum-list? "}"
    //                | ident ("{" enum-list? "}")?
    //
    // enum-list      = ident ("=" num)? ("," ident ("=" num)?)*
    fn enum_specifier(&mut self) -> Rc<RefCell<Type>> {
        let ty = Rc::new(RefCell::new(ty_enum(None)));

        // Read a struct tag.
        let mut tag = None;
        if self.tokenizer.cur_token().kind == TokenKind::Ident {
            tag = Some(self.tokenizer.cur_token().clone());
            self.tokenizer.next_token();
        }

        if tag.is_some() && !self.tokenizer.equal("{") {
            let ty = self.scope.borrow().find_tag(
                tag.as_ref().unwrap().literal.clone()
            );
            if ty.is_none() {
                if let Some(token) = tag {
                    token.error("unknown enum type");
                }
            }
            return Rc::clone(&ty.unwrap());
        }
        
        self.tokenizer.skip("{");

        // Read an enum-list.
        let mut i = 0;
        let mut val = 0;
        while !self.tokenizer.consume("}") {
            if i > 0 {
                self.tokenizer.skip(",");
            }

            let name = self.tokenizer.cur_token().clone();
            self.tokenizer.next_token();

            if self.tokenizer.consume("=") {
                val = self.tokenizer.cur_token().get_number();
                self.tokenizer.next_token();
            }

            let constant = enum_const(name, val);
            self.push_scope(Rc::new(RefCell::new(constant)));

            val += 1;
            i += 1;
        }

        if tag.is_some() {
            self.push_tag_scope(&tag.unwrap().literal, Rc::clone(&ty));
        }

        Rc::clone(&ty)
    }

    // declaration = declspec (declarator ("=" expr)? ("," declarator ("=" expr)?)*)? ";"
    fn declaration(&mut self, basety: Rc<RefCell<Type>>) -> Node {
        let token = self.tokenizer.cur_token().clone();
        let mut decls = Vec::new();

        let mut i = 0;

        while !self.tokenizer.consume(";") {
            if i > 0 {
                self.tokenizer.skip(",");
            }
            i += 1;

            let ty = self.declarator(Rc::clone(&basety));

            if ty.borrow().kind == TypeKind::Array && ty.borrow().size == 0 {
                ty.borrow().name.as_ref().unwrap().error("variable has incomplete type");
            }

            if ty.borrow().kind == TypeKind::Void {
                ty.borrow().name.as_ref().unwrap().error("variable declared void");
            }

            let tok_lhs = &*(ty.borrow().name.as_ref().unwrap()).clone();
            let name = tok_lhs.clone().literal;
            let obj = Rc::clone(&self.new_lvar(Rc::clone(&ty), &tok_lhs.clone()));

            if !self.tokenizer.consume("=") {
                continue;
            }

            let lhs = Node::Var {
                name,
                ty,
                token:  tok_lhs.clone(),
                obj:    Rc::clone(&obj),
            };

            let mut rhs = self.assign();

            if lhs.get_type().borrow().kind != TypeKind::Struct {
                rhs = Node::Cast {
                    expr:   Box::new(rhs.clone()),
                    ty:     lhs.clone().get_type(),
                    token:  rhs.get_token().clone(),
                };
            }

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
    //      | "goto" ident ";"
    //      | "break" ";"
    //      | ident ":" stmt
    //      | compound-stmt
    //      | expr-stmt
    fn stmt(&mut self) -> Node {
        let mut token = self.tokenizer.cur_token().clone();
        if self.tokenizer.consume("return") {
            let mut expr = self.expr();
            self.tokenizer.skip(";");

            expr = Node::Cast {
                expr:   Box::new(expr),
                ty:     Rc::clone(self.current_fn.as_ref().unwrap().borrow().ret_ty.as_ref().unwrap()),
                token:  token.clone(),
            };

            return Node::Return(
                Box::new(expr),
                token,
            );
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

            self.enter_scope();

            let brk = self.brk_label.clone();
            let brk_label = self.new_unique_name();
            self.brk_label = Some(brk_label.clone());

            let init = if !self.tokenizer.consume(";") {
                let token = self.tokenizer.cur_token();
                if self.is_typename(&token) {
                    let basety = self.declspec(&mut None);
                    Some(Box::new(self.declaration(basety)))
                } else {
                    Some(Box::new(self.expr_stmt()))
                }
            } else {
                None
            };

            let cond = if !self.tokenizer.equal(";") {
                Some(Box::new(self.expr()))
            } else {
                None
            };

            self.tokenizer.skip(";");

            let inc = if !self.tokenizer.equal(")") {
                Some(Box::new(self.expr()))
            } else {
                None
            };

            self.tokenizer.skip(")");

            let body = Box::new(self.stmt());

            self.leave_scope();

            self.brk_label = brk;

            return Node::For {
                init,
                cond,
                inc,
                body,
                brk_label,
                token,
             }
        }

        if self.tokenizer.consume("while") {
            self.tokenizer.skip("(");
            let cond = if !self.tokenizer.equal(")") {
                Some(Box::new(self.expr()))
            } else {
                None
            };

            self.tokenizer.skip(")");

            let brk = self.brk_label.clone();
            let brk_label = self.new_unique_name();
            self.brk_label = Some(brk_label.clone());

            let body = Box::new(self.stmt());

            self.brk_label = brk;

            return Node::For {
                init: None,
                cond,
                inc: None,
                body,
                brk_label,
                token,
             };
        }

        if self.tokenizer.consume("goto") {
            token = self.tokenizer.cur_token().clone();
            let node = Node::Goto {
                label:          Some(self.get_ident()),
                unique_label:   None,
                token,
            };
            self.tokenizer.next_token();
            self.tokenizer.skip(";");

            return node;
        }

        if self.tokenizer.consume("break") {
            if self.brk_label.is_none() {
                token.error("stray break");
            }
            self.tokenizer.skip(";");

            return Node::Goto {
                label:          None,
                unique_label:   Some(self.brk_label.as_ref().unwrap().to_string()),
                token,
            };
        }

        if token.kind == TokenKind::Ident && self.tokenizer.peek_token().equal(":") {
            let ident = self.get_ident();
            self.tokenizer.next_token();
            self.tokenizer.next_token();
            let stmt = self.stmt();

            let node = Node::Label {
                stmt:   Box::new(stmt),
                label:  ident,
                unique_label:   self.new_unique_name(),
                token,
            };

            self.labels.push(node.clone());

            return node;
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
            if self.is_typename(&self.tokenizer.cur_token()) &&
              !self.tokenizer.peek_token().equal(":") {
                let token = self.tokenizer.cur_token().clone();
                let mut attr = Some(VarAttr {
                    token:      Some(token),
                    is_typedef: false,
                    is_static:  false,
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

    // Convert `A op= B` to `tmp = &A, *tmp = *tmp op B`
    // where tmp is a fresh pointer variable.
    fn to_assign(&mut self, lhs: Node, rhs: Node, token: Token, op: &str) -> Node {
        let var = Rc::new(RefCell::new(new_lvar(
            0,
            token.literal.clone(),
            Rc::new(RefCell::new(ty_ptr(None, Some(lhs.get_type())))),
        )));

        let expr1 = Node::Assign {
            lhs:    Box::new(Node::Var{
                name:   token.literal.clone(),
                ty:     Rc::new(RefCell::new(ty_ptr(None, Some(lhs.get_type())))),
                token:  token.clone(),
                obj:    Rc::clone(&var),
            }),
            rhs:    Box::new(Node::Addr (
                Box::new(lhs.clone()),
                token.clone(),
            )),
            token:  token.clone(),
        };

        let expr2_rhs = if op == "+=" || op == "++" {
            Box::new(self.new_add(
                Node::Deref(
                    Box::new(Node::Var{
                        name:   token.literal.clone(),
                        ty:     Rc::new(RefCell::new(ty_ptr(None, Some(lhs.get_type())))),
                        token:  token.clone(),
                        obj:    Rc::clone(&var),
                    }),
                    token.clone(),
                ),
                rhs,
                token.clone(),
            ))
        } else if op == "-=" || op == "--" {
            Box::new(self.new_sub(
                Node::Deref(
                    Box::new(Node::Var{
                        name:   token.literal.clone(),
                        ty:     Rc::new(RefCell::new(ty_ptr(None, Some(lhs.get_type())))),
                        token:  token.clone(),
                        obj:    Rc::clone(&var),
                    }),
                    token.clone(),
                ),
                rhs,
                token.clone(),
            ))
        } else if op == "*=" {
            Box::new(Node::Mul {
                lhs:    Box::new(Node::Deref(
                    Box::new(Node::Var{
                        name:   token.literal.clone(),
                        ty:     Rc::new(RefCell::new(ty_ptr(None, Some(lhs.get_type())))),
                        token:  token.clone(),
                        obj:    Rc::clone(&var),
                    }),
                    token.clone(),
                )),
                rhs:    Box::new(rhs),
                token:  token.clone(),
            })
        } else if op == "/=" {
            Box::new(Node::Div {
                lhs:    Box::new(Node::Deref(
                    Box::new(Node::Var{
                        name:   token.literal.clone(),
                        ty:     Rc::new(RefCell::new(ty_ptr(None, Some(lhs.get_type())))),
                        token:  token.clone(),
                        obj:    Rc::clone(&var),
                    }),
                    token.clone(),
                )),
                rhs:    Box::new(rhs),
                token:  token.clone(),
            })
        } else if op == "%=" {
            Box::new(Node::Mod {
                lhs:    Box::new(Node::Deref(
                    Box::new(Node::Var{
                        name:   token.literal.clone(),
                        ty:     Rc::new(RefCell::new(ty_ptr(None, Some(lhs.get_type())))),
                        token:  token.clone(),
                        obj:    Rc::clone(&var),
                    }),
                    token.clone(),
                )),
                rhs:    Box::new(rhs),
                token:  token.clone(),
            })
        } else if op == "&=" {
            Box::new(Node::BitAnd {
                lhs:    Box::new(Node::Deref(
                    Box::new(Node::Var{
                        name:   token.literal.clone(),
                        ty:     Rc::new(RefCell::new(ty_ptr(None, Some(lhs.get_type())))),
                        token:  token.clone(),
                        obj:    Rc::clone(&var),
                    }),
                    token.clone(),
                )),
                rhs:    Box::new(rhs),
                token:  token.clone(),
            })
        } else if op == "|=" {
            Box::new(Node::BitOr {
                lhs:    Box::new(Node::Deref(
                    Box::new(Node::Var{
                        name:   token.literal.clone(),
                        ty:     Rc::new(RefCell::new(ty_ptr(None, Some(lhs.get_type())))),
                        token:  token.clone(),
                        obj:    Rc::clone(&var),
                    }),
                    token.clone(),
                )),
                rhs:    Box::new(rhs),
                token:  token.clone(),
            })
        } else if op == "^=" {
            Box::new(Node::BitXor {
                lhs:    Box::new(Node::Deref(
                    Box::new(Node::Var{
                        name:   token.literal.clone(),
                        ty:     Rc::new(RefCell::new(ty_ptr(None, Some(lhs.get_type())))),
                        token:  token.clone(),
                        obj:    Rc::clone(&var),
                    }),
                    token.clone(),
                )),
                rhs:    Box::new(rhs),
                token:  token.clone(),
            })
        } else {
            unreachable!();
        };

        let expr2 = Node::Assign {
            lhs:    Box::new(Node::Deref (
                Box::new(Node::Var{
                    name:   token.literal.clone(),
                    ty:     Rc::new(RefCell::new(ty_ptr(None, Some(lhs.get_type())))),
                    token:  token.clone(),
                    obj:    Rc::clone(&var),
                }),
                token.clone(),
            )),
            rhs:    expr2_rhs,
            token:  token.clone(),
        };

        return Node::Comma {
            lhs:    Box::new(expr1),
            rhs:    Box::new(expr2),
            token,
        };
    } 

    // assign    = logor (assign-op assign)?
    // assign-op = "=" | "+=" | "-=" | "*=" | "/=" | "%=" | "&=" | "|=" | "^="
    fn assign(&mut self) -> Node {
        let token = self.tokenizer.cur_token().clone();
        let node = self.logor();
        let op = self.tokenizer.cur_token().clone().literal;

        if self.tokenizer.consume("=") {
            return Node::Assign {
                lhs: Box::new(node),
                rhs: Box::new(self.assign()),
                token,
            };
        }

        if  self.tokenizer.consume("+=") || self.tokenizer.consume("-=") ||
            self.tokenizer.consume("*=") || self.tokenizer.consume("/=") ||
            self.tokenizer.consume("%=") || self.tokenizer.consume("&=") || 
            self.tokenizer.consume("|=") || self.tokenizer.consume("^=") {
            let rhs = self.assign();
            return self.to_assign(node, rhs, token, &op);
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

    // logor = logand ("||" logand)*
    fn logor(&mut self) -> Node {
        let mut node = self.logand();

        loop {
            let token = self.tokenizer.cur_token().clone();
            if self.tokenizer.consume("||") {
                node = Node::LogOr {
                    lhs: Box::new(node),
                    rhs: Box::new(self.logand()),
                    token,
                };
                continue;
            }
            
            return node;
        }
    }

    // logand = bitor ("&&" bitor)*
    fn logand(&mut self) -> Node {
        let mut node = self.bitor();

        loop {
            let token = self.tokenizer.cur_token().clone();
            if self.tokenizer.consume("&&") {
                node = Node::LogAnd {
                    lhs: Box::new(node),
                    rhs: Box::new(self.bitor()),
                    token,
                };
                continue;
            }
            
            return node;
        }
    }

    // bitor = bitxor ("|" bitxor)*
    fn bitor(&mut self) -> Node {
        let mut node = self.bitxor();

        loop {
            let token = self.tokenizer.cur_token().clone();
            if self.tokenizer.consume("|") {
                node = Node::BitOr {
                    lhs: Box::new(node),
                    rhs: Box::new(self.bitxor()),
                    token,
                };
                continue;
            }
            
            return node;
        }
    }

    // bitxor = bitand ("^" bitand)*
    fn bitxor(&mut self) -> Node {
        let mut node = self.bitand();
        
        loop {
            let token = self.tokenizer.cur_token().clone();
            if self.tokenizer.consume("^") {
                node = Node::BitXor {
                    lhs: Box::new(node),
                    rhs: Box::new(self.bitand()),
                    token,
                };
                continue;
            }
            
            return node;
        }
    }

    // bitand = equality ("&" equality)*
    fn bitand(&mut self) -> Node {
        let mut node = self.equality();
        
        loop {
            let token = self.tokenizer.cur_token().clone();
            if self.tokenizer.consume("&") {
                node = Node::BitAnd {
                    lhs: Box::new(node),
                    rhs: Box::new(self.equality()),
                    token,
                };
                continue;
            }
            
            return node;
        }
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
        if lhs.get_type().borrow().is_num() && rhs.get_type().borrow().is_num() {
            return  Node::Add {
                lhs: Box::new(lhs.clone()),
                rhs: Box::new(rhs),
                token,
            };
        }

        if lhs.get_type().borrow().is_ptr() && rhs.get_type().borrow().is_ptr() {
            token.error("invalid operands");
        }

        // Canonicalize `num + ptr` to `ptr + num`.
        if !lhs.get_type().borrow().is_ptr() && rhs.get_type().borrow().is_ptr() {
            let tmp = lhs;
            lhs = rhs;
            rhs = tmp;
        }
        
        // ptr + num
        rhs = Node::Mul {
            lhs: Box::new(rhs.clone()),
            rhs: Box::new(Node::Num(
                lhs.get_type().borrow().base.as_ref().unwrap().borrow().size,
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
        if lhs.get_type().borrow().is_num() && rhs.get_type().borrow().is_num() {
            return Node::Sub {
                lhs: Box::new(lhs.clone()),
                rhs: Box::new(rhs),
                token,
            };
        }

        // ptr - num
        if lhs.get_type().borrow().is_ptr() && rhs.get_type().borrow().is_num() {
            rhs = Node::Mul {
                lhs: Box::new(rhs.clone()),
                rhs: Box::new(Node::Num(
                    lhs.get_type().borrow().base.as_ref().unwrap().borrow().size,
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
        if lhs.get_type().borrow().is_ptr() && rhs.get_type().borrow().is_ptr() {
            lhs = Node::Sub {
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
                token: token.clone(),
            };
            return Node::Div {
                lhs: Box::new(lhs.clone()),
                rhs: Box::new(Node::Num(
                    lhs.get_type().borrow().size,
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

        let var = self.global.borrow().find_var(&name);

        if let Some(ref func) = var {
            if func.borrow().ty.borrow().kind != TypeKind::Function {
                token.error("not a function");
            }
        } else {
            token.error("implicit declaration of a function");
        }

        self.tokenizer.next_token();
        self.tokenizer.next_token();

        let ty = Rc::clone(&var.clone().unwrap().borrow().ty);
        let mut params = ty.borrow_mut().params.clone();

        let mut i = 0;
        while !self.tokenizer.consume(")") {
            if i > 0 {
                self.tokenizer.skip(",");
            }

            let mut arg = self.assign();

            if params.len() > 0 {
                let param = params.remove(0);

                if param.borrow().kind == TypeKind::Struct ||
                    param.borrow().kind == TypeKind::Union {
                    arg.get_token().error("passing struct or union is not support yet");
                }

                arg = Node::Cast {
                    expr:   Box::new(arg.clone()),
                    ty:     param.clone(),
                    token:  arg.get_token().clone(),
                };
            }

            args.push(Box::new(arg));
            i += 1;
        }

        Node::FuncCall {
            name,
            args,
            ret_ty: Some(Rc::clone(var.unwrap().borrow().ty.borrow().ret_ty.as_ref().unwrap())),
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
        if self.tokenizer.equal("(") &&
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
            if self.tokenizer.equal("(") &&
               self.is_typename(&self.tokenizer.peek_token()) {
                self.tokenizer.next_token();
                let token = self.tokenizer.cur_token().clone();
                let ty = self.typename();
                self.tokenizer.skip(")");

                return Node::Num(
                    ty.borrow().size,
                    token,
                );
            }
            else {
                let node = self.unary();
                return Node::Num(
                    node.get_type().borrow().size,
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

            if obj.borrow().ty.borrow().kind == TypeKind::Enum {
                return Node::Num(
                    obj.borrow().enum_val,
                    token, 
                );
            } else {
                return Node::Var{
                    name,
                    ty:     Rc::clone(&obj.borrow().ty),
                    token,
                    obj:    Rc::clone(&obj),
                };
            }
        }

        if token.kind == TokenKind::Str {
            let var = self.new_string_literal(
                token.clone(), Rc::clone(token.ty.as_ref().unwrap()),
            );
            self.tokenizer.next_token();
            let ty = token.clone().ty.unwrap();
            return Node::Var {
                name:   var.borrow().ty.borrow().name.as_ref().unwrap().literal.clone(),
                ty:     Rc::clone(&ty),
                token,
                obj:    Rc::clone(&var),
            };
        }

        if token.kind == TokenKind::Num {
            let node = Node::Num(
                token.get_number(),
                token,
            );
            self.tokenizer.next_token();
            return node;
        }

        token.error("expected an expression");
    }

    // mul = cast ("*" cast | "/" cast | "%" cast)*
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
            
            if self.tokenizer.consume("%") {
                node = Node::Mod {
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

    // unary = ("+" | "-" | "*" | "&" | "!" | "~") cast
    //       | ("++" | "--") unary
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

        if self.tokenizer.consume("!") {
            return Node::Not(
                Box::new(self.cast()),
                token,
            );
        }

        if self.tokenizer.consume("~") {
            return Node::BitNot(
                Box::new(self.cast()),
                token,
            );
        }

        let op = self.tokenizer.cur_token().clone().literal;

        if self.tokenizer.consume("++") {
            let lhs = self.unary();
            let rhs = Node::Num(1, token.clone());
            return self.to_assign(lhs, rhs, token, &op);
        }
        
        if self.tokenizer.consume("--") {
            let lhs = self.unary();
            let rhs = Node::Num(1, token.clone());
            return self.to_assign(lhs, rhs, token, &op);
        }

        self.postfix()
    }

    // struct-members = (declspec declarator ("," declarator)* ";")*
    fn struct_members(&mut self) -> Vec<Box<Member>> {
        let mut members = Vec::new();

        while !self.tokenizer.equal("}") {
            let basety = self.declspec(&mut None);
            let mut i = 0;

            while !self.tokenizer.consume(";") {
                if i > 0 {
                    self.tokenizer.skip(",");
                }
                let ty = self.declarator(basety.clone());
                members.push(Box::new(Member {
                    ty:     ty.clone(),
                    name:   ty.borrow().name.as_ref().unwrap().literal.clone(),
                    offset: 0,
                }));
                i += 1;
            }
        }
        self.tokenizer.next_token();

        members

    }

    fn struct_union_decl(&mut self) -> Rc<RefCell<Type>> {
        let mut tag = None;

        if self.tokenizer.cur_token().kind == TokenKind::Ident {
            tag = Some(self.tokenizer.cur_token().clone());
            self.tokenizer.next_token();
        }
        
        if tag.is_some() && !self.tokenizer.equal("{") {
            let ty = self.scope.borrow().find_tag(
                tag.as_ref().unwrap().literal.clone()
            );

            if ty.is_some() {
                return ty.unwrap();
            }

            let mut ty2 = ty_struct(Some(Rc::new(tag.clone().unwrap())), Vec::new());
            ty2.is_incomplete = true;

            let p_ty2 = Rc::new(RefCell::new(ty2));
            self.push_tag_scope(&tag.as_ref().unwrap().literal, Rc::clone(&p_ty2));
            return Rc::clone(&p_ty2);
        }

        self.tokenizer.skip("{");
            
        let mut ty = ty_struct(None, Vec::new());
        ty.members = self.struct_members();

        let p_ty = Rc::new(RefCell::new(ty.clone()));

        if tag.is_some() {
            if let Some(tag) = self.scope.borrow().find_tag(tag.as_ref().unwrap().literal.clone()) {
                tag.borrow_mut().members = ty.members.clone();
                tag.borrow_mut().assign_offsets();
                return Rc::clone(&p_ty);
            }
            self.push_tag_scope(&tag.as_ref().unwrap().literal, Rc::clone(&p_ty));
        }

        return Rc::clone(&p_ty);
    }

    // struct-decl = ident? "{" struct-members
    fn struct_decl(&mut self) -> Rc<RefCell<Type>> {
        let ty = self.struct_union_decl();

        if ty.borrow().is_incomplete {
            return Rc::clone(&ty);
        }

        // Assign offsets within the struct to member.
        ty.borrow_mut().assign_offsets();

        ty
    }

    // union-decl = ident? "{" struct-members
    fn union_decl(&mut self) -> Rc<RefCell<Type>> {

        // Read a union tag.
        let mut tag = None;
        if self.tokenizer.cur_token().kind == TokenKind::Ident {
            tag = Some(self.tokenizer.cur_token().clone());
            self.tokenizer.next_token();
        }

        if tag != None && !self.tokenizer.equal("{") {
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
        let mut ty = ty_union(
            None,
            self.struct_members(),
        );

        for member in ty.members.iter_mut() {
            if ty.align < member.ty.borrow().align {
                ty.align = member.ty.borrow().align;
            }
            if ty.size < member.ty.borrow().size {
                ty.size = member.ty.borrow().size;
            }
        }
        ty.size = align_to(ty.size, ty.align);

        let ty2 = Rc::new(RefCell::new(ty));

        if tag != None {
            self.push_tag_scope(&tag.unwrap().literal, Rc::clone(&ty2));
        }

        Rc::clone(&ty2)
    }

    fn get_struct_member(&self, ty: Rc<RefCell<Type>>) -> Member {
        let token = self.tokenizer.cur_token();
        match ty.borrow().kind {
            TypeKind::Struct    |
            TypeKind::Union     =>  {
                for member in &ty.borrow().members {
                    if member.name == token.literal {
                        return *member.clone();
                    }
                }
                token.error("no such member");
            },
            _   =>  token.error("no such member"),
        }
    }

    fn struct_ref(&mut self, lhs: &mut Node) -> Node {
        let token = self.tokenizer.cur_token();

        match lhs.get_type().borrow().kind {
            TypeKind::Struct    |
            TypeKind::Union     => (),
            _   =>  lhs.get_token().error("not a struct nor union"),
        }

        let node = Node::Member {
            base:   Box::new(lhs.clone()),
            member: self.get_struct_member(lhs.get_type()),
            token:  token.clone(),
        };

        node        
    }

    // Convert A++ to `(typeof A)((A += 1) - 1)`
    fn new_inc_dec(&mut self, node: Node, plus: bool) -> Node {
        let token = self.tokenizer.cur_token().clone();
        let addend = if plus {
            Node::Num(1, token.clone())
        } else {
            Node::Neg(Box::new(Node::Num(1, token.clone())), token.clone())
        };

        let a = self.to_assign(
            node.clone(),
            addend.clone(),
            token.clone(),
            "++",
        );

        return Node::Cast {
            expr:   Box::new(self.new_add(
                a,
                Node::Neg(Box::new(addend), token.clone()),
                token.clone(),
            )),
            ty:     node.get_type(),
            token
        };
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
                node = self.struct_ref(&mut node);
                self.tokenizer.next_token();
                continue;
            }

            if self.tokenizer.consume("->") {
                let token = self.tokenizer.cur_token().clone();
                node = Node::Deref(
                    Box::new(node),
                    token,
                );
                node = self.struct_ref(&mut node);
                self.tokenizer.next_token();
                continue;
            };

            if self.tokenizer.consume("++") {
                node = self.new_inc_dec(node, true);
                continue;
            }

            if self.tokenizer.consume("--") {
                node = self.new_inc_dec(node, false);
                continue;
            }

            return node;
        }
    }

    fn parse_typedef(&mut self, basety: Rc<RefCell<Type>>) {
        let mut first = true;

        while !self.tokenizer.consume(";") {
            if !first {
                self.tokenizer.skip(",");
            }
            first = false;

            let ty = self.declarator(basety.clone());
            self.push_typedef_scope(
                &ty.borrow().name.as_ref().unwrap().literal, ty.clone()
            );
        }
    }

    // function-definition = declspec declarator compound-stmt
    fn function(&mut self, basety: Rc<RefCell<Type>>, attr: &mut Option<VarAttr>) -> Option<Node> {
        let locals = Rc::new(RefCell::new( Env {
            parent:     Some(Rc::clone(&self.global)),
            objs:       Vec::new(),
            stack_size: 0,
        }));
        self.local = Rc::clone(&locals);

        let token = self.tokenizer.cur_token().clone();
        let ty = self.declarator(basety.clone());
        ty.borrow_mut().is_definition = !self.tokenizer.consume(";");
        let name = ty.borrow().name.as_ref().unwrap().literal.clone();

        self.new_gvar(Rc::clone(&ty), &ty.borrow().name.as_ref().unwrap());
        self.current_fn = Some(Rc::clone(&ty));

        if !ty.borrow().is_definition {
            return None;
        }

        self.enter_scope();
        self.new_param_lvars(&ty.borrow().params);

        let params = Env {
            parent: None,
            objs:   self.local.borrow().objs.clone(),
            stack_size: 0,
        };

        self.labels = Vec::new();
        let mut body = Box::new(self.compound_stmt());
        body.resolve_goto_labels(&self.labels);

        self.leave_scope();
        Some(Node::Function {
            name,
            params,
            body,
            locals:     Rc::clone(&self.local),
            ret_ty:     Some(ty),
            is_static:  attr.as_ref().unwrap().is_static,
            token,
        })
    }

    fn global_variables(&mut self, basety: Rc<RefCell<Type>>) {
        let mut first = true;

        while !self.tokenizer.consume(";") {
            if !first {
                self.tokenizer.skip(",");
            }
            first = false;

            let ty = self.declarator(basety.clone());
            let token = ty.borrow().name.as_ref().unwrap().clone();

            self.new_gvar(ty, &token);
        }
    }
 
    // function = "*"* ident "(" func-params ")"
    fn is_function(&mut self) -> bool {
        if self.tokenizer.equal(";") {
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

        if !self.tokenizer.equal("(") {
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
                is_static:  false,
            });
            let basety = self.declspec(&mut attr);

            if self.is_function() {
                if let Some(func) = self.function(basety.clone(), &mut attr) {
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