use std::rc::Rc;
use std::cell::RefCell;

use crate::tokenizer::Token;
use crate::ty::*;
use crate::obj::Obj;
use crate::env::Env;

// Ast node type
#[derive(Debug, Clone, PartialEq)]
pub enum Node {
    Add         { lhs: Box<Node>, rhs: Box<Node>, token: Token },   // +
    Sub         { lhs: Box<Node>, rhs: Box<Node>, token: Token },   // -
    Mul         { lhs: Box<Node>, rhs: Box<Node>, token: Token },   // *
    Div         { lhs: Box<Node>, rhs: Box<Node>, token: Token },   // /
    Mod         { lhs: Box<Node>, rhs: Box<Node>, token: Token },   // %
    BitAnd      { lhs: Box<Node>, rhs: Box<Node>, token: Token },   // &
    BitOr       { lhs: Box<Node>, rhs: Box<Node>, token: Token },   // |
    BitXor      { lhs: Box<Node>, rhs: Box<Node>, token: Token },   // ^
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
    Not         ( Box<Node>, Token ),                               // !
    BitNot      ( Box<Node>, Token ),                               // ~
    LogAnd      { lhs: Box<Node>, rhs: Box<Node>, token: Token },   // &&
    LogOr       { lhs: Box<Node>, rhs: Box<Node>, token: Token },   // ||
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
        name:   String,
        ty:     Rc<RefCell<Type>>,
        token:  Token,
        obj:    Rc<RefCell<Obj>>
    },
    FuncCall    {                                                   // Function call
        name:   String,
        args:   Vec<Box<Node>>,
        ret_ty: Option<Rc<RefCell<Type>>>,
        token:  Token
    },
    Function    {                                                   // Function definition
        name:       String,
        params:     Env,
        body:       Vec<Box<Node>>,
        locals:     Rc<RefCell<Env>>,
        ret_ty:     Option<Rc<RefCell<Type>>>,
        is_static:  bool,
        token:      Token,
    },
    Program     {                                                   // Program
        data:   Rc<RefCell<Env>>,
        text:   Vec<Box<Node>>,
        token:  Token,
    },
    Num         ( u64, Token ),                                     // Integer
    Cast        {
        expr:   Box<Node>,
        ty:     Rc<RefCell<Type>>,
        token:  Token,
    }
}

impl Node {
    pub fn get_type(&self) -> Rc<RefCell<Type>> {
        match self {
            Node::Add { lhs, rhs, .. }      => get_common_type(lhs.get_type(), rhs.get_type()),
            Node::Sub { lhs, rhs, .. }      =>  {
                // ptr - ptr, which returns how many elements are between the two.
                if lhs.get_type().borrow().is_ptr() && rhs.get_type().borrow().is_ptr() {
                    Rc::new(RefCell::new(ty_int(None)))
                } else {
                    get_common_type(lhs.get_type(), rhs.get_type())
                }
            },
            Node::Mul { lhs, rhs, .. }      |
            Node::Div { lhs, rhs, .. }      |
            Node::Mod { lhs, rhs, .. }      |
            Node::BitAnd { lhs, rhs, .. }   |
            Node::BitOr  { lhs, rhs, .. }   |
            Node::BitXor { lhs, rhs, .. }   =>  get_common_type(lhs.get_type(), rhs.get_type()),
            Node::Neg (..)              =>  Rc::new(RefCell::new(ty_long(None))),
            Node::Eq { .. }             |
            Node::Ne { .. }             |
            Node::Lt { .. }             |
            Node::Le { .. }             =>  Rc::new(RefCell::new(ty_int(None))),
            Node::Assign { lhs, .. }    =>  {
                let ty = lhs.get_type();
                if ty.borrow().kind == TypeKind::Array {
                    self.get_token().error("not an lvalue");
                }

                ty
            }
            Node::Comma { rhs, .. }         =>  rhs.get_type(),
            Node::Member { member, ..}      =>  Rc::clone(&member.ty),
            Node::Addr (expr, ..)           =>  {
                let ty = expr.get_type();
                let ret = match ty.borrow().kind {
                    TypeKind::Array =>  {
                        let base = Rc::clone(ty.borrow().base.as_ref().unwrap());
                        Rc::new(RefCell::new(ty_ptr(
                            None,
                            Some(base),
                        )))
                    },
                    _   =>  Rc::new(RefCell::new(ty_ptr(
                        None,
                        Some(Rc::clone(&ty)),
                    ))),
                };

                ret
            },
            Node::Deref (expr, ..)  =>  {
                let ty = expr.get_type();

                if ty.borrow().kind == TypeKind::Void {
                    self.get_token().error("deferencing a void pointer");
                }

                if ty.borrow().base.is_none() {
                    self.get_token().error("invalid pointer dereference");
                }

                let base = Rc::clone(&ty.borrow().base.as_ref().unwrap());
                base
            },
            Node::Not (..)                      |
            Node::LogAnd {..}                   |
            Node::LogOr  {..}                   =>  Rc::new(RefCell::new(ty_int(None))),
            Node::BitNot (expr, ..)             |
            Node::ExprStmt (expr, ..)           => expr.get_type(),
            Node::StmtExpr (body, ..)           => {
                if let Node::Block (stmts, ..)  = &**body {
                    if let Some(expr)           = stmts.last() {
                        return expr.get_type();
                    }
                }
                self.get_token().error("statement expression returning void is not supported");
            },
            Node::Var { ty, .. }            =>  ty.clone(),
            Node::FuncCall { ret_ty, .. }   =>  ret_ty.as_ref().unwrap().clone(),
            Node::Num ( val, ..)            =>  {
                if *val == *val as u32 as u64 {
                    return Rc::new(RefCell::new(ty_int(None)));
                } else {
                    return Rc::new(RefCell::new(ty_long(None)));
                }
            },
            Node::Cast { ty, .. }       =>  ty.clone(),
            _   =>  self.get_token().error("not an expression"),
        }
    }

    pub fn get_token(&self) -> &Token {
        match self {
            Node::Add       { token, .. }   |
            Node::Sub       { token, .. }   |
            Node::Mul       { token, .. }   |
            Node::Div       { token, .. }   |
            Node::Mod       { token, .. }   |
            Node::BitAnd    { token, .. }   |
            Node::BitOr     { token, .. }   |
            Node::BitXor    { token, .. }   |
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
            Node::Not       ( .., token )   |
            Node::BitNot    ( .., token )   |
            Node::LogAnd    { token, .. }   |
            Node::LogOr     { token, .. }   |
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