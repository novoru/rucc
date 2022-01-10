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
    Shl         { lhs: Box<Node>, rhs: Box<Node>, token: Token },   // <<
    Shr         { lhs: Box<Node>, rhs: Box<Node>, token: Token },   // >>
    Eq          { lhs: Box<Node>, rhs: Box<Node>, token: Token },   // ==
    Ne          { lhs: Box<Node>, rhs: Box<Node>, token: Token },   // !=
    Lt          { lhs: Box<Node>, rhs: Box<Node>, token: Token },   // <
    Le          { lhs: Box<Node>, rhs: Box<Node>, token: Token },   // <=
    Assign      { lhs: Box<Node>, rhs: Box<Node>, token: Token },   // =
    Cond        {                                                   // ?:
        cond:   Box<Node>,
        then:   Box<Node>,
        els:    Box<Node>,
        token:  Token,
    },
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
        cond:       Box<Node>,
        then:       Box<Node>,
        els:        Option<Box<Node>>,
        token:      Token,
    },
    For         {                                                   // "for" of "while"
        init:       Option<Box<Node>>,
        cond:       Option<Box<Node>>,
        inc:        Option<Box<Node>>,
        body:       Box<Node>,
        brk_label:  String,
        cont_label: String,
        token:      Token,
    },
    Switch      {                                                   // "switch"
        cond:           Box<Node>,
        stmt:           Box<Node>,
        cases:          Rc<RefCell<Vec<Box<Node>>>>,
        default:        Option<Box<Node>>,
        brk_label:      String,
        token:          Token,
    },
    Case        {                                                   // "case"
        label:  String,
        stmt:   Box<Node>,
        val:    Option<u64>,    // if val is None, it's "default"
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
    Goto        {                                                   // "goto"
        label:          Option<String>,                             // if label is None, it's break statement
        unique_label:   Option<String>,
        token:          Token,
    },
    Label       {                                                   // Labeled statement
        stmt:           Box<Node>,
        label:          String,
        unique_label:   String,
        token:          Token,
    },
    FuncCall    {                                                   // Function call
        name:  String,
        args:   Vec<Box<Node>>,
        ret_ty: Option<Rc<RefCell<Type>>>,
        token:  Token
    },
    Function    {                                                   // Function definition
        name:       String,
        params:     Env,
        body:       Box<Node>,
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
            Node::Shl { lhs, .. }       |
            Node::Shr { lhs, .. }       =>  lhs.get_type(),
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
            Node::Cond  { then, els, ..}    =>  {
                if then.get_type().borrow().kind == TypeKind::Void ||
                   els.get_type().borrow().kind == TypeKind::Void {
                    Rc::new(RefCell::new(ty_void(None)))
                } else {
                    get_common_type(then.get_type(), els.get_type())
                }
            },
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
            Node::Shl       { token, .. }   |
            Node::Shr       { token, .. }   |
            Node::Eq        { token, .. }   |
            Node::Ne        { token, .. }   |
            Node::Lt        { token, .. }   |
            Node::Le        { token, .. }   |
            Node::Assign    { token, .. }   |
            Node::Cond      { token, .. }   |
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
            Node::Switch    { token, .. }   |
            Node::Case      { token, .. }   |
            Node::Block     ( .., token )   |
            Node::ExprStmt  ( .., token )   |
            Node::StmtExpr  ( .., token )   |
            Node::Var       { token, .. }   |
            Node::Goto      { token, .. }   |
            Node::Label     { token, .. }   |
            Node::FuncCall  { token, .. }   |
            Node::Function  { token, .. }   |
            Node::Program   { token, .. }   |
            Node::Num       ( .., token )   |
            Node::Cast      { token, .. }   =>  token,
        }
    }

    // This function matches gotos with labels.
    pub fn resolve_goto_labels(&mut self, labels: &Vec<Node>) {
        match self {
            Node::Add       { lhs, rhs, .. }  |
            Node::Sub       { lhs, rhs, .. }  |
            Node::Mul       { lhs, rhs, .. }  |
            Node::Div       { lhs, rhs, .. }  |
            Node::Mod       { lhs, rhs, .. }  |
            Node::BitAnd    { lhs, rhs, .. }  |
            Node::BitOr     { lhs, rhs, .. }  |
            Node::BitXor    { lhs, rhs, .. }  =>    {
                lhs.resolve_goto_labels(labels);
                rhs.resolve_goto_labels(labels);
            },
            Node::Neg   (expr, ..)  =>  expr.resolve_goto_labels(labels),
            Node::Shl       { lhs, rhs, .. }  |
            Node::Shr       { lhs, rhs, .. }  |
            Node::Eq        { lhs, rhs, .. }  |
            Node::Ne        { lhs, rhs, .. }  |
            Node::Lt        { lhs, rhs, .. }  |
            Node::Le        { lhs, rhs, .. }  |
            Node::Assign    { lhs, rhs, .. }  =>    {
                lhs.resolve_goto_labels(labels);
                rhs.resolve_goto_labels(labels);
            },
            Node::Cond      { cond, then, els, .. } =>  {
                cond.resolve_goto_labels(labels);
                then.resolve_goto_labels(labels);
                els.resolve_goto_labels(labels);
            }
            Node::Comma     { lhs, rhs, .. }  =>    {
                lhs.resolve_goto_labels(labels);
                rhs.resolve_goto_labels(labels);
            },
            Node::Addr      (expr, ..)  |
            Node::Deref     (expr, ..)  |
            Node::Not       (expr, ..)  |
            Node::BitNot    (expr, ..)  =>  expr.resolve_goto_labels(labels),
            Node::LogAnd    { lhs, rhs, .. }    |
            Node::LogOr     { lhs, rhs, .. }    =>    {
                lhs.resolve_goto_labels(labels);
                rhs.resolve_goto_labels(labels);
            },
            Node::Return    (expr, ..)  =>  expr.resolve_goto_labels(labels),
            Node::If        { cond, then, els, .. } =>  {
                cond.resolve_goto_labels(labels);
                then.resolve_goto_labels(labels);
                if let Some(block) = els {
                    block.resolve_goto_labels(labels);
                }
            },
            Node::For       { init, cond, inc, body, .. }   =>  {
                if let Some(exprstmt) = init {
                    exprstmt.resolve_goto_labels(labels);
                }
                if let Some(expr) = cond {
                    expr.resolve_goto_labels(labels);
                }
                if let Some(expr) = inc {
                    expr.resolve_goto_labels(labels);
                }
                body.resolve_goto_labels(labels);
            },
            Node::Switch    { stmt, .. }    |
            Node::Case      { stmt, .. }    =>  stmt.resolve_goto_labels(labels),
            Node::Block     ( ref mut stmts, .. )   =>  {
                for stmt in stmts {
                    stmt.resolve_goto_labels(labels);
                }
            },
            Node::StmtExpr(expr, ..)    =>  expr.resolve_goto_labels(labels),
            Node::ExprStmt(stmt, ..)    =>  stmt.resolve_goto_labels(labels),
            Node::Goto { label: glabel, unique_label: gulabel, token }  =>  {
                if glabel.is_none() {
                    return;
                }
                for label in labels {
                    if let Node::Label { label: llabel, unique_label: uulabel, .. } = &*label {
                        if glabel.as_ref().unwrap() == llabel {
                            *gulabel = Some(uulabel.to_string());
                            return;
                        }
                    }
                }
    
                if gulabel.is_none() {
                    token.error("use of undeclared label");
                }
            },
            Node::Label     { stmt, .. }    =>  {
                stmt.resolve_goto_labels(labels);
            },
            Node::FuncCall  { args, .. }    =>  {
                for arg in args {
                    arg.resolve_goto_labels(labels);
                }
            }
            Node::Cast  { expr, .. }    =>  expr.resolve_goto_labels(labels),
            _   =>  return,
        }        
    }

    pub fn eval(&self) -> u64 {
        match self {
            Node::Add       { lhs, rhs, .. }            =>  {
                match get_common_type(lhs.get_type(), rhs.get_type()).borrow().size {
                    4   =>  (lhs.eval() as u32).wrapping_add(rhs.eval() as u32) as u64,
                    _   =>  lhs.eval().wrapping_add(rhs.eval()),
                }
            },
            Node::Sub       { lhs, rhs, .. }            =>  {
                match get_common_type(lhs.get_type(), rhs.get_type()).borrow().size {
                    4   =>  (lhs.eval() as u32).wrapping_sub(rhs.eval() as u32) as u64,
                    _   =>  lhs.eval().wrapping_sub(rhs.eval()),
                }
            },
            Node::Mul       { lhs, rhs, .. }            =>  {
                match get_common_type(lhs.get_type(), rhs.get_type()).borrow().size {
                    4   =>  (lhs.eval() as u32).wrapping_mul(rhs.eval() as u32) as u64,
                    _   =>  lhs.eval().wrapping_mul(rhs.eval()),
                }
            },
            Node::Div       { lhs, rhs, .. }            =>  {
                match get_common_type(lhs.get_type(), rhs.get_type()).borrow().size {
                    4   =>  (lhs.eval() as u32).wrapping_div(rhs.eval() as u32) as u64,
                    _   =>  lhs.eval().wrapping_div(rhs.eval()),
                }
            },
            Node::Mod       { lhs, rhs, .. }            =>  lhs.eval() % rhs.eval(),
            Node::BitAnd    { lhs, rhs, .. }            =>  lhs.eval() & rhs.eval(),
            Node::BitOr     { lhs, rhs, .. }            =>  lhs.eval() | rhs.eval(),
            Node::BitXor    { lhs, rhs, .. }            =>  lhs.eval() ^ rhs.eval(),
            Node::Neg       ( expr, .. )                =>  (-(expr.eval() as i64)) as u64,
            Node::Shl       { lhs, rhs, .. }            =>  lhs.eval() << rhs.eval(),
            Node::Shr       { lhs, rhs, .. }            =>  lhs.eval() >> rhs.eval(),
            Node::Eq        { lhs, rhs, .. }            =>  (lhs.eval() == rhs.eval()) as u64,
            Node::Ne        { lhs, rhs, .. }            =>  (lhs.eval() != rhs.eval()) as u64,
            Node::Lt        { lhs, rhs, .. }            =>  (lhs.eval() < rhs.eval()) as u64,
            Node::Le        { lhs, rhs, .. }            =>  (lhs.eval() >= rhs.eval()) as u64,
            Node::Cond      { cond, then, els, .. }     =>  if cond.eval() != 0 { then.eval() } else { els.eval() }
            Node::Comma     { rhs, .. }                 =>  rhs.eval(),
            Node::Not       ( expr, .. )                =>  !(expr.eval() != 0) as u64,
            Node::BitNot    ( expr, .. )                =>  !expr.eval(),
            Node::LogAnd    { lhs, rhs, .. }            =>  (lhs.eval() != 0 && rhs.eval() != 0) as u64,
            Node::LogOr     { lhs, rhs, .. }            =>  (lhs.eval() != 0 || rhs.eval() != 0) as u64,
            Node::Num       ( val, .. )                 =>  *val,
            Node::Cast      { expr, ty,.. }             =>  {
                if ty.borrow().is_num() {
                    match ty.borrow().size {
                        1   =>  return expr.eval() as u8 as u64,
                        2   =>  return expr.eval() as u16 as u64,
                        4   =>  return expr.eval() as u32 as u64,
                        _   =>  (),
                    }
                }

                expr.eval()
            },
            _   =>  self.get_token().error("not a compile-time constant"),
        }
    }
}