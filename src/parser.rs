use std::rc::Rc;
use std::cell::RefCell;
use crate::tokenizer::{ TokenKind, Tokenizer };

// Ast node type
#[derive(Debug, PartialEq)]
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
    Return      ( Box<Node> ),                          // "return"
    Block       ( Vec<Box<Node>> ),                     // { ... }
    ExprStmt    ( Box<Node> ),                          // Expression statement
    Var         ( String ),                             // Variable
    FuncCall    { name: String, args: Vec<Box<Node>> }, // Function call
    FuncDef     {                                       // Function definition
                    body: Vec<Box<Node>>,
                    locals: RefCell<Scope>,
                    stack_size: usize
                },
    Program     ( Vec<Box<Node>> ),                     // Program
    Num         ( u32 ),                                // Integer
}

#[derive(Debug, PartialEq)]
struct Obj {
    name:   String,
    offset: usize,
}

#[derive(Debug, PartialEq)]
pub struct Scope {
    parent: Option<Rc<Scope>>,
    objs:   Vec<Obj>,
}

#[derive(Debug)]
pub struct Parser {
    global:     RefCell<Scope>,
    tokenizer:  Tokenizer,
}

impl Parser {
    pub fn new(input: &str) -> Self {
        let mut tokenizer = Tokenizer::new(input);
        tokenizer.tokenize();

        Parser {
            global:     RefCell::new( Scope {
                parent: None, objs: Vec::new()
            }),
            tokenizer:  tokenizer,
        }
    }

    // stmt = "return" expr ";"
    //      | "{" compound-stmt
    //      | expr-stmt
    fn stmt(&mut self) -> Option<Node> {
        if self.tokenizer.cur_token().equal("return") {
            self.tokenizer.next_token();
            let node = Node::Return(Box::new(self.expr().unwrap()));
            self.tokenizer.skip(";");
            return Some(node);
        }

        if self.tokenizer.cur_token().equal("{") {
            self.tokenizer.next_token();
            return self.compound_stmt();
        }

        self.expr_stmt()
    }

    // compound-stmt = stmt* "}"
    fn compound_stmt(&mut self) -> Option<Node> {
        let mut stmts = Vec::new();

        while !self.tokenizer.cur_token().equal("}") {
            stmts.push(Box::new(self.stmt().unwrap()));
        }

        self.tokenizer.next_token();

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
                rhs: Box::new(self.assign().unwrap())
            };
        }

        Some(node)
    }

    // expr-stmt = expr ";"
    fn expr_stmt(&mut self) -> Option<Node> {
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
                    rhs: Box::new(self.relational().unwrap())
                };
                continue;
            }
            
            if self.tokenizer.consume("!=") {
                node = Node::Ne {
                    lhs: Box::new(node),
                    rhs: Box::new(self.relational().unwrap())
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
                    rhs: Box::new(self.add().unwrap())
                };
                continue;
            }
            
            if self.tokenizer.consume("<=") {
                node = Node::Le {
                    lhs: Box::new(node),
                    rhs: Box::new(self.add().unwrap())
                };
                continue;
            }
            
            if self.tokenizer.consume(">") {
                node = Node::Lt {
                    lhs: Box::new(self.add().unwrap()),
                    rhs: Box::new(node)
                };
                continue;
            }
            
            if self.tokenizer.consume(">=") {
                node = Node::Le {
                    lhs: Box::new(self.add().unwrap()),
                    rhs: Box::new(node)
                };
                continue;
            }

            return Some(node);
        }
    }

    // add = mul ("+" mul | "-" mul)*
    fn add(&mut self) -> Option<Node> {
        let mut node = self.mul().unwrap();

        loop {
            if self.tokenizer.consume("+") {
                node = Node::Add {
                    lhs: Box::new(node),
                    rhs: Box::new(self.mul().unwrap())
                };
                continue;
            }
            
            if self.tokenizer.consume("-") {
                node = Node::Sub {
                    lhs: Box::new(node),
                    rhs: Box::new(self.mul().unwrap())
                };
                continue;
            }

            return Some(node);
        }
    }

    // primary = "(" expr ")" | ident | num
    fn primary(&mut self) -> Option<Node> {
        if self.tokenizer.consume("(") {
            let node = self.expr().unwrap();
            self.tokenizer.skip(")");
            return Some(node);
        }

        let token = self.tokenizer.next_token().unwrap();

        if token.kind == TokenKind::Ident {
            let node = Node::Var(token.literal.clone());
            return Some(node);
        }

        if token.kind == TokenKind::Num {
            let node = Node::Num(token.val.unwrap());
            return Some(node);
        }

        self.tokenizer.error_tok(
            self.tokenizer.cur_token(),
            "expected an expression"
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
                    rhs: Box::new(self.unary().unwrap())
                };
                continue;
            }
            
            if self.tokenizer.consume("/") {
                node = Node::Div {
                    lhs: Box::new(node), rhs: Box::new(self.unary().unwrap())
                };
                continue;
            }

            return Some(node);
        }
    }

    // unary = ("+" | "-") unary
    //       | primary
    fn unary(&mut self) -> Option<Node> {
        if self.tokenizer.consume("+") {
            return self.unary();
        }

        if self.tokenizer.consume("-") {
            return Some(Node::Neg(Box::new(self.unary().unwrap())));
        }

        self.primary()
    }
 
    // program = "{" compound-stmt
    pub fn parse(&mut self) -> Option<Node> {
        self.tokenizer.skip("{");

        let mut body = Vec::new();
        body.push(Box::new(self.compound_stmt().unwrap()));
        let mut prog = Node::Program(body);

        Some(prog)
    }
}