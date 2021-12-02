use crate::tokenizer::{ TokenKind, Tokenizer };

#[derive(Debug, PartialEq)]
pub enum Node {
    Add { lhs: Box<Node>, rhs: Box<Node> },
    Sub { lhs: Box<Node>, rhs: Box<Node> },
    Mul { lhs: Box<Node>, rhs: Box<Node> },
    Div { lhs: Box<Node>, rhs: Box<Node> },
    Neg (Box<Node>),
    Eq  { lhs: Box<Node>, rhs: Box<Node> },
    Ne  { lhs: Box<Node>, rhs: Box<Node> },
    Lt  { lhs: Box<Node>, rhs: Box<Node> },
    Le  { lhs: Box<Node>, rhs: Box<Node> },
    Num (u32),
}

#[derive(Debug)]
pub struct Parser<'a> {
    tokenizer:  &'a mut Tokenizer<'a>,
}

impl<'a> Parser<'a> {
    pub fn new(tokenizer: &'a mut Tokenizer<'a>) -> Self {
        Parser {
            tokenizer:  tokenizer,
        }
    }

    // equality = relational ("==" relational | "!=" relational)*
    fn equality(&mut self) -> Option<Node> {
        let mut node = self.relational().unwrap();

        loop {
            if self.tokenizer.consume("==") {
                node = Node::Eq { lhs: Box::new(node), rhs: Box::new(self.relational().unwrap()) };
                continue;
            }
            
            if self.tokenizer.consume("!=") {
                node = Node::Ne { lhs: Box::new(node), rhs: Box::new(self.relational().unwrap()) };
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
                node = Node::Lt { lhs: Box::new(node), rhs: Box::new(self.add().unwrap()) };
                continue;
            }
            
            if self.tokenizer.consume("<=") {
                node = Node::Le { lhs: Box::new(node), rhs: Box::new(self.add().unwrap()) };
                continue;
            }
            
            if self.tokenizer.consume(">") {
                node = Node::Lt { lhs: Box::new(self.add().unwrap()), rhs: Box::new(node) };
                continue;
            }
            
            if self.tokenizer.consume(">=") {
                node = Node::Le { lhs: Box::new(self.add().unwrap()), rhs: Box::new(node) };
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
                node = Node::Add { lhs: Box::new(node), rhs: Box::new(self.mul().unwrap()) };
                continue;
            }
            
            if self.tokenizer.consume("-") {
                node = Node::Sub { lhs: Box::new(node), rhs: Box::new(self.mul().unwrap()) };
                continue;
            }

            return Some(node);
        }
    }

    // primary = "(" expr ")" | num
    fn primary(&mut self) -> Option<Node> {
        if self.tokenizer.consume("(") {
            let node = self.expr().unwrap();
            if !self.tokenizer.consume(")") {
                panic!("expected ')'");
            }
            return Some(node);
        }

        let token = self.tokenizer.next_token().unwrap();

        if token.kind == TokenKind::Int {
            let node = Node::Num(token.val.unwrap());
            return Some(node);
        }

        self.tokenizer.error_tok(self.tokenizer.cur_token(), "expected an expression");
        
        None
    }

    // mul = unary ("*" unary | "/" unary)*
    fn mul(&mut self) -> Option<Node> {
        let mut node = self.unary().unwrap();
        
        loop {
            if self.tokenizer.consume("*") {
                node = Node::Mul { lhs: Box::new(node), rhs: Box::new(self.unary().unwrap()) };
                continue;
            }
            
            if self.tokenizer.consume("/") {
                node = Node::Div { lhs: Box::new(node), rhs: Box::new(self.unary().unwrap()) };
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

    // expr = equality
    fn expr(&mut self) -> Option<Node> {
        self.equality()
    }

    pub fn parse(&mut self) -> Option<Node> {
        self.expr()
    }
}

#[test]
fn test_parser() {
    let mut tokenizer = Tokenizer::new("12+42*(3-9)");
    tokenizer.tokenize();
    let mut parser = Parser::new(&mut tokenizer);
    let prog = parser.parse().unwrap();
    let expected = Node::Add {
        lhs: Box::new(Node::Num(12)),
        rhs: Box::new(Node::Mul {
            lhs: Box::new(Node::Num(42)),
            rhs: Box::new(Node::Sub {
                lhs: Box::new(Node::Num(3)),
                rhs: Box::new(Node::Num(9)),
            })
        }),
    };
    assert_eq!(prog, expected);
}