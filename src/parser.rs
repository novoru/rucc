use crate::tokenizer::{ TokenKind, Token, Tokenizer };

#[derive(Debug, PartialEq)]
pub enum Node {
    Add { lhs: Box<Node>, rhs: Box<Node> },
    Sub { lhs: Box<Node>, rhs: Box<Node> },
    Mul { lhs: Box<Node>, rhs: Box<Node> },
    Div { lhs: Box<Node>, rhs: Box<Node> },
    Num (u32),
}

#[derive(Debug)]
struct Parser<'a> {
    tokenizer:  &'a mut Tokenizer<'a>,
}

impl<'a> Parser<'a> {
    pub fn new(tokenizer: &'a mut Tokenizer<'a>) -> Self {
        Parser {
            tokenizer:  tokenizer,
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

        None
    }

    // mul = primary ("*" primary | "/" primary)*
    fn mul(&mut self) -> Option<Node> {
        let mut node = self.primary().unwrap();
        
        loop {
            if self.tokenizer.consume("*") {
                node = Node::Mul { lhs: Box::new(node), rhs: Box::new(self.primary().unwrap()) };
                continue;
            }
            
            if self.tokenizer.consume("/") {
                node = Node::Div { lhs: Box::new(node), rhs: Box::new(self.primary().unwrap()) };
                continue;
            }

            return Some(node);
        }
    }

    // expr = mul ("+" mul | "-" mul)*
    fn expr(&mut self) -> Option<Node> {
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