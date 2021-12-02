use std::process;
use std::rc::Rc;

#[derive(Debug, PartialEq)]
pub enum TokenKind {
    Empty,
    Int,
    Punct,
    Eof,
}

#[derive(Debug, PartialEq)]
pub struct Token<'a> {
    pub kind:   TokenKind,
    loc:        usize,
    pub val:    Option<u32>,
    literal:    Rc<&'a str>,
}

impl<'a> Token<'a> {
    pub fn new(kind: TokenKind, loc: usize, s: Rc<&'a str>) -> Self {
        Token {
            kind:       kind,
            loc:        loc,
            val:        None,
            literal:    s.clone(),
        }
    }

    pub fn new_num(val: u32, loc: usize, s: Rc<&'a str>) -> Self {
        Token {
            kind:       TokenKind::Int,
            loc:        loc,
            val:        Some(val),
            literal:    s.clone(),
        }
    }

    pub fn equal(&self, op: &str) -> bool {
        *self.literal == op
    }
}

#[derive(Debug)]
pub struct Tokenizer<'a> {
    input:  &'a str,
    pos:    usize,
    rpos:   usize,
    idx:    usize,
    tokens: Vec<Token<'a>>,
    ch:     char,
}

impl<'a> Tokenizer<'a> {
    pub fn new(input: &'a str) -> Self {
        Self {
            input:  input,
            pos:    0,
            rpos:   0,
            idx:    0,
            tokens: Vec::new(),
            ch:     '\0',
        }
    }

    pub fn tokenize(&mut self) {
        self.read_char();
        while self.ch != '\0' {
            if self.ch.is_whitespace() {
                self.read_char();
                continue;
            }

            if self.ch.is_digit(10) {
                self.read_num();
                continue;
            }

            let punct_len = self.read_punct(&self.input[self.pos..self.input.len()]);
            if punct_len != 0 {
                self.tokens.push(Token::new(
                    TokenKind::Punct, self.pos, Rc::new(&self.input[self.pos..self.pos+punct_len]
                )));
                for _ in 0..punct_len {
                    self.read_char();
                }
                continue;
            }

            self.error_at(self.pos, "invalide token");
        }
        self.tokens.push(Token::new(
            TokenKind::Eof, self.pos, Rc::new("")
        ));
    }

    pub fn next_token(&mut self) -> Option<&Token> {
        if self.idx >= self.tokens.len() {
            return None;
        }
        let token = &self.tokens[self.idx];
        self.idx += 1;
        Some(token)
    }

    pub fn skip(&mut self, s: &str) {
        let token = self.cur_token();
        if !token.equal(s) {
            self.error_tok(token, &format!("expected '{}'", s));
        }
        self.next_token();
    }

    fn read_char(&mut self) {
        if self.rpos >= self.input.len() {
            self.pos = self.rpos;
            self.ch = '\0';
            return;
        }
        self.ch = self.input.chars().skip(self.rpos).next().unwrap();
        self.pos = self.rpos;
        self.rpos += 1;
    }

    fn read_num(&mut self) {
        let start = self.pos;
        while self.ch.is_digit(10) {
            self.read_char();
        }
        let literal = &self.input[start..self.pos];
        self.tokens.push(Token::new_num(
            literal.parse::<u32>().unwrap(), start, Rc::new(literal)
        ));
    }

    fn read_punct(&self, s: &str) -> usize {
        if  s.starts_with("==") || s.starts_with("!=") ||
            s.starts_with("<=") || s.starts_with(">=") {
            return 2;
        }

        if self.ch.is_ascii_punctuation() {
            1
        } else {
            0
        }
    }

    pub fn consume(&mut self, op: &str) -> bool {
        if self.idx >= self.tokens.len() {  
            return false;
        }
        let token = &self.tokens[self.idx];

        if token.equal(op) {
            self.next_token();
            return true;
        }

        return false;
    }

    pub fn cur_token(&self) -> &Token {
        &self.tokens[self.idx]
    }

    fn error_at(&self, loc: usize, s: &str) {
        eprintln!("{}", &self.input);
        eprint!("{:indent$}^ ", "", indent=loc);
        eprintln!("{}", s);
        process::exit(1);
    }

    pub fn error_tok(&self, token: &Token, s: &str) {
        self.error_at(token.loc, s);
    }
}

#[test]
fn test_tokenizer() {
    let mut tokenizer = Tokenizer::new(" 123 456\t789");
    tokenizer.tokenize();
    assert_eq!(*tokenizer.next_token().unwrap(), Token::new_num(123, 1, Rc::new("123")));
    assert_eq!(*tokenizer.next_token().unwrap(), Token::new_num(456, 5, Rc::new("456")));
    assert_eq!(*tokenizer.next_token().unwrap(), Token::new_num(789, 9, Rc::new("789")));
    assert_eq!(*tokenizer.next_token().unwrap(), Token::new(TokenKind::Eof, 12, Rc::new("")));
    assert_eq!(tokenizer.next_token(), None);
}

#[test]
fn test_consume() {
    let mut tokenizer = Tokenizer::new("(1+2)");
    tokenizer.tokenize();
    assert!(tokenizer.consume("("));
    assert!(tokenizer.consume("1"));
    assert!(tokenizer.consume("+"));
    assert!(tokenizer.consume("2"));
    assert!(tokenizer.consume(")"));
}