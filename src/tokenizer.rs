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
    kind:       TokenKind,
    loc:        usize,
    val:        Option<u32>,
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
        loop {
            self.skip();

            match self.ch {
                '0' ..= '9' =>  self.read_num(),
                '+'         |
                '-'         |
                '*'         |
                '/'         =>  {
                    self.tokens.push(Token::new(
                        TokenKind::Punct, self.pos, Rc::new(&self.input[self.pos..self.pos+1]
                    )));
                    self.read_char();
                }
                '\0'        =>  {
                    self.tokens.push(Token::new(
                        TokenKind::Eof, self.pos, Rc::new("")
                    ));
                    break;
                },
                _           =>  panic!(),
            }
        }
    }

    pub fn next_token(&mut self) -> Option<&Token> {
        if self.idx >= self.tokens.len() {
            return None;
        }
        let token = &self.tokens[self.idx];
        self.idx += 1;
        Some(token)
    }

    fn skip(&mut self) {
        while self.ch.is_whitespace() {
            self.read_char();
        }
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