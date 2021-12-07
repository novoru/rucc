use std::process;

static KWDS: &'static [&str] = &["return", "if", "for", "while"];

#[derive(Debug, Clone, PartialEq)]
pub enum TokenKind {
    Ident,      // Identifiers
    Keyword,    // Keywords
    Num,        // Numeric literals
    Punct,      // Punctuators
    Eof,        // End-of-file markers
}

#[derive(Debug, Clone, PartialEq)]
pub struct Token {
    pub kind:       TokenKind,
    loc:            usize,
    pub val:        Option<u32>,
    pub literal:    String,
}

impl Token {
    pub fn new(kind: TokenKind, loc: usize, s: &str) -> Self {
        Token {
            kind:       kind,
            loc:        loc,
            val:        None,
            literal:    s.to_string(),
        }
    }

    pub fn new_num(val: u32, loc: usize, s: &str) -> Self {
        Token {
            kind:       TokenKind::Num,
            loc:        loc,
            val:        Some(val),
            literal:    s.to_string(),
        }
    }

    pub fn equal(&self, op: &str) -> bool {
        self.literal == op
    }
}

#[derive(Debug)]
pub struct Tokenizer {
    input:  String,
    pos:    usize,
    rpos:   usize,
    idx:    usize,
    tokens: Vec<Token>,
    ch:     char,
}

impl Tokenizer {
    pub fn new(input: &str) -> Self {
        Self {
            input:  input.to_string(),
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
            // Skip whitespace characters.
            if self.ch.is_whitespace() {
                self.read_char();
                continue;
            }

            // Numeric literal
            if self.ch.is_digit(10) {
                self.read_num();
                continue;
            }

            // Identifiers or Keywords
            if self.is_ident1(self.ch) {
                let start = self.pos;

                loop {
                    self.read_char();
                    if !self.is_ident2(self.ch) {
                        break;
                    }
                }

                if self.is_keywords(&self.input[start..self.pos]) {
                    self.tokens.push(Token::new(
                        TokenKind::Keyword, start, &self.input[start..self.pos]
                    ));
                } else {
                    self.tokens.push(Token::new(
                        TokenKind::Ident, start, &self.input[start..self.pos]
                    ));
                }

                continue;
            }

            let punct_len = self.read_punct(&self.input[self.pos..self.input.len()]);
            if punct_len != 0 {
                self.tokens.push(Token::new(
                    TokenKind::Punct, self.pos, &self.input[self.pos..self.pos+punct_len]
                ));
                for _ in 0..punct_len {
                    self.read_char();
                }
                continue;
            }

            self.error_at(self.pos, "invalide token");
        }
        self.tokens.push(Token::new(
            TokenKind::Eof, self.pos, ""
        ));
    }

    pub fn next_token(&mut self) -> Option<Token> {
        if self.idx >= self.tokens.len() {
            return None;
        }
        let token = &self.tokens[self.idx];
        self.idx += 1;
        Some(token.clone())
    }

    pub fn peek_token(&self, s: &str) -> bool {
        if self.idx >= self.tokens.len() {
            return false;
        }
        self.tokens[self.idx+1].equal(s)
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
            literal.parse::<u32>().unwrap(), start, literal
        ));
    }

    // Returns true if c is valid as the first character of an identifier.
    fn is_ident1(&self, c: char) -> bool {
        matches!(c, 'A' ..= 'Z' | 'a' ..= 'z' | '_')
    }

    // Returns true if c is valid as a non-first character of an identifier.
    fn is_ident2(&self, c: char) -> bool {
        self.is_ident1(c) || matches!(c, '0' ..= '9')
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

    fn is_keywords(&self, s: &str) -> bool {
        for kwd in KWDS.iter() {
            if &s == kwd {
                return true;
            }
        }
        false
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
    assert_eq!(tokenizer.next_token().unwrap(), Token::new_num(123, 1, "123"));
    assert_eq!(tokenizer.next_token().unwrap(), Token::new_num(456, 5, "456"));
    assert_eq!(tokenizer.next_token().unwrap(), Token::new_num(789, 9, "789"));
    assert_eq!(tokenizer.next_token().unwrap(), Token::new(TokenKind::Eof, 12, ""));
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

#[test]
fn test_tokenize_kwds() {
    let mut tokenizer = Tokenizer::new("for for1");
    tokenizer.tokenize();
    assert_eq!(
        tokenizer.next_token().unwrap(),
        Token {
            kind:       TokenKind::Keyword,
            loc:        0,
            val:        None,
            literal:    "for".to_string(),
        }
    );
    assert_eq!(
        tokenizer.next_token().unwrap(),
        Token {
            kind:       TokenKind::Ident,
            loc:        4,
            val:        None,
            literal:    "for1".to_string(),
        }
    );
}