use std::process;
use crate::ty::*;

static KWDS: &'static [&str] = &[
    "return", "if", "for", "while", "int", "sizeof", "char", "struct",
];

#[derive(Debug, Clone, PartialEq)]
pub enum TokenKind {
    Ident,      // Identifiers
    Keyword,    // Keywords
    Str,        // String
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
    pub ty:         Option<Type>,   // Used if TokenKind::Str
    line:           String,
    lineno:         usize,
    indent:         usize,
}

impl Token {
    pub fn new(kind: TokenKind, loc: usize, s: &str, line: String, lineno: usize, indent: usize) -> Self {
        Token {
            kind:       kind,
            loc:        loc,
            val:        None,
            literal:    s.to_string(),
            ty:         None,
            line:       line,
            lineno:     lineno,
            indent:     indent,
        }
    }

    pub fn new_num(val: u32, loc: usize, s: &str, line: String, lineno: usize, indent: usize) -> Self {
        Token {
            kind:       TokenKind::Num,
            loc:        loc,
            val:        Some(val),
            literal:    s.to_string(),
            ty:         None,
            line:       line,
            lineno:     lineno,
            indent:     indent,
        }
    }

    pub fn new_str(loc: usize, s: &str, len: u32, line: String, lineno: usize, indent: usize) -> Self {
        Token {
            kind:       TokenKind::Str,
            loc:        loc,
            val:        None,
            literal:    s.to_string(),
            ty:         Some(Type::Array {
                name:   None,
                base:   Box::new(ty_char(None)),
                size:   len,
                len:    len,
            }),
            line:       line,
            lineno:     lineno,
            indent:     indent,
        }
    }

    pub fn equal(&self, op: &str) -> bool {
        self.literal == op
    }

    pub fn error(&self, s: &str) {
        eprintln!("{}", self.line);
        eprint!("{:indent$}^ ", "", indent=self.indent);
        eprintln!("{}", s);
        process::exit(1);
    }
}

#[derive(Debug)]
pub struct Tokenizer {
    input:  String,
    pos:    usize,
    rpos:   usize,
    pub idx:    usize,
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
            // Skip line comments.
            if self.input[self.pos..].to_string().starts_with("//") {
                self.read_char();
                self.read_char();
                while self.ch != '\n' {
                    self.read_char();
                }
                continue;
            }

            // Skip block comments.
            if self.input[self.pos..].to_string().starts_with("/*") {
                let loc = self.pos;
                self.read_char();
                self.read_char();
                while !self.input[self.pos..].to_string().starts_with("*/") {
                    if self.ch == '\0' {
                        self.error_at(loc, "unclosed block comment");
                    }
                    self.read_char();
                }
                self.read_char();
                self.read_char();
                continue;
            }

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

            // String literal
            if self.ch == '"' {
                self.read_string_literal();
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
                        TokenKind::Keyword,
                        start,
                        &self.input[start..self.pos],
                        self.get_line(start),
                        self.get_lineno(start),
                        self.get_indent(start),
                    ));
                } else {
                    self.tokens.push(Token::new(
                        TokenKind::Ident,
                        start,
                        &self.input[start..self.pos],
                        self.get_line(start),
                        self.get_lineno(start),
                        self.get_indent(start),
                    ));
                }

                continue;
            }

            let start = self.pos;
            let punct_len = self.read_punct(&self.input[self.pos..self.input.len()]);
            if punct_len != 0 {
                self.tokens.push(Token::new(
                    TokenKind::Punct,
                    self.pos,
                    &self.input[self.pos..self.pos+punct_len],
                    self.get_line(start),
                    self.get_lineno(start),
                    self.get_indent(start),
                ));
                for _ in 0..punct_len {
                    self.read_char();
                }
                continue;
            }

            self.error_at(self.pos, "invalide token");
        }
        self.tokens.push(Token::new(
            TokenKind::Eof,
            self.pos,
            "",
            self.get_line(self.pos),
            self.get_lineno(self.pos),
            self.get_indent(self.pos),
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
            token.error(&format!("expected '{}'", s));
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
            literal.parse::<u32>().unwrap(),
            start,
            literal,
            self.get_line(start),
            self.get_lineno(start),
            self.get_indent(start),
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

    fn read_escape_char(&mut self) -> char {
        // Read an octal number.
        if matches!(self.ch, '0' ..= '7') {
            let mut c = self.ch.to_digit(8).unwrap();
            self.read_char();
            if matches!(self.ch, '0' ..= '7') {
                c = (c << 3) + self.ch.to_digit(8).unwrap();
                self.read_char();
                if matches!(self.ch, '0' ..= '7') {
                    c = (c << 3) + self.ch.to_digit(8).unwrap();
                    self.read_char();
                }
            }

            return std::char::from_u32(c).unwrap();
        }

        if self.ch == 'x' {
            self.read_char();
            if !self.ch.is_digit(16) {
                self.error_at(self.pos, "invalid hex escape sequence");
            }

            let mut c = 0;
            while self.ch.is_digit(16) {
                c = (c << 4) + self.ch.to_digit(16).unwrap();
                self.read_char();
            }

            return std::char::from_u32(c).unwrap();
        }

        let ch = match self.ch {
            'a' =>  '\x07',
            'b' =>  '\x08',
            't' =>  '\t',
            'n' =>  '\n',
            'v' =>  '\x0B',
            'f' =>  '\x0C',
            'r' =>  '\r',
            // [GNU] \e for the ASCII escape character is a GNU C extension.
            'e' =>  '\x1B',
            _   =>  self.ch,
        };

        self.read_char();

        ch
    }

    fn read_string_literal(&mut self) {
        self.read_char();
        let start = self.pos;
        let mut s = String::new();

        while self.ch != '"' {
            if self.ch == '\\' {
                self.read_char();
                s.push(self.read_escape_char());
            } else {
                s.push(self.ch);
                self.read_char();
            }
        }
        self.read_char();
        s.push('\0');
        self.tokens.push(Token::new_str(
            start,
            &s,
            s.chars().count() as u32,
            self.get_line(start),
            self.get_lineno(start),
            self.get_indent(start),
        ));
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
        let idx = if self.idx >= self.tokens.len() {
            self.tokens.len()-1
        } else {
            self.idx
        };

        &self.tokens[idx]
    }

    fn get_line(&self, loc: usize) -> String {
        let mut line = 0;

        for (i, ch) in self.input.chars().rev().skip(self.input.len()-loc).enumerate() {
            if ch =='\n' && i != 0 {
                line = loc - i;
                break;
            }
        }

        let mut end = if loc >= self.input.len() {
            loc
        } else {
            0
        };

        for (i, ch) in self.input.chars().skip(loc).enumerate() {
            if ch == '\n' || ch == '\0' {
                end = i + loc;
                break;
            }
        }

        self.input[line..end].to_string().replace("\n", "")
    }

    fn get_lineno(&self, loc: usize) -> usize {
        let mut lineno = 1;
        for (i, ch) in self.input.chars().enumerate() {
            if i == loc {
                break;
            }
            if ch == '\n' {
                lineno += 1;
            }
        }
        
        lineno
    }

    fn get_indent(&self, mut loc: usize) -> usize {
        if loc >= self.input.len() {
            loc = self.input.len()-1;
        }
        
        let mut line = 0;

        for (i, ch) in self.input.chars().rev().skip(self.input.len()-loc).enumerate() {
            if ch =='\n' && i != 0 {
                line = loc - i;
                break;
            }
        }

        loc-line
    }

    fn error_at(&self, loc: usize, s: &str) {
        let mut line = 0;

        for (i, ch) in self.input.chars().rev().skip(self.input.len()-loc).enumerate() {
            if ch =='\n' && i != 0 {
                line = loc - i;
                break;
            }
        }

        let mut end = 0;

        for (i, ch) in self.input.chars().skip(loc).enumerate() {
            if ch == '\n' || ch == '\0' {
                end = i + loc;
                break;
            }
        }

        eprintln!("{}", self.input[line..end].to_string().replace("\n", ""));
        eprint!("{:indent$}^ ", "", indent=loc-line);
        eprintln!("{}", s);
        process::exit(1);
    }

    pub fn error_tok(&self, token: &Token, s: &str) {
        self.error_at(token.loc, s);
    }
}
