#[derive(Debug, Clone, PartialEq)]
pub struct Member {
    pub ty:     Type,
    pub name:   String,
    pub offset: u64,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    Char        { name: Option<String>, size: u64, align: u64 },
    Int         { name: Option<String>, size: u64, align: u64 },
    Long        { name: Option<String>, size: u64, align: u64 },
    Ptr         { name: Option<String>, base: Box<Type>, size: u64, align: u64 },
    Function    { name: Option<String>, params: Option<Vec<Type>> ,ret_ty: Box<Type>, align: u64 },
    Array       { name: Option<String>, base: Box<Type>, size: u64, len: u64, align: u64 },
    Struct      { name: Option<String>, members: Vec<Box<Member>>, size: u64, align: u64 },
    Union       { name: Option<String>, members: Vec<Box<Member>>, size: u64, align: u64 },
}

pub fn ty_char(name: Option<String>) -> Type {
    Type::Char { name: name, size: 1, align: 1 }
}

pub fn ty_int(name: Option<String>) -> Type {
    Type::Int { name: name, size: 4, align: 4 }
}

pub fn ty_long(name: Option<String>) -> Type {
    Type::Int { name: name, size: 8, align: 8 }
}

impl Type {
    pub fn is_num(&self) -> bool {
        self.is_char() || self.is_integer() || self.is_long()
    }

    pub fn is_char(&self) -> bool {
        match self {
            Type::Char {..} =>  true,
            _               =>  false,
        }
    }

    pub fn is_integer(&self) -> bool {
        match self {
            Type::Int {..}  =>  true,
            _               =>  false,
        }
    }

    pub fn is_long(&self) -> bool {
        match self {
            Type::Long {..} =>  true,
            _               =>  false,
        }
    }

    pub fn is_ptr(&self) -> bool {
        match self {
            Type::Ptr   {..}    |
            Type::Array {..}    =>  true,
            _                   =>  false,
        }
    }

    pub fn set_size(&mut self, sz: u64) {
        match self {
            Type::Char      { size, .. }    |
            Type::Int       { size, .. }    |
            Type::Long      { size, .. }    |
            Type::Ptr       { size, .. }    |
            Type::Array     { size, .. }    |
            Type::Struct    { size, .. }    |
            Type::Union     { size, .. }    => *size = sz,
            _   => panic!("dont have the size field: {:?}", self),
        }
    }

    pub fn get_size(&self) -> u64 {
        match self {
            Type::Char      { size, .. }    |
            Type::Int       { size, .. }    |
            Type::Ptr       { size, .. }    |
            Type::Array     { size, .. }    |
            Type::Struct    { size, .. }    |
            Type::Union     { size, .. }    => *size,
            _   => panic!("dont have the size field: {:?}", self),
        }
    }

    pub fn get_name(&self) -> Option<String> {
        match self {
            Type::Char      { name, .. }    |
            Type::Int       { name, .. }    |
            Type::Long      { name, .. }    |
            Type::Ptr       { name, .. }    |
            Type::Function  { name, .. }    |
            Type::Array     { name, .. }    |
            Type::Struct    { name, .. }    |
            Type::Union     { name, .. }    =>  name.clone(),
        }
    }

    pub fn set_name(&mut self, s: String) {
        match self {
            Type::Char      { name, .. }    |
            Type::Int       { name, .. }    |
            Type::Long      { name, .. }    |
            Type::Ptr       { name, .. }    |
            Type::Function  { name, .. }    |
            Type::Array     { name, .. }    |
            Type::Struct    { name, .. }    |
            Type::Union     { name, .. }   =>  *name = Some(s),
        }
    }

    pub fn get_base(&mut self) -> Type {
        match self {
            Type::Ptr   { base, .. }    |
            Type::Array { base, .. }    =>  *base.clone(),
            _   => panic!("dont have the base field: {:?}", self),
        }
    }

    pub fn set_align(&mut self, val: u64) {
        match self {
            Type::Char      { align, .. }   |
            Type::Int       { align, .. }   |
            Type::Long      { align, .. }   |
            Type::Ptr       { align, .. }   |
            Type::Function  { align, .. }   |
            Type::Array     { align, .. }   |
            Type::Struct    { align, .. }   |
            Type::Union     { align, .. }   =>  *align = val,
        }
    }

    pub fn get_align(&self) -> u64 {
        match self {
            Type::Char      { align, .. }   |
            Type::Int       { align, .. }   |
            Type::Long      { align, .. }   |
            Type::Ptr       { align, .. }   |
            Type::Function  { align, .. }   |
            Type::Array     { align, .. }   |
            Type::Struct    { align, .. }   |
            Type::Union     { align, .. }   =>  *align,
        }
    }
}