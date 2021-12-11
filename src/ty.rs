#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    Char { name: Option<String>, size: u32 },
    Int { name: Option<String>, size: u32 },
    Ptr { name: Option<String>, base: Box<Type>, size: u32 },
    Function { name: Option<String>, params: Option<Vec<Type>> ,ret_ty: Box<Type> },
    Array { name: Option<String>, base: Box<Type>, size: u32, len: u32 },
}

pub fn ty_char(name: Option<String>) -> Type {
    Type::Char { name: name, size: 1 }
}

pub fn ty_int(name: Option<String>) -> Type {
    Type::Int { name: name, size: 8 }
}

impl Type {
    pub fn is_num(&self) -> bool {
        self.is_char() || self.is_integer()
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

    pub fn is_ptr(&self) -> bool {
        match self {
            Type::Ptr {..}      |
            Type::Array {..}    =>  true,
            _                   =>  false,
        }
    }

    pub fn get_size(&self) -> u32 {
        match self {
            Type::Char { size, .. }     |
            Type::Int { size, .. }      |
            Type::Ptr { size, .. }      |
            Type::Array { size, .. }    => *size,
            _   => panic!("dont have the size field: {:?}", self),
        }
    }

    pub fn get_name(&self) -> Option<String> {
        match self {
            Type::Char { name, .. }     |
            Type::Int { name, .. }      |
            Type::Ptr { name,.. }       |
            Type::Function { name, .. } |
            Type::Array { name, .. }    =>  name.clone(),
        }
    }

    pub fn set_name(&mut self, s: String) {
        match self {
            Type::Char { name, .. }     |
            Type::Int { name, .. }      |
            Type::Ptr { name,.. }       |
            Type::Function { name, .. } |
            Type::Array { name, .. }    =>  *name = Some(s),
        }
    }

    pub fn get_base(&mut self) -> Type {
        match self {
            Type::Ptr { base, .. }  |
            Type::Array {base, .. } =>  *base.clone(),
            _   => panic!("dont have the base field: {:?}", self),
        }
    }
}