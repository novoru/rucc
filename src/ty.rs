pub static TY_INT: &'static Type = &Type::Int { size: 8 };

#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    Int { size: u32 },
    Ptr { base: Box<Type>, size: u32 },
}

pub fn ty_int() -> Type {
    Type::Int { size: 8 }
}

impl Type {
    pub fn is_integer(&self) -> bool {
        match self {
            Type::Int {..}  =>  true,
            _               =>  false,
        }
    }

    pub fn is_ptr(&self) -> bool {
        match self {
            Type::Ptr {..}  =>  true,
            _               =>  false,
        }
    }

    pub fn get_size(&self) -> u32 {
        match self {
            Type::Int { size }          |
            Type::Ptr { base:_, size }  => *size,
        }
    }
}