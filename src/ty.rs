#[derive(Debug, PartialEq)]
pub enum Type {
    Int,
    Ptr(Box<Type>),
}

impl Type {
    pub fn is_integer(&self) -> bool {
        match self {
            Type::Int   =>  true,
            _           =>  false,
        }
    }

    pub fn is_ptr(&self) -> bool {
        match self {
            Type::Ptr(_)    =>  true,
            _               =>  false,
        }
    }
}