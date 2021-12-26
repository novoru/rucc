use std::rc::Rc;
use crate::tokenizer::Token;

#[derive(Debug, Clone, PartialEq)]
pub struct Member {
    pub ty:     Type,
    pub name:   String,
    pub offset: u64,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypeKind {
    Void,
    Bool,
    Char,
    Short,
    Int,
    Long,
    Ptr,
    Function,
    Array,
    Struct,
    Union,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Type {
    pub kind:   TypeKind,
    pub name:   Option<Rc<Token>>,
    pub size:   u64,
    pub align:  u64,

    // Ptr or Array
    pub base:   Option<Box<Type>>,

    // Array
    pub len:    u64,
    
    // Function
    pub params: Vec<Type>,
    pub ret_ty: Option<Box<Type>>,
    pub is_definition:  bool,

    // Struct or Union
    pub members:    Vec<Box<Member>>,
}

pub fn ty_void(name: Option<Rc<Token>>) -> Type {
    Type {
        kind:           TypeKind::Void,
        name,
        size:           1,
        align:          1,
        base:           None,
        len:            0,
        params:         Vec::new(),
        ret_ty:         None,
        is_definition:  false,
        members:        Vec::new(),
    }
}

pub fn ty_bool(name: Option<Rc<Token>>) -> Type {
    Type {
        kind:           TypeKind::Bool,
        name,
        size:           1,
        align:          1,
        base:           None,
        len:            0,
        params:         Vec::new(),
        ret_ty:         None,
        is_definition:  false,
        members:        Vec::new(),
    }
}

pub fn ty_char(name: Option<Rc<Token>>) -> Type {
    Type {
        kind:           TypeKind::Char,
        name,
        size:           1,
        align:          1,
        base:           None,
        len:            0,
        params:         Vec::new(),
        ret_ty:         None,
        is_definition:  false,
        members:        Vec::new(),
    }
}

pub fn ty_short(name: Option<Rc<Token>>) -> Type {
    Type {
        kind:           TypeKind::Short,
        name,
        size:           2,
        align:          2,
        base:           None,
        len:            0,
        params:         Vec::new(),
        ret_ty:         None,
        is_definition:  false,
        members:        Vec::new(),
    }
}

pub fn ty_int(name: Option<Rc<Token>>) -> Type {
    Type {
        kind:           TypeKind::Int,
        name,
        size:           4,
        align:          4,
        base:           None,
        len:            0,
        params:         Vec::new(),
        ret_ty:         None,
        is_definition:  false,
        members:        Vec::new(),
    }
}

pub fn ty_long(name: Option<Rc<Token>>) -> Type {
    Type {
        kind:           TypeKind::Long,
        name,
        size:           8,
        align:          8,
        base:           None,
        len:            0,
        params:         Vec::new(),
        ret_ty:         None,
        is_definition:  false,
        members:        Vec::new(),
    }
}

pub fn ty_ptr(name: Option<Rc<Token>>, base: Option<Box<Type>>) -> Type {
    Type {
        kind:           TypeKind::Ptr,
        name,
        size:           8,
        align:          8,
        base:           base,
        len:            0,
        params:         Vec::new(),
        ret_ty:         None,
        is_definition:  false,
        members:        Vec::new(),
    }
}

pub fn ty_function(name: Option<Rc<Token>>, params: Vec<Type>, ret_ty: Option<Box<Type>>) -> Type {
    Type {
        kind:           TypeKind::Function,
        name,
        size:           0,
        align:          1,
        base:           None,
        len:            0,
        params,
        ret_ty,
        is_definition:  false,
        members:        Vec::new(),
    }
}

pub fn ty_array(name: Option<Rc<Token>>, base: Option<Box<Type>>, size: u64, len: u64, align: u64) -> Type {
    Type {
        kind:           TypeKind::Array,
        name,
        size:           size,
        align:          align,
        base:           base,
        len:            len,
        params:         Vec::new(),
        ret_ty:         None,
        is_definition:  false,
        members:        Vec::new(),
    }
}

pub fn ty_struct(name: Option<Rc<Token>>, members: Vec<Box<Member>>) -> Type {
    Type {
        kind:           TypeKind::Struct,
        name,
        size:           0,
        align:          1,
        base:           None,
        len:            0,
        params:         Vec::new(),
        ret_ty:         None,
        is_definition:  false,
        members,
    }
}

pub fn ty_union(name: Option<Rc<Token>>, members: Vec<Box<Member>>) -> Type {
    Type {
        kind:           TypeKind::Union,
        name,
        size:           0,
        align:          1,
        base:           None,
        len:            0,
        params:         Vec::new(),
        ret_ty:         None,
        is_definition:  false,
        members,
    }
}

impl Type {
    pub fn is_num(&self) -> bool {
        matches!(self.kind,
            TypeKind::Bool | TypeKind::Char | TypeKind::Short |
            TypeKind::Int  | TypeKind::Long
        )
    }

    pub fn is_ptr(&self) -> bool {
        matches!(self.kind,
            TypeKind::Array | TypeKind::Ptr
        )
    }
}