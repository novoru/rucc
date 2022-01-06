use std::rc::Rc;
use std::cell::RefCell;
use crate::tokenizer::Token;
use crate::env::align_to;

#[derive(Debug, Clone, PartialEq)]
pub struct Member {
    pub ty:     Rc<RefCell<Type>>,
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
    Enum,
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
    pub base:   Option<Rc<RefCell<Type>>>,

    // Array
    pub len:    u64,
    
    // Function
    pub params: Vec<Rc<RefCell<Type>>>,
    pub ret_ty: Option<Rc<RefCell<Type>>>,
    pub is_definition:  bool,

    // Struct or Union or Enum
    pub members:    Vec<Box<Member>>,
    pub is_incomplete:  bool,
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
        is_incomplete:  false,
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
        is_incomplete:  false,
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
        is_incomplete:  false,
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
        is_incomplete:  false,
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
        is_incomplete:  false,
    }
}

pub fn ty_enum(name: Option<Rc<Token>>) -> Type {
    Type {
        kind:           TypeKind::Enum,
        name,
        size:           4,
        align:          4,
        base:           None,
        len:            0,
        params:         Vec::new(),
        ret_ty:         None,
        is_definition:  false,
        members:        Vec::new(),
        is_incomplete:  false,
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
        is_incomplete:  false,
    }
}

pub fn ty_ptr(name: Option<Rc<Token>>, base: Option<Rc<RefCell<Type>>>) -> Type {
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
        is_incomplete:  false,
    }
}

pub fn ty_function(name: Option<Rc<Token>>, params: Vec<Rc<RefCell<Type>>>, ret_ty: Option<Rc<RefCell<Type>>>) -> Type {
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
        is_incomplete:  false,
    }
}

pub fn ty_array(name: Option<Rc<Token>>, base: Option<Rc<RefCell<Type>>>, size: u64, len: u64, align: u64) -> Type {
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
        is_incomplete:  false,
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
        is_incomplete:  false,
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
        is_incomplete:  false,
    }
}

impl Type {
    pub fn is_num(&self) -> bool {
        matches!(self.kind,
            TypeKind::Bool | TypeKind::Char | TypeKind::Short |
            TypeKind::Int  | TypeKind::Long | TypeKind::Enum
        )
    }

    pub fn is_ptr(&self) -> bool {
        matches!(self.kind,
            TypeKind::Array | TypeKind::Ptr
        )
    }

    pub fn assign_offsets(&mut self) {
        let mut offset = 0;
        for member in self.members.iter_mut() {
            offset = align_to(offset, member.ty.borrow().align);
            member.offset = offset;
            offset += member.ty.borrow().size;

            if self.align < member.ty.borrow().align {
                self.align = member.ty.borrow().align;
            }
        }

        self.size = align_to(offset, self.align);
    }
}

pub fn get_common_type(ty1: Rc<RefCell<Type>>, ty2: Rc<RefCell<Type>>) -> Rc<RefCell<Type>> {
    if let Some(base) = &ty1.borrow().base {
        let name = if let Some(token) = &base.borrow().name {
            Some(Rc::clone(&token))
        } else {
            None
        };
        return Rc::new(RefCell::new(ty_ptr(name, Some(base.clone()))));
    }

    if ty1.borrow().size == 8 || ty2.borrow().size == 8 {
        return Rc::new(RefCell::new(ty_long(None)));
    }

    Rc::new(RefCell::new(ty_int(None)))
}