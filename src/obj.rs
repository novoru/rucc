use std::rc::Rc;
use std::cell::RefCell;

use crate::tokenizer::Token;
use crate::ty::*;
use crate::env::Env;
use crate::node::Node;

#[derive(Debug, Clone, PartialEq)]
pub struct Obj {
    // Local variables
    pub offset:     u64,
    pub ty:         Rc<RefCell<Type>>,  // Type
    pub is_local:   bool,               // local or global/function
    pub name:       String,             // Variable name

    // Global variable of function
    pub is_function:    bool,
    pub is_definition:  bool,

    // Global variable
    pub init_data:      Option<Vec<char>>,

    // Function
    pub params: Option<Env>,
    pub body:   Vec<Box<Node>>,
    pub locals: Option<Rc<RefCell<Env>>>,

    // Enum constant
    pub enum_val:   u64,
}

pub fn new_lvar(offset: u64, name: String, ty: Rc<RefCell<Type>>) -> Obj {
    Obj {
        offset,
        ty,
        is_local:       true,
        name,
        is_function:    false,
        is_definition:  false,
        init_data:      None,
        params:         None,
        body:           Vec::new(),
        locals:         None,
        enum_val:       0,
    }
}


pub fn new_gvar(offset: u64, name: String, ty: Rc<RefCell<Type>>, init_data: Option<Vec<char>>) -> Obj {
    Obj {
        offset,
        ty,
        is_local:       false,
        name,
        is_function:    false,
        is_definition:  false,
        init_data,
        params:         None,
        body:           Vec::new(),
        locals:         None,
        enum_val:       0,
    }
}

pub fn obj_function(name: String, ty: Rc<RefCell<Type>>) -> Obj {
    Obj {
        offset:         0,
        ty,
        name,
        is_local:       false,
        is_function:    true,
        is_definition:  false,
        init_data:      None,
        params:         None,
        body:           Vec::new(),
        locals:         None,
        enum_val:       0,
    }
}

pub fn enum_const(name: Token, val: u64) -> Obj {
    Obj {
        offset:         0,
        ty:             Rc::new(RefCell::new(ty_enum(Some(Rc::new(name.clone()))))),
        is_local:       true,
        name:           name.literal,
        is_function:    true,
        is_definition:  false,
        init_data:      None,
        params:         None,
        body:           Vec::new(),
        locals:         None,
        enum_val:       val,
    }
}