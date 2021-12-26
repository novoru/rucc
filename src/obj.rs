use std::rc::Rc;
use std::cell::RefCell;

use crate::ty::Type;
use crate::env::Env;
use crate::node::Node;

#[derive(Debug, Clone, PartialEq)]
pub struct Obj {
    // Local variables
    pub offset:     u64,
    pub ty:         Type,   // Type
    pub is_local:   bool,   // local or global/function

    // Global variable of function
    pub is_function:    bool,
    pub is_definition:  bool,

    // Global variable
    pub init_data:      Option<Vec<char>>,

    // Function
    pub params: Option<Env>,
    pub body:   Vec<Box<Node>>,
    pub locals: Option<Rc<RefCell<Env>>>,
}

pub fn new_lvar(offset: u64, ty: Type) -> Obj {
    Obj {
        offset,
        ty,
        is_local:       true,
        is_function:    false,
        is_definition:  false,
        init_data:      None,
        params:         None,
        body:           Vec::new(),
        locals:         None,
    }
}


pub fn new_gvar(offset: u64, ty: Type, init_data: Option<Vec<char>>) -> Obj {
    Obj {
        offset,
        ty,
        is_local:       false,
        is_function:    false,
        is_definition:  false,
        init_data,
        params:         None,
        body:           Vec::new(),
        locals:         None,
    }
}

pub fn obj_function(ty: Type) -> Obj {
    Obj {
        offset:         0,
        ty,
        is_local:       false,
        is_function:    true,
        is_definition:  false,
        init_data:      None,
        params:         None,
        body:           Vec::new(),
        locals:         None,
    }
}