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

    // Global variable
    pub is_function:    bool,
    pub init_data:      Option<Vec<char>>,

    // Function
    pub params: Option<Env>,
    pub body:   Vec<Box<Node>>,
    pub locals: Option<Rc<RefCell<Env>>>,
    pub ret_ty: Option<Type>,
}

pub fn new_lvar(offset: u64, ty: Type) -> Obj {
    Obj {
        offset,
        ty,
        is_local:       true,
        is_function:    false,
        init_data:      None,
        params:         None,
        body:           Vec::new(),
        locals:         None,
        ret_ty:         None,
    }
}


pub fn new_gvar(offset: u64, ty: Type, init_data: Option<Vec<char>>) -> Obj {
    Obj {
        offset,
        ty,
        is_local:       false,
        is_function:    false,
        init_data,
        params:         None,
        body:           Vec::new(),
        locals:         None,
        ret_ty:         None,
    }
}