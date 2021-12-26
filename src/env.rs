use std::rc::Rc;
use std::cell::RefCell;

use crate::tokenizer::Token;
use crate::ty::Type;
use crate::obj::*;
use crate::scope::Scope;

#[derive(Debug, Clone, PartialEq)]
pub struct Env {
    pub parent:     Option<Rc<RefCell<Env>>>,
    pub objs:       Vec<Rc<RefCell<Obj>>>,   // variables
    pub stack_size: u64,
}

pub fn align_to(n: u64, align: u64) -> u64 {
    (n + align - 1) / align * align
}

impl Env {
    pub fn add_var(&mut self, ty: &Type, init_data: Option<Vec<char>>, token: &Token, is_local: bool, scope: &Scope) -> Rc<RefCell<Obj>> {
        if scope.find_svar(&ty.name.as_ref().unwrap().literal).is_some() {
            token.error(&format!("redefinition of '{}'", &ty.name.as_ref().unwrap().literal));
        }

        let mut offset = ty.size;
        for obj in &mut self.objs {
            obj.borrow_mut().offset += ty.size;
            offset += obj.borrow().ty.size;
        }

        let obj = if is_local {
            Rc::new(RefCell::new( new_lvar(ty.size, ty.clone())))
        } else {
            Rc::new(RefCell::new( new_gvar(ty.size, ty.clone(), init_data)))
        };

        self.objs.push(Rc::clone(&obj));
        self.stack_size = align_to(offset, 16);

        obj
    }

    // find variable from local and global
    pub fn find_var(&self, name: &str) -> Option<Rc<RefCell<Obj>>> {
        for obj in self.objs.iter().rev() {
            if obj.borrow().ty.name.as_ref().unwrap().literal == name {
                return Some(Rc::clone(obj))
            }
        }

        if let Some(scope) = &self.parent {
            return scope.borrow().find_var(name);
        }

        None
    }
    
    // find variable from local
    pub fn find_lvar(&self, name: &str) -> Option<Rc<RefCell<Obj>>> {
        for obj in &self.objs {
            if obj.borrow().ty.name.as_ref().unwrap().literal == name {
                return Some(Rc::clone(obj))
            }
        }

        None
    }

    pub fn add_parent(&mut self, parent: &Rc<RefCell<Env>>) {
        self.parent = Some(Rc::clone(parent));
    }
}
