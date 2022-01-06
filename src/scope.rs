use std::rc::Rc;
use std::cell::RefCell;
use std::collections::HashMap;

use crate::ty::Type;
use crate::obj::Obj;

#[derive(Debug)]
pub struct Scope {
    pub parent:     Option<Rc<RefCell<Scope>>>,
    pub objs:       Vec<Rc<RefCell<Obj>>>,
    pub tags:       HashMap<String, Rc<RefCell<Type>>>, // struct tags, union or enum tags
    pub typedefs:   HashMap<String, Rc<RefCell<Type>>>,              // typedef
}

impl Scope {
    pub fn find_lvar(&self, name: &str) -> Option<Rc<RefCell<Obj>>> {
        for obj in &self.objs {
            if obj.borrow().name == name {
                return Some(Rc::clone(obj));
            }
        }

        if let Some(parent) = &self.parent {
            return parent.borrow().find_lvar(name);
        }

        None
    }

    // find variable from scope
    pub fn find_svar(&self, name: &str) -> Option<Rc<RefCell<Obj>>> {
        for obj in &self.objs {
            if obj.borrow().name == name {
                return Some(Rc::clone(obj));
            }
        }

        None
    }

    pub fn find_tag(&self, name: String) -> Option<Rc<RefCell<Type>>> {
        if let Some(tag) = self.tags.get(&name) {
            Some(tag.clone())
        } else {
            None
        }
    }

    pub fn find_typedef(&self, name: String) -> Option<Rc<RefCell<Type>>> {
        if let Some(typedef) = self.typedefs.get(&name) {
            return Some(typedef.clone());
        }

        if let Some(parent) = &self.parent {
            return parent.borrow().find_typedef(name);
        }

        None
    }
}
