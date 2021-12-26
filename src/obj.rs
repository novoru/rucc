use crate::ty::Type;

#[derive(Debug, Clone, PartialEq)]
pub struct Obj {
    pub offset:     u64,
    pub ty:         Type,
    pub is_local:   bool,
    pub init_data:  Option<Vec<char>> // Global variable
}
