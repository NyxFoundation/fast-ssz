#![forbid(unsafe_code)]

pub struct Bookkeeping {
    bytes: Vec<u8>,
}

pub struct UserDrop {
    bytes: Vec<u8>,
}

impl Drop for UserDrop {
    fn drop(&mut self) {
        panic!("user destructor must not be erased");
    }
}

pub fn discard_bookkeeping(value: Bookkeeping) -> usize {
    value.bytes.len()
}

pub fn discard_nodes(values: Vec<[u8; 32]>) -> usize {
    values.len()
}

pub fn discard_optional_bytes(value: Option<Vec<Vec<u8>>>) -> bool {
    value.is_some()
}

pub fn discard_optional_user(value: Option<UserDrop>) -> bool {
    value.is_some()
}

pub fn discard_user_value(value: UserDrop) -> usize {
    value.bytes.len()
}
