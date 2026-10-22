use libssz_derive::{HashTreeRoot, SszDecode, SszEncode};
use libssz_types::SszList;

#[derive(SszEncode, SszDecode, HashTreeRoot)]
pub struct Header {
    pub slot: u64,
    pub proposer_index: u64,
    pub parent_root: [u8; 32],
    pub state_root: [u8; 32],
    pub body_root: [u8; 32],
}

#[derive(SszEncode, SszDecode, HashTreeRoot)]
pub struct Mixed {
    pub slot: u64,
    pub payload: SszList<u8, 4096>,
    pub votes: SszList<u64, 1024>,
}

pub fn header() -> Header {
    Header {
        slot: 0x0102030405060708,
        proposer_index: 0x1122334455667788,
        parent_root: super::root_bytes(0),
        state_root: super::root_bytes(128),
        body_root: super::root_bytes(224),
    }
}
pub fn mixed() -> Mixed {
    Mixed {
        slot: 42,
        payload: vec![7; 4096].try_into().unwrap(),
        votes: vec![1; 1024].try_into().unwrap(),
    }
}
