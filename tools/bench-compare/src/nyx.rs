use nyx_ssz::{
    bytecollections::{ByteList, ByteVector},
    collections::{list, List},
};

#[derive(nyx_ssz::Ssz)]
pub struct Header {
    pub slot: u64,
    pub proposer_index: u64,
    pub parent_root: ByteVector<32>,
    pub state_root: ByteVector<32>,
    pub body_root: ByteVector<32>,
}

#[derive(nyx_ssz::Ssz)]
pub struct Mixed {
    pub slot: u64,
    pub payload: ByteList<4096>,
    pub votes: List<u64, 1024>,
}

pub fn header() -> Header {
    Header {
        slot: 0x0102030405060708,
        proposer_index: 0x1122334455667788,
        parent_root: ByteVector::from_bytes(super::root_bytes(0).to_vec()).unwrap(),
        state_root: ByteVector::from_bytes(super::root_bytes(128).to_vec()).unwrap(),
        body_root: ByteVector::from_bytes(super::root_bytes(224).to_vec()).unwrap(),
    }
}

pub fn mixed() -> Mixed {
    Mixed {
        slot: 42,
        payload: ByteList::from_bytes(vec![7; 4096]).unwrap(),
        votes: list(vec![1; 1024]).unwrap(),
    }
}
