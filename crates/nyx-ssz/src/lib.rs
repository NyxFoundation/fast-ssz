#![doc = include_str!("../../../README.md")]
#![forbid(unsafe_code)]
#![cfg_attr(feature = "verification", feature(register_tool))]
#![cfg_attr(feature = "verification", register_tool(verify))]

pub use ruint::aliases::U256;

mod bit_codec;
mod bit_storage;
pub mod bitcollections;
pub mod bitfield;
pub mod bytecollections;
pub mod bytes;
pub mod codec;
mod collection_codec;
mod collection_tree;
mod collection_wire;
pub mod collections;
pub mod error;
pub mod gindex;
pub mod merkle;
mod progressive_codec;
pub mod scalar;
pub mod sequence;
pub mod sha256;
pub mod tree_hash;
pub mod type_info;
