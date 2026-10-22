use nyx_ssz::{
    codec::Ssz,
    error::{CodecError, DecodeFailure},
    type_info::TypeDescriptor as D,
};
use std::sync::atomic::{AtomicUsize, Ordering};
static DROPS: AtomicUsize = AtomicUsize::new(0);
static DECODES: AtomicUsize = AtomicUsize::new(0);
struct Owner;
impl Drop for Owner {
    fn drop(&mut self) {
        DROPS.fetch_add(1, Ordering::SeqCst);
    }
}
impl Ssz for Owner {
    type DecodeState = Self;
    const TYPE: &'static D = &D::Uint(1);
    fn encode(&self) -> Result<Vec<u8>, CodecError> {
        Ok(vec![0])
    }
    fn decode(bytes: &[u8]) -> Result<Self, DecodeFailure<Self>> {
        DECODES.fetch_add(1, Ordering::SeqCst);
        if bytes == [0] {
            Ok(Self)
        } else {
            Err(DecodeFailure {
                kind: CodecError::InvalidBoolean,
                state: Self,
            })
        }
    }
    fn hash_tree_root(&self) -> Result<[u8; 32], CodecError> {
        Ok([0; 32])
    }
}
#[derive(nyx_ssz::Ssz)]
struct Record {
    first: Owner,
    second: nyx_ssz::collections::List<Owner, 4>,
    third: Owner,
}
#[derive(nyx_ssz::Ssz)]
enum Choice {
    #[ssz(selector = 1)]
    A(Owner),
    #[ssz(selector = 2)]
    B(Owner),
}

#[test]
fn should_return_every_heterogeneous_owner_when_nested_decoding_fails() {
    let failure = Record::decode(&[0, 6, 0, 0, 0, 0, 0, 1]).err().unwrap();
    assert_eq!(failure.kind, CodecError::InvalidBoolean);
    assert_eq!(DECODES.load(Ordering::SeqCst), 3);
    assert_eq!(DROPS.load(Ordering::SeqCst), 0);
    assert!(failure.state.first.value.is_some());
    let nested = failure.state.second.child.as_ref().unwrap();
    assert_eq!(nested.values.len(), 1);
    assert!(nested.child.is_some());
    assert!(failure.state.third.value.is_none());
    drop(failure);
    assert_eq!(DROPS.load(Ordering::SeqCst), 3);
    let refusal = Record::decode(&[0]).err().unwrap();
    assert_eq!(DECODES.load(Ordering::SeqCst), 3);
    drop(refusal);
    let refusal = Choice::decode(&[2, 1]).err().unwrap();
    assert_eq!(DROPS.load(Ordering::SeqCst), 3);
    assert!(refusal.state.is_some());
    drop(refusal);
    assert_eq!(DROPS.load(Ordering::SeqCst), 4);
}

struct Oversized;
impl Ssz for Oversized {
    type DecodeState = ();
    const TYPE: &'static D = &D::Vector(&D::Uint(32), usize::MAX);
    fn encode(&self) -> Result<Vec<u8>, CodecError> {
        Err(CodecError::NativeOutputOverflow)
    }
    fn decode(_: &[u8]) -> Result<Self, DecodeFailure<()>> {
        Err(DecodeFailure {
            kind: CodecError::InvalidLength,
            state: (),
        })
    }
    fn hash_tree_root(&self) -> Result<[u8; 32], CodecError> {
        Ok([0; 32])
    }
}
struct Refusal;
impl Ssz for Refusal {
    type DecodeState = ();
    const TYPE: &'static D = &D::Boolean;
    fn encode(&self) -> Result<Vec<u8>, CodecError> {
        Err(CodecError::InvalidBoolean)
    }
    fn decode(_: &[u8]) -> Result<Self, DecodeFailure<()>> {
        Err(DecodeFailure {
            kind: CodecError::InvalidBoolean,
            state: (),
        })
    }
    fn hash_tree_root(&self) -> Result<[u8; 32], CodecError> {
        Err(CodecError::InvalidBoolean)
    }
}
#[derive(nyx_ssz::Ssz)]
struct Deferred {
    huge: Oversized,
    later: Refusal,
}
#[derive(nyx_ssz::Ssz)]
struct Budget {
    huge: Oversized,
    later: u8,
}
#[derive(nyx_ssz::Ssz)]
enum HugeUnion {
    #[ssz(selector = 1)]
    Huge(Oversized),
}
#[derive(nyx_ssz::Ssz)]
enum InvalidUnion {
    #[ssz(selector = 1)]
    A(Owner),
    #[ssz(selector = 2)]
    B(bool),
}

#[test]
fn should_preserve_protocol_error_precedence_when_a_child_has_oversized_native_success() {
    assert_eq!(
        Deferred {
            huge: Oversized,
            later: Refusal
        }
        .encode(),
        Err(CodecError::InvalidBoolean)
    );
    assert_eq!(
        Budget {
            huge: Oversized,
            later: 0
        }
        .encode(),
        Err(CodecError::SizeOverflow)
    );
    assert_eq!(
        HugeUnion::Huge(Oversized).encode(),
        Err(CodecError::NativeOutputOverflow)
    );
    assert_eq!(
        InvalidUnion::decode(&[]).err().unwrap().kind,
        CodecError::UnionIncompatible
    );
}

mod private {
    #[derive(nyx_ssz::Ssz)]
    struct Child {
        value: u8,
    }
    #[derive(nyx_ssz::Ssz)]
    pub struct Public {
        child: Child,
    }
    pub fn make() -> Public {
        Public {
            child: Child { value: 1 },
        }
    }
}
#[test]
fn should_allow_public_containers_when_their_field_types_are_private() {
    assert_eq!(private::make().encode().unwrap(), vec![1]);
}
