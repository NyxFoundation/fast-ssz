#![allow(non_camel_case_types)]
use nyx_ssz::codec::Ssz;
#[derive(nyx_ssz::Ssz)]
struct DecodeState {
    r#type: u8,
}
#[derive(nyx_ssz::Ssz)]
struct Marker<__NyxSszDecodeStateForMarker> {
    marker: __NyxSszDecodeStateForMarker,
    r#__nyx_ssz_marker: u8,
}

#[derive(nyx_ssz::Ssz)]
struct __nyx {
    value: u8,
}
#[derive(nyx_ssz::Ssz)]
struct Vec {
    state: DecodeState,
    value: __nyx,
}
#[derive(nyx_ssz::Ssz)]
enum Option {
    #[ssz(selector = 1)]
    Value(Vec),
}
#[derive(nyx_ssz::Ssz)]
struct Result<__nyx> {
    item: __nyx,
}
#[test]
fn should_avoid_generated_name_collisions_when_user_types_shadow_common_identifiers() {
    let value = Option::Value(Vec {
        state: DecodeState { r#type: 1 },
        value: __nyx { value: 2 },
    });
    let bytes = value.encode().unwrap();
    assert_eq!(bytes, [1, 1, 2]);
    assert_eq!(Option::decode(&bytes).unwrap().encode().unwrap(), bytes);
    let marker = Marker {
        marker: 7u8,
        r#__nyx_ssz_marker: 8,
    };
    assert_eq!(marker.encode().unwrap(), [7, 8]);
    assert_eq!(Marker::<u8>::decode(&[7, 8]).unwrap().marker, 7);
    let generic = Result { item: 5u8 };
    assert_eq!(generic.encode().unwrap(), [5]);
}
