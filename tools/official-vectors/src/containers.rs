//! Schemas from consensus-specs v1.6.0-beta.0, generators/runners/ssz_generic_cases.
#![allow(non_snake_case)]
use crate::{
    fixture::Case,
    types::{verify, FromFixture},
    TestResult,
};
use nyx_ssz::{
    bitcollections::{BitList, BitVector, ProgressiveBitList},
    bytecollections::ByteList,
    codec::Ssz,
    collections::{List, ProgressiveList, Vector},
};
use yaml_serde::Value;

macro_rules! container {
    ($(#[$attr:meta])* $name:ident { $($(#[$field_attr:meta])* $field:ident: $ty:ty),* $(,)? }) => {
        #[derive(Debug, nyx_ssz::Ssz)] $(#[$attr])*
        struct $name { $($(#[$field_attr])* $field: $ty,)* }
        impl FromFixture for $name {
            fn from_fixture(value: &Value) -> TestResult<Self> {
                let names = [$(stringify!($field)),*];
                if value.as_mapping().map(|m|m.len()) != Some(names.len()) { return Err("invalid container YAML fields".into()); }
                Ok(Self { $($field: <$ty>::from_fixture(value.get(stringify!($field)).ok_or("missing container YAML field")?)?,)* })
            }
            fn equivalent(&self, other: &Self) -> bool { true $(&& self.$field.equivalent(&other.$field))* }
        }
    }
}
container!(SingleFieldTestStruct { A: u8 });
container!(SmallTestStruct { A: u16, B: u16 });
container!(FixedTestStruct {
    A: u8,
    B: u64,
    C: u32
});
container!(VarTestStruct { A: u16, B: List<u16,1024>, C: u8 });
container!(ComplexTestStruct { A: u16, B: List<u16,128>, C: u8, D: ByteList<256>, E: VarTestStruct, F: Vector<FixedTestStruct,4>, G: Vector<VarTestStruct,2> });
container!(ProgressiveTestStruct { A: ProgressiveList<u8>, B: ProgressiveList<u64>, C: ProgressiveList<SmallTestStruct>, D: ProgressiveList<ProgressiveList<VarTestStruct>> });
container!(BitsStruct { A: BitList<5>, B: BitVector<2>, C: BitVector<1>, D: BitList<6>, E: BitVector<8> });
container!(ProgressiveBitsStruct { A: BitVector<256>, B: BitList<256>, C: ProgressiveBitList, D: BitVector<257>, E: BitList<257>, F: ProgressiveBitList, G: BitVector<1280>, H: BitList<1280>, I: ProgressiveBitList, J: BitVector<1281>, K: BitList<1281>, L: ProgressiveBitList });
container!(
    #[ssz(progressive)]
    ProgressiveSingleFieldContainerTestStruct {
        #[ssz(position = 0)]
        A: u8
    }
);
container!(
    #[ssz(progressive)]
    ProgressiveSingleListContainerTestStruct {
        #[ssz(position = 4)]
        C: ProgressiveBitList
    }
);
container!(#[ssz(progressive)] ProgressiveVarTestStruct { #[ssz(position=0)] A: u8, #[ssz(position=2)] B: List<u16,123>, #[ssz(position=4)] C: ProgressiveBitList });
container!(#[ssz(progressive)] ProgressiveComplexTestStruct {
    #[ssz(position=0)] A: u8, #[ssz(position=2)] B: List<u16,123>, #[ssz(position=4)] C: ProgressiveBitList,
    #[ssz(position=8)] D: ProgressiveList<u64>, #[ssz(position=12)] E: ProgressiveList<SmallTestStruct>,
    #[ssz(position=13)] F: ProgressiveList<ProgressiveList<VarTestStruct>>,
    #[ssz(position=20)] G: List<ProgressiveSingleFieldContainerTestStruct,10>, #[ssz(position=21)] H: ProgressiveList<ProgressiveVarTestStruct>
});

const ORDINARY: &[&str] = &[
    "SingleFieldTestStruct",
    "SmallTestStruct",
    "FixedTestStruct",
    "VarTestStruct",
    "ComplexTestStruct",
    "ProgressiveTestStruct",
    "BitsStruct",
    "ProgressiveBitsStruct",
];
const PROGRESSIVE: &[&str] = &[
    "ProgressiveSingleFieldContainerTestStruct",
    "ProgressiveSingleListContainerTestStruct",
    "ProgressiveVarTestStruct",
    "ProgressiveComplexTestStruct",
];

pub(crate) fn parse(family: &str, name: &str) -> TestResult<String> {
    let schema = name
        .split_once('_')
        .ok_or("container case requires identifier")?
        .0;
    let names = if family == "containers" {
        ORDINARY
    } else {
        PROGRESSIVE
    };
    if !names.contains(&schema) {
        return Err("unknown container schema".into());
    }
    Ok(schema.to_owned())
}

pub(crate) fn check(schema: &str, case: &Case) -> TestResult {
    match schema {
        "SingleFieldTestStruct" => verify::<SingleFieldTestStruct>(case),
        "SmallTestStruct" => verify::<SmallTestStruct>(case),
        "FixedTestStruct" => verify::<FixedTestStruct>(case),
        "VarTestStruct" => verify::<VarTestStruct>(case),
        "ComplexTestStruct" => verify::<ComplexTestStruct>(case),
        "ProgressiveTestStruct" => verify::<ProgressiveTestStruct>(case),
        "BitsStruct" => verify::<BitsStruct>(case),
        "ProgressiveBitsStruct" => verify::<ProgressiveBitsStruct>(case),
        "ProgressiveSingleFieldContainerTestStruct" => {
            verify::<ProgressiveSingleFieldContainerTestStruct>(case)
        }
        "ProgressiveSingleListContainerTestStruct" => {
            verify::<ProgressiveSingleListContainerTestStruct>(case)
        }
        "ProgressiveVarTestStruct" => verify::<ProgressiveVarTestStruct>(case),
        "ProgressiveComplexTestStruct" => verify::<ProgressiveComplexTestStruct>(case),
        _ => Err("unknown container schema".into()),
    }
}

fn packed_fixture<T: Ssz>(value: &Value) -> TestResult<T> {
    let text = value
        .as_str()
        .and_then(|s| s.strip_prefix("0x"))
        .ok_or("expected packed hexadecimal bits")?;
    let bytes = hex::decode(text).map_err(|_| "invalid packed hexadecimal bits")?;
    T::decode(&bytes).map_err(|_| "invalid packed bit value".into())
}
macro_rules! packed_fixture_impl {
    ($ty:ty $(, const $param:ident: usize)?) => {
        impl<$(const $param: usize)?> FromFixture for $ty {
            fn from_fixture(value: &Value) -> TestResult<Self> { packed_fixture(value) }
            fn equivalent(&self, other: &Self) -> bool { self.encode().ok() == other.encode().ok() }
        }
    }
}
packed_fixture_impl!(BitVector<N>, const N: usize);
packed_fixture_impl!(BitList<N>, const N: usize);
packed_fixture_impl!(ProgressiveBitList);

impl<T: FromFixture, const N: usize> FromFixture for List<T, N> {
    fn from_fixture(value: &Value) -> TestResult<Self> {
        let values = value
            .as_sequence()
            .ok_or("expected YAML list")?
            .iter()
            .map(T::from_fixture)
            .collect::<TestResult<Vec<_>>>()?;
        nyx_ssz::collections::list(values).map_err(|_| "YAML list exceeds limit".into())
    }
    fn equivalent(&self, other: &Self) -> bool {
        self.as_slice().len() == other.as_slice().len()
            && self
                .as_slice()
                .iter()
                .zip(other.as_slice())
                .all(|(a, b)| a.equivalent(b))
    }
}
