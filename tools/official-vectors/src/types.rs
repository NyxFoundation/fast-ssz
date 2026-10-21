use std::fmt::Debug;

use nyx_ssz::{
    codec::Ssz,
    collections::{progressive_list, vector, ProgressiveList, Vector},
    U256,
};
use yaml_serde::Value;

use crate::{
    bits::BitSchema,
    fixture::{Case, Outcome},
    TestResult,
};

const FAMILIES: [&str; 7] = [
    "boolean",
    "uints",
    "basic_vector",
    "bitvector",
    "bitlist",
    "progressive_bitlist",
    "basic_progressive_list",
];

pub(crate) fn validate_families(families: &[String]) -> TestResult {
    let unique = families.iter().collect::<std::collections::BTreeSet<_>>();
    if families.is_empty() || unique.len() != families.len() {
        return Err("a nonempty distinct family selection is required".into());
    }
    if families
        .iter()
        .any(|family| !FAMILIES.contains(&family.as_str()))
    {
        return Err("unsupported official family selected".into());
    }
    Ok(())
}

pub(crate) trait FromFixture: Sized + Debug {
    fn from_fixture(value: &Value) -> TestResult<Self>;
    fn equivalent(&self, expected: &Self) -> bool;
}

impl FromFixture for bool {
    fn from_fixture(value: &Value) -> TestResult<Self> {
        value
            .as_bool()
            .ok_or_else(|| "expected YAML boolean".into())
    }

    fn equivalent(&self, expected: &Self) -> bool {
        self == expected
    }
}

fn unsigned_text(value: &Value) -> TestResult<String> {
    let text = match value {
        Value::String(text) => text.clone(),
        Value::Number(number) => number
            .as_u64()
            .ok_or("expected unsigned integer")?
            .to_string(),
        _ => return Err("expected unsigned integer".into()),
    };
    if text.is_empty() || !text.bytes().all(|byte| byte.is_ascii_digit()) {
        return Err("expected decimal unsigned integer".into());
    }
    Ok(text)
}

macro_rules! unsigned_fixture {
    ($($ty:ty),* $(,)?) => {$(
        impl FromFixture for $ty {
            fn from_fixture(value: &Value) -> TestResult<Self> {
                unsigned_text(value)?.parse().map_err(|_| "unsigned integer exceeds its width".into())
            }

            fn equivalent(&self, expected: &Self) -> bool {
                self == expected
            }
        }
    )*};
}
unsigned_fixture!(u8, u16, u32, u64, u128, U256);

impl<T: FromFixture, const N: usize> FromFixture for Vector<T, N> {
    fn from_fixture(value: &Value) -> TestResult<Self> {
        let values = value.as_sequence().ok_or("expected YAML sequence")?;
        let values = values
            .iter()
            .map(T::from_fixture)
            .collect::<TestResult<Vec<_>>>()?;
        vector(values).map_err(|_| "YAML sequence violates vector length".into())
    }

    fn equivalent(&self, expected: &Self) -> bool {
        let actual = self.as_slice();
        let expected = expected.as_slice();
        actual.len() == expected.len()
            && actual
                .iter()
                .zip(expected)
                .all(|(actual, expected)| actual.equivalent(expected))
    }
}

impl<T: FromFixture> FromFixture for ProgressiveList<T> {
    fn from_fixture(value: &Value) -> TestResult<Self> {
        let values = value.as_sequence().ok_or("expected YAML sequence")?;
        Ok(progressive_list(
            values
                .iter()
                .map(T::from_fixture)
                .collect::<TestResult<Vec<_>>>()?,
        ))
    }

    fn equivalent(&self, expected: &Self) -> bool {
        self.as_slice().len() == expected.as_slice().len()
            && self
                .as_slice()
                .iter()
                .zip(expected.as_slice())
                .all(|(actual, expected)| actual.equivalent(expected))
    }
}

fn verify<T: Ssz + FromFixture>(case: &Case) -> TestResult {
    let actual = T::decode(&case.bytes);
    if case.outcome == Outcome::Invalid {
        return if actual.is_err() {
            Ok(())
        } else {
            Err("invalid encoding was accepted".into())
        };
    }
    let actual = actual.map_err(|_| "valid encoding was rejected")?;
    let expected = T::from_fixture(case.value.as_ref().ok_or("missing expected value")?)?;
    if !actual.equivalent(&expected) {
        return Err("decoded value differs from the expected YAML value".into());
    }
    if actual
        .encode()
        .map_err(|_| "valid value could not be encoded")?
        != case.bytes
    {
        return Err("encoding differs from official bytes".into());
    }
    if actual
        .hash_tree_root()
        .map_err(|_| "valid value has no root")?
        != case.root.ok_or("missing expected root")?
    {
        return Err("root differs from official metadata".into());
    }
    Ok(())
}

#[derive(Clone, Copy, Debug)]
enum Primitive {
    Bool,
    U8,
    U16,
    U32,
    U64,
    U128,
    U256,
}

impl Primitive {
    fn parse(name: &str) -> TestResult<Self> {
        match name {
            "bool" => Ok(Self::Bool),
            "uint8" => Ok(Self::U8),
            "uint16" => Ok(Self::U16),
            "uint32" => Ok(Self::U32),
            "uint64" => Ok(Self::U64),
            "uint128" => Ok(Self::U128),
            "uint256" => Ok(Self::U256),
            _ => Err("unknown primitive schema".into()),
        }
    }

    fn verify(self, case: &Case) -> TestResult {
        match self {
            Self::Bool => verify::<bool>(case),
            Self::U8 => verify::<u8>(case),
            Self::U16 => verify::<u16>(case),
            Self::U32 => verify::<u32>(case),
            Self::U64 => verify::<u64>(case),
            Self::U128 => verify::<u128>(case),
            Self::U256 => verify::<U256>(case),
        }
    }

    fn progressive(self, case: &Case) -> TestResult {
        match self {
            Self::Bool => verify::<ProgressiveList<bool>>(case),
            Self::U8 => verify::<ProgressiveList<u8>>(case),
            Self::U16 => verify::<ProgressiveList<u16>>(case),
            Self::U32 => verify::<ProgressiveList<u32>>(case),
            Self::U64 => verify::<ProgressiveList<u64>>(case),
            Self::U128 => verify::<ProgressiveList<u128>>(case),
            Self::U256 => verify::<ProgressiveList<U256>>(case),
        }
    }

    fn vector<const N: usize>(self, case: &Case) -> TestResult {
        match self {
            Self::Bool => verify::<Vector<bool, N>>(case),
            Self::U8 => verify::<Vector<u8, N>>(case),
            Self::U16 => verify::<Vector<u16, N>>(case),
            Self::U32 => verify::<Vector<u32, N>>(case),
            Self::U64 => verify::<Vector<u64, N>>(case),
            Self::U128 => verify::<Vector<u128, N>>(case),
            Self::U256 => verify::<Vector<U256, N>>(case),
        }
    }
}

#[derive(Debug)]
enum SchemaKind {
    Basic {
        primitive: Primitive,
        count: Option<usize>,
    },
    Bits(BitSchema),
    Progressive(Primitive),
}

#[derive(Debug)]
pub(crate) struct Schema {
    kind: SchemaKind,
}

fn progressive_schema(name: &str) -> TestResult<SchemaKind> {
    let mut parts = name.split('_');
    if parts.next() != Some("proglist") {
        return Err("unknown Progressive list schema".into());
    }
    let primitive = Primitive::parse(parts.next().ok_or("missing Progressive element type")?)?;
    if parts.next().is_none() {
        return Err("missing Progressive case identifier".into());
    }
    Ok(SchemaKind::Progressive(primitive))
}

impl Schema {
    pub(crate) fn parse(family: &str, name: &str) -> TestResult<Self> {
        if matches!(family, "bitvector" | "bitlist" | "progressive_bitlist") {
            return Ok(Self {
                kind: SchemaKind::Bits(BitSchema::parse(family, name)?),
            });
        }
        if family == "basic_progressive_list" {
            return Ok(Self {
                kind: progressive_schema(name)?,
            });
        }
        let mut parts = name.split('_');
        let (primitive, count) = match family {
            "boolean" => (Primitive::Bool, None),
            "uints" if parts.next() == Some("uint") => (
                Primitive::parse(&format!(
                    "uint{}",
                    parts.next().ok_or("missing integer width")?
                ))?,
                None,
            ),
            "basic_vector" if parts.next() == Some("vec") => {
                let primitive =
                    Primitive::parse(parts.next().ok_or("missing vector element type")?)?;
                let count = parts
                    .next()
                    .ok_or("missing vector length")?
                    .parse::<usize>()
                    .map_err(|_| "invalid vector length")?;
                if !matches!(count, 0 | 1 | 2 | 3 | 4 | 5 | 8 | 16 | 31 | 512 | 513) {
                    return Err("unknown vector length in pinned corpus".into());
                }
                (primitive, Some(count))
            }
            _ => return Err("unknown family or schema in pinned corpus".into()),
        };
        Ok(Self {
            kind: SchemaKind::Basic { primitive, count },
        })
    }

    pub(crate) fn verify(&self, case: &Case) -> TestResult {
        let (primitive, count) = match &self.kind {
            SchemaKind::Bits(schema) => return schema.verify(case),
            SchemaKind::Progressive(primitive) => return primitive.progressive(case),
            SchemaKind::Basic { primitive, count } => (primitive, count),
        };
        match count {
            None => primitive.verify(case),
            Some(0) => primitive.vector::<0>(case),
            Some(1) => primitive.vector::<1>(case),
            Some(2) => primitive.vector::<2>(case),
            Some(3) => primitive.vector::<3>(case),
            Some(4) => primitive.vector::<4>(case),
            Some(5) => primitive.vector::<5>(case),
            Some(8) => primitive.vector::<8>(case),
            Some(16) => primitive.vector::<16>(case),
            Some(31) => primitive.vector::<31>(case),
            Some(512) => primitive.vector::<512>(case),
            Some(513) => primitive.vector::<513>(case),
            Some(_) => Err("unknown vector length in pinned corpus".into()),
        }
    }
}
