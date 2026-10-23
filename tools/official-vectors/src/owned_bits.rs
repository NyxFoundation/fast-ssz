//! Exercise the actual packed owned dictionaries in addition to borrowed APIs.

use crate::{
    bits::expected_bits,
    fixture::{Case, Outcome},
    TestResult,
};
use nyx_ssz::{
    bitcollections::{BitList, BitVector, ProgressiveBitList},
    codec::Ssz,
};

pub(crate) trait BitAccess: Ssz {
    fn bit_length(&self) -> u128;
    fn bit(&self, index: u128) -> Option<bool>;
}

impl<const N: usize> BitAccess for BitVector<N> {
    fn bit_length(&self) -> u128 {
        self.len_bits()
    }
    fn bit(&self, index: u128) -> Option<bool> {
        self.get(index)
    }
}

impl<const MAX: usize> BitAccess for BitList<MAX> {
    fn bit_length(&self) -> u128 {
        self.len_bits()
    }
    fn bit(&self, index: u128) -> Option<bool> {
        self.get(index)
    }
}

impl BitAccess for ProgressiveBitList {
    fn bit_length(&self) -> u128 {
        self.len_bits()
    }
    fn bit(&self, index: u128) -> Option<bool> {
        self.get(index)
    }
}

pub(crate) fn verify_owned<T: BitAccess>(case: &Case, fixed: Option<usize>) -> TestResult {
    let actual = T::decode(&case.bytes);
    if case.outcome == Outcome::Invalid {
        return if actual.is_err() {
            Ok(())
        } else {
            Err("owned bit codec accepted invalid bytes".into())
        };
    }
    let actual = actual.map_err(|_| "owned bit codec rejected valid bytes")?;
    let expected = expected_bits(
        case.value.as_ref().ok_or("missing expected bit value")?,
        fixed,
    )?;
    if actual.bit_length() != expected.len() as u128
        || actual.bit(expected.len() as u128).is_some()
        || actual.bit(u128::MAX).is_some()
    {
        return Err("owned bit count or out-of-range access differs from YAML".into());
    }
    for (index, bit) in expected.iter().enumerate() {
        if actual.bit(index as u128) != Some(*bit) {
            return Err("owned bit value differs from YAML".into());
        }
    }
    crate::types::verify_encoding(&actual, &case.bytes)?;
    if actual
        .hash_tree_root()
        .map_err(|_| "owned bit root failed")?
        != case.root.ok_or("missing expected bit root")?
    {
        return Err("owned bit root differs from current reference metadata".into());
    }
    Ok(())
}

macro_rules! dispatch_owned {
    ($kind:ident, $case:expr, $bound:expr, $fixed:expr; $($count:expr),* $(,)?) => {
        match $bound {
            $($count => verify_owned::<$kind<$count>>($case, $fixed),)*
            _ => Err("unknown owned bit bound in pinned corpus".into()),
        }
    };
}

pub(crate) fn verify_bounded(case: &Case, bound: usize, vector: bool) -> TestResult {
    if vector {
        dispatch_owned!(BitVector, case, bound, Some(bound);
            0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 15, 16, 17, 31, 32, 33, 511, 512, 513)
    } else {
        dispatch_owned!(BitList, case, bound, None;
            0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 15, 16, 17, 31, 32, 33, 511, 512, 513)
    }
}

pub(crate) fn verify_progressive(case: &Case) -> TestResult {
    verify_owned::<ProgressiveBitList>(case, None)
}

pub(crate) fn verify_missing_delimiter(case: &Case) -> TestResult {
    if case.outcome != Outcome::Invalid
        || BitList::<0>::decode(&case.bytes).is_ok()
        || BitList::<{ usize::MAX }>::decode(&case.bytes).is_ok()
    {
        return Err("owned bitlist failed the explicit delimiter-only rejection checks".into());
    }
    Ok(())
}
