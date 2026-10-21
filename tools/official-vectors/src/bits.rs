use nyx_ssz::{bitfield, tree_hash};
use yaml_serde::Value;

use crate::{
    fixture::{Case, Outcome},
    owned_bits, TestResult,
};

const MAX_EXPECTED_BITS: usize = 16 * 1024 * 1024;

#[derive(Debug)]
pub(crate) enum BitSchema {
    Vector(usize),
    List(usize),
    Progressive,
    MissingDelimiter,
}

fn bound(name: &str, prefix: &str) -> TestResult<usize> {
    name.strip_prefix(prefix)
        .and_then(|rest| rest.split('_').next())
        .ok_or_else(|| "unknown bit schema".to_owned())?
        .parse()
        .map_err(|_| "invalid bit declaration".into())
}

impl BitSchema {
    pub(crate) fn parse(family: &str, name: &str) -> TestResult<Self> {
        match family {
            "bitvector" => Ok(Self::Vector(bound(name, "bitvec_")?)),
            "bitlist" => match name {
                "bitlist_no_delimiter_empty"
                | "bitlist_no_delimiter_zero_byte"
                | "bitlist_no_delimiter_zeroes" => Ok(Self::MissingDelimiter),
                _ => Ok(Self::List(bound(name, "bitlist_")?)),
            },
            "progressive_bitlist" if name == "progbitlist" || name.starts_with("progbitlist_") => {
                Ok(Self::Progressive)
            }
            _ => Err("unknown bit family or schema".into()),
        }
    }

    pub(crate) fn verify(&self, case: &Case) -> TestResult {
        match *self {
            Self::Vector(length) => {
                verify_bounded(case, length, true)?;
                owned_bits::verify_bounded(case, length, true)
            }
            Self::List(limit) => {
                verify_bounded(case, limit, false)?;
                owned_bits::verify_bounded(case, limit, false)
            }
            Self::Progressive => {
                verify_progressive(case)?;
                owned_bits::verify_progressive(case)
            }
            Self::MissingDelimiter => {
                if case.outcome != Outcome::Invalid {
                    return Err("delimiter-only schema must be an invalid case".into());
                }
                // Upstream omits the bound for these three format failures.
                // Exercise both extremes rather than inventing a default declaration.
                for limit in [0, usize::MAX] {
                    require_rejection(bitfield::decode_bit_list(&case.bytes, limit).is_err())?;
                }
                owned_bits::verify_missing_delimiter(case)
            }
        }
    }
}

fn require_rejection(rejected: bool) -> TestResult {
    if rejected {
        Ok(())
    } else {
        Err("invalid bit encoding was accepted".into())
    }
}

pub(crate) fn expected_bits(value: &Value, fixed: Option<usize>) -> TestResult<Vec<bool>> {
    let text = value
        .as_str()
        .and_then(|value| value.strip_prefix("0x"))
        .ok_or("expected hexadecimal YAML bitfield")?;
    let bytes = hex::decode(text).map_err(|_| "invalid hexadecimal YAML bitfield")?;
    let count = match fixed {
        Some(count) => {
            if bytes.len() != count.div_ceil(8) {
                return Err("YAML bitvector width differs from its declaration".into());
            }
            let remainder = count % 8;
            if remainder != 0 && bytes.last().ok_or("empty YAML bitvector")? >> remainder != 0 {
                return Err("YAML bitvector has noncanonical padding".into());
            }
            count
        }
        None => {
            let final_byte = *bytes.last().ok_or("YAML bitlist has no delimiter")?;
            if final_byte == 0 {
                return Err("YAML bitlist has no delimiter".into());
            }
            (bytes.len() - 1)
                .checked_mul(8)
                .and_then(|whole| whole.checked_add(7 - final_byte.leading_zeros() as usize))
                .ok_or("YAML bit count overflows")?
        }
    };
    if count > MAX_EXPECTED_BITS {
        return Err("YAML bit fixture exceeds the test-tool limit".into());
    }
    Ok((0..count)
        .map(|index| (bytes[index / 8] >> (index % 8)) & 1 != 0)
        .collect())
}

fn artifacts(case: &Case, encoded: Vec<u8>, root: [u8; 32]) -> TestResult {
    if encoded != case.bytes {
        return Err("bit encoding differs from official bytes".into());
    }
    if root != case.root.ok_or("missing expected bit root")? {
        return Err("bit root differs from official metadata".into());
    }
    Ok(())
}

fn verify_bounded(case: &Case, bound: usize, vector: bool) -> TestResult {
    let actual = if vector {
        bitfield::decode_bit_vector(&case.bytes, bound)
    } else {
        bitfield::decode_bit_list(&case.bytes, bound)
    };
    if case.outcome == Outcome::Invalid {
        return require_rejection(actual.is_err());
    }
    let actual = actual.map_err(|_| "valid bit encoding was rejected")?;
    let expected = expected_bits(
        case.value.as_ref().ok_or("missing YAML bit value")?,
        vector.then_some(bound),
    )?;
    if actual != expected {
        return Err("decoded bit order/value differs from YAML".into());
    }
    let encoded = if vector {
        bitfield::encode_bit_vector(&expected, bound)
    } else {
        bitfield::encode_bit_list(&expected, bound)
    }
    .map_err(|_| "valid bit value could not be encoded")?;
    let root = if vector {
        tree_hash::hash_tree_root_bit_vector(&actual, bound)
    } else {
        tree_hash::hash_tree_root_bit_list(&actual, bound)
    }
    .map_err(|_| "valid bit value has no root")?;
    artifacts(case, encoded, root)
}

fn verify_progressive(case: &Case) -> TestResult {
    let actual = bitfield::decode_progressive_bit_list(&case.bytes, None);
    if case.outcome == Outcome::Invalid {
        return require_rejection(actual.is_err());
    }
    let actual = actual.map_err(|_| "valid progressive bit encoding was rejected")?;
    let expected = expected_bits(case.value.as_ref().ok_or("missing YAML bit value")?, None)?;
    if actual.len_bits() != expected.len() as u128 || actual.as_ssz_bytes() != case.bytes {
        return Err("progressive view differs from the expected bit value".into());
    }
    let encoded = bitfield::encode_progressive_bit_list(&expected, None)
        .map_err(|_| "valid progressive bit value could not be encoded")?;
    let root = tree_hash::hash_tree_root_progressive_bit_list_view(&actual, None)
        .map_err(|_| "valid progressive bit view has no root")?;
    for limit in [None, Some(expected.len())] {
        let bits_root = tree_hash::hash_tree_root_progressive_bit_list(&expected, limit)
            .map_err(|_| "valid progressive bit value has no root")?;
        if root != bits_root {
            return Err("progressive bit value and view roots differ".into());
        }
    }
    artifacts(case, encoded, root)
}
