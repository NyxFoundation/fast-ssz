use std::{fs, io::Read, path::Path};

use yaml_serde::Value;

use crate::TestResult;

const MAX_BYTES: usize = 64 * 1024 * 1024;

#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum Outcome {
    Valid,
    Invalid,
}

pub(crate) struct Case {
    pub(crate) outcome: Outcome,
    pub(crate) bytes: Vec<u8>,
    pub(crate) value: Option<Value>,
    pub(crate) root: Option<[u8; 32]>,
}

pub(crate) fn read_file(path: &Path) -> TestResult<Vec<u8>> {
    if !fs::symlink_metadata(path)
        .map_err(|_| "fixture file is missing")?
        .is_file()
    {
        return Err("fixture must be a regular file".into());
    }
    let file = fs::File::open(path).map_err(|_| "fixture file cannot be opened")?;
    let mut data = Vec::new();
    file.take(MAX_BYTES as u64 + 1)
        .read_to_end(&mut data)
        .map_err(|_| "fixture file cannot be read")?;
    if data.len() > MAX_BYTES {
        return Err("fixture file exceeds the input limit".into());
    }
    Ok(data)
}

pub(crate) fn decode_snappy(data: &[u8]) -> TestResult<Vec<u8>> {
    let size = snap::raw::decompress_len(data).map_err(|_| "invalid raw Snappy input")?;
    if size > MAX_BYTES {
        return Err("decompressed fixture exceeds the input limit".into());
    }
    snap::raw::Decoder::new()
        .decompress_vec(data)
        .map_err(|_| "invalid raw Snappy input".into())
}

fn load_yaml(path: &Path) -> TestResult<Value> {
    yaml_serde::from_slice(&read_file(path)?).map_err(|_| "invalid YAML fixture".into())
}

fn load_root(path: &Path) -> TestResult<[u8; 32]> {
    let meta = load_yaml(path)?;
    if meta.as_mapping().map(|mapping| mapping.len()) != Some(1) {
        return Err("unexpected root metadata fields".into());
    }
    let text = meta
        .get("root")
        .and_then(Value::as_str)
        .ok_or("missing root metadata")?;
    parse_root(text)
}

pub(crate) fn parse_root(text: &str) -> TestResult<[u8; 32]> {
    let text = text.strip_prefix("0x").ok_or("root must be hexadecimal")?;
    let mut root = [0; 32];
    hex::decode_to_slice(text, &mut root).map_err(|_| "root must contain exactly 32 bytes")?;
    Ok(root)
}

impl Case {
    pub(crate) fn load(directory: &Path, outcome: Outcome) -> TestResult<Self> {
        let expected = if outcome == Outcome::Valid {
            &["meta.yaml", "serialized.ssz_snappy", "value.yaml"][..]
        } else {
            &["serialized.ssz_snappy"][..]
        };
        let entries = fs::read_dir(directory).map_err(|_| "fixture is unavailable")?;
        let mut count = 0;
        for entry in entries {
            let entry = entry.map_err(|_| "cannot enumerate fixture files")?;
            let name = entry.file_name();
            if !expected.iter().any(|allowed| name == *allowed) {
                return Err("unexpected fixture file".into());
            }
            count += 1;
        }
        if count != expected.len() {
            return Err("incomplete fixture".into());
        }
        let bytes = decode_snappy(&read_file(&directory.join("serialized.ssz_snappy"))?)?;
        let (value, root) = if outcome == Outcome::Valid {
            (
                Some(load_yaml(&directory.join("value.yaml"))?),
                Some(load_root(&directory.join("meta.yaml"))?),
            )
        } else {
            (None, None)
        };
        Ok(Self {
            outcome,
            bytes,
            value,
            root,
        })
    }
}
