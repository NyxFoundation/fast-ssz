use std::{collections::BTreeMap, path::Path};

use yaml_serde::Value;

use crate::{
    fixture::{parse_root, read_file, Case, Outcome},
    TestResult,
};

struct RootRecord {
    source: [u8; 32],
    current: [u8; 32],
}

pub(crate) struct ReferenceRoots {
    roots: BTreeMap<String, RootRecord>,
}

fn fields(value: &Value, count: usize) -> TestResult {
    if value.as_mapping().map(|mapping| mapping.len()) != Some(count) {
        return Err("unexpected reference-root fields".into());
    }
    Ok(())
}

fn revision(value: &Value, key: &str, expected: &str) -> TestResult {
    if expected.len() != 40
        || !expected.bytes().all(|byte| byte.is_ascii_hexdigit())
        || value.get(key).and_then(Value::as_str) != Some(expected)
    {
        return Err("reference-root source revision mismatch".into());
    }
    Ok(())
}

fn case_key(key: &Value) -> TestResult<&str> {
    let key = key.as_str().ok_or("invalid reference case name")?;
    let name = key
        .strip_prefix("progressive_bitlist/valid/")
        .ok_or("unexpected reference root family")?;
    if name.is_empty()
        || !name
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
    {
        return Err("invalid reference case name".into());
    }
    Ok(key)
}

fn root_record(value: &Value) -> TestResult<RootRecord> {
    fields(value, 2)?;
    let source = parse_root(
        value
            .get("source_root")
            .and_then(Value::as_str)
            .ok_or("missing original published root")?,
    )?;
    let current = parse_root(
        value
            .get("root")
            .and_then(Value::as_str)
            .ok_or("missing current reference root")?,
    )?;
    Ok(RootRecord { source, current })
}

impl ReferenceRoots {
    pub(crate) fn load(path: &Path, reference: &str, corpus: &str) -> TestResult<Self> {
        let document: Value = yaml_serde::from_slice(&read_file(path)?)
            .map_err(|_| "invalid generated reference-root document")?;
        Self::from_document(&document, reference, corpus)
    }

    pub(crate) fn from_document(
        document: &Value,
        reference: &str,
        corpus: &str,
    ) -> TestResult<Self> {
        fields(document, 4)?;
        if document.get("format_version").and_then(Value::as_u64) != Some(1) {
            return Err("unsupported reference-root format".into());
        }
        revision(document, "reference_revision", reference)?;
        revision(document, "corpus_revision", corpus)?;
        let entries = document
            .get("roots")
            .and_then(Value::as_mapping)
            .ok_or("missing generated root inventory")?;
        if entries.is_empty() {
            return Err("empty generated root inventory".into());
        }
        let mut roots = BTreeMap::new();
        for (key, value) in entries {
            let key = case_key(key)?;
            if roots.insert(key.to_owned(), root_record(value)?).is_some() {
                return Err("duplicate generated root".into());
            }
        }
        Ok(Self { roots })
    }

    pub(crate) fn apply(
        &mut self,
        family: &str,
        kind: &str,
        name: &str,
        case: Case,
    ) -> TestResult<Case> {
        if family != "progressive_bitlist" || case.outcome != Outcome::Valid {
            return Ok(case);
        }
        let key = format!("{family}/{kind}/{name}");
        let record = self
            .roots
            .remove(&key)
            .ok_or("missing or repeated generated reference root")?;
        if case.root != Some(record.source) {
            return Err("generated root is paired with the wrong original fixture".into());
        }
        Ok(Case {
            root: Some(record.current),
            ..case
        })
    }

    pub(crate) fn finish(self) -> TestResult {
        if self.roots.is_empty() {
            Ok(())
        } else {
            Err("generated reference-root inventory was not fully exercised".into())
        }
    }
}
