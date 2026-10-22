use std::{
    collections::{BTreeMap, BTreeSet},
    path::Path,
};

use yaml_serde::Value;

use crate::{
    fixture::{parse_root, read_file, Case, Outcome},
    TestResult,
};

struct RootRecord {
    source: [u8; 32],
    current: [u8; 32],
    witness: Option<String>,
}

pub(crate) struct ReferenceRoots {
    roots: BTreeMap<String, RootRecord>,
    aliases: BTreeSet<String>,
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

pub(crate) fn is_progressive_family(family: &str) -> bool {
    matches!(
        family,
        "progressive_bitlist" | "basic_progressive_list" | "containers" | "progressive_containers"
    )
}

fn case_key(key: &Value) -> TestResult<(&str, bool)> {
    let key = key.as_str().ok_or("invalid reference case name")?;
    let alias = key.starts_with("basic_progressive_list/invalid/");
    let name = [
        "containers/valid/",
        "progressive_containers/valid/",
        "progressive_bitlist/valid/",
        "basic_progressive_list/valid/",
        "basic_progressive_list/invalid/",
    ]
    .iter()
    .find_map(|prefix| key.strip_prefix(prefix))
    .ok_or("unexpected reference root family")?;
    if name.is_empty()
        || !name
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
    {
        return Err("invalid reference case name".into());
    }
    Ok((key, alias))
}

fn published_record(value: &Value) -> TestResult<RootRecord> {
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
    Ok(RootRecord {
        source,
        current,
        witness: None,
    })
}

fn primitive_of(key: &str) -> Option<&str> {
    key.rsplit('/')
        .next()?
        .strip_prefix("proglist_")?
        .split('_')
        .next()
}

fn alias_record(
    key: &str,
    value: &Value,
    roots: &BTreeMap<String, RootRecord>,
) -> TestResult<RootRecord> {
    fields(value, 1)?;
    let witness = value
        .get("witness")
        .and_then(Value::as_str)
        .ok_or("missing valid witness")?;
    if !witness.starts_with("basic_progressive_list/valid/") {
        return Err("invalid witness family or outcome".into());
    }
    if primitive_of(key).is_none() || primitive_of(key) != primitive_of(witness) {
        return Err("correction and valid witness must declare the same primitive".into());
    }
    let published = roots
        .get(witness)
        .ok_or("missing published valid witness")?;
    if published.witness.is_some() {
        return Err("a correction cannot witness another correction".into());
    }
    Ok(RootRecord {
        source: published.source,
        current: published.current,
        witness: Some(witness.to_owned()),
    })
}

fn root_inventory(document: &Value) -> TestResult<BTreeMap<String, RootRecord>> {
    let entries = document
        .get("roots")
        .and_then(Value::as_mapping)
        .ok_or("missing generated root inventory")?;
    if entries.is_empty() {
        return Err("empty generated root inventory".into());
    }
    let mut roots = BTreeMap::new();
    for (key, value) in entries {
        let (key, alias) = case_key(key)?;
        if !alias
            && roots
                .insert(key.to_owned(), published_record(value)?)
                .is_some()
        {
            return Err("duplicate generated root".into());
        }
    }
    for (key, value) in entries {
        let (key, alias) = case_key(key)?;
        if alias {
            let record = alias_record(key, value, &roots)?;
            if roots.insert(key.to_owned(), record).is_some() {
                return Err("duplicate correction witness".into());
            }
        }
    }
    Ok(roots)
}

fn adjusted_case(record: RootRecord, case: Case, corpus: &Path) -> TestResult<Case> {
    let Some(witness) = record.witness else {
        if case.outcome != Outcome::Valid || case.root != Some(record.source) {
            return Err("generated root is paired with the wrong original fixture".into());
        }
        return Ok(Case {
            root: Some(record.current),
            ..case
        });
    };
    if case.outcome != Outcome::Invalid || case.root.is_some() || case.value.is_some() {
        return Err("correction must refer to an originally invalid fixture".into());
    }
    let published = Case::load(&corpus.join(witness), Outcome::Valid)?;
    if case.bytes != published.bytes || published.root != Some(record.source) {
        return Err("correction is not byte-identical to its published valid witness".into());
    }
    Ok(Case {
        outcome: Outcome::Valid,
        value: published.value,
        root: Some(record.current),
        ..case
    })
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
        if document.get("format_version").and_then(Value::as_u64) != Some(2) {
            return Err("unsupported reference-root format".into());
        }
        revision(document, "reference_revision", reference)?;
        revision(document, "corpus_revision", corpus)?;
        let roots = root_inventory(document)?;
        let aliases = roots
            .iter()
            .filter(|(_, record)| record.witness.is_some())
            .map(|(key, _)| key.clone())
            .collect();
        Ok(Self { roots, aliases })
    }

    pub(crate) fn apply(
        &mut self,
        family: &str,
        kind: &str,
        name: &str,
        case: Case,
        corpus: &Path,
    ) -> TestResult<Case> {
        if !is_progressive_family(family) {
            return Ok(case);
        }
        let key = format!("{family}/{kind}/{name}");
        match self.roots.remove(&key) {
            Some(record) => adjusted_case(record, case, corpus),
            None if case.outcome == Outcome::Invalid && !self.aliases.contains(&key) => Ok(case),
            None => Err("missing or repeated generated reference root".into()),
        }
    }

    pub(crate) fn finish(self) -> TestResult {
        if self.roots.is_empty() {
            Ok(())
        } else {
            Err("generated reference-root inventory was not fully exercised".into())
        }
    }
}
