use crate::{
    fixture::{Case, Outcome},
    reference::ReferenceRoots,
};
use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicUsize, Ordering},
};
use yaml_serde::Value;

const REFERENCE: &str = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
const CORPUS: &str = "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";
const WITNESS: &str = "basic_progressive_list/valid/proglist_uint16_max_0";
const ALIAS: &str = "basic_progressive_list/invalid/proglist_uint16_0_bad";
static NEXT: AtomicUsize = AtomicUsize::new(0);

fn document() -> Value {
    yaml_serde::from_str(&format!(
        r#"{{"format_version":2,"reference_revision":"{REFERENCE}","corpus_revision":"{CORPUS}","roots":{{"{WITNESS}":{{"source_root":"0x{}","root":"0x{}"}},"{ALIAS}":{{"witness":"{WITNESS}"}}}}}}"#,
        "00".repeat(32), "11".repeat(32)
    )).unwrap()
}

fn temporary_corpus() -> PathBuf {
    let root = std::env::temp_dir().join(format!(
        "nyx-ssz-witness-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir(&root).unwrap();
    let case = root.join(WITNESS);
    fs::create_dir_all(&case).unwrap();
    let wire = snap::raw::Encoder::new().compress_vec(&[2, 1]).unwrap();
    fs::write(case.join("serialized.ssz_snappy"), wire).unwrap();
    fs::write(case.join("value.yaml"), "[258]\n").unwrap();
    fs::write(
        case.join("meta.yaml"),
        format!("root: '0x{}'\n", "00".repeat(32)),
    )
    .unwrap();
    root
}

fn invalid(bytes: Vec<u8>) -> Case {
    Case {
        outcome: Outcome::Invalid,
        bytes,
        root: None,
        value: None,
    }
}

#[test]
fn should_recheck_every_alias_when_a_same_type_published_witness_is_byte_identical() {
    let root = temporary_corpus();
    let mut roots = ReferenceRoots::from_document(&document(), REFERENCE, CORPUS).unwrap();
    let published = Case::load(&root.join(WITNESS), Outcome::Valid).unwrap();
    roots
        .apply(
            "basic_progressive_list",
            "valid",
            "proglist_uint16_max_0",
            published,
            &root,
        )
        .unwrap();
    let result = roots
        .apply(
            "basic_progressive_list",
            "invalid",
            "proglist_uint16_0_bad",
            invalid(vec![2, 1]),
            &root,
        )
        .unwrap();
    assert!(result.outcome == Outcome::Valid);
    assert_eq!(result.bytes, [2, 1]);
    assert_eq!(result.value, Some(Value::Sequence(vec![Value::from(258)])));
    assert_eq!(result.root, Some([17; 32]));
    assert!(roots
        .apply(
            "basic_progressive_list",
            "invalid",
            "proglist_uint16_0_bad",
            invalid(vec![2, 1]),
            &root
        )
        .is_err());
    assert!(roots.finish().is_ok());
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn should_refuse_reclassification_when_bytes_or_original_witness_metadata_differ() {
    let root = temporary_corpus();
    let mut roots = ReferenceRoots::from_document(&document(), REFERENCE, CORPUS).unwrap();
    assert!(roots
        .apply(
            "basic_progressive_list",
            "invalid",
            "proglist_uint16_0_bad",
            invalid(vec![2, 1, 0]),
            &root
        )
        .is_err());
    fs::write(
        root.join(WITNESS).join("meta.yaml"),
        format!("root: '0x{}'\n", "22".repeat(32)),
    )
    .unwrap();
    let mut roots = ReferenceRoots::from_document(&document(), REFERENCE, CORPUS).unwrap();
    assert!(roots
        .apply(
            "basic_progressive_list",
            "invalid",
            "proglist_uint16_0_bad",
            invalid(vec![2, 1]),
            &root
        )
        .is_err());
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn should_reject_cross_type_missing_or_escaping_witnesses_before_loading_files() {
    for witness in [
        "../outside",
        "basic_progressive_list/valid/unknown",
        "basic_progressive_list/invalid/proglist_uint16_other",
    ] {
        let mut data = document();
        *data
            .get_mut("roots")
            .unwrap()
            .get_mut(ALIAS)
            .unwrap()
            .get_mut("witness")
            .unwrap() = Value::String(witness.into());
        assert!(ReferenceRoots::from_document(&data, REFERENCE, CORPUS).is_err());
    }
    let mut data = document();
    let entries = data.get_mut("roots").unwrap().as_mapping_mut().unwrap();
    let alias = entries.remove(Value::String(ALIAS.into())).unwrap();
    entries.insert(Value::String(ALIAS.replace("uint16", "uint32")), alias);
    assert!(ReferenceRoots::from_document(&data, REFERENCE, CORPUS).is_err());
}
