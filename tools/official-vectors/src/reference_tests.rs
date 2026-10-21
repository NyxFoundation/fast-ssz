use std::{ffi::OsString, path::Path};

use yaml_serde::Value;

use crate::{
    arguments::Arguments,
    fixture::{Case, Outcome},
    reference::ReferenceRoots,
};

const REFERENCE: &str = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
const CORPUS: &str = "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";

fn document() -> Value {
    yaml_serde::from_str(&format!(
        r#"{{"format_version":2,"reference_revision":"{REFERENCE}","corpus_revision":"{CORPUS}","roots":{{"progressive_bitlist/valid/progbitlist_nil_0_0":{{"source_root":"0x{}","root":"0x{}"}}}}}}"#,
        "00".repeat(32), "11".repeat(32)
    )).unwrap()
}

fn case(root: [u8; 32]) -> Case {
    Case {
        outcome: Outcome::Valid,
        bytes: vec![1],
        value: Some(Value::String("0x01".into())),
        root: Some(root),
    }
}

#[test]
fn should_apply_current_roots_only_when_both_source_identity_and_original_root_match() {
    let mut roots = ReferenceRoots::from_document(&document(), REFERENCE, CORPUS).unwrap();
    let value = roots
        .apply(
            "progressive_bitlist",
            "valid",
            "progbitlist_nil_0_0",
            case([0; 32]),
            Path::new("/unused"),
        )
        .unwrap();
    assert_eq!(value.root, Some([17; 32]));
    assert_eq!(value.bytes, [1]);
    assert!(roots.finish().is_ok());
    assert!(ReferenceRoots::from_document(&document(), CORPUS, CORPUS).is_err());
    let mut roots = ReferenceRoots::from_document(&document(), REFERENCE, CORPUS).unwrap();
    assert!(roots
        .apply(
            "progressive_bitlist",
            "valid",
            "progbitlist_nil_0_0",
            case([2; 32]),
            Path::new("/unused"),
        )
        .is_err());
}

#[test]
fn should_refuse_unused_or_missing_reference_inventory_entries() {
    let roots = ReferenceRoots::from_document(&document(), REFERENCE, CORPUS).unwrap();
    assert!(roots.finish().is_err());
    let mut roots = ReferenceRoots::from_document(&document(), REFERENCE, CORPUS).unwrap();
    assert!(roots
        .apply(
            "progressive_bitlist",
            "valid",
            "unknown",
            case([0; 32]),
            Path::new("/unused")
        )
        .is_err());
}

#[test]
fn should_require_explicit_regenerated_root_inputs_for_progressive_families() {
    let parse = |args: &[&str]| Arguments::parse(args.iter().map(OsString::from));
    assert!(parse(&["/fixtures", "progressive_bitlist"]).is_err());
    assert!(parse(&["/fixtures", "boolean", "--reference-roots", "/roots.json"]).is_err());
    assert!(parse(&["/fixtures", "boolean", "--skip-root"]).is_err());
    assert!(parse(&[
        "/fixtures",
        "progressive_bitlist",
        "--reference-roots",
        "/roots.json",
        "--reference-revision",
        REFERENCE,
        "--corpus-revision",
        CORPUS
    ])
    .is_ok());
}
