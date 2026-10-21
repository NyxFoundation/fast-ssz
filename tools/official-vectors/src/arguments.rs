use std::{collections::BTreeMap, ffi::OsString, path::PathBuf};

use crate::{reference::is_progressive_family, types::validate_families, TestResult};

pub(crate) struct ReferenceArguments {
    pub(crate) path: PathBuf,
    pub(crate) reference: String,
    pub(crate) corpus: String,
}

pub(crate) struct Arguments {
    pub(crate) root: PathBuf,
    pub(crate) families: Vec<String>,
    pub(crate) reference: Option<ReferenceArguments>,
}

fn reference_arguments(
    mut options: BTreeMap<String, OsString>,
    families: &[String],
) -> TestResult<Option<ReferenceArguments>> {
    if !families.iter().any(|family| is_progressive_family(family)) {
        if !options.is_empty() {
            return Err("unused regenerated-root options".into());
        }
        return Ok(None);
    }
    let path = options
        .remove("--reference-roots")
        .ok_or("progressive roots require the current reference oracle")?;
    let reference = options
        .remove("--reference-revision")
        .ok_or("missing pinned reference revision")?
        .into_string()
        .map_err(|_| "invalid reference revision")?;
    let corpus = options
        .remove("--corpus-revision")
        .ok_or("missing pinned corpus revision")?
        .into_string()
        .map_err(|_| "invalid corpus revision")?;
    Ok(Some(ReferenceArguments {
        path: path.into(),
        reference,
        corpus,
    }))
}

impl Arguments {
    pub(crate) fn parse(mut arguments: impl Iterator<Item = OsString>) -> TestResult<Self> {
        let root = PathBuf::from(
            arguments
                .next()
                .ok_or("usage: official-vectors ROOT FAMILY...")?,
        );
        let mut families = Vec::new();
        let mut options = BTreeMap::new();
        while let Some(argument) = arguments.next() {
            let argument = argument
                .into_string()
                .map_err(|_| "invalid family or option name")?;
            match argument.as_str() {
                "--reference-roots" | "--reference-revision" | "--corpus-revision" => {
                    let value = arguments.next().ok_or("missing reference option value")?;
                    if options.insert(argument, value).is_some() {
                        return Err("duplicate reference option".into());
                    }
                }
                value if value.starts_with('-') => return Err("unknown runner option".into()),
                _ => families.push(argument),
            }
        }
        validate_families(&families)?;
        let reference = reference_arguments(options, &families)?;
        Ok(Self {
            root,
            families,
            reference,
        })
    }
}
