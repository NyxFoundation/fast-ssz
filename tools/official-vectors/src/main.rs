mod arguments;
mod bits;
mod fixture;
mod owned_bits;
mod reference;
mod types;

#[cfg(test)]
mod reference_tests;
#[cfg(test)]
mod tests;
#[cfg(test)]
mod witness_tests;

use std::{env, fs, path::Path};

use arguments::Arguments;
use fixture::{Case, Outcome};
use reference::{is_progressive_family, ReferenceRoots};
use types::Schema;

type TestResult<T = ()> = Result<T, String>;

fn sorted_directories(path: &Path) -> TestResult<Vec<std::path::PathBuf>> {
    let entries = fs::read_dir(path).map_err(|_| "fixture directory is unavailable")?;
    let mut directories = Vec::new();
    for entry in entries {
        let entry = entry.map_err(|_| "cannot enumerate fixture directory")?;
        let kind = entry
            .file_type()
            .map_err(|_| "cannot inspect fixture entry")?;
        if !kind.is_dir() {
            return Err("unexpected non-directory in fixture index".into());
        }
        directories.push(entry.path());
    }
    directories.sort();
    if directories.is_empty() {
        return Err("empty fixture index".into());
    }
    Ok(directories)
}

fn verify_case(
    corpus: &Path,
    directory: &Path,
    outcome: Outcome,
    family: &str,
    name: &str,
    reference: &mut Option<ReferenceRoots>,
) -> TestResult {
    let schema = Schema::parse(family, name)?;
    let case = Case::load(directory, outcome)?;
    let case = if is_progressive_family(family) {
        let kind = if outcome == Outcome::Valid {
            "valid"
        } else {
            "invalid"
        };
        reference
            .as_mut()
            .ok_or("missing version-aligned reference roots")?
            .apply(family, kind, name, case, corpus)?
    } else {
        case
    };
    schema.verify(&case)
}

fn run_family(
    root: &Path,
    family: &str,
    reference: &mut Option<ReferenceRoots>,
) -> TestResult<usize> {
    let mut count = 0;
    for (kind, outcome) in [("valid", Outcome::Valid), ("invalid", Outcome::Invalid)] {
        for directory in sorted_directories(&root.join(family).join(kind))? {
            let name = directory
                .file_name()
                .and_then(|name| name.to_str())
                .ok_or("non-UTF-8 fixture name")?;
            if !name
                .bytes()
                .all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
            {
                return Err("non-canonical fixture name".into());
            }
            let result = verify_case(root, &directory, outcome, family, name, reference);
            result.map_err(|error| format!("{family}/{kind}/{name}: {error}"))?;
            count += 1;
        }
    }
    Ok(count)
}

fn run() -> TestResult {
    let arguments = Arguments::parse(env::args_os().skip(1))?;
    let mut reference = arguments
        .reference
        .as_ref()
        .map(|source| ReferenceRoots::load(&source.path, &source.reference, &source.corpus))
        .transpose()?;
    let mut count = 0;
    for family in &arguments.families {
        count += run_family(&arguments.root, family, &mut reference)?;
    }
    if let Some(reference) = reference {
        reference.finish()?;
    }
    let profile = if arguments.reference.is_some() {
        " (version-aligned reference roots)"
    } else {
        ""
    };
    println!(
        "Verified {count} source-corpus cases for {}{profile}.",
        arguments.families.join(", ")
    );
    Ok(())
}

fn main() {
    if let Err(error) = run() {
        eprintln!("Official vector verification failed: {error}");
        std::process::exit(1);
    }
}
