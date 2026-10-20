mod fixture;
mod types;

#[cfg(test)]
mod tests;

use std::{env, fs, path::Path};

use fixture::{Case, Outcome};
use types::{validate_families, Schema};

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

fn run_family(root: &Path, family: &str) -> TestResult<usize> {
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
            let result = Schema::parse(family, name).and_then(|schema| {
                Case::load(&directory, outcome).and_then(|case| schema.verify(&case))
            });
            result.map_err(|error| format!("{family}/{kind}/{name}: {error}"))?;
            count += 1;
        }
    }
    Ok(count)
}

fn run() -> TestResult {
    let mut arguments = env::args_os().skip(1);
    let root = arguments
        .next()
        .ok_or("usage: official-vectors ROOT FAMILY...")?;
    let families = arguments
        .map(|value| value.into_string().map_err(|_| "invalid family name"))
        .collect::<Result<Vec<_>, _>>()?;
    validate_families(&families)?;
    let root = Path::new(&root);
    let mut count = 0;
    for family in &families {
        count += run_family(root, family)?;
    }
    println!(
        "Verified {count} official cases for {}.",
        families.join(", ")
    );
    Ok(())
}

fn main() {
    if let Err(error) = run() {
        eprintln!("Official vector verification failed: {error}");
        std::process::exit(1);
    }
}
