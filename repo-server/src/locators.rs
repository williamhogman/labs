use walkdir::{DirEntry, WalkDir};
use std::path::{Path, PathBuf};

static IGNORED: &'static [&str] = &["Library", "Pictures", "go"];

fn is_hidden(entry: &DirEntry) -> bool {
    entry.file_name()
         .to_str()
         .map(|s| s.starts_with(".") || s == "node_modules")
         .unwrap_or(false)
}

pub fn find_repos() -> Vec<PathBuf> {
    let home = dirs::home_dir();
    if home == None {
	return vec![];
    }
    let home = home.unwrap();

    let bad_paths: Vec<_> = IGNORED.into_iter().map(|x| Path::new(&home).join(x)).collect();

    let mut it = WalkDir::new(home.clone()).into_iter().filter_entry(|e| !is_hidden(e));
    let mut paths: Vec<PathBuf> = Vec::new();
    loop {
	let entry = match it.next() {
            None => break,
            Some(Err(err)) => {
		println!("{}", err);
		continue
	    }
            Some(Ok(entry)) => entry,
	};
	if entry.file_type().is_file() {
	    continue
	}
	if bad_paths.iter().any(|p| *p == entry.path()) {
	    it.skip_current_dir();
	    continue;
	}
	if is_hidden(&entry) {
            if entry.file_type().is_dir() {
		it.skip_current_dir();
		continue
            }
	}
	if entry.path().join(".git").exists() {
	    paths.push(entry.path().into());
	    it.skip_current_dir();
	}
        continue;
    }
    paths
}
