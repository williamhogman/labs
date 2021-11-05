use snafu::{ensure, Backtrace, ErrorCompat, ResultExt, Snafu};
use std::path::{Path, PathBuf};
use std::env::VarError;

#[derive(Debug, Snafu)]
pub enum Error {
    #[snafu(context(false))]
    PathError { source: shellexpand::LookupError<VarError> },
    #[snafu(context(false))]
    TomlError { source: toml::de::Error },
    #[snafu(context(false))]
    IoError { source: std::io::Error },
    #[snafu(context(false))]
    GithubError { source: octocrab::Error },
    #[snafu(context(false))]
    GitError { source: git2::Error },
    #[snafu(context(false))]
    CacheReadingError { source: crate::cache::CacheReadingError },
    #[snafu(context(false))]
    CacheWritingError { source: crate::cache::CacheWritingError },
}

pub type Result<T, E = Error> = std::result::Result<T, E>;
