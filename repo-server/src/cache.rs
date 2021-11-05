use snafu::{ensure, Snafu, ResultExt};
use serde::{Serialize, Deserialize};
use tokio::fs;
use tokio::io;
use std::path::PathBuf;
use crate::err::Result;

#[derive(Serialize, Deserialize, Default)]
pub struct Cache {
    pub repo_paths: Vec<PathBuf>
}


#[derive(Debug, Snafu)]
pub enum CacheReadingError {
    #[snafu(context(false))]
    IOError { source: io::Error },
    #[snafu(context(false))]
    DeserializationError { source: flexbuffers::DeserializationError },
    #[snafu(context(false))]
    ReaderError { source: flexbuffers::ReaderError },
}

#[derive(Debug, Snafu)]
pub enum CacheWritingError {
    #[snafu(context(false))]
    IOError { source: io::Error },
    #[snafu(context(false))]
    SerializationError { source: flexbuffers::SerializationError },
}

async fn load_slice() -> io::Result<Option<Vec<u8>>> {
    let d = dirs::cache_dir()
	.map(|x| x.join("repo-server").join("cache.bin"))
	.filter(|x| x.exists());
    match d {
	Some(x) => fs::read(x).await.map(|x| Some(x)),
	None => Ok(None),
    }
}

fn cache_from_bytes(v: Vec<u8>) -> Result<Cache, CacheReadingError> {
    let r = flexbuffers::Reader::get_root(&v)?;
    Ok(Cache::deserialize(r)?)
}

impl Cache {
    pub async fn load() -> Result<Cache, CacheReadingError> {
	load_slice().await?
	.map(|x| cache_from_bytes(x))
            .transpose()
            .map(|x| x.unwrap_or_default())
    }
    pub async fn save(&self) -> Result<(), CacheWritingError> {
	let d = dirs::cache_dir().unwrap().join("repo-server");
	fs::create_dir_all(&d).await?;
	let f = d.join("cache.bin");
	let mut s = flexbuffers::FlexbufferSerializer::new();
	self.serialize(&mut s)?;
	fs::write(f, s.view()).await?;
	Ok(())
    }

    pub fn update_repo_paths(&mut self, new_paths: Vec<PathBuf>) -> Vec<PathBuf> {
	let newly_added = self.repo_paths.iter().filter(|x| !self.repo_paths.contains(x)).map(|x| x.clone()).collect();
	self.repo_paths = new_paths;
	newly_added
    }
}
