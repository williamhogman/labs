use serde::{Serialize, Deserialize};
use tokio::fs;
use std::path::Path;
use crate::err::Result;
use std::ffi::OsStr;

#[derive(Deserialize, Default)]
pub struct Config {
    pub keys: Keys,
    pub folders: Vec<Folder>
}

#[derive(Deserialize, Default)]
pub struct Keys {
    github: Option<String>,
}

#[derive(Deserialize)]
pub struct Folder {
    github: String,
    path: String,
}

const GITHUB_TOKEN_VAR: &str = "GITHUB_TOKEN";

impl Keys {
    pub fn github_key(&self) -> Option<String> {
	self.github.clone().or(std::env::var(GITHUB_TOKEN_VAR).ok())
    }
}

impl Folder {
    pub fn as_path(&self) -> Result<String> {
	let path = shellexpand::full(&self.path)?;
	Ok(path.to_string())
    }

    pub fn github_name(&self) -> &str {
	&self.github
    }
}

const APP_NAME: &str = "repo-server";
const CONFIG_FILE: &str = "config.toml";

impl Config {
    pub async fn load() -> Result<Config> {
	let cfg_path = dirs::config_dir().map(|p| p.join(APP_NAME).join(CONFIG_FILE)).filter(|p| p.exists());
	if let Some(path) = cfg_path {
	    let buf = fs::read(path).await?;
	    Ok(toml::from_slice(&buf)?)
	} else {
	    Ok(Config::default())
	}
    }
}
