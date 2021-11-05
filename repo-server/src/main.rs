mod config;
mod err;
mod cache;
mod locators;
mod git;

use err::Result;
use config::Config;
use serde_json::Value;
use octocrab::params;
use std::sync::{Arc};
use tokio::sync::RwLock;

async fn get_org_repos(octocrab: &octocrab::Octocrab, name: &str) -> Result<Vec<octocrab::models::Repository>, octocrab::Error> {
    let mut v = Vec::new();
    let mut current_page = octocrab
        .orgs(name)
        .list_repos()
        .repo_type(params::repos::Type::Sources)
        .per_page(100)
        .send()
        .await?;
    let mut prs = current_page.take_items();
    for pr in prs.drain(..) {
	v.push(pr)
    }

    while let Ok(Some(mut new_page)) = octocrab.get_page(&current_page.next).await {
        prs.extend(new_page.take_items());

        for pr in prs.drain(..) {
	    v.push(pr)
        }

        current_page = new_page;
    }
    Ok(v)
}

struct App {
    pub config: config::Config,
    pub cache: RwLock<cache::Cache>,
}

impl App {
    pub async fn load() -> crate::err::Result<Arc<App>> {
	let config = config::Config::load().await?;
	let cache = RwLock::new(cache::Cache::load().await?);
	Ok(Arc::new(App { config, cache }))
    }
    pub async fn save(&self) -> crate::err::Result<()> {
	self.cache.write().await.save().await?;
	Ok(())
    }
}


#[tokio::main]
async fn main() -> crate::err::Result<()> {
    let app = App::load().await.unwrap();
    /*

    let github_key = res.keys.github_key().unwrap();

    let octocrab = octocrab::OctocrabBuilder::new()
        .personal_token(github_key)
    .build()?;*/

    let a = app.clone();
    let je = tokio::task::spawn(async move {
	let repos = {
	    let cache = a.cache.read().await;
	    cache.repo_paths.clone()
	};
	let errs = git::update_git_repos(&repos).await;
	for r in errs {
	    println!("{:?}", r);
	}
    });

    let a = app.clone();
    let jo = tokio::task::spawn(async move {
	let r = locators::find_repos();
	println!("located repos! {:}", r.len());
	let new_repos = {
	    let mut cache = a.cache.write().await;
	    cache.update_repo_paths(r)
	};
	println!("new_repos: {:?}", new_repos);
	let errs = git::update_git_repos(&new_repos).await;
	for r in errs {
	    println!("{:?}", r);
	}
    });

    je.await.unwrap();
    jo.await.unwrap();
    app.save().await.unwrap();
    Ok(())
}
