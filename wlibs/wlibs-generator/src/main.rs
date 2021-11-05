use octocrab::{params, Octocrab, models, Page};
use tokio::time::{sleep, Duration};
use tokio_stream::{self as stream, StreamExt};
use tokio_stream::wrappers::ReadDirStream;
use tokio::fs;
use tokio::sync::mpsc;
use std::env;
use std::path::PathBuf;
use std::io;
use tokio::io::AsyncWriteExt;
use std::collections::HashSet;
use std::path::Path;

async fn load_data(token: String, chan: mpsc::Sender::<models::Repository>) -> Result<(), octocrab::Error> {
    let octocrab = octocrab::OctocrabBuilder::new()
        .personal_token(token)
        .build()?;

    let page: Page<models::Repository> = octocrab
        .get("/users/williamhogman/starred", None::<&()>)
	.await?;


    let mut next = page.next.clone();

    while let Some(p) = octocrab.get_page::<models::Repository>(&next).await? {
	next = p.next.clone();
        for x in p.into_iter() {
	    chan.send(x).await.unwrap();
        }
    }

    Ok(())
}

#[tokio::main]
async fn main() {
    let entries = ReadDirStream::new(fs::read_dir("..").await.unwrap())
        .map(|e| e.unwrap().path())
	.filter(|x| if let Some(name) = x.file_name() { name != "wlibs-generator" && name != "todo" } else { true })
	.map(|e| e.to_str().unwrap_or("").to_owned())
        .collect::<Vec<String>>().await;

    let (tx, mut rx) = mpsc::channel::<models::Repository>(100);
    let github_token = env::var("GITHUB_TOKEN").unwrap();
    let ld = load_data(github_token, tx);
    tokio::spawn(async move {

	while let Some(x) = rx.recv().await {
	    let name = x.name.clone() + ".md";
	    let mut any_exist = false;
	    for e in &entries {
		let p = Path::new(e).join(&name);
		if fs::metadata(p).await.is_ok() {
		    any_exist = true;
		    break;
		}
	    }
	    if !any_exist {
		let md_path = Path::new("todo").join(&name);
		match fs::File::create(md_path).await {
		    Ok(mut f) => {
			let mut data = String::new();
			data.push_str("---\n");
			data.push_str(&format!("name: \"{}\"\n", x.full_name));
			if let Some(hp) = x.homepage.filter(|x| x != "") {
			    data.push_str(&format!("homepage: \"{}\"\n", hp));
			}
			data.push_str("---\n");
			data.push_str("# ");
			data.push_str(&x.name);
			data.push('\n');
			f.write_all(data.as_bytes()).await.unwrap();
		    }
		    Err(err) => eprintln!("Error creating file {:?}", err)
		}
	    }
	}
    });
    ld.await.unwrap();
}
