use git2::{Repository, RemoteCallbacks, Cred, FetchOptions, Direction, Reference, AnnotatedCommit, Error};
use std::path::{Path, PathBuf};

fn fetch(repo: &Repository) -> Result<(), git2::Error> {
    let mut callbacks = RemoteCallbacks::new();
    callbacks.credentials(|_url, username_from_url, _allowed_types| {
	git2::Cred::ssh_key(
	    username_from_url.unwrap(),
	    None,
	    &dirs::home_dir().unwrap().join(".ssh").join("id_rsa"),
	    None,
	)
    });
    let mut remote = repo.find_remote("origin")?;
    let mut fetch_opts = FetchOptions::new();
    fetch_opts.remote_callbacks(callbacks);

    let mut callbacks = RemoteCallbacks::new();
    callbacks.credentials(|_url, username_from_url, _allowed_types| {
	git2::Cred::ssh_key(
	    username_from_url.unwrap(),
	    None,
	    Path::new(&format!("{}/.ssh/id_rsa", std::env::var("HOME").unwrap())),
	    None,
	)
    });
    remote.connect_auth(Direction::Fetch, Some(callbacks), None)?;
    remote.fetch(&["master"], Some(&mut fetch_opts), None)?;
    remote.disconnect()?;
    Ok(())
}

fn fast_forward(
    repo: &Repository,
    lb: &mut Reference,
    rc: &AnnotatedCommit,
) -> Result<(), Error> {
    let name = match lb.name() {
        Some(s) => s.to_string(),
        None => String::from_utf8_lossy(lb.name_bytes()).to_string(),
    };
    let msg = format!("Fast-Forward: Setting {} to id: {}", name, rc.id());
    println!("{}", msg);
    lb.set_target(rc.id(), &msg)?;
    repo.set_head(&name)?;
    repo.checkout_head(None)?;
    Ok(())
}


fn fast_forward_if_relevant(repo: &git2::Repository) -> Result<(), git2::Error> {
    let fetch_head = repo.find_reference("FETCH_HEAD")?;
    let rc = repo.reference_to_annotated_commit(&fetch_head)?;
    let analysis = repo.merge_analysis(&[&rc])?;
    if !analysis.0.is_fast_forward() {
	return Ok(())
    }
    let refname = format!("refs/heads/{}", "master");
    let mut r = repo.find_reference(&refname)?;
    fast_forward(repo, &mut r, &rc)?;
    Ok(())
}



async fn update_git_repo(path: PathBuf) -> Result<(), git2::Error> {
    let p = path.clone();
    tokio::task::spawn_blocking(move || {
	let repo = git2::Repository::open(p)?;
	fetch(&repo)?;
	fast_forward_if_relevant(&repo)?;
	Ok(())
    }).await.unwrap()
}

pub async fn update_git_repos(repos: &Vec<PathBuf>) -> Vec<git2::Error> {
    let mut errors = Vec::new();
    for r in repos {
	if let Err(e) = update_git_repo(r.to_path_buf()).await {
	    errors.push(e);
	}
    }
    return errors;
}
