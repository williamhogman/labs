use tantivy::collector::TopDocs;
use tantivy::query::QueryParser;
use std::path::Path;
use tantivy::schema::*;
use tantivy::{Index, ReloadPolicy, IndexWriter, IndexReader};
use tempfile::TempDir;
use bollard::Docker;
use bollard::container::{ListContainersOptions, LogOutput, LogsOptions};
use futures::future;
use std::sync::{Arc, RwLock};
use futures::stream::{self, StreamExt};

use std::time::Duration;


fn build_schema() -> tantivy::schema::Schema {
    // First we need to define a schema ...
    let mut schema_builder = Schema::builder();
    schema_builder.add_text_field("source", TEXT | STORED);

    schema_builder.add_text_field("line", TEXT | STORED);

    schema_builder.build()
}

struct Search {
    pub index: Box<Index>,
    pub writer: IndexWriter,
    pub reader: IndexReader,

}

impl Search {
    pub fn new_in_tempdir() -> tantivy::Result<(TempDir, Search)> {
	let td = TempDir::new()?;
	let search = Self::new(td.as_ref())?;
	Ok((td, search))
    }
    pub fn new(path: &Path) -> tantivy::Result<Search> {
	println!("Creating in {:?}", path);
	let index = Box::new(Index::create_in_dir(&path, build_schema())?);
	let reader = index
		.reader_builder()
		.reload_policy(ReloadPolicy::OnCommit)
	    .try_into()?;
	let writer = index.writer(50_000_000)?;
	Ok(Search {
	    index: index,
	    reader: reader,
	    writer: writer,
	})
    }

    pub fn index_line(&mut self, ll: &LogLine) -> tantivy::Result<()> {
	let schema = self.index.schema();
	let source_f = schema.get_field("source").unwrap();
	let line_f = schema.get_field("line").unwrap();
	let mut doc = Document::new();
	doc.add_text(source_f, &ll.source);
	doc.add_text(line_f, &ll.line);
	self.writer.add_document(doc);
	self.writer.commit()?;
	Ok(())
    }

    pub fn search(&self, query: &str) -> tantivy::Result<()> {
	let searcher = self.reader.searcher();

	let schema = self.index.schema();
	let source_f = schema.get_field("source").unwrap();
	let line_f = schema.get_field("line").unwrap();
	let query_parser = QueryParser::for_index(&self.index, vec![source_f, line_f]);

	// `QueryParser` may fail if the query is not in the right
	// format. For user facing applications, this can be a problem.
	// A ticket has been opened regarding this problem.
	let query = query_parser.parse_query(query)?;
	let top_docs = searcher.search(&query, &TopDocs::with_limit(10))?;

	for (_score, doc_address) in top_docs {
            let retrieved_doc = searcher.doc(doc_address)?;
            println!("{}", schema.to_json(&retrieved_doc));
	};
	Ok(())
    }
}



struct LogLine {
    source: String,
    line: String,
}


#[tokio::main]
async fn main() {
    let (_td, search) = Search::new_in_tempdir().unwrap();

    let d = Docker::connect_with_local_defaults().unwrap();
    let opts = Some(ListContainersOptions::<String>{..Default::default()});
    let v = d.list_containers(opts).await.unwrap();

    let search = Arc::new(RwLock::new(search));

    let mut hands = Vec::new();
    for x in v {
	let id = x.id.unwrap().clone();
	let name = x.names.and_then(|x| Some(x.first()?.clone())).unwrap().strip_prefix("/").unwrap_or("").to_string();
	let search = search.clone();
	let stream = d.logs(&name, Some(LogsOptions::<String>{follow: true, stdout: true, stderr: true, since: 0, tail: "all".to_string(), timestamps: true, until: -1})).for_each(move |row| {
	    if let Ok(output) = row {
		let m = match output {
		    LogOutput::StdErr { message: m } => m,
		    LogOutput::StdOut { message: m } => m,
		    LogOutput::StdIn { message: m } => m,
		    LogOutput::Console { message: m } => m,
		};
		let m = std::str::from_utf8(&m).unwrap().to_string();
		search.write().unwrap().index_line(&LogLine{source: name.clone(), line: m}).unwrap();
	    }
	    future::ready(())
	});
	hands.push(tokio::spawn(stream));
    }
    future::join_all(hands).await;
    search.read().unwrap().search("database").unwrap();
}
