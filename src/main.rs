extern crate tokio;
extern crate futures;
extern crate tokio_postgres;
extern crate bytes;
use bytes::Bytes;
use tokio::io;
use tokio::prelude::*;
use tokio::fs::{read_dir, File};
use futures::future::{poll_fn, result};
use tokio_postgres::NoTls;

fn get_queries(dir: String) -> impl Future<Item=Vec<(String, String)>, Error=std::io::Error> {
    let stream = read_dir(dir)
        .flatten_stream()
        .map(|x| {
            let path = x.path();
            poll_fn(move || x.poll_file_type()).map(|res| (path, res.is_file())).into_stream()
        })
        .flatten()
        .filter(|(_, is_file)| *is_file)
        .map(|(path, _b)| path)
        .filter(|path| path.extension().map(|ext| ext == "sql").unwrap_or(false))
        .map(|path| {
            let fname = path.to_path_buf();
            File::open(path.to_path_buf()).map(move |mut file| {
                let mut buffer = String::new();
                result(file.read_to_string(&mut buffer).map(move |_x| {
                    (fname.to_str().unwrap().clone().to_string(), buffer)    
                })).into_stream()
            }).into_stream().flatten()
        })
        .flatten();
    stream.collect().into_future()
}

fn query_to_file(client: mut tokion_postgres::Client, query: String, outfile: String) {
    let outfile = File::create(outfile).map_err(|e| {
        eprintln!("err {}", e);
    }).and_then(|mut file| {
        pg_c.map(|mut client| {
            client.prepare("COPY (" + query + ") TO STDOUT WITH CSV HEADER")
                .map(move |smnt| client.copy_out(&smnt, &[]))
                .flatten_stream()
                .map_err(|x| ())
        })
            .map_err(|x| ())
            .flatten_stream()
            .map(move |b| file.poll_write(&b) )
            .map(|x| { println!("{:#?}", x); x })
            .collect()
            .into_future()
    });
    
}

fn main() {
    let res =
        get_queries(".".to_string())
        .map(|x| {
            println!("{:#?}", x);
            ()
        })
        .map_err(|err| {
            println!("{:#?}", err);
            ()
        });

    let pg_c = tokio_postgres::connect("host=localhost user=whn", NoTls)
        .map(|(client, connection)| {
            // The connection object performs the actual communication with the database,
            // so spawn it off to run on its own.
            let connection = connection.map_err(|e| eprintln!("connection error: {}", e));
            tokio::spawn(connection);

            // The client is what you use to make requests.
            client
        });
    let outfile = File::create("res.csv").map_err(|e| {
        eprintln!("err {}", e);
    }).and_then(|mut file| {
        pg_c.map(|mut client| {
            client.prepare("COPY (SELECT 1) TO STDOUT WITH CSV HEADER")
                .map(move |smnt| client.copy_out(&smnt, &[]))
                .flatten_stream()
                .map_err(|x| ())
        })
            .map_err(|x| ())
            .flatten_stream()
            .map(move |b| file.poll_write(&b) )
            .map(|x| { println!("{:#?}", x); x })
            .collect()
            .into_future()
    });
    
    let pg_f = outfile.map(|_| ());

    tokio::run(pg_f);
}
