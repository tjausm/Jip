extern crate lalrpop;
use std::env;
use std::fs::read_dir;
use std::fs::DirEntry;
use std::fs::File;
use std::io::Write;
use std::path::Path;

fn main() {

    //necessary for the Lalrpop to work ()
    lalrpop::process_root().unwrap();

    // code to generate one unit test per oox program in the tests/programs folder
    // src: https://blog.cyplo.dev/posts/2018/12/generate-rust-tests-from-data/
    let out_dir = env::var("OUT_DIR").unwrap();
    let destination = Path::new(&out_dir).join("tests.rs");
    let mut test_file = File::create(&destination).unwrap();

    // writes test file header, put `use`, `const` etc there
    write_header(&mut test_file);

    let test_programs = read_dir("./tests/programs").unwrap();

    for directory in test_programs {
        write_test(&mut test_file, &directory.unwrap());
    }
}

//generates 1 test per file using either the test_template or the test_faulty_template 
fn write_test(test_file: &mut File, directory: &DirEntry) {
    let directory = directory.path().canonicalize().unwrap();
    let path = directory.display();
    let faulty = format!("{}", path).ends_with("faulty");
    let test_name = format!("{}", directory.file_name().unwrap().to_string_lossy());

    if faulty {
        write!(
            test_file,
            include_str!("./tests/test_faulty_template"),
            name = test_name,
            path = path
        )
        .unwrap();
    } else {
        write!(
            test_file,
            include_str!("./tests/test_template"),
            name = test_name,
            path = path
        )
        .unwrap();
    }
}
fn write_header(test_file: &mut File) {
    write!(test_file, 
    r#"
    use assert_cmd::Command;
    use predicates::prelude::*;
    use predicates::str::*;
    "#).unwrap();
}

