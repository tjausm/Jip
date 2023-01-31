extern crate lalrpop;
use std::env;
use std::fs::ReadDir;
use std::fs::read_dir;
use std::fs::DirEntry;
use std::fs::File;
use std::io::Write;
use std::path::Path;

fn main() {
    //necessary for the Lalrpop to work
    lalrpop::process_root().unwrap();

    // code to generate one unit test per oox program in the tests/programs folder
    // src: https://blog.cyplo.dev/posts/2018/12/generate-rust-tests-from-data/
    let out_dir = env::var("OUT_DIR").unwrap();
    let destination = Path::new(&out_dir).join("tests.rs");
    let mut test_file = File::create(&destination).unwrap();

    // writes test file header, put `use`, `const` etc there
    write_header(&mut test_file);

    
    let test_folder = read_dir("./tests/programs").unwrap();
    build_test_from_directory(&mut test_file, test_folder, "")
}

/// recursively build test for each oox program in folder and all it's child folders
fn build_test_from_directory(test_file: &mut File, directory: ReadDir, parent: &str){

    for entry in directory {

        let entry = entry.unwrap();

        // if is directory recurse and pass directory name 
        if entry.file_type().unwrap().is_dir() {
            build_test_from_directory(test_file, read_dir(entry.path()).unwrap(), &format!("{}{}_", parent, entry.file_name().to_string_lossy()))
        } 

        // if is .oox file write test
        else if entry.path().extension().map(|ext| ext == "oox" ) == Some(true) {
            write_test(test_file, &entry, parent);
        }
    }
}

//gens 1 test per program in 'tests/programs/..' folder (file can't have extension)
//tests check if program ending with '_faulty' are shown incorrect,
//and if all other program are proven to be correct
fn write_test(test_file: &mut File, entry: &DirEntry, parent: &str) {
    let entry = entry.path().canonicalize().unwrap();
    let path = entry.display();
    let faulty = entry.file_stem().unwrap().to_string_lossy().ends_with("faulty");
    let test_name = format!("{}{}", parent, entry.file_stem().unwrap().to_string_lossy());

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
    write!(
        test_file,
        r#"
use assert_cmd::Command;
"#
    )
    .unwrap();
}
