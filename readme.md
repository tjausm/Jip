# Building
1. [Install rustup](https://www.rust-lang.org/tools/install)
2. 
    1. **Ubuntu**: `sudo apt install z3`
    2. **Windows** download z3 version 4.8.5 [z3](https://github.com/Z3Prover/z3/releases) and make sure z3 is available as a binary on PATH
4.
    1. **Ubuntu**: ```sudo apt install cmake llvm```
    2. **Windows**: download [cmake](https://cmake.org/download/) and [llvm](https://llvm.org/builds/)
5. run `cargo build  --release` in the root folder (it can take 20 - 30 min to build due to z3 the package)
6. Run with cmd `target/release/jip`



# Usage:

```
jip.exe <LOAD_MODE> <PROGRAM> <SUBCOMMAND>

ARGS:
    <LOAD_MODE>    How to load the program [possible values: file, string]
    <PROGRAM>      Filepath or program as string

OPTIONS:
    -h, --help       Print help information
    -V, --version    Print version information

SUBCOMMANDS:
    bench        Measure time to verify a program
        USAGE:
            jip.exe <LOAD_MODE> <PROGRAM> bench <START> [ARGS]

        ARGS:
            <START>       Given start depth s we measure verification time for depth s
            <END>         Gven end depth e we measure verification time for each depth between s and e
                          with intervals of 5
            <INTERVAL>    Given interval i we measure verification time for each depth between s and e
                          with intervals of i [default: 5]

    print-cfg    Print cfg in Dot format

    verify       Verify program and print result
        USAGE:
            jip.exe <LOAD_MODE> <PROGRAM> verify [OPTIONS] [DEPTH]

        ARGS:
            <DEPTH>    Up to which depth program is evaluated [default: 40]
```


# Testing
All tests are executed with `cargo test -r`, we have 2 types of tests:

1. **Unit tests**: constructed using the [default method](https://doc.rust-lang.org/rust-by-example/testing/unit_testing.html).
1. **Program tests**: one test is constructed for each OOX program in the `src/tests/programs` folder. We assume a test program contains no violation of it's assertions unless it has a file name ending in `_faulty`.

# Cheatsheet
- **Testing** 
    - `cargo test -r` 
    - `cargo test -- --test-threads 3`   
    - `cargo test -- --no-capture`   
- **Build** 
    - `cargo build`
    - `cargo build --release`
- **Generate docs** -> `cargo doc --open`
- **Run** -> `cargo build` and then `target/debug/jip.exe`

