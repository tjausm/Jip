# Build
1. [Install rustup](https://www.rust-lang.org/tools/install)
2. Install [z3](https://github.com/z3prover/z3) and make sure cmd `z3` is in your path (Jip starts the smt-solver in de backend as a seperate process using said cmd)
3. optional: to use [yices2](https://yices.csl.sri.com/) as backend install and make sure cmd `yices` is in your path and refers to the smt2 version of yices (standard yices uses it's own input language but Jip needs the version of yices using `smt-lib` language)
4. optional: to use [cvc4](https://cvc4.github.io/downloads.html) as backend install and make sure cmd `cvc4` is in your path 
5. run `cargo build`


# Usage:

```
    jip.exe [OPTIONS] <PATH> [ARGS] <SUBCOMMAND>

ARGS:
    <PATH>           path to oox program
    <PRUNE_RATIO>    number between 0 and 255 denoting how deep we should prune , 0 = no
                     pruning, 127 = prune to 50% of depth and so on [default: 0]
    <SOLVER>         Defines the smt-solver used by the backend [default: z3] [possible values:
                     z3, yices2, cvc4]

OPTIONS:
    -h, --help          Print help information
    -s, --simplifier    Turns on the front end simplifier
    -V, --version       Print version information

SUBCOMMANDS:
    bench        Measure time to verify a program
    help         Print this message or the help of the given subcommand(s)
    print-cfg    Print cfg in Dot format
    verify       Verify program and print result
```


# Testing
All tests are executed with `cargo test`, we have 2 types of tests:

1. **Unit tests**: constructed using the [default method](https://doc.rust-lang.org/rust-by-example/testing/unit_testing.html).
1. **Program tests**: one test is constructed for each OOX program in the `src/tests/programs` folder. We assume a test program contains no violation of it's assertions unless it has a file name ending in `_faulty`.

# Cheatsheet
- **Testing** 
    - `cargo test`
    - `cargo test -- --no-fail-fast --test-threads 3`   
    - `cargo test -- --no-capture`   
- **Build** 
    - `cargo build`
    - `cargo build --release`
- **Generate docs** -> `cargo doc --open`
- **Run** -> `cargo build` and then `target/debug/jip.exe`

