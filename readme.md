# Installation
1. [Install rustup](https://www.rust-lang.org/tools/install)
2. 
    1. **Ubuntu**: `sudo apt install z3`
    2. **Windows** download [z3](https://github.com/Z3Prover/z3/releases) version 4.8.5  and make sure z3 is available as a binary on PATH
3.
    1. **Ubuntu**: ```sudo apt install cmake llvm clang libclang-dev```
    2. **Windows**: download [cmake](https://cmake.org/download/) and [llvm](https://llvm.org/builds/)
5. run `cargo build  --release` in the root folder (it can take 20 - 30 min to build due to z3 rust bindings the package)
6. Run with cmd `target/release/jip`



# Usage:

```
    jip [OPTIONS] <PATH> <SUBCOMMAND>

ARGS:
    <PATH>    path to oox program

OPTIONS:
    -a, --adaptive-pruning
            Turns on adaptive adaptive probabilistic pruning (prune probability will increase with
            succesfull prunes and vice versa)

    -c, --constant-pruning
            Turns on constant pruning (SEE will try to prune all paths)

        --cvc4-arg <CVC4_ARG>
            Passes the custom argument to call cvc4

    -e, --expression-evaluator
            Turns on the expression evaluator

    -f, --formula-caching
            Turns on formula caching

    -h, --help
            Print help information

    -i, --infer-size <INFER_SIZE>
            The maximum number of iterations that the interval inference algorithm performs
            [default: 0]

    -p, --probabilistic-pruning
            Turns on probabilistic pruning (SEE will try to prune 25% of all paths)

    -s, --symbolic-array-size <SYMBOLIC_ARRAY_SIZE>
            The maximum size of a symbolic array, if none is set the size is symbolic

    -V, --version
            Print version information

        --yices2-arg <YICES2_ARG>
            Passes the custom argument to call yices2

        --z3-api
            Use z3's c++ api

        --z3-arg <Z3_ARG>
            Passes the custom argument to call z3

SUBCOMMANDS:
    bench        Measure time to verify a program
    help         Print this message or the help of the given subcommand(s)
    print-cfg    Print cfg in Dot format
    verify       Verify program and print result

```

# OOX
Due to the shortcomings of Jip's parser you must prepended fields with a hyphen: 
```
class Node {
    int value;
    Node next;
}
```
becomes
```
class Node {
    - int value;
    - Node next;
}
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

