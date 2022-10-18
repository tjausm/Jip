## Installation (windows)
1. Install rust & cargo
2. Install cmake 
3. Install llvm
4. run `cargo build -vv` in the root folder (it can take 20 - 30 min to build due to z3 the package, add the `-vv` flag to make sure the build process is still in progress)

### Profiler (windows)
1. install [wsl](https://learn.microsoft.com/en-us/windows/wsl/install)

## Testing
All tests are executed with `cargo test`, we have 2 types of tests:

1. **Unit tests**: constructed using the [default method](https://doc.rust-lang.org/rust-by-example/testing/unit_testing.html).
1. **Program tests**: one test is constructed for each OOX program in the `src/tests/programs` folder. We assume a test program contains no violation of it's assertions unless it has a file name ending in `_faulty`.

## Cheatsheet
- **Testing** -> `cargo test`
- **Build** -> `cargo build`
- **Generate docs** -> `cargo doc --open`
- **Run** -> `cargo build` and then `target/debug/jip.exe`

## vragen
- Does require translate to assume and ensure to assert?

## Todo's
- [ ] generate benchmark flag
- [ ] objects representeren in de cfg
    - if we enter constructor we initialize fields, assign referenc of oject to 'this' and we assign 'this' to 'retval'
    - if we enter a method we assign reference of object to 'this'
- [ ] add require and ensure

- [ ] add profiling als program is veel langzamer dan die van stefan
- [ ] object accesing vanaf de heap e.g.
- [ ] generalise over get_from_env and get_from_anEnv
- [ ] fix vector formatting of edges
- [ ] change retval_id to a static string in shared?
- [ ] put all error msgs in one or more enums to 'streamline' them
- [ ] best practices opzoeken voor variable shadowing