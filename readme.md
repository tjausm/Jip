## Installation (windows)
1. Install rust & cargo
2. Install cmake 
3. Install llvm
4. run `cargo build -vv` in the root folder (it can take 20 - 30 min to build due to z3 the package, add the `-vv` flag to make sure the build process is still in progress)

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
- every path through a program a valid path? e.g. do we need an ending note to denote the ending or can we just assume that a node without edges is the end
- how can i test that arguments are currently working e.g. 

## Todo's

- [ ] maak numers onderdeel van identifiers (zolang ze niet het eerste teken zijn)
- [ ] move scope entering and leaving to the edges, e.g. if we leave the wrong scope we just dismiss path in SEE0 
- [ ] verwijderen cfg uit return type van recursive cfg builder
- [ ] moeten we onderscheidt maken tussen classes en objects tijdens scope boekhouding
- [ ] generalise over get_from_env and get_from_anEnv
- [ ] vastleggen van vaste namen in de ast e.g. main class (veroorzaakt wel verschil tussen syntax stefan en ast datatype)
- [ ] think about scope leaving loop like fibonaci
- [ ] objects representeren in de cfg
    - if we enter constructor we initialize fields, assign referenc of oject to 'this' and we assign 'this' to 'retval'
    - if we enter a method we assign reference of object to 'this'

- [ ] change retval_id to a static string in shared?
- [ ] add method parameters as edge weights

- [ ] object accesing vanaf de heap e.g.
- [ ] add question mark instead of endless match expressions

- [ ] put all error msgs in one or more enums to 'streamline' them
- [ ] best practices opzoeken voor variable shadowing