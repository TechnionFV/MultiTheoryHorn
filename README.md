# MultiTheoryHorn
TODO [Omer]: Fill

## API
MultiTheoryHorn's API is defined in: src/multi_theory_fixedpoint.h.
The API follows the same general design as Z3’s `fixedpoint` engine, while adding
support for cross-theory constraints and interface constraints that connect different theories.

## How to build?
Before building, make sure to have cloned the z3 repository locally.
Run the following in the top level directory of the repository.
```
export <path_to_z3_root>
make
```
A build directory will be created which contains the benchmark binary.

## Dependencies
* [The Z3 Theorem Prover](https://github.com/Z3Prover/z3)
