# Simulator

This is an ocaml simulator for the compositional memory model. The
simulator outputs a denotation for an input program.

## Batch mode

To run the program and get a list of derivations do `make check` in `data/`.

## Usage

Example usage:

```
./compositional.byte --check data/tests/test6/LB.lit
```


## Build
To install dependancies and build: 

```
opam switch install 4.10.0
opam install ocamlbuild ocamlfind ppx_deriving batteries oUnit ocamlgraph menhir yojson ppx_deriving_yojson
# Optionally if you want to use an older version of OCaml:
opam install stdlib-shims
make
```
