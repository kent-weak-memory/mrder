# Simulator
This simulator implements a denotational semantics for weak memory concurrency that avoids thin-air reads, provides
data-race free programs with sequentially consistent semantics (DRF-SC), and supports a compositional refinement
relation for validating optimisations. The semantics identifies false program dependencies that might be removed by
compiler optimisation, and leaves in place just the dependencies necessary to rule out thin-air reads. We argue that the
dependency calculation of this semantics offers a practical route to fixing the long-standing problem of thin-air reads
in the C++ specification.

This work was published at ESOP 2020:
https://link.springer.com/chapter/10.1007/978-3-030-44914-8_22

There is an online interface to the semantics:
https://www.cs.kent.ac.uk/projects/MRDer/

Since publication this code has been refined for improved performance and adaptation into a web tool. 

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
