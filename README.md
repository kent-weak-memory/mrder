# Simulator

This is an ocaml simulator for the compositional memory model. The
simulator outputs a denotation for an input program.

## Batch mode

You can build a set of diagrams using `make` in `data/`. To run the
program and get a list of derivations do `make check` in `data/`.

## Usage

Example usage:

```
./compositional.byte --pp-denotation data/lb.lit
```

This will output the justification relation from the denotation.

To generate a pdf of a program there's a `Makefile` template you can
follow. Alternatively, to make a diagram in a stand-alone way:

```
cat data/diagrams/preamble.tex > diagram.tex
./compositional.byte --pp-tex --hide-denotation data/foo.lit >> diagram.tex
lualatex diagram.tex
```

With these diagrams you may use the event numbers to pick an
interesting configuration and test if its in ⊢*.

You can adjust the `--values` option to modify the value set used in
the denotation.

## Build
To install dependancies and build: 

```
opam switch install 4.07.1
opam install ocamlbuild ocamlfind ppx_deriving batteries oUnit ocamlgraph menhir yojson ppx_deriving_yojson
# Optionally if you want to use an older version of OCaml:
opam install stdlib-shims
make
```

## Architecture

The project is broken into two implementations of similar memory
models. A Non-coherent memory model, under `src/non-coherent` and a
coherent memory model, under `src/coherent`.

These provide functions and types to satisfy the interface specified
in `src/Model.ml`, which are realised in `src/non-coherent/NC.ml` and
`src/coherent/C.ml` respectively.

Common code to these models exist, and is in the top level of the
`src/` folder.

The `MM` interface is a functor which takes an implementation of a
memory model (i.e. `C.Coherent` or `NC.NonCoherent` modules), and a
instantiated `RunConfig.Configuration` module.
