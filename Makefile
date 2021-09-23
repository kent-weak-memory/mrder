BINARIES = compositional.byte 
PACKAGES = ppx_deriving.show,ppx_deriving.eq,ppx_deriving_yojson
SOURCE_FILES = src/*.ml src/*.mli \
               src/parse/*.ml src/parse/*.mly src/parse/*.mll \
               src/tex/*.ml src/tex/*.mli \
               src/json/*.ml\
               src/axiomatic/*.ml src/axiomatic/*.mli \
               src/ppo/*.ml src/ppo/*.mli \
               test/*.ml

all: $(BINARIES)

%.byte: $(SOURCE_FILES)
	ocamlbuild -use-ocamlfind -tag 'debug' -package $(PACKAGES) $@

%.native: $(SOURCE_FILES)
	ocamlbuild -use-ocamlfind -package $(PACKAGES) $@

clean:
	ocamlbuild -clean
