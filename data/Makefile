OCAMLRUNPARAM=OCAMLRUNPARAM="l=8G,b"
TOOL = ../compositional.byte
VALUES ?= "0,1"
MODEL = ppo
OPTIONS = --pp-denotation --values $(VALUES) --check --closed-programs --max-steps 2
PREAMBLE = ./diagrams/preamble.tex
TEX_OPTIONS = --interaction=batchmode

PROGRAMS = tests/basic.lit \
           $(wildcard tests/jctc/*.lit) \
           $(wildcard tests/imm/*.lit) \
           $(wildcard tests/test6/*.lit) \
           $(wildcard tests/atomics/*.lit) \
           $(wildcard tests/popl_promising/*.lit) \
           $(wildcard tests/popl_bridging/*.lit) \
           $(wildcard tests/popl_bubbly/*.lit) \
           $(wildcard tests/esop_problem/*.lit) \
           $(wildcard tests/pldi_repairing/*.lit)
#          $(wildcard tests/popl_grounding/*.lit)
#          $(wildcard tests/test6/*.lit) \


DIAGRAMS = $(shell echo $(patsubst %.lit,diagrams/%.pdf,$(PROGRAMS)) | tr ' ' '\n' | sort -V)
DERIVATIONS = $(shell echo $(patsubst %.lit,diagrams/%.deriv,$(PROGRAMS)) | tr ' ' '\n' | sort -V)
INTERMEDIATE = $(patsubst %.pdf,%.out,$(DIAGRAMS) $(DIAGRAM_MERGED)) \
	$(patsubst %.pdf,%.log,$(DIAGRAMS) $(DIAGRAM_MERGED)) \
	$(patsubst %.pdf,%.aux,$(DIAGRAMS) $(DIAGRAM_MERGED))

.INTERMEDIATE: $(INTERMEDIATE)
.PRECIOUS: $(TOOL)

all: $(PREAMBLE) $(DIAGRAMS) $(TOOL)
check: $(DERIVATIONS) $(TOOL)

tool:
	make -C .. || true

diagrams/%.tex: %.lit $(TOOL)
	@mkdir -p $(dir $@)
	@cat $(PREAMBLE) > $@
	@$(OCAMLRUNPARAM) $(TOOL) $(OPTIONS) --pp-tex $(MODEL) $@ $<
	@cat end_document >> $@

diagrams/%.pdf diagrams/%.out diagrams/%.log diagrams/%.aux: diagrams/%.tex $(TOOL)
	@cd $(dir $<) && lualatex $(TEX_OPTIONS) $(notdir $<) 2>&1 > /dev/null

diagrams/jctc/%.pdf diagrams/jctc/%.out diagrams/jctc/%.log diagrams/jctc/%.aux: diagrams/jctc/%.tex $(TOOL)
	@cd $(dir $<) && lualatex $(TEX_OPTIONS) $(notdir $<) 2>&1 > /dev/null

diagrams/%.deriv: %.lit $(TOOL)
	@mkdir -p $(dir $@)
	@$(OCAMLRUNPARAM) $(TOOL) $(OPTIONS) --pp-tex $(MODEL) /dev/null $< | tee $@

run: $(DERIVATIONS)

jctc: $(patsubst %.lit,diagrams/%.pdf, $(wildcard tests/jctc/*.lit))

clean: tidy
	@echo Removing diagrams...
	@rm -f $(DIAGRAMS)

tidy: 	
	@echo Removing latex files...
	@rm -f $(patsubst %.lit,diagrams/%.tex,$(PROGRAMS))
	@rm -f diagrams.tex dbody.tex
	@rm -f $(INTERMEDIATE)
	@echo Removing derivations...
	@rm -f $(DERIVATIONS)

