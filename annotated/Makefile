-include Makefile.config

DEPFLAGS:=$(COQFLAGS)
COQC=$(COQBIN)coqc -w -deprecated-focus,-deprecated-unfocus
COQTOP=$(COQBIN)coqtop
COQDEP=$(COQBIN)coqdep $(DEPFLAGS)
COQDOC=$(COQBIN)coqdoc -d doc/html -g  $(DEPFLAGS)

all: _CoqProject append_verif.vo

# make sure clightgen is built in parent directory
.PHONY: clightgen depend
clightgen:
	$(MAKE) -C .. clightgen

CLIGHTGEN=../clightgen

depend .depend:
	@$(COQDEP) *.v > .depend

%.v: %.c clightgen
	$(CLIGHTGEN) -normalize $<

%_annotation.v: %.c clightgen %_def.vo
	$(CLIGHTGEN) -normalize -A -o $@ -V $*_def -V $* $<

%.vo: %.v
	@echo COQC $<
	@$(COQC) $(COQFLAGS) $<

_CoqProject:
	@echo $(COQFLAGS) > _CoqProject

include .depend
