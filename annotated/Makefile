ifeq (,$(wildcard ./Makefile.config))
 $(error FAILURE: You need a file Makefile.config to indicate VST location)
endif
include Makefile.config
VSTDIRS=msl sepcomp veric floyd
COMPCERT=$(VSTDIR)compcert/
COQFLAGS=$(foreach d, $(VSTDIRS), -Q $(VSTDIR)$(d) VST.$(d)) -R $(COMPCERT) compcert $(EXTFLAGS) -Q cprogs/ ""

DEPFLAGS:=$(COQFLAGS)
COQC=$(COQBIN)coqc -w -deprecated-focus,-deprecated-unfocus
COQTOP=$(COQBIN)coqtop
COQDEP=$(COQBIN)coqdep $(DEPFLAGS)
COQDOC=$(COQBIN)coqdoc -d doc/html -g  $(DEPFLAGS)

CPROGSDIR=cprogs
CPROGS=append

all: clightgen
	@test -f .depend || $(MAKE) depend
	$(MAKE) _CoqProject $(CPROGS:=_verif.vo)

# make sure clightgen is built in parent directory
.PHONY: clightgen depend
clightgen ../clightgen.exe:
	$(MAKE) -C .. clightgen

CLIGHTGEN=../clightgen

depend .depend: cprogs
	@$(COQDEP) *.v $(CPROGSDIR)/*.v > .depend

$(CPROGSDIR)/%.v: %.c ../clightgen.exe
	$(CLIGHTGEN) -normalize -o $@ $<

$(CPROGSDIR)/%_annotation.v: %.c ../clightgen.exe
	$(CLIGHTGEN) -normalize -A -V $*_def -V $* -o $@ $<

cprogs: $(foreach c, $(CPROGS), $(CPROGSDIR)/$(c).v $(CPROGSDIR)/$(c)_annotation.v)

%.vo: %.v
	@echo COQC $<
	@$(COQC) $(COQFLAGS) $<

_CoqProject:
	@echo '$(COQFLAGS)' > _CoqProject

.PHONY: clean
clean:
	@rm -f $(CPROGSDIR)/*.v $(CPROGSDIR)/*.vo $(CPROGSDIR)/*.glob $(CPROGSDIR)/.*.aux
	@rm -f *.vo
	@rm -f *.glob
	@rm -f .*.aux
	@rm -f .depend
	@rm -f _CoqProject


-include .depend
