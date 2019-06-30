ifeq (,$(wildcard ./Makefile.config))
 $(error FAILURE: You need a file Makefile.config to indicate VST location)
endif
include Makefile.config
VSTDIRS=msl sepcomp veric floyd
COMPCERT=$(VSTDIR)compcert/
COQFLAGS=$(foreach d, $(VSTDIRS), -Q $(VSTDIR)$(d) VST.$(d)) -R $(COMPCERT) compcert $(EXTFLAGS) -Q cprogs/ ""

DEPFLAGS:=$(COQFLAGS)
COQC=$(COQBIN)coqc
COQTOP=$(COQBIN)coqtop
COQDEP=$(COQBIN)coqdep $(DEPFLAGS)
COQDOC=$(COQBIN)coqdoc -d doc/html -g  $(DEPFLAGS)

CPROGSDIR=cprogs/
CPROGS=append sumarray2 min
all: clightgen
	@test -f .depend || $(MAKE) depend
	$(MAKE) _CoqProject $(addprefix $(CPROGSDIR), $(CPROGS:=_verif.vo))

# make sure clightgen is built in parent directory
.PHONY: clightgen depend
clightgen ../clightgen.exe:
	$(MAKE) -C .. clightgen

CLIGHTGEN=../clightgen

depend .depend: cprogs
	@$(COQDEP) *.v $(CPROGSDIR)/*.v > .depend

$(CPROGSDIR)/%_prog.v: %.c ../clightgen.exe
	$(CLIGHTGEN) -normalize -o $@ $<

$(CPROGSDIR)/%_annot.v: %.c ../clightgen.exe
	$(CLIGHTGEN) -normalize -A -V $*_def -V $*_prog -o $@ $<

cprogs: $(foreach c, $(CPROGS), $(CPROGSDIR)$(c)_prog.v $(CPROGSDIR)$(c)_annot.v)

%.vo: %.v
	@echo COQC $<
	@$(COQC) $(COQFLAGS) $<

_CoqProject:
	@echo '$(COQFLAGS)' > _CoqProject

.PHONY: clean
clean:
	@rm -f $(CPROGSDIR)/*_prog.v $(CPROGSDIR)/*_annot.v $(CPROGSDIR)/*.vo $(CPROGSDIR)/*.glob $(CPROGSDIR)/.*.aux
	@rm -f *.vo
	@rm -f *.glob
	@rm -f .*.aux
	@rm -f .depend
	@rm -f _CoqProject


-include .depend
