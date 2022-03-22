ifeq (, $(wildcard ./Makefile.config))
_:=$(shell (\
  echo "VSTDIR= \# /path/to/VST";\
  echo "COMPCERTDIR= \# /path/to/CompCert"\
) > ./Makefile.config)
$(error FAILURE: Please fill paths to VST and CompCert in Makefile.config)
endif

include Makefile.config
VSTDIRS=msl sepcomp veric floyd
VSTCOMPCERT=$(VSTDIR)/compcert

ACLIGHTDIR=AClight
CPROGSDIR=cprogs
FRONTENDDIR=frontend
DIRS=$(ACLIGHTDIR) $(CPROGSDIR) vfa wand_demo

CPROGS=append sumarray2 reverse min sgn leap_year bst linkedlist unionfind dlinklist


COQFLAGS=$(foreach d, $(VSTDIRS), -Q $(VSTDIR)/$(d) VST.$(d))\
 -R $(VSTCOMPCERT) compcert -Q $(CPROGSDIR) cprogs -Q $(ACLIGHTDIR) AClight $(EXTFLAGS)\
 -Q vfa VFA -Q wand_demo WandDemo
 -Q Split Split
 -Q CSplit CSplit

ifneq (, $(RAMIFYCOQDIR))
 COQFLAGS += -Q $(RAMIFYCOQDIR) RamifyCoq
endif

DEPFLAGS:=$(COQFLAGS)
COQC=$(COQBIN)coqc
COQTOP=$(COQBIN)coqtop
COQDEP=$(COQBIN)coqdep $(DEPFLAGS)
COQDOC=$(COQBIN)coqdoc -d doc/html -g $(DEPFLAGS)

all: _CoqProject frontend
	$(MAKE) $(addprefix $(CPROGSDIR)/, $(CPROGS:=_verif.vo))

_CoqProject: Makefile
	@echo '$(COQFLAGS)' > _CoqProject

ifneq ($(MAKECMDGOALS),clean) # only if the goal is not clean, include actual make rules

.PHONY: frontend
frontend frontend/STAMP:
	@$(MAKE) -f Makefile.frontend

ifneq ($(MAKECMDGOALS),frontend)

include frontend/STAMP # an empty file, to force reloading Makefile after making aclightgen

ACLIGHTGEN=$(wildcard ./aclightgen*)

ifneq (, $(ACLIGHTGEN)) # the following rules are only applicable when $(ACLIGHTGEN) exists

.PHONY: depend
depend .depend: cprogs
	@$(COQDEP) $(patsubst %, %/*.v, $(DIRS)) > .depend

$(CPROGSDIR)/%_prog.v: $(CPROGSDIR)/%.c $(ACLIGHTGEN)
	@$(ACLIGHTGEN) -normalize -o $@ $<

$(CPROGSDIR)/%_annot.v: $(CPROGSDIR)/%.c $(ACLIGHTGEN)
	@$(ACLIGHTGEN) -normalize -A -V cprogs.$*_def -V cprogs.$*_prog -o $@ $<

cprogs: $(foreach c, $(CPROGS), $(CPROGSDIR)/$(c)_prog.v $(CPROGSDIR)/$(c)_annot.v)

include .depend

ifneq (, $(wildcard .depend)) # the following rules are only applicable when .depend exists

%.vo: %.v
	@echo COQC $<
	@$(COQC) $(COQFLAGS) $<

endif # if .depend exists
endif # if $(ACLIGHTGEN) exists
endif # if the goal is not frontend
endif # if the goal is not clean

.PHONY: clean
clean:
	@rm -f $(patsubst %, %/*.vo, $(DIRS))
	@rm -f $(patsubst %, %/*.glob, $(DIRS))
	@rm -f $(patsubst %, %/.*.aux, $(DIRS))
	@rm -f .depend
	@rm -f $(CPROGSDIR)/*_prog.v $(CPROGSDIR)/*_annot.v
	@rm -f _CoqProject
	@$(MAKE) -f Makefile.frontend clean
