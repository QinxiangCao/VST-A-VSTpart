ifeq (,$(wildcard ./Makefile.config))
 $(error FAILURE: You need a file Makefile.config to indicate locations of VST and clightgen)
endif
include Makefile.config
VSTDIRS=msl sepcomp veric floyd
VSTCOMPCERT=$(VSTDIR)compcert/

ACLIGHTDIR=AClight/
CPROGSDIR=cprogs/
DIRS= $(ACLIGHTDIR) $(CPROGSDIR)
CPROGS=append sumarray2 reverse min

COQFLAGS=$(foreach d, $(VSTDIRS), -Q $(VSTDIR)$(d) VST.$(d))\
 -R $(VSTCOMPCERT) compcert -Q $(CPROGSDIR) cprogs -Q $(ACLIGHTDIR) AClight $(EXTFLAGS)

DEPFLAGS:=$(COQFLAGS)
COQC=$(COQBIN)coqc
COQTOP=$(COQBIN)coqtop
COQDEP=$(COQBIN)coqdep $(DEPFLAGS)
COQDOC=$(COQBIN)coqdoc -d doc/html -g  $(DEPFLAGS)

all: .depend _CoqProject frontend
	$(MAKE) _CoqProject $(addprefix $(CPROGSDIR), $(CPROGS:=_verif.vo))

CLIGHTGEN=$(wildcard ./main*)
#CLIGHTGEN=$(wildcard $(COMPCERTANNOTDIR)/clightgen*)
ifeq (,$(CLIGHTGEN))
 $(error FAILURE: clightgen is not found in parent directory)
endif
ifeq ($(MAKE_CLIGHTGEN), true)
# make sure clightgen is built in parent directory
.PHONY: clightgen
clightgen $(CLIGHTGEN):
	$(MAKE) -C .. clightgen
all: clightgen
endif

.PHONY: depend
depend .depend: cprogs
	@$(COQDEP) $(ACLIGHTDIR)*.v $(CPROGSDIR)*.v > .depend

$(CPROGSDIR)%_prog.v: $(CPROGSDIR)%.c $(CLIGHTGEN)
	$(CLIGHTGEN) -normalize -o $@ $<

$(CPROGSDIR)%_annot.v: $(CPROGSDIR)%.c $(CLIGHTGEN)
	$(CLIGHTGEN) -normalize -A -V cprogs.$*_def -V cprogs.$*_prog -o $@ $<

cprogs: $(foreach c, $(CPROGS), $(CPROGSDIR)$(c)_prog.v $(CPROGSDIR)$(c)_annot.v)

%.vo: %.v
	@echo COQC $<
	@$(COQC) $(COQFLAGS) $<

_CoqProject:
	@echo '$(COQFLAGS)' > _CoqProject

_CoqProject .depend: Makefile

.PHONY: frontend
frontend:
	$(MAKE) -f Makefile.frontend

.PHONY: clean
clean:
#	$(MAKE) -f Makefile.frontend clean
	@rm -f $(CPROGSDIR)*_prog.v $(CPROGSDIR)*_annot.v
	@rm -f $(patsubst %, %/*.vo, $(DIRS))
	@rm -f $(patsubst %, %/*.glob, $(DIRS))
	@rm -f $(patsubst %, %/.*.aux, $(DIRS))
	@rm -f .depend
	@rm -f _CoqProject

ifneq ($(MAKECMDGOALS),clean)
 include .depend
endif
