include Makefile.config

ifeq ($(VSTDIR),)
  $(error please set variable 'VSTDIR' in 'Makefile.config')
endif

ifeq ($(COMPCERTDIR),)
  $(error please set variable 'COMPCERTDIR' in 'Makefile.config')
endif

ifeq ($(COMPCERTADIR),)
  $(error please set variable 'COMPCERTADIR' in 'Makefile.config')
endif

ifeq ($(SETSDIR),)
  $(error please set variable 'SETSDIR' in 'Makefile.config')
endif

COQC = $(COQBIN)coqc
COQDEP = $(COQBIN)coqdep
PYTHON = python3

CPROGSDIR = cprogs
CPROGS = add abs swap max3 list dlist bst interpreter

-include $(foreach p,$(CPROGS),$(CPROGSDIR)/$p/Makefile.config)

CSPLIT_FILE_NAMES = model_lemmas.v logic_lemmas.v strong.v AClight.v semantics.v \
  semantics_lemmas.v soundness.v AClightFunc.v strongFacts.v strongSoundness.v \
  precise_model_lemmas.v
CSPLIT_FILES = $(addprefix csplit/, $(CSPLIT_FILE_NAMES))

FLOYD_FILE_NAMES = \
  base.v base2.v canon.v client_lemmas.v closed_lemmas.v canonicalize.v \
  proj_reptype_lemmas.v local2ptree_denote.v local2ptree_eval.v \
  local2ptree_typecheck.v semax_tactics.v go_lower.v entailer.v \
  loadstore_mapsto.v loadstore_field_at.v globals_lemmas.v \
  replace_refill_reptype_lemmas.v nested_loadstore.v compare_lemmas.v \
  simple_reify.v simpl_reptype.v sc_set_load_store.v forward_lemmas.v \
  for_lemmas.v subsume_funspec.v call_lemmas.v extcall_lemmas.v diagnosis.v \
  freezer.v forward.v start_function.v library.v deadvars.v Clightnotations.v \
  hints.v reassoc_seq.v linking.v proofauto.v extract_smt.v \
  precise_lemmas.v precise_proofauto.v

FLOYD_FILES = $(addprefix floyd-seq/, $(FLOYD_FILE_NAMES))

UTIL_FILE_NAMES = AClightNotations.v VSTALib.v
UTIL_FILES = $(addprefix utils/, $(UTIL_FILE_NAMES))

CPROG_FILES  = $(CPROGS:%=$(CPROGSDIR)/%/program.v)
CDEF_FILES   = $(CPROGS:%=$(CPROGSDIR)/%/definitions.v)
CANNOT_FILES = $(CPROGS:%=$(CPROGSDIR)/%/annotation.v)

CVERIF_FILES = $(CPROG_FUNCS:%=$(CPROGSDIR)/%/verif.v)
CPROG_PATH_FILES = $(CPROG_PATHS:%=$(CPROGSDIR)/%.v)
CPROG_PATH_VERIF_FILES = $(CPROG_PATHS:%=$(CPROGSDIR)/%_verif.v)

VST_DIRS = msl sepcomp veric floyd
INCLUDE_ACLIGHT = -Q csplit Csplit -Q floyd-seq FloydSeq -R $(CPROGSDIR) cprogs
INCLUDE_COMPCERT = -R $(COMPCERTDIR) compcert
INCLUDE_VST = $(foreach d, $(VST_DIRS), -Q $(VSTDIR)/$(d) VST.$(d))
INCLUDE_UTIL = -Q utils utils
INCLUDE_SETS = -Q $(SETSDIR) SetsClass
COQFLAGS = -w -omega-is-deprecated $(INCLUDE_ACLIGHT) $(INCLUDE_VST) $(INCLUDE_COMPCERT) $(INCLUDE_UTIL) $(INCLUDE_SETS)

GENERATED_ROOTS = $(CPROG_FILES) $(CANNOT_FILES)

$(CPROGSDIR)/%/program.v: $(CPROGSDIR)/%.c
	@mkdir -p $(shell dirname $@)
	@echo "CLIGHTGEN  $<"
	@$(COMPCERTADIR)/clightgen -normalize -o $@ $<

$(CPROGSDIR)/%/annotation.v: $(CPROGSDIR)/%.c
	@mkdir -p $(shell dirname $@)
	@echo "ACLIGHTGEN $<"
	@$(PYTHON) $(COMPCERTADIR)/split.py $< > $(CPROGSDIR)/$*.pc
	@$(COMPCERTADIR)/aclightgen $(CPROGSDIR)/$*.pc
	@rm $(CPROGSDIR)/$*.pc

FILES = $(CSPLIT_FILES) $(FLOYD_FILES) $(UTIL_FILES) \
  $(CPROG_FILES) $(CDEF_FILES) $(CANNOT_FILES) \
  $(CVERIF_FILES) $(CPROG_PATH_FILES) $(CPROG_PATH_VERIF_FILES)

all: $(GENERATED_ROOTS)
	@$(MAKE) _CoqProject
	@test -f .depend || $(MAKE) depend
	@$(MAKE) proof

rebuild:
	@rm -f .depend
	@$(MAKE) all

proof: $(GENERATED_ROOTS) $(FILES:%.v=%.vo)

depend: $(GENERATED_ROOTS)
	@$(COQDEP) $(COQFLAGS) $(FILES) > .depend

_CoqProject:
	@echo '$(COQFLAGS)' > _CoqProject

cprogs: $(GENERATED_ROOTS)

%.vo: %.v
	@echo "COQC       $<"
	@$(COQC) $(COQFLAGS) $<

-include .depend

.PHONY: all rebuild proof depend clean cleanprogs config proofcount

GENERATED=$(GENERATED_ROOTS) $(CPROG_PATH_FILES) $(CPROGS:%=$(CPROGSDIR)/%/Makefile.config)

clean:
	@rm -f .depend
	@rm -f _CoqProject
	@rm -f $(FILES:%.v=%.vo)
	@rm -f $(FILES:%.v=%.vos)
	@rm -f $(FILES:%.v=%.vok)
	@rm -f $(FILES:%.v=%.glob)
	@rm -f .lia.cache
	@rm -f $(foreach f, $(FILES:%.v=%), $(dir $(f)).$(shell basename $(f)).aux)
	@rm -f $(GENERATED)

cleanprogs:
	@rm -f .depend
	@rm -f $(GENERATED:%.v=%.vo)
	@rm -f $(GENERATED:%.v=%.vos)
	@rm -f $(GENERATED:%.v=%.vok)
	@rm -f $(GENERATED:%.v=%.glob)
	@rm -f $(foreach f, $(GENERATED:%.v=%), $(dir $(f)).$(shell basename $(f)).aux)
	@rm -f $(GENERATED)

config:
	@echo "COQBIN=" > Makefile.config
	@echo "VSTDIR=../VST-2.5-patch" >> Makefile.config
	@echo "COMPCERTDIR=../VST-2.5-patch/compcert" >> Makefile.config
	@echo "COMPCERTADIR=../compcert-for-vsta" >> Makefile.config
	@echo "SETSDIR=../sets" >> Makefile.config

proofcount:
	@$(PYTHON) $(COMPCERTADIR)/proofcount.py $(CPROG_FUNCS:%=$(CPROGSDIR)/%)
