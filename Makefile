ifeq (, $(wildcard ./CONFIGURE))
_:=$(shell (\
  echo "VSTDIR= \# /path/to/VST";\
  echo "COMPCERTDIR= \# /path/to/CompCert";\
  echo "COQBIN= \# /path/to/Coq";\
  echo "RAMIFYCOQDIR= \# /path/to/RamifyCoq";\
  echo "COMPCERTADIR= \# /path/to/CompCertA";\
) > ./CONFIGURE)
$(error FAILURE: Please fill paths to VST and CompCert in CONFIGURE)
endif

CURRENT_DIR = "./"
-include CONFIGURE

COQC=$(COQBIN)coqc
COQDEP=$(COQBIN)coqdep

VST_DIRS = msl sepcomp veric floyd
VSTCOMPCERT=$(VSTDIR)/compcert
CPROGSDIR=cprogs
FRONTENDDIR=frontend
CPROGS=append mytest sgn # reverse #sumarray2  min  leap_year bst linkedlist unionfind dlinklist

# CSPLIT_FILE_NAMES = vst_ext.v model_lemmas.v logic_lemmas.v strong.v AClight.v semantics.v soundness.v AClightFunc.v
CSPLIT_FILE_NAMES = model_lemmas.v logic_lemmas.v strong.v AClight.v semantics.v soundness.v AClightFunc.v
CSPLIT_FILES = $(addprefix CSplit/, $(CSPLIT_FILE_NAMES))

FLOYD_FILE_NAMES = coqlib3.v jmeq_lemmas.v \
   find_nth_tactic.v  sublist.v functional_base.v  val_lemmas.v \
   assert_lemmas.v  \
   SeparationLogicFacts.v SeparationLogicAsLogic.v SeparationLogicAsLogicSoundness.v \
   base.v seplog_tactics.v typecheck_lemmas.v const_only_eval.v \
   computable_theorems.v computable_functions.v \
   base2.v \
   canon.v client_lemmas.v closed_lemmas.v canonicalize.v  \
   fieldlist.v \
   type_induction.v \
   nested_pred_lemmas.v \
   align_compatible_dec.v compact_prod_sum.v \
   reptype_lemmas.v aggregate_type.v mapsto_memory_block.v aggregate_pred.v \
   nested_field_lemmas.v \
   efield_lemmas.v proj_reptype_lemmas.v \
   data_at_rec_lemmas.v field_at.v \
   local2ptree_denote.v local2ptree_eval.v local2ptree_typecheck.v \
   semax_tactics.v \
   go_lower.v \
   entailer.v \
   loadstore_mapsto.v loadstore_field_at.v field_compat.v \
   globals_lemmas.v \
   stronger.v \
   replace_refill_reptype_lemmas.v \
   nested_loadstore.v \
   field_at_wand.v \
   compare_lemmas.v \
   simple_reify.v \
   simpl_reptype.v \
   sc_set_load_store.v \
   forward_lemmas.v \
   for_lemmas.v \
   subsume_funspec.v call_lemmas.v extcall_lemmas.v \
   diagnosis.v \
   freezer.v forward.v \
   library.v \
   deadvars.v Clightnotations.v unfold_data_at.v hints.v reassoc_seq.v \
   linking.v list_solver.v data_at_lemmas.v \
   proofauto.v \
   extract_smt.v
FLOYD_FILES = $(addprefix floyd-seq/, $(FLOYD_FILE_NAMES))

CPROG_FILE_NAMES = $(addsuffix _prog.v, $(CPROGS))
CPROG_FILES = $(addprefix cprogs/, $(CPROG_FILE_NAMES))

CDEF_FILE_NAMES = $(addsuffix _def.v, $(CPROGS))
CDEF_FILES = $(addprefix cprogs/, $(CDEF_FILE_NAMES))


INCLUDE_ACLIGHT = -Q CSplit CSplit -Q floyd-seq FloydSeq -Q cprogs cprogs
INCLUDE_COMPCERT = -R $(COMPCERTDIR) compcert
INCLUDE_VST = $(foreach d, $(VST_DIRS), -Q $(VSTDIR)/$(d) VST.$(d))
NORMAL_FLAG = $(INCLUDE_ACLIGHT) $(INCLUDE_VST) $(INCLUDE_COMPCERT)


ifneq (, $(RAMIFYCOQDIR))
 NORMAL_FLAG += -Q $(RAMIFYCOQDIR) RamifyCoq
endif


all: _CoqProject frontend
# $(MAKE) $(addprefix $(CPROGSDIR)/, $(CPROGS:=_verif.vo))

_CoqProject: Makefile
	@echo '$(NORMAL_FLAG)' > _CoqProject

ifneq ($(MAKECMDGOALS),clean) # only if the goal is not clean, include actual make rules
ifneq ($(MAKECMDGOALS),cleanall) # only if the goal is not cleanall, include actual make rules 

.PHONY: frontend
frontend frontend/STAMP:
	@$(MAKE) -f Makefile.frontend

ifneq ($(MAKECMDGOALS),frontend)

include frontend/STAMP # an empty file, to force reloading Makefile after making aclightgen

ACLIGHTGEN=$(wildcard ./aclightgen*)

ifneq (, $(ACLIGHTGEN)) # the following rules are only applicable when $(ACLIGHTGEN) exists

# .PHONY: depend
# depend .depend: cprogs
# 	@$(COQDEP) $(NORMAL_FLAG) $(CSPLIT_FILES) > .depend


$(CPROGSDIR)/%_prog.v: $(CPROGSDIR)/%.c $(ACLIGHTGEN)
	@$(ACLIGHTGEN) -normalize -o $@ $<

$(CPROGSDIR)/%_annot.v: $(CPROGSDIR)/%.c $(ACLIGHTGEN)
	@$(ACLIGHTGEN) -normalize -A -V cprogs.$*_def -V cprogs.$*_prog -o $@ $<

cprogs: $(foreach c, $(CPROGS), $(CPROGSDIR)/$(c)_prog.v $(CPROGSDIR)/$(c)_annot.v)

# include .depend

#ifneq (, $(wildcard .depend)) # the following rules are only applicable when .depend exists

%.vo: %.v
	@echo COQC $<
	@$(COQC) $(COQFLAGS) $<

$(CSPLIT_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(NORMAL_FLAG) $(CURRENT_DIR)$*.v

$(FLOYD_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(NORMAL_FLAG) $(CURRENT_DIR)$*.v

$(CPROG_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(NORMAL_FLAG) $(CURRENT_DIR)$*.v

$(CDEF_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(NORMAL_FLAG) $(CURRENT_DIR)$*.v

all: frontend \
  $(CSPLIT_FILES:%.v=%.vo) \
  $(FLOYD_FILES:%.v=%.vo) \
  $(CPROG_FILES:%.v=%.vo) \
  $(CDEF_FILES:%.v=%.vo)


# endif # if .depend exists
endif # if $(ACLIGHTGEN) exists
endif # if the goal is not frontend
endif # if the goal is not clean
endif # if the goal is not cleanall



.PHONY: clean


cleanall: 
	@make -f Makefile.frontend clean
	@rm -f CSplit/*.vo CSplit/*.glob CSplit/*.aux


clean:
	@rm -f .depend
	@rm -f $(CPROGSDIR)/*_prog.v $(CPROGSDIR)/*_annot.v
	@rm -f _CoqProject
	@rm -f floyd-seq/*.vo floyd-seq/*.glob floyd-seq/*.aux
	@rm -f $(CPROGDIR)/*.vo $(CPROGDIR)/*.glob $(CPROGDIR)/*.aux
