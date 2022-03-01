CURRENT_DIR = "./"
-include CONFIGURE

COQC=$(COQBIN)coqc
COQDEP=$(COQBIN)coqdep

VST_DIRS = msl sepcomp veric floyd

INCLUDE_ACLIGHT = -Q ../AClight AClight -Q ../Split Split
INCLUDE_COMPCERT = -R $(COMPCERTDIR) compcert
INCLUDE_VST = $(foreach d, $(VST_DIRS), -Q $(VSTDIR)/$(d) VST.$(d))
NORMAL_FLAG = $(INCLUDE_ACLIGHT) $(INCLUDE_VST) $(INCLUDE_COMPCERT)



NORMAL_FILES = AClight2.v model_lemmas.v logic_lemmas.v vst_ext.v function.v defs.v rule.v strong.v semantics.v soundness.v

$(NORMAL_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(NORMAL_FLAG) $(CURRENT_DIR)$*.v


all: \
  $(NORMAL_FILES:%.v=%.vo) 

.depend:
	@$(COQDEP) $(NORMAL_FLAG) $(NORMAL_FILES) > .depend

depend:
	$(COQDEP) $(NORMAL_FLAG) $(NORMAL_FILES) > .depend

clean:
	@rm ./*.vo ./*.glob ./*.aux

.DEFAULT_GOAL := all

include .depend
