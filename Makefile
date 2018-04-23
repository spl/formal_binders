############################################################################
#
#  Usage:
#  1) make lib   to compile only the generic metatheory library
#  2) make main  to compile library and main developments
#  3) make all   to compile library and all developments
#  4) make       alias for make all
#
############################################################################

COQC = coqc -I .
COQDEP = coqdep
COQDOC = coqdoc --quiet --utf8 --html
BEAUTICOQ = php ../tools/beauticoq.php

FILES = \
	Lib_Tactic \
	Lib_FinSet \
	Lib_FinSetImpl \
	Lib_ListFacts \
	Lib_MyFSetInterface \
	Lib_ListFactsMore \
	\
	Metatheory_Var \
	Metatheory_Env \
	Metatheory_Fresh \
	Metatheory \
	\
	Fsub_Definitions \
	Fsub_Infrastructure \
	Fsub_Soundness \
	CoC_Definitions \
	CoC_Infrastructure \
	CoC_BetaStar \
	CoC_ChurchRosser \
	CoC_Conversion \
	CoC_Preservation \
	ML_Definitions \
	ML_Infrastructure \
	ML_Soundness \
	\
	Fsub_Part1A \
	STLC_Core_Definitions \
	STLC_Core_Infrastructure \
	STLC_Core_Soundness \
	STLC_Core_Adequacy \
	STLC_Core_FullBeta \
	STLC_Core_Light \
	STLC_Core_WF_Definitions \
	STLC_Core_WF_Infrastructure \
	STLC_Core_WF_Soundness \
	STLC_Exn_Definitions \
	STLC_Exn_Infrastructure \
	STLC_Exn_Soundness \
	STLC_Ref_Definitions \
	STLC_Ref_Infrastructure \
	STLC_Ref_Soundness \
	STLC_Data_Definitions \
	STLC_Data_Infrastructure \
	STLC_Data_Soundness \
	STLC_Dec_Definitions \
	STLC_Dec_Infrastructure \
	STLC_Dec_Soundness \
	STLC_Dec_Decidability \
	Lambda_Definitions \
	Lambda_Infrastructure \
	Lambda_ChurchRosser \
	ML_Core_Definitions \
	ML_Core_Infrastructure \
	ML_Core_Soundness \



############################################################################

VFILES = $(foreach i, $(FILES), $(i).v)
VOFILES = $(foreach i, $(FILES), $(i).vo)

.PHONY: all coq analyze clean clean_doc clean_all default doc coqdoc
.SUFFIXES: .v .vo

all : coq

dos :
	dos2unix $(VFILES)

main : ML_Soundness.vo Fsub_Soundness.vo CoC_Preservation.vo

coq : $(VOFILES)

lib : Metatheory.vo

doc : coqdoc beauticoq

coqdoc :#ATTENTION
	#@mkdir -p doc_light
	#$(COQDOC) --gallina -d doc_light $(VFILES)

beauticoq :
	@mkdir -p src_color
	$(BEAUTICOQ) -quiet -out src_color $(VFILES)

clean_all : clear clean_doc

clean :
	rm -f *.vo .depend *.deps *.dot

clean_doc :
	rm -f doc_light/* src_color/*

.v.vo : .depend
	$(COQC) $<

.depend : $(VFILES)
	$(COQDEP) -I . $(VFILES) > .depend

include .depend

