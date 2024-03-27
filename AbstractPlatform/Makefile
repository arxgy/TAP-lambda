SMOKE?=0
ifeq ($(SMOKE),1)
	BOOGIESMOKE:=/smoke
else
	BOOGIESMOKE:=
endif
BOOGIE := boogie
# 1. UpperLevel OPT is used for top level proof, 
#    which use relevancy propagation to speedup the z3 prover.

# 2. LowerLevel OPT is used for lower level measurment case (Part I), 
#    which shows high performance on bit-vector-related while loop.
UPPERLEVELOPT_DBG:=	/proverOpt:O:smt.relevancy=2 /proverOpt:O:smt.case_split=2 /errorLimit:1 $(BOOGIESMOKE) \
					/proverOpt:O:parallel.enable=true \
					/traceverify \
					/trace	\
					/printModel:1 \
					/errorTrace:2 \
					/enhancedErrorMessages:0 \
					/proverLog:log/prover.log \
					/printCFG:dotfiles/ctrlflow \
					/proverWarnings:1 \
					/printModelToFile:log/model.log \
					

LOWERLEVELOPT_DBG:=	/proverOpt:O:smt.relevancy=0 /proverOpt:O:smt.case_split=2 /errorLimit:1 $(BOOGIESMOKE) \
					/proverOpt:O:parallel.enable=true \
					/traceverify \
					/trace	\
					/printModel:1 \
					/errorTrace:2 \
					/enhancedErrorMessages:0 \
					/proverLog:log/prover.log \
					/printCFG:dotfiles/ctrlflow \
					/proverWarnings:1 \
					/proc:launch  \
					/printModelToFile:log/model.log \

UPPERLEVELOPT:=		/proverOpt:O:smt.relevancy=2 /proverOpt:O:smt.case_split=2 /errorLimit:1 $(BOOGIESMOKE) 
LOWERLEVELOPT:=		/proverOpt:O:smt.relevancy=0 /proverOpt:O:smt.case_split=2 /errorLimit:1 $(BOOGIESMOKE) 

COMMON=../Common
BUILD=build
CPU_TARGET:=$(BUILD)/CPU.xml
INTEGRITY_PROOF_TARGET=$(BUILD)/IntegrityProof.xml
MEM_CONFIDENTIALITY_PROOF_TARGET=$(BUILD)/MemConfidentialityProof.xml
CACHE_CONFIDENTIALITY_PROOF_TARGET=$(BUILD)/CacheConfidentialityProof.xml
PT_CONFIDENTIALITY_PROOF_TARGET=$(BUILD)/PTConfidentialityProof.xml
COMMON_PROOF_TARGET:=$(BUILD)/ProofCommon.xml
MEASUREMENT_TARGET:=$(BUILD)/Measure.xml
MEASUREMENT_PROOF_TARGET=$(BUILD)/MeasurementProof.xml
TEMP_PROOF_TARGET:=$(BUILD)/temp.xml

CPU_TARGET_DBG:=$(BUILD)/CPU_DBG.xml
INTEGRITY_PROOF_TARGET_DBG=$(BUILD)/IntegrityProof_DBG.xml
MEM_CONFIDENTIALITY_PROOF_TARGET_DBG=$(BUILD)/MemConfidentialityProof_DBG.xml
CACHE_CONFIDENTIALITY_PROOF_TARGET_DBG=$(BUILD)/CacheConfidentialityProof_DBG.xml
PT_CONFIDENTIALITY_PROOF_TARGET_DBG=$(BUILD)/PTConfidentialityProof_DBG.xml
COMMON_PROOF_TARGET_DBG:=$(BUILD)/ProofCommon_DBG.xml
MEASUREMENT_TARGET_DBG:=$(BUILD)/Measure_DBG.xml
MEASUREMENT_PROOF_TARGET_DBG=$(BUILD)/MeasurementProof_DBG.xml
TEMP_PROOF_TARGET_DBG:=$(BUILD)/temp_DBG.xml

COMMON_FILES:=$(COMMON)/Types.bpl $(COMMON)/Common.bpl $(COMMON)/Cache.bpl
ATP_COMMON_FILES:=Types.bpl $(COMMON_FILES)
CPU_FILES:=CPU.bpl
CPU_IMPL_FILES:=CPUImpl.bpl
COMMON_PROOF_FILES:=ProofCommon.bpl
COMMON_IMPL_FILES:=ImplCommon.bpl
INTEGRITY_PROOF_FILES:=IntegrityProof.bpl $(COMMON_PROOF_FILES)
CONFIDENTIALITY_COMMON_FILES:=ConfidentialityProof.bpl $(COMMON_PROOF_FILES)
MEM_CONFIDENTIALITY_PROOF_FILES:=MemConfidentialityProof.bpl
CACHE_CONFIDENTIALITY_PROOF_FILES:=CacheConfidentialityProof.bpl
PT_CONFIDENTIALITY_PROOF_FILES:=PTConfidentialityProof.bpl
MEASUREMENT_FILES:=Measure.bpl 
MEASUREMENT_IMPL_FILES:=MeasureImpl.bpl 
MEASUREMENT_PROOF_FILES:=MeasurementProof.bpl
TEMP_PROOF_FILES:=temp.bpl

all: $(CPU_TARGET) $(MEASUREMENT_TARGET) $(COMMON_PROOF_TARGET) $(INTEGRITY_PROOF_TARGET) $(MEM_CONFIDENTIALITY_PROOF_TARGET) $(CACHE_CONFIDENTIALITY_PROOF_TARGET) $(PT_CONFIDENTIALITY_PROOF_TARGET) $(MEASUREMENT_PROOF_TARGET)

cpu: $(CPU_TARGET)
intipf: $(INTEGRITY_PROOF_TARGET)
# M
memconf: $(MEM_CONFIDENTIALITY_PROOF_TARGET)
# C
cacheconf : $(CACHE_CONFIDENTIALITY_PROOF_TARGET)
# P
ptconf : $(PT_CONFIDENTIALITY_PROOF_TARGET)
measurepf: $(MEASUREMENT_PROOF_TARGET)

measure : $(MEASUREMENT_TARGET)

commonpf : $(COMMON_PROOF_TARGET)

cpu_dbg: $(CPU_TARGET_DBG)
intipf_dbg: $(INTEGRITY_PROOF_TARGET_DBG)
# M
memconf_dbg: $(MEM_CONFIDENTIALITY_PROOF_TARGET_DBG)
# C
cacheconf_dbg : $(CACHE_CONFIDENTIALITY_PROOF_TARGET_DBG)
# P
ptconf_dbg : $(PT_CONFIDENTIALITY_PROOF_TARGET_DBG)
measurepf_dbg: $(MEASUREMENT_PROOF_TARGET_DBG)

measure_dbg : $(MEASUREMENT_TARGET_DBG)

commonpf_dbg : $(COMMON_PROOF_TARGET_DBG)

$(CPU_TARGET): $(ATP_COMMON_FILES) $(CPU_FILES) $(CPU_IMPL_FILES)
	$(BOOGIE) $(LOWERLEVELOPT) /xml:$@ $^

$(INTEGRITY_PROOF_TARGET): $(ATP_COMMON_FILES) $(CPU_FILES) $(INTEGRITY_PROOF_FILES)
	$(BOOGIE) $(UPPERLEVELOPT) /xml:$@ $^

$(MEM_CONFIDENTIALITY_PROOF_TARGET): $(ATP_COMMON_FILES) $(CPU_FILES) $(CONFIDENTIALITY_COMMON_FILES) $(MEM_CONFIDENTIALITY_PROOF_FILES)
	$(BOOGIE) $(UPPERLEVELOPT) /xml:$@ $^

$(CACHE_CONFIDENTIALITY_PROOF_TARGET): $(ATP_COMMON_FILES) $(CPU_FILES) $(CONFIDENTIALITY_COMMON_FILES) $(CACHE_CONFIDENTIALITY_PROOF_FILES)
	$(BOOGIE) $(UPPERLEVELOPT) /xml:$@ $^

$(PT_CONFIDENTIALITY_PROOF_TARGET): $(ATP_COMMON_FILES) $(CPU_FILES) $(CONFIDENTIALITY_COMMON_FILES) $(PT_CONFIDENTIALITY_PROOF_FILES)
	$(BOOGIE) $(UPPERLEVELOPT) /xml:$@ $^

$(COMMON_PROOF_TARGET): $(ATP_COMMON_FILES) $(CPU_FILES) $(COMMON_PROOF_FILES)  $(COMMON_IMPL_FILES)
	$(BOOGIE) $(UPPERLEVELOPT) /xml:$@ $^

$(MEASUREMENT_TARGET): $(ATP_COMMON_FILES) $(CPU_FILES)  $(COMMON_PROOF_FILES)  $(MEASUREMENT_FILES) $(MEASUREMENT_IMPL_FILES)
	$(BOOGIE) $(LOWERLEVELOPT) /xml:$@ $^

$(MEASUREMENT_PROOF_TARGET): $(ATP_COMMON_FILES) $(CPU_FILES) $(MEASUREMENT_PROOF_FILES) $(MEASUREMENT_FILES) $(COMMON_PROOF_FILES) 
	$(BOOGIE) $(UPPERLEVELOPT) /xml:$@ $^

$(TEMP_PROOF_TARGET):  $(TEMP_PROOF_FILES) $(COMMON_PROOF_FILES) $(CPU_FILES) $(ATP_COMMON_FILES)
	$(BOOGIE) $(UPPERLEVELOPT) /xml:$@ $^

$(CPU_TARGET_DBG): $(ATP_COMMON_FILES) $(CPU_FILES) $(CPU_IMPL_FILES)
	$(BOOGIE) $(LOWERLEVELOPT_DBG) /xml:$@ $^

$(INTEGRITY_PROOF_TARGET_DBG): $(ATP_COMMON_FILES) $(CPU_FILES) $(INTEGRITY_PROOF_FILES)
	$(BOOGIE) $(UPPERLEVELOPT_DBG) /xml:$@ $^

$(MEM_CONFIDENTIALITY_PROOF_TARGET_DBG): $(ATP_COMMON_FILES) $(CPU_FILES) $(CONFIDENTIALITY_COMMON_FILES) $(MEM_CONFIDENTIALITY_PROOF_FILES)
	$(BOOGIE) $(UPPERLEVELOPT_DBG) /xml:$@ $^

$(CACHE_CONFIDENTIALITY_PROOF_TARGET_DBG): $(ATP_COMMON_FILES) $(CPU_FILES) $(CONFIDENTIALITY_COMMON_FILES) $(CACHE_CONFIDENTIALITY_PROOF_FILES)
	$(BOOGIE) $(UPPERLEVELOPT_DBG) /xml:$@ $^

$(PT_CONFIDENTIALITY_PROOF_TARGET_DBG): $(ATP_COMMON_FILES) $(CPU_FILES) $(CONFIDENTIALITY_COMMON_FILES) $(PT_CONFIDENTIALITY_PROOF_FILES)
	$(BOOGIE) $(UPPERLEVELOPT_DBG) /xml:$@ $^

$(COMMON_PROOF_TARGET_DBG): $(ATP_COMMON_FILES) $(CPU_FILES) $(COMMON_PROOF_FILES)  $(COMMON_IMPL_FILES)
	$(BOOGIE) $(UPPERLEVELOPT_DBG) /xml:$@ $^

$(MEASUREMENT_TARGET_DBG): $(ATP_COMMON_FILES) $(CPU_FILES)  $(COMMON_PROOF_FILES)  $(MEASUREMENT_FILES) $(MEASUREMENT_IMPL_FILES)
	$(BOOGIE) $(LOWERLEVELOPT_DBG) /xml:$@ $^

$(MEASUREMENT_PROOF_TARGET_DBG): $(ATP_COMMON_FILES) $(CPU_FILES) $(MEASUREMENT_PROOF_FILES) $(MEASUREMENT_FILES) $(COMMON_PROOF_FILES) 
	$(BOOGIE) $(UPPERLEVELOPT_DBG) /xml:$@ $^

$(TEMP_PROOF_TARGET_DBG):  $(TEMP_PROOF_FILES) $(COMMON_PROOF_FILES) $(CPU_FILES) $(ATP_COMMON_FILES)
	$(BOOGIE) $(UPPERLEVELOPT_DBG) /xml:$@ $^


clean:
	rm -f build/*.xml

cut:
	sed -n -e'/peep/,$$p' log/run.log > log/optimized_code.log
	sed -n -e'/catch/,$$p' log/run.log > log/catch.log	
	sed '/passive/,$$d' log/catch.log > log/onlyCatch.log
	sed -n -e'/z3/,$$p' log/optimized_code.log > log/result.log	
	sed -i 's/#AT#/@/g' log/run.log 
	sed -i 's/#AT#/@/g' log/optimized_code.log
	# rm log/catch.log


.PHONY: clean, cut
