VFILES := \
  pxl-minimal-kernel-main/coq/PXLv3.v \
  pxl-minimal-kernel-main/coq/PXL_Deep_Soundness.v \
  pxl-minimal-kernel-main/coq/PXL_Completeness_Truth_WF.v \
  modules/IEL/ChronoPraxis/substrate/ChronoAxioms.v \
  modules/IEL/ChronoPraxis/substrate/Bijection.v \
  modules/IEL/ChronoPraxis/substrate/ChronoMappings.v \
  modules/IEL/ChronoPraxis/tactics/ChronoTactics.v \
  modules/IEL/ChronoPraxis/theorems/ChronoProofs.v \
  modules/IEL/ChronoPraxis/theorems/MetaTheorems.v \
  modules/IEL/ChronoPraxis/interfaces/ChronoPraxis.v \
  modules/IEL/ChronoPraxis/domains/Compatibilism/CompatibilismTheory.v \
  modules/IEL/ChronoPraxis/domains/Empiricism/UnifiedFieldLogic.v \
  modules/IEL/ChronoPraxis/domains/ModalOntology/ModalCollapse.v \
  tests/ConstructiveCoreTests.v \
  tests/CompatibilismTests.v \
  tests/EmpiricismTests.v \
  tests/ModalOntologyTests.v

COQMF := _CoqProject

all: Makefile.coq
	$(MAKE) -f Makefile.coq all

Makefile.coq: $(VFILES) $(COQMF)
	coq_makefile -f $(COQMF) $(VFILES) -o Makefile.coq

clean:
	[ -f Makefile.coq ] && $(MAKE) -f Makefile.coq clean || true
	rm -f Makefile.coq

status:
	@bash scripts/gen_status.sh > docs/IEL_STATUS.md && echo "Wrote docs/IEL_STATUS.md"

prove:
	@echo "=== ChronoPraxis IEL Proof Verification ==="
	@bash scripts/check_policy.sh && echo "✅ All proofs constructive, zero admits"

domain-compatibilism:
	coqc modules/IEL/ChronoPraxis/domains/Compatibilism/CompatibilismTheory.v
	coqc tests/CompatibilismTests.v

domain-empiricism:
	coqc modules/IEL/ChronoPraxis/domains/Empiricism/UnifiedFieldLogic.v
	coqc tests/EmpiricismTests.v

domain-modal-ontology:
	coqc modules/IEL/ChronoPraxis/domains/ModalOntology/ModalCollapse.v
	coqc tests/ModalOntologyTests.v

.PHONY: all clean status prove domain-compatibilism domain-empiricism domain-modal-ontology