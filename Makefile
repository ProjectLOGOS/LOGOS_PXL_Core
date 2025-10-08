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
  modules/IEL/ChronoPraxis/theorems/ModalStrength/ModalFree.v \
  modules/IEL/ChronoPraxis/theorems/ModalStrength/S4Overlay.v \
  modules/IEL/ChronoPraxis/theorems/ModalStrength/S5Overlay.v \
  modules/IEL/ChronoPraxis/interfaces/ChronoPraxis.v \
  modules/IEL/ChronoPraxis/domains/Compatibilism/CompatibilismTheory.v \
  modules/IEL/ChronoPraxis/domains/Empiricism/UnifiedFieldLogic.v \
  modules/IEL/ChronoPraxis/domains/Empiricism/Relativity.v \
  modules/IEL/ChronoPraxis/domains/ModalOntology/ModalCollapse.v \
  examples/Compatibilism_CoffeeTea.v \
  examples/Empiricism_LabClock.v \
  examples/ModalOntology_Routes.v \
  tests/ConstructiveCoreTests.v \
  tests/CompatibilismTests.v \
  tests/EmpiricismTests.v \
  tests/EmpiricismLorentzTests.v \
  tests/RelativityTests.v \
  tests/ModalStrengthTests.v \
  tests/ModalOntologyTests.v \
  tests/DomainProperties.v \
  pxl-minimal-kernel-main/coq/Constructive_Lindenbaum_Simple.v

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
	coqc modules/IEL/ChronoPraxis/domains/Empiricism/Relativity.v
	coqc tests/EmpiricismTests.v

domain-modal-ontology:
	coqc modules/IEL/ChronoPraxis/domains/ModalOntology/ModalCollapse.v
	coqc tests/ModalOntologyTests.v

examples:
	@echo "=== Building ChronoPraxis Examples ==="
	coqc examples/Compatibilism_CoffeeTea.v
	coqc examples/Empiricism_LabClock.v
	coqc examples/ModalOntology_Routes.v
	@echo "✅ All examples compile successfully"

docs-html:
	@echo "Generating HTML docs for examples and tests..."
	coqdoc --utf8 --toc --index examples/Compatibilism_CoffeeTea.v examples/Empiricism_LabClock.v examples/ModalOntology_Routes.v tests/DomainProperties.v
	@echo "Moving HTML files to docs/html/"
	@if not exist docs\\html mkdir docs\\html
	@move *.html docs\\html\\ 2>nul || echo "HTML files moved"
	@echo "✅ Generated HTML documentation in docs/html/"

.PHONY: all clean status prove domain-compatibilism domain-empiricism domain-modal-ontology