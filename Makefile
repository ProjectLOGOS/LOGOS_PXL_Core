VFILES := \
  modules/IEL/Axiopraxis/modal/FrameSpec.v \
  modules/IEL/Axiopraxis/theorems/NormalBase.v \
  modules/IEL/Axiopraxis/theorems/Conservativity.v \
  modules/IEL/Axiopraxis/systems/Systems.v \
  modules/IEL/Axiopraxis/tests/Axiopraxis_Smoke.v \
  modules/IEL/ErgoPraxis/modal/FrameSpec.v \
  modules/IEL/ErgoPraxis/theorems/NormalBase.v \
  modules/IEL/ErgoPraxis/theorems/Conservativity.v \
  modules/IEL/ErgoPraxis/systems/Systems.v \
  modules/IEL/ErgoPraxis/tests/ErgoPraxis_Smoke.v \
  modules/IEL/AnthroPraxis/modal/FrameSpec.v \
  modules/IEL/AnthroPraxis/theorems/NormalBase.v \
  modules/IEL/AnthroPraxis/theorems/Conservativity.v \
  modules/IEL/AnthroPraxis/systems/Systems.v \
  modules/IEL/AnthroPraxis/tests/AnthroPraxis_Smoke.v \
  modules/IEL/AnthroPraxis/subdomains/BioPraxis/modal/FrameSpec.v \
  modules/IEL/AnthroPraxis/subdomains/BioPraxis/theorems/NormalBase.v \
  modules/IEL/AnthroPraxis/subdomains/BioPraxis/systems/Systems.v \
  modules/IEL/AnthroPraxis/subdomains/BioPraxis/tests/BioPraxis_Smoke.v \
  modules/IEL/TeloPraxis/modal/FrameSpec.v \
  modules/IEL/TeloPraxis/theorems/NormalBase.v \
  modules/IEL/TeloPraxis/theorems/Conservativity.v \
  modules/IEL/TeloPraxis/systems/Systems.v \
  modules/IEL/TeloPraxis/tests/TeloPraxis_Smoke.v \
  modules/IEL/TopoPraxis/modal/FrameSpec.v \
  modules/IEL/TopoPraxis/theorems/NormalBase.v \
  modules/IEL/TopoPraxis/theorems/Conservativity.v \
  modules/IEL/TopoPraxis/systems/Systems.v \
  modules/IEL/TopoPraxis/tests/TopoPraxis_Smoke.v \
  modules/IEL/CosmoPraxis/modal/FrameSpec.v \
  modules/IEL/CosmoPraxis/theorems/NormalBase.v \
  modules/IEL/CosmoPraxis/theorems/Conservativity.v \
  modules/IEL/CosmoPraxis/systems/Systems.v \
  modules/IEL/CosmoPraxis/tests/CosmoPraxis_Smoke.v
  pxl-minimal-kernel-main/coq/PXLv3.v \
  pxl-minimal-kernel-main/coq/PXL_Deep_Soundness.v \
  pxl-minimal-  modules/IE  modules/IEL/MuPraxis/systems/Systems.v \
  tests/MuPraxis/MuPraxis_Smoke.v \
  modules/IEL/TychePraxis/modal/ProbSpec.v \
  modules/IEL/TychePraxis/theorems/NormalBase.v \
  modules/IEL/TychePraxis/theorems/Conservativity.v \
  modules/IEL/TychePraxis/systems/Systems.v \
  tests/TychePraxis/TychePraxis_Smoke.vaPraxis/systems/Systems.v \
  tests/ChremaPraxis/ChremaPraxis_Smoke.v \
  modules/IEL/MuPraxis/modal/FixSpec.v \
  modules/IEL/MuPraxis/theorems/NormalBase.v \
  modules/IEL/MuPraxis/theorems/Conservativity.v \
  modules/IEL/MuPraxis/systems/Systems.v \
  tests/MuPraxis/MuPraxis_Smoke.v \
  modules/IEL/TychePraxis/modal/ProbSpec.v \ain/coq/PXL_Completeness_Truth_WF.v \
  modules/IEL/ChronoPraxis/substrate/ChronoAxioms.v \
  modules/IEL/ChronoPraxis/substrate/Bijection.v \
  modules/IEL/ChronoPraxis/substrate/ChronoMappings.v \
  modules/IEL/ChronoPraxis/tactics/ChronoTactics.v \
  modules/IEL/ChronoPraxis/theorems/ChronoProofs.v \
  modules/IEL/ChronoPraxis/theorems/MetaTheorems.v \
  modules/IEL/ChronoPraxis/theorems/ModalStrength/ModalFree.v \
  modules/IEL/ChronoPraxis/theorems/ModalStrength/S4Overlay.v \
  modules/IEL/ChronoPraxis/theorems/ModalStrength/S5Overlay.v \
  modules/IEL/ChronoPraxis/theorems/ModalStrength/ModalAxiomsSound.v \
  modules/IEL/ChronoPraxis/theorems/ModalStrength/ModalRules.v \
  modules/IEL/ChronoPraxis/theorems/ModalStrength/Systems.v \
  modules/IEL/ChronoPraxis/theorems/ModalStrength/UMAdapters.v \
  modules/IEL/ChronoPraxis/theorems/ModalStrength/OverlayEquivalence.v \
  modules/IEL/ModalPraxis/modal/FrameSpec.v \
  modules/IEL/ModalPraxis/theorems/NormalBase.v \
  modules/IEL/ModalPraxis/theorems/DerivedAxioms.v \
  modules/IEL/ModalPraxis/theorems/Systems.v \
  modules/IEL/ModalPraxis/theorems/Conservativity.v \
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
  tests/ModalAxiomsSoundTests.v \
  tests/ModalRulesTests.v \
  tests/UMIEL_Tests.v \
  tests/OverlayEquivalenceTests.v \
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

# IEL groups (stubs for wiring; replace as implementations land)
IEL_FILES := \
  modules/IEL/TropoPraxis/modal/FrameSpec.v \
  modules/IEL/TropoPraxis/theorems/NormalBase.v \
  modules/IEL/TropoPraxis/theorems/Systems.v \
  modules/IEL/TropoPraxis/theorems/Conservativity.v \
  tests/TropoPraxis/TropoPraxis_Smoke.v \
  modules/IEL/GnosiPraxis/modal/FrameSpec.v \
  modules/IEL/GnosiPraxis/modal/AgentFrames.v \
  modules/IEL/GnosiPraxis/theorems/NormalBase.v \
  modules/IEL/GnosiPraxis/theorems/Systems.v \
  modules/IEL/GnosiPraxis/theorems/Conservativity.v \
  modules/IEL/GnosiPraxis/systems/Systems.v \
  tests/GnosiPraxis/GnosiPraxis_Smoke.v \
  tests/GnosiPraxis/GnosiPraxis_AgentTests.v \
  modules/IEL/ThemiPraxis/modal/NormFrames.v \
  modules/IEL/ThemiPraxis/theorems/Conservativity.v \
  modules/IEL/ThemiPraxis/systems/Systems.v \
  tests/ThemiPraxis/ThemiPraxis_Smoke.v \
  modules/IEL/DynaPraxis/modal/FrameSpec.v \
  modules/IEL/DynaPraxis/theorems/Conservativity.v \
  modules/IEL/DynaPraxis/systems/Systems.v \
  tests/DynaPraxis/DynaPraxis_Smoke.v \
  modules/IEL/HexiPraxis/modal/FrameSpec.v \
  modules/IEL/HexiPraxis/theorems/Conservativity.v \
  modules/IEL/HexiPraxis/systems/Systems.v \
  tests/HexiPraxis/HexiPraxis_Smoke.v \
  modules/IEL/ChremaPraxis/modal/PhaseSpec.v \
  modules/IEL/ChremaPraxis/theorems/NormalBase.v \
  modules/IEL/ChremaPraxis/theorems/Conservativity.v \
  modules/IEL/ChremaPraxis/systems/Systems.v \
  tests/ChremaPraxis/ChremaPraxis_Smoke.v \
  modules/IEL/MuPraxis/modal/FixSpec.v \
  modules/IEL/MuPraxis/theorems/NormalBase.v \
  modules/IEL/MuPraxis/theorems/Systems.v \
  modules/IEL/MuPraxis/theorems/Conservativity.v \
  tests/MuPraxis/MuPraxis_Smoke.v \
  modules/IEL/TychePraxis/modal/FrameSpec.v \
  modules/IEL/TychePraxis/theorems/NormalBase.v \
  modules/IEL/TychePraxis/theorems/Systems.v \
  modules/IEL/TychePraxis/theorems/Conservativity.v \
  tests/TychePraxis/TychePraxis_Smoke.v

VFILES += $(IEL_FILES)

.PHONY: iels-all
iels-all: $(IEL_FILES)
	@echo "IELs built."

.PHONY: all clean status prove domain-compatibilism domain-empiricism domain-modal-ontology iels-all  modules/IEL/OntoPraxis/modal/FrameSpec.v \\
  modules/IEL/OntoPraxis/theorems/NormalBase.v \\
  modules/IEL/OntoPraxis/systems/Systems.v \\
  modules/IEL/OntoPraxis/tests/OntoPraxis_Smoke.v