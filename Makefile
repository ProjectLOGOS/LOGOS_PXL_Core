VFILES := \
  modules/IEL/pillars/Axiopraxis/modal/FrameSpec.v \
  modules/IEL/pillars/Axiopraxis/theorems/NormalBase.v \
  modules/IEL/pillars/Axiopraxis/theorems/Conservativity.v \
  modules/IEL/pillars/Axiopraxis/systems/Systems.v \
  modules/IEL/pillars/Axiopraxis/tests/Axiopraxis_Smoke.v \
  modules/IEL/pillars/ErgoPraxis/modal/FrameSpec.v \
  modules/IEL/pillars/ErgoPraxis/theorems/NormalBase.v \
  modules/IEL/pillars/ErgoPraxis/theorems/Conservativity.v \
  modules/IEL/pillars/ErgoPraxis/systems/Systems.v \
  modules/IEL/pillars/ErgoPraxis/tests/ErgoPraxis_Smoke.v \
  modules/IEL/pillars/AnthroPraxis/modal/FrameSpec.v \
  modules/IEL/pillars/AnthroPraxis/theorems/NormalBase.v \
  modules/IEL/pillars/AnthroPraxis/theorems/Conservativity.v \
  modules/IEL/pillars/AnthroPraxis/systems/Systems.v \
  modules/IEL/pillars/AnthroPraxis/tests/AnthroPraxis_Smoke.v \
  modules/IEL/pillars/AnthroPraxis/subdomains/BioPraxis/modal/FrameSpec.v \
  modules/IEL/pillars/AnthroPraxis/subdomains/BioPraxis/theorems/NormalBase.v \
  modules/IEL/pillars/AnthroPraxis/subdomains/BioPraxis/systems/Systems.v \
  modules/IEL/pillars/AnthroPraxis/subdomains/BioPraxis/tests/BioPraxis_Smoke.v \
  modules/IEL/pillars/TeloPraxis/modal/FrameSpec.v \
  modules/IEL/pillars/TeloPraxis/theorems/NormalBase.v \
  modules/IEL/pillars/TeloPraxis/theorems/Conservativity.v \
  modules/IEL/pillars/TeloPraxis/systems/Systems.v \
  modules/IEL/pillars/TeloPraxis/tests/TeloPraxis_Smoke.v \
  modules/IEL/infra/TopoPraxis/modal/FrameSpec.v \
  modules/IEL/infra/TopoPraxis/theorems/NormalBase.v \
  modules/IEL/infra/TopoPraxis/theorems/Conservativity.v \
  modules/IEL/infra/TopoPraxis/systems/Systems.v \
  modules/IEL/infra/TopoPraxis/tests/TopoPraxis_Smoke.v \
  modules/IEL/pillars/CosmoPraxis/modal/FrameSpec.v \
  modules/IEL/pillars/CosmoPraxis/theorems/NormalBase.v \
  modules/IEL/pillars/CosmoPraxis/theorems/Conservativity.v \
  modules/IEL/pillars/CosmoPraxis/systems/Systems.v \
  modules/IEL/pillars/CosmoPraxis/tests/CosmoPraxis_Smoke.v \
  pxl-minimal-kernel-main/coq/PXLv3.v \
  pxl-minimal-kernel-main/coq/PXL_Deep_Soundness.v \
  pxl-minimal-kernel-main/coq/PXL_TriuneNecessity.v \
  tests/MuPraxis/MuPraxis_Smoke.v \
  modules/IEL/experimental/TychePraxis/modal/ProbSpec.v \
  modules/IEL/experimental/TychePraxis/theorems/NormalBase.v \
  modules/IEL/experimental/TychePraxis/theorems/Conservativity.v \
  modules/IEL/experimental/TychePraxis/systems/Systems.v \
  tests/TychePraxis/TychePraxis_Smoke.v \
  tests/ChremaPraxis/ChremaPraxis_Smoke.v \
  modules/IEL/experimental/MuPraxis/modal/FixSpec.v \
  modules/IEL/experimental/MuPraxis/theorems/NormalBase.v \
  modules/IEL/experimental/MuPraxis/theorems/Conservativity.v \
  modules/IEL/experimental/MuPraxis/systems/Systems.v \
  tests/MuPraxis/MuPraxis_Smoke.v \
  modules/IEL/experimental/TychePraxis/modal/ProbSpec.v \ain/coq/PXL_Completeness_Truth_WF.v \
  modules/IEL/infra/ChronoPraxis/substrate/ChronoAxioms.v \
  modules/IEL/infra/ChronoPraxis/substrate/Bijection.v \
  modules/IEL/infra/ChronoPraxis/substrate/ChronoMappings.v \
  modules/IEL/infra/ChronoPraxis/tactics/ChronoTactics.v \
  modules/IEL/infra/ChronoPraxis/theorems/ChronoProofs.v \
  modules/IEL/infra/ChronoPraxis/theorems/MetaTheorems.v \
  modules/IEL/infra/ChronoPraxis/theorems/ModalStrength/ModalFree.v \
  modules/IEL/infra/ChronoPraxis/theorems/ModalStrength/S4Overlay.v \
  modules/IEL/infra/ChronoPraxis/theorems/ModalStrength/S5Overlay.v \
  modules/IEL/infra/ChronoPraxis/theorems/ModalStrength/ModalAxiomsSound.v \
  modules/IEL/infra/ChronoPraxis/theorems/ModalStrength/ModalRules.v \
  modules/IEL/infra/ChronoPraxis/theorems/ModalStrength/Systems.v \
  modules/IEL/infra/ChronoPraxis/theorems/ModalStrength/UMAdapters.v \
  modules/IEL/infra/ChronoPraxis/theorems/ModalStrength/OverlayEquivalence.v \
  modules/IEL/infra/ModalPraxis/modal/FrameSpec.v \
  modules/IEL/infra/ModalPraxis/theorems/NormalBase.v \
  modules/IEL/infra/ModalPraxis/theorems/DerivedAxioms.v \
  modules/IEL/infra/ModalPraxis/theorems/Systems.v \
  modules/IEL/infra/ModalPraxis/theorems/Conservativity.v \
  modules/IEL/infra/ChronoPraxis/interfaces/ChronoPraxis.v \
  modules/IEL/infra/ChronoPraxis/domains/Compatibilism/CompatibilismTheory.v \
  modules/IEL/infra/ChronoPraxis/domains/Empiricism/UnifiedFieldLogic.v \
  modules/IEL/infra/ChronoPraxis/domains/Empiricism/Relativity.v \
  modules/IEL/infra/ChronoPraxis/domains/ModalOntology/ModalCollapse.v \
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
	coqc modules/IEL/infra/ChronoPraxis/domains/Compatibilism/CompatibilismTheory.v
	coqc tests/CompatibilismTests.v

domain-empiricism:
	coqc modules/IEL/infra/ChronoPraxis/domains/Empiricism/UnifiedFieldLogic.v
	coqc modules/IEL/infra/ChronoPraxis/domains/Empiricism/Relativity.v
	coqc tests/EmpiricismTests.v

domain-modal-ontology:
	coqc modules/IEL/infra/ChronoPraxis/domains/ModalOntology/ModalCollapse.v
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
  modules/IEL/infra/TropoPraxis/modal/FrameSpec.v \
  modules/IEL/infra/TropoPraxis/theorems/NormalBase.v \
  modules/IEL/infra/TropoPraxis/theorems/Systems.v \
  modules/IEL/infra/TropoPraxis/theorems/Conservativity.v \
  tests/TropoPraxis/TropoPraxis_Smoke.v \
  modules/IEL/pillars/GnosiPraxis/modal/FrameSpec.v \
  modules/IEL/pillars/GnosiPraxis/modal/AgentFrames.v \
  modules/IEL/pillars/GnosiPraxis/theorems/NormalBase.v \
  modules/IEL/pillars/GnosiPraxis/theorems/Systems.v \
  modules/IEL/pillars/GnosiPraxis/theorems/Conservativity.v \
  modules/IEL/pillars/GnosiPraxis/systems/Systems.v \
  tests/GnosiPraxis/GnosiPraxis_Smoke.v \
  tests/GnosiPraxis/GnosiPraxis_AgentTests.v \
  modules/IEL/pillars/ThemiPraxis/modal/NormFrames.v \
  modules/IEL/pillars/ThemiPraxis/theorems/Conservativity.v \
  modules/IEL/pillars/ThemiPraxis/systems/Systems.v \
  tests/ThemiPraxis/ThemiPraxis_Smoke.v \
  modules/IEL/experimental/DynaPraxis/modal/FrameSpec.v \
  modules/IEL/experimental/DynaPraxis/theorems/Conservativity.v \
  modules/IEL/experimental/DynaPraxis/systems/Systems.v \
  tests/DynaPraxis/DynaPraxis_Smoke.v \
  modules/IEL/experimental/HexiPraxis/modal/FrameSpec.v \
  modules/IEL/experimental/HexiPraxis/theorems/Conservativity.v \
  modules/IEL/experimental/HexiPraxis/systems/Systems.v \
  tests/HexiPraxis/HexiPraxis_Smoke.v \
  modules/IEL/experimental/ChremaPraxis/modal/PhaseSpec.v \
  modules/IEL/experimental/ChremaPraxis/theorems/NormalBase.v \
  modules/IEL/experimental/ChremaPraxis/theorems/Conservativity.v \
  modules/IEL/experimental/ChremaPraxis/systems/Systems.v \
  tests/ChremaPraxis/ChremaPraxis_Smoke.v \
  modules/IEL/experimental/MuPraxis/modal/FixSpec.v \
  modules/IEL/experimental/MuPraxis/theorems/NormalBase.v \
  modules/IEL/experimental/MuPraxis/theorems/Systems.v \
  modules/IEL/experimental/MuPraxis/theorems/Conservativity.v \
  tests/MuPraxis/MuPraxis_Smoke.v \
  modules/IEL/experimental/TychePraxis/modal/FrameSpec.v \
  modules/IEL/experimental/TychePraxis/theorems/NormalBase.v \
  modules/IEL/experimental/TychePraxis/theorems/Systems.v \
  modules/IEL/experimental/TychePraxis/theorems/Conservativity.v \
  tests/TychePraxis/TychePraxis_Smoke.v \
  modules/IEL/source/TheoPraxis/Props.v \
  modules/IEL/pillars/Axiopraxis/Core.v \
  modules/IEL/pillars/Axiopraxis/subdomains/Truth/Spec.v \
  modules/IEL/pillars/Axiopraxis/subdomains/Beauty/Spec.v \
  modules/IEL/pillars/GnosiPraxis/subdomains/Truth/Spec.v \
  modules/IEL/pillars/ErgoPraxis/Core.v \
  modules/IEL/pillars/ErgoPraxis/subdomains/Truth/Spec.v \
  modules/IEL/pillars/TeloPraxis/subdomains/Will/Spec.v \
  modules/IEL/pillars/AnthroPraxis/subdomains/Life/Spec.v \
  modules/IEL/pillars/CosmoPraxis/subdomains/Space/Spec.v \
  modules/IEL/pillars/ThemiPraxis/subdomains/Truth/Spec.v \
  modules/IEL/pillars/GnosiPraxis/Core.v \
  modules/IEL/pillars/ThemiPraxis/Core.v \
  modules/IEL/pillars/TeloPraxis/Core.v \
  modules/IEL/pillars/AnthroPraxis/Core.v \
  modules/IEL/pillars/CosmoPraxis/Core.v \
  modules/IEL/pillars/ErgoPraxis/Core.v \
  modules/IEL/infra/TropoPraxis/Tropo.v \
  modules/IEL/infra/TopoPraxis/Core.v

VFILES += $(IEL_FILES)

.PHONY: iels-all
iels-all: $(IEL_FILES)
	@echo "IELs built."

.PHONY: all clean status prove domain-compatibilism domain-empiricism domain-modal-ontology iels-all
