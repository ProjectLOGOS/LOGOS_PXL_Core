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
  tests/ConstructiveCoreTests.v

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

.PHONY: all clean status prove