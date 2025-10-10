(* ChronoProofs.v - PXL Canonical Constructive Proofs *)

Require Import PXLs.IEL.Infra.ChronoPraxis.Substrate.ChronoAxioms
               PXLs.IEL.Infra.ChronoPraxis.Substrate.Bijection
               PXLs.IEL.Infra.ChronoPraxis.Substrate.ChronoMappings
               PXLs.IEL.Infra.ChronoPraxis.Tactics.ChronoTactics.

Module ChronoProofs.

Import ChronoAxioms.
Import ChronoMappings.

(* Proposition identity within temporal modes *)
Theorem P_chi_identity_preservation : forall (m : ChronoAxioms.chi) (p : ChronoAxioms.P_chi m), p = p.
Proof.
  intros m p.
  reflexivity.
Qed.

(* ChronoAxioms.Eternal proposition identity *)
Theorem eternal_identity_preservation : forall (e : ChronoAxioms.Eternal), e = e.
Proof.
  intro e.
  apply ChronoAxioms.eternal_timeless.
Qed.

End ChronoProofs.