From PXLs Require Import PXLv3.

Class Cap_ChiReflexive (A:Type) (χ: A -> A -> Prop) : Prop :=
  { chi_refl : forall x, χ x x }.

Class Cap_TauReflexive (T:Type) (τ: T -> T -> Prop) : Prop :=
  { tau_refl : forall t, τ t t }.

(* Import chi and tau definitions *)
From PXLs.IEL.Infra.ChronoPraxis.Substrate Require Import ChronoAxioms.

(* Instance for chi eq *)
Lemma chi_eq_refl : forall m : ChronoAxioms.chi, m = m.
Proof. intros m; reflexivity. Qed.

Global Instance CapChiRefl_chi : Cap_ChiReflexive ChronoAxioms.chi (@eq ChronoAxioms.chi) :=
  { chi_refl := chi_eq_refl }.

(* For tau, assume we have a lemma from PXL *)
Hypothesis pxl_tau_refl : forall t : ChronoAxioms.tau, ChronoAxioms.tau_le t t.

Global Instance CapTauRefl_tau : Cap_TauReflexive ChronoAxioms.tau ChronoAxioms.tau_le :=
  { tau_refl := pxl_tau_refl }.