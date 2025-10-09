From PXLs Require Import PXLv3.

Class Cap_ChiReflexive (A:Type) (χ: A -> A -> Prop) : Prop :=
  { chi_refl : forall x, χ x x }.

Class Cap_TauReflexive (T:Type) (τ: T -> T -> Prop) : Prop :=
  { tau_refl : forall t, τ t t }.

Class Cap_TauTransitive (T:Type) (τ:T->T->Prop) : Prop :=
  { tau_trans : forall x y z, τ x y -> τ y z -> τ x z }.

Class Cap_TauAntisymmetric (T:Type) (τ:T->T->Prop) : Prop :=
  { tau_antisym : forall x y, τ x y -> τ y x -> x = y }.

(* Import chi and tau definitions *)
From PXLs.IEL.Infra.ChronoPraxis.Substrate Require Import ChronoAxioms.

(* Instance for chi eq *)
Lemma chi_eq_refl : forall m : ChronoAxioms.chi, m = m.
Proof. intros m; reflexivity. Qed.

Global Instance CapChiRefl_chi : Cap_ChiReflexive ChronoAxioms.chi (@eq ChronoAxioms.chi) :=
  { chi_refl := chi_eq_refl }.

(* For tau, assume we have lemmas from PXL *)
Hypothesis pxl_tau_refl : forall t : ChronoAxioms.tau, ChronoAxioms.tau_le t t.
Hypothesis pxl_tau_trans : forall t1 t2 t3 : ChronoAxioms.tau, ChronoAxioms.tau_le t1 t2 -> ChronoAxioms.tau_le t2 t3 -> ChronoAxioms.tau_le t1 t3.
Hypothesis pxl_tau_antisym : forall t1 t2 : ChronoAxioms.tau, ChronoAxioms.tau_le t1 t2 -> ChronoAxioms.tau_le t2 t1 -> t1 = t2.

Global Instance CapTauRefl_tau : Cap_TauReflexive ChronoAxioms.tau ChronoAxioms.tau_le :=
  { tau_refl := pxl_tau_refl }.

Global Instance CapTauTrans_tau : Cap_TauTransitive ChronoAxioms.tau ChronoAxioms.tau_le :=
  { tau_trans := pxl_tau_trans }.

Global Instance CapTauAntisym_tau : Cap_TauAntisymmetric ChronoAxioms.tau ChronoAxioms.tau_le :=
  { tau_antisym := pxl_tau_antisym }.