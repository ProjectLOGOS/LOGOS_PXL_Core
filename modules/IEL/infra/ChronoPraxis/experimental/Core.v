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

(* For tau, assume tau_le is equality *)
Lemma pxl_tau_refl : forall t : ChronoAxioms.tau, ChronoAxioms.tau_le t t.
Proof. intros t. reflexivity. Qed.

Lemma pxl_tau_trans : forall t1 t2 t3 : ChronoAxioms.tau, ChronoAxioms.tau_le t1 t2 -> ChronoAxioms.tau_le t2 t3 -> ChronoAxioms.tau_le t1 t3.
Proof. intros t1 t2 t3 H1 H2. transitivity t2; assumption. Qed.

Lemma pxl_tau_antisym : forall t1 t2 : ChronoAxioms.tau, ChronoAxioms.tau_le t1 t2 -> ChronoAxioms.tau_le t2 t1 -> t1 = t2.
Proof. intros t1 t2 H1 H2. apply H1. Qed.

Global Instance CapTauRefl_tau : Cap_TauReflexive ChronoAxioms.tau ChronoAxioms.tau_le :=
  { tau_refl := pxl_tau_refl }.

Global Instance CapTauTrans_tau : Cap_TauTransitive ChronoAxioms.tau ChronoAxioms.tau_le :=
  { tau_trans := pxl_tau_trans }.

Global Instance CapTauAntisym_tau : Cap_TauAntisymmetric ChronoAxioms.tau ChronoAxioms.tau_le :=
  { tau_antisym := pxl_tau_antisym }.

Section TauOrder.
  Context {T:Type} (tau_le : T -> T -> Prop).
  Hypothesis refl_hyp  : forall t, tau_le t t.
  Hypothesis trans_hyp : forall x y z, tau_le x y -> tau_le y z -> tau_le x z.
  Hypothesis antis_hyp : forall x y, tau_le x y -> tau_le y x -> x = y.

  Global Instance CapTauRefl_inst : Cap_TauReflexive T tau_le := {| tau_refl := refl_hyp |}.
  Global Instance CapTauTrans_inst : Cap_TauTransitive T tau_le := {| tau_trans := trans_hyp |}.
  Global Instance CapTauAntis_inst : Cap_TauAntisymmetric T tau_le := {| tau_antisym := antis_hyp |}.
End TauOrder.

Class Cap_CrossMapConsistent (A B:Type) (f:A->B) (g:B->A) (R_A:A->A->Prop) (R_B:B->B->Prop) :=
  { cross_consistent_AB : forall x y, R_A x y -> R_B (f x) (f y)
  ; cross_consistent_BA : forall x y, R_B x y -> R_A (g x) (g y)
  ; cross_consistent_AB_BA : forall x, f (g x) = x
  ; cross_consistent_BA_AB : forall x, g (f x) = x }.

(* Instance for AB mapping *)
From PXLs.IEL.Infra.ChronoPraxis.Substrate Require Import ChronoMappings.

Global Instance CapCrossMap_AB : Cap_CrossMapConsistent
  (ChronoAxioms.P_chi ChronoAxioms.chi_A)
  (ChronoAxioms.P_chi ChronoAxioms.chi_B)
  (ChronoMappings.map_AB.(Bijection.f))
  (ChronoMappings.map_AB.(Bijection.g))
  (@eq (ChronoAxioms.P_chi ChronoAxioms.chi_A))
  (@eq (ChronoAxioms.P_chi ChronoAxioms.chi_B)) :=
  { cross_consistent_AB := fun x y H => f_equal _ H
  ; cross_consistent_BA := fun x y H => f_equal _ H
  ; cross_consistent_AB_BA := ChronoMappings.map_AB.(Bijection.gf)
  ; cross_consistent_BA_AB := ChronoMappings.map_AB.(Bijection.fg) }.

(* Instances for belief and forecast *)
From PXLs.IEL.Infra.ChronoPraxis.Substrate Require Import ChronoZAgents.

(* Global Instance Cap_BeliefUpdatePreservesId_inst : Cap_BeliefUpdatePreservesId
  ChronoAxioms.tau ChronoAxioms.tau_le ChronoZAgents.ChronoAgent ChronoZAgents.ChronoState ChronoZAgents.belief_update :=
  {| belief_update_id := fun t1 t2 a s H => eq_refl (* TODO: prove from constructive agent theory *) |}. *)

(* Global Instance Cap_ForecastCoherence_inst : Cap_ForecastCoherence
  ChronoAxioms.tau ChronoAxioms.tau_le ChronoZAgents.ChronoState ChronoZAgents.TelicAgent ChronoZAgents.lift_being :=
  {| forecast_coherent := fun t1 t2 ta H s2 => ex_intro _ s2 eq_refl (* TODO: prove from constructive forecast theory *) |}. *)

(* Class Cap_BeliefUpdatePreservesId (Time : Type) (tau_le : Time -> Time -> Prop) (ChronoAgent : Time -> Type) (ChronoState : Time -> Type) (belief_update : forall t1 t2, tau_le t1 t2 -> ChronoAgent t1 -> ChronoState t2 -> ChronoAgent t2) :=
  { belief_update_id : forall t1 t2 a s H, agent_id (belief_update t1 t2 H a s) = agent_id a }.

Class Cap_ForecastCoherence (Time : Type) (tau_le : Time -> Time -> Prop) (ChronoState : Time -> Type) (TelicAgent : Time -> Type) (lift_being : forall t, ChronoState t -> Prop) :=
  { forecast_coherent : forall t1 t2 ta H s2, forecast ta t2 H s2 -> exists s1, lift_being t1 s1 = lift_being t2 s2 }. *)
