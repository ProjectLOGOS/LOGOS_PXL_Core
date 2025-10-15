From PXLs Require Import PXLv3.
From PXLs.Internal Emergent Logics.Pillars.Axiopraxis.subdomains Require Import Truth.Spec Beauty.Spec.
Module Axiopraxis.
  Definition V := TheoProps.Truth.  (* canonical carrier *)

  Theorem ValueMonotone : forall p q, (p -> q) -> V p -> V q.
  Proof. apply TruthSub.monotone. Qed.

  Theorem ConjElim : forall p q, V (p /\ q) -> V p /\ V q.
  Proof. apply BeautySub.conj_elim. Qed.

  Theorem NonExplosion : ~ V False.
  Proof. apply TruthSub.non_explosion. Qed.

  Theorem Conservativity : forall p, V p -> p.
  Proof. apply TruthSub.conservative. Qed.
End Axiopraxis.

(* Exported capabilities *)
Require Import PXLs.Internal Emergent Logics.Source.TheoPraxis.Props.
Class Cap_ValueMonotone : Prop := { value_monotone : forall φ ψ, Axiopraxis.V φ -> (φ -> ψ) -> Axiopraxis.V ψ }.
Class Cap_ReflectsPXL : Prop := { cap_reflect : forall φ, Axiopraxis.V φ -> φ }.
Global Instance Cap_ValueMonotone_inst : Cap_ValueMonotone := {| value_monotone := Axiopraxis.ValueMonotone |}.
Global Instance Cap_ReflectsPXL_inst : Cap_ReflectsPXL := {| cap_reflect := Axiopraxis.Conservativity |}.
Export Cap_ValueMonotone Cap_ReflectsPXL.
