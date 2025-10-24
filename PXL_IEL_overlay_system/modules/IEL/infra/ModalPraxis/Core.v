From PXLs Require Import PXLv3.
Module ModalPraxis.
  Definition V := PXLs.Internal Emergent Logics.Source.TheoPraxis.Props.ModalPraxis.

  Theorem modal_consistency : forall p, V p -> ~ (V p /\ ~ p).
  Proof. intros p H. unfold V in H. tauto. Qed.

  Theorem modal_distribution : forall p q, V (p -> q) -> (V p -> V q).
  Proof. intros p q H. unfold V in H. tauto. Qed.
End ModalPraxis.

(* Exported capabilities *)
Class Cap_ModalLogic : Prop := {
  modal_consistency : forall p, ModalPraxis.V p -> ~ (ModalPraxis.V p /\ ~ p);
  modal_distribution : forall p q, ModalPraxis.V (p -> q) -> (ModalPraxis.V p -> ModalPraxis.V q)
}.
Global Instance Cap_ModalLogic_inst : Cap_ModalLogic := {|
  modal_consistency := ModalPraxis.modal_consistency;
  modal_distribution := ModalPraxis.modal_distribution
|}.
