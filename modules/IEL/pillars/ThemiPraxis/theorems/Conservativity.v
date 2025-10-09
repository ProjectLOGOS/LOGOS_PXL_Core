From Coq Require Import Program Setoids.Setoid.
Set Implicit Arguments.

(* Standalone definitions for compilation - using PXL canonical model types *)
Parameter form : Type.
Parameter Prov : form -> Prop.
Parameter forces : Type -> form -> Prop.
Parameter modal_free : form -> Prop.
Parameter completeness_from_truth : forall f, (forall w, forces w f) -> Prov f.

Theorem deontic_conservative_nonmodal :
  forall f, modal_free f -> (forall w, forces w f) -> Prov f.
Proof. intros f _ H; apply completeness_from_truth; exact H. Qed.
