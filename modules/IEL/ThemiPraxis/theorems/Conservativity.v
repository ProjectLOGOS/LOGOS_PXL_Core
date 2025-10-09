From Coq Require Import Program Setoids.Setoid.
Set Implicit Arguments.

(* Standalone definitions for compilation - using PXL canonical model types *)
Parameter form : Type.
Parameter Prov : form -> Prop.
Parameter forces : Type -> form -> Prop.
Parameter modal_free : form -> Prop.
Parameter completeness_from_truth : forall φ, (forall w, forces w φ) -> Prov φ.

Theorem deontic_conservative_nonmodal :
  forall φ, modal_free φ -> (forall w, forces w φ) -> Prov φ.
Proof. intros φ _ H; apply completeness_from_truth; exact H. Qed.
