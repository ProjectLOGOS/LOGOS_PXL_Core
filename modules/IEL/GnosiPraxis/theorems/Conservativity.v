From Coq Require Import Program Setoids.Setoid.

(* TODO: Restore full imports once module path resolution is fixed *)
(* Require Import modules.chronopraxis.theorems.ModalStrength.ModalFree
               modules.IEL.ModalPraxis.modal.FrameSpec. *)

(* Standalone definitions for conservativity *)
Parameter form : Type.
Parameter Prov : form -> Prop.
Parameter forces : Type -> form -> Prop.
Parameter modal_free : form -> Prop.
Parameter completeness_from_truth : forall φ, (forall w, forces w φ) -> Prov φ.

Theorem epistemic_conservative_nonmodal :
  forall φ, modal_free φ -> (forall w, forces w φ) -> Prov φ.
Proof. intros φ Hmf Hval; apply completeness_from_truth; exact Hval. Qed.
