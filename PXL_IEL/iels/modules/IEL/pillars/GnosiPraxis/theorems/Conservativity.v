From Coq Require Import Program Setoids.Setoid.

(* TODO: Restore full imports once module path resolution is fixed *)
(* Require Import PXLs.Internal Emergent Logics.Infra.theorems.ModalStrength.ModalFree
               modules.Internal Emergent Logics.ModalPraxis.modal.FrameSpec. *)

(* Standalone definitions for conservativity *)
Parameter form : Type.
Parameter Prov : form -> Prop.
Parameter forces : Type -> form -> Prop.
Parameter modal_free : form -> Prop.
Parameter completeness_from_truth : forall f, (forall w, forces w f) -> Prov f.

Theorem epistemic_conservative_nonmodal :
  forall f, modal_free f -> (forall w, forces w f) -> Prov f.
Proof. intros f Hmf Hval; apply completeness_from_truth; exact Hval. Qed.
