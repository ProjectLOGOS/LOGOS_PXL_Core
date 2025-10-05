(* PXL_Expressiveness_NormalForms.v *)
Require Import PXLv3 PXL_Deep_Soundness Assumptions.
Section NormalForms.
  Theorem nnf_exists : forall φ, exists φ', Prov (Iff φ φ') /\ nnf φ'. Admitted.
  Theorem modal_cnf_exists : forall φ, exists φ', Prov (Iff φ φ') /\ mcnf φ'. Admitted.
End NormalForms.