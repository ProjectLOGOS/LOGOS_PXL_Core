(* PXL_Expressiveness_Filtration.v *)
Require Import PXLv3 PXL_Deep_Soundness Assumptions PXL_Completeness_Truth_WF.
Section Filtration.
  Theorem filtration : forall M φ, exists M', filtered M φ M' /\ (* size bound *) True. Admitted.
  Corollary fmp : forall φ, ~ Prov φ -> exists finite_model M, M ⊭ φ. Admitted.
  Corollary decidable_bounded_depth :
    forall d, decidable (fun φ => md φ <= d /\ Prov φ). Admitted.
End Filtration.