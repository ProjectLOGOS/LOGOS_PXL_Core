(* PXL_Expressiveness_Intertranslation.v *)
Require Import PXLv3 PXL_Deep_Soundness Assumptions PXL_Completeness_Truth_WF.
Section Intertranslation.
  Fixpoint T (φ:form) : s5_form := (* PXL→S5 *) admit.
  Fixpoint U (ψ:s5_form) : form := (* S5→PXL *) admit.
  Theorem UoT_sound : forall φ, Prov (Iff (U (T φ)) φ). Admitted.
  Theorem ToU_complete : forall ψ, s5_valid (iff (T (U ψ)) ψ). Admitted.
  Theorem conservativity_S5_to_PXL : forall ψ, s5_valid ψ -> Prov (U ψ). Admitted.
  Theorem conservativity_PXL_to_S5 : forall φ, Prov φ -> s5_valid (T φ). Admitted.
End Intertranslation.