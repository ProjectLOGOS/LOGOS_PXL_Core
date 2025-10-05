(* PXL_Expressiveness_ModalDuals.v *)
Require Import PXLv3 PXL_Deep_Soundness Assumptions PXL_Completeness_Truth_WF.
Section ModalDuals.
  Variable φ : form.
  Theorem dia_def : Prov (Iff (Dia φ) (Neg (Box (Neg φ)))). Admitted.
  Theorem box_dia_dual1 : Prov (Impl (Box φ) (Neg (Dia (Neg φ)))). Admitted.
  Theorem box_dia_dual2 : Prov (Impl (Dia φ) (Neg (Box (Neg φ)))). Admitted.
End ModalDuals.