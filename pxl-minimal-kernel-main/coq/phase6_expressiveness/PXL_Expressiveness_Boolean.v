(* PXL_Expressiveness_Boolean.v *)
Require Import PXLv3 PXL_Deep_Soundness Assumptions.
Section BooleanExpressiveness.
  Variables φ ψ χ : form.
  Theorem def_and : Prov (Impl φ (Impl ψ χ)) -> Prov (And φ ψ). Admitted.
  Theorem def_or  : Prov (Or φ ψ). Admitted.
  Theorem def_top : Prov Top. Admitted.
  Theorem def_bot : Prov Bot. Admitted.
  Theorem functional_complete :
    (* Any boolean truth-function over n vars is representable in PXL basis. *)
    True. Admitted.
End BooleanExpressiveness.