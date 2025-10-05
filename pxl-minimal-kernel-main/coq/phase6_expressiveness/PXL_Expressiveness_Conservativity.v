(* PXL_Expressiveness_Conservativity.v *)
Require Import PXLv3 PXL_Deep_Soundness Assumptions.
Section Conservativity.
  Theorem definitional_extension_safe :
    forall φ, Prov (eliminate_macros φ) -> Prov φ. Admitted.
End Conservativity.