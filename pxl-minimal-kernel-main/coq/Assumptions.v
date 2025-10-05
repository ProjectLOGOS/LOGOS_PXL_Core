(* Assumptions.v: Unavoidable constructive assumptions for PXL completeness *)

From PXLs Require Import PXLv3.

(* Frame assumption for modal duality: constructive witness extraction for failure of universal *)
Axiom NotAll_to_ExNot_R :
  forall (M:Model) w φ,
    (~ forall v, R w v -> forces M v (Neg φ)) ->
    exists v, R w v /\ forces M v φ.

(* If decidability of consistency for finite sets is not constructive, add here *)
(* Axiom decidable_cons_finite : ... *)

(* Philosophical justification: This captures the intuitionistic notion of "not all" implying "some not",
   which holds in Kripke semantics for S5 frames with constructive accessibility. *)