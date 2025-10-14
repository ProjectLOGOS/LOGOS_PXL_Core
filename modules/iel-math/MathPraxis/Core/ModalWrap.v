(** MathPraxis/Core/ModalWrap.v *)
From Coq Require Import Bool Arith Lia.
From PXLs Require Import PXLv3.    (* PXL core, as per your repo standard *)

Module ModalWrap.
  (* Thin, explicit wrappers so math predicates can be lifted into PXL formulas. *)
  Parameter Necessarily : Prop -> Prop.   (* alias for □ *)
  Parameter Possibly    : Prop -> Prop.   (* alias for ◇ *)

  Axiom Nec_implies_Poss : forall P, Necessarily P -> Possibly P.

  (* Glue to PXL operators/symbols: keep names stable for later proof automation. *)
  Notation "□ p" := (Necessarily p) (at level 65).
  Notation "◇ p" := (Possibly p) (at level 65).

End ModalWrap.
