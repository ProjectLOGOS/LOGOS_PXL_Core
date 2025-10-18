(** ArithmoPraxis/Core/ModalWrap.v *)
From Coq Require Import Bool Arith Lia.
(* PXL integration will be added when PXLv3 is available *)

Module ArithmoPraxis_ModalWrap.
  (* Thin, explicit wrappers so math predicates can be lifted into PXL formulas. *)
  Parameter Necessarily : Prop -> Prop.   (* alias for □ *)
  Parameter Possibly    : Prop -> Prop.   (* alias for ◇ *)

  Axiom Nec_implies_Poss : forall P, Necessarily P -> Possibly P.

  (* Glue to PXL operators/symbols: keep names stable for later proof automation. *)
  Notation "□ p" := (Necessarily p) (at level 65).
  Notation "◇ p" := (Possibly p) (at level 65).

End ArithmoPraxis_ModalWrap.
