From PXLs Require Import PXLv3.

(* Metaphysical Necessity Overlay *)

Definition Father := Var 0.
Definition Son := Var 1.
Definition Spirit := Var 2.
Definition Essence := Var 3.

Definition Meta_Necessary (φ : form) := Box φ.

Theorem meta_necessary_father : Prov (Meta_Necessary Father).
Admitted.

Theorem meta_necessary_son : Prov (Meta_Necessary Son).
Admitted.

Theorem meta_necessary_spirit : Prov (Meta_Necessary Spirit).
Admitted.

Theorem meta_necessary_essence : Prov (Meta_Necessary Essence).
Admitted.

(* Grounding Laws *)
Theorem grounding_father : Prov (Impl Father Essence).
Admitted.

Theorem grounding_son : Prov (Impl Son Essence).
Admitted.

Theorem grounding_spirit : Prov (Impl Spirit Essence).
Admitted.

(* Privation *)
Theorem privation : Prov (Impl (Neg Essence) Bot).
Admitted.

(* Uniqueness *)
Theorem uniqueness_father : Prov (Impl (And Father (Meta_Necessary (Neg Father))) Bot).
Admitted.

Theorem uniqueness_son : Prov (Impl (And Son (Meta_Necessary (Neg Son))) Bot).
Admitted.

Theorem uniqueness_spirit : Prov (Impl (And Spirit (Meta_Necessary (Neg Spirit))) Bot).
Admitted.

