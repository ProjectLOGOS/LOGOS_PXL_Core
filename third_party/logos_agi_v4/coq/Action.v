(* V4/Action.v - Mock V4 Action Module *)

From Coq Require Import Program.

Module V4.

(* Mock V4 action types *)
Definition action := Prop -> Prop.

(* Mock V4 Hoare logic *)
Definition Hoare (P : Prop) (a : action) (Q : Prop) := (P -> a P) /\ (a P -> Q).

End V4.
