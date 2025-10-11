(* V4/Value.v - Mock V4 Value Module *)

From Coq Require Import Program.

Module V4.

(* Mock V4 value types *)
Definition value := nat.

(* Mock V4 value ordering *)
Definition vle (x y : value) := x <= y.

End V4.
