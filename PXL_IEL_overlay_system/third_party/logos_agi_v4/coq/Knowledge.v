(* V4/Knowledge.v - Mock V4 Knowledge Module *)

From Coq Require Import Program.

Module V4.

(* Mock V4 knowledge types *)
Definition claim := Prop.
Definition world := unit.

(* Mock V4 forcing relation *)
Definition Forces (w : world) (φ : claim) := φ.

(* Mock V4 proof system *)
Definition proves (φ : claim) := φ.

End V4.
