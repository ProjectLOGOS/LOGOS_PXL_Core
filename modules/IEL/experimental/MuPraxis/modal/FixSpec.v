From Coq Require Import Program.
(* From PXLs Require Import PXLv3. *)
Set Implicit Arguments.

(* Standalone definitions for compilation - using PXL canonical model types *)
Parameter form : Type.
Parameter Box : form -> form.

Module MuPraxis.
  (* Syntactic placeholders for fixpoint operators (guarded later) *)
  Inductive MuOp := Mu | Nu.
  Definition MuBox (φ:form) : form := Box φ.
End MuPraxis.
