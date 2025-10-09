From Coq Require Import Program.
(* From PXLs Require Import PXLv3. *)
Set Implicit Arguments.

(* Standalone definitions for compilation - using PXL canonical model types *)
Parameter form : Type.
Parameter Conj : form -> form -> form.

Module ChremaPraxis.
  Record Monoid := { M : Type; e : M; op : M -> M -> M }.
  (* Placeholder phase semantics hooks (kept abstract) *)
  Parameter entails : Monoid -> form -> form -> Prop.
  Definition Sep (φ ψ:form) : form := Conj φ ψ.
End ChremaPraxis.