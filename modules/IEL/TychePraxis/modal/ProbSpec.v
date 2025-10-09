From Coq Require Import QArith Program.
(* From PXLs Require Import PXLv3. *)
Set Implicit Arguments.

(* Standalone definitions for compilation - using PXL canonical model types *)
Parameter form : Type.
Parameter Box : form -> form.

Module TychePraxis.
  (* Finite probabilistic Kripke sketch with rational weights *)
  Parameter World : Type.
  Parameter trans : World -> World -> Q.  (* transition weight *)
  Definition L_ge (q:Q) (φ:form) : form := Box φ.  (* threshold placeholder *)
End TychePraxis.