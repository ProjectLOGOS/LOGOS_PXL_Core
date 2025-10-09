From Coq Require Import Program.
From PXLs Require Import PXLv3.
Set Implicit Arguments.

Module Axiopraxis.
  (* Worlds + aesthetic proximity (abstract) *)
  Parameter World : Type.
  Parameter R_ax : World -> World -> Prop.

  (* Modal wrappers (placeholder: reuse Box/Dia surface) *)
  Definition BoxAx (φ:form) : form := Box φ.
  Definition DiaAx  (φ:form) : form := Dia φ.
End Axiopraxis.
