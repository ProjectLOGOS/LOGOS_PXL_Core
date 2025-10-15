From Coq Require Import Program.
From PXLs Require Import PXLv3.
Set Implicit Arguments.

Module TeloPraxis.
  Parameter GoalSym : Type.
  Parameter intends  : GoalSym -> form -> Prop.
  (* Purpose modality placeholder *)
  Definition BoxTel (φ:form) : form := Box φ.
  Definition DiaTel (φ:form) : form := Dia φ.
End TeloPraxis.
