From Coq Require Import Program.
From PXLs Require Import PXLv3.
Set Implicit Arguments.

Module ErgoPraxis.
  (* Actions/programs sketch *)
  Inductive Act := Skip | Seq (a b:Act) | Choice (a b:Act) | Test (φ:form).
  (* Program modality placeholders *)
  Definition BoxDo (a:Act) (φ:form) : form := Box φ.
  Definition DiaDo (a:Act) (φ:form) : form := Dia φ.
End ErgoPraxis.
