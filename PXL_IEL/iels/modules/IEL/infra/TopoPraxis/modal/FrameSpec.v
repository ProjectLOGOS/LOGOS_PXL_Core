From Coq Require Import Program.
From PXLs Require Import PXLv3.
Set Implicit Arguments.

Parameter form : Type.
Parameter Box : form -> form.
Parameter Dia : form -> form.

Module TopoPraxis.
  Parameter Region : Type.
  Parameter inside : Region -> Region -> Prop.
  Parameter adjacent : Region -> Region -> Prop.
  (* Spatial necessity placeholder *)
  Definition BoxTopo (φ:form) : form := Box φ.
  Definition DiaTopo (φ:form) : form := Dia φ.
End TopoPraxis.
