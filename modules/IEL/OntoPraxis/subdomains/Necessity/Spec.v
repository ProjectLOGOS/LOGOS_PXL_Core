From PXLs.Core Require Import PXL_Kernel.
From PXLs.Theo Require Import Props.
Module NecessitySub.
  Import TheoProps.
  Definition V := Necessity.
  Theorem conservative : forall φ, V φ -> φ. (* prove from PXL lemmas chosen for Necessity *)
Admitted. (* must be proved before CI passes; no Admitted in final branch *)
End NecessitySub.
