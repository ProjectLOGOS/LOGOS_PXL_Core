From PXLs Require Import PXLv3.
Require Import PXLs.IEL.Source.TheoPraxis.Props.
Module LifeSub.
  Import TheoProps.
  Definition V := Life.
  Theorem conservative : forall φ, V φ -> φ. (* prove from PXL lemmas chosen for Life *)
Admitted. (* must be proved before CI passes; no Admitted in final branch *)
End LifeSub.
