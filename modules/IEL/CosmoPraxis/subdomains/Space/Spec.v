From PXLs Require Import PXLv3.
Require Import PXLs.IEL.Source.TheoPraxis.Props.
Module SpaceSub.
  Import TheoProps.
  Definition V := Space.
  Theorem conservative : forall φ, V φ -> φ. (* prove from PXL lemmas chosen for Space *)
Admitted. (* must be proved before CI passes; no Admitted in final branch *)
End SpaceSub.
