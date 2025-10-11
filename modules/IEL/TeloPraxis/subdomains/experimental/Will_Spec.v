From PXLs Require Import PXLv3.
Require Import PXLs.IEL.Source.TheoPraxis.Props.
Module WillSub.
  Import TheoProps.
  Definition V := Will.
  Theorem conservative : forall φ, V φ -> φ. (* prove from PXL lemmas chosen for Will *)
Admitted. (* must be proved before CI passes; no Admitted in final branch *)
End WillSub.
