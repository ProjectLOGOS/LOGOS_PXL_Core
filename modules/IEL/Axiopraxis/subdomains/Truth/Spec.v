From PXLs Require Import PXLv3.
Require Import PXLs.IEL.Source.TheoPraxis.Props.
Module TruthSub.
  Import TheoProps.
  Definition V := Truth.
  Theorem conservative : forall φ, V φ -> φ. (* prove from PXL lemmas chosen for Truth *)
Admitted. (* must be proved before CI passes; no Admitted in final branch *)
End TruthSub.
