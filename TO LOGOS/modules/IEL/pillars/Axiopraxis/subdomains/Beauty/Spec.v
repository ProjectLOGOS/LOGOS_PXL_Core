From PXLs Require Import PXLv3.
Require Import PXLs.Internal Emergent Logics.Source.TheoPraxis.Props.
Module BeautySub.
  Import TheoProps.
  Definition V := Beauty.
  Theorem conservative : forall φ, V φ -> φ. (* prove from PXL lemmas chosen for Beauty *)
Admitted. (* must be proved before CI passes; no Admitted in final branch *)
End BeautySub.
