From Coq Require Import FunctionalExtensionality.

Module TopoPraxis.
  Class Isometry (A B : Type) := {
    iso_f : A -> B;
    iso_g : B -> A;
    iso_fg : forall x, iso_f (iso_g x) = x;
    iso_gf : forall x, iso_g (iso_f x) = x
  }.

  Theorem BC_invariant {A B} (I : Isometry A B) (P : B -> Prop) :
    (forall x, P x) <-> (forall x, P (iso_f I x)).
  Proof.
    split; intros H x.
    - apply H.
    - rewrite <- iso_fg; apply H.
  Qed.
End TopoPraxis.
