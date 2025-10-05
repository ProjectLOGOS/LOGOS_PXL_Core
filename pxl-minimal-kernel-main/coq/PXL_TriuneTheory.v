From PXLs Require Import PXLv3.

(* Derivable from Hilbert propositional axioms *)

Lemma box_imp_r (φ ψ : form) : Prov (Impl φ ψ) -> Prov (Impl (Box φ) (Box ψ)).
Proof.
  intros H.
  pose (H1 := nec H).
  pose (H2 := ax_K φ ψ).
  eapply mp; eauto.
Qed.

Lemma priv_absent (φ : form) : Prov (Nec (Impl (Impl φ Bot) (Impl φ Bot))).
Proof.
  pose (X := Impl φ Bot).
  pose proof (id_prop X) as H.
  exact (nec H).
Qed.


