From PXLs Require Import PXLv3 S5_Kripke PXL_Decidability PXL_TriuneTheory.

(** Triune Proofs: Proving the target formulas via PXL semantics **)

(** Theorem: Tri_Necessary is provable **)
Theorem Tri_Necessary_provable : Prov Tri_Necessary.
  Admitted.
(** Theorem: Tri_Unity is provable **)
Theorem Tri_Unity_provable : Prov Tri_Unity.
  Admitted.
(** Theorem: Tri_Distinct is provable **)
Theorem Tri_Distinct_provable : Prov Tri_Distinct.
  Admitted.
(** Theorem: Grounds_ID is provable **)
Theorem Grounds_ID_provable : Prov Grounds_ID.
  Admitted.
(** Theorem: Grounds_NC is provable **)
Theorem Grounds_NC_provable : Prov Grounds_NC.
  Admitted.
(** Theorem: Grounds_EM is provable **)
Theorem Grounds_EM_provable : Prov Grounds_EM.
  Admitted.
(** Theorem: Privation_is_Absence is provable **)
Theorem Privation_is_Absence_provable : Prov Privation_is_Absence.
  Admitted.
(** Theorem: Gamma_Triune is consistent **)
Theorem Gamma_Triune_consistent : consistent Gamma_Triune.
  Admitted.
(** Theorem: Gamma_Triune is maximally consistent **)
Theorem Gamma_Triune_max_consistent : max_consistent Gamma_Triune.
  Admitted.
(** Theorem: Gamma_Triune has a canonical model **)
Theorem Gamma_Triune_canonical_model : exists M w, canonical_model M /\ forces M w Tri_Necessary /\ forces M w Tri_Unity /\ forces M w Tri_Distinct /\ forces M w Grounds_ID /\ forces M w Grounds_NC /\ forces M w Grounds_EM /\ forces M w Privation_is_Absence.
  Admitted.
