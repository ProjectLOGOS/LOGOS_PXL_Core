(** Final demonstration of invariant mining system *)
Load "modules/iel-math/MathPraxis/Problems/Goldbach/ScanFeatures.v".
Import ScanFeatures.

(* Demonstrate invariant miners working *)
Eval compute in (mk_feat 10).
Eval compute in (mk_feat 20).
Eval compute in (mk_feat 30).

(* Show closure analysis *)
Eval compute in (closure_score 50).
Eval compute in (invariant_summary 50).
Eval compute in (closure_rate 50).

(* Feature extraction demo *)
Eval compute in (extract_features 12).
Eval compute in (extract_features 18).