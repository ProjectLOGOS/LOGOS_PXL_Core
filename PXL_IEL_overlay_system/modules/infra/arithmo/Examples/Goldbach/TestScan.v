(** MathPraxis/Problems/Goldbach/TestScan.v *)
Load "modules/iel-math/MathPraxis/Problems/Goldbach/ScanFeatures.v".
Import ScanFeatures.

(* Test individual features *)
Eval compute in (mk_feat 4).
Eval compute in (mk_feat 6).
Eval compute in (mk_feat 8).

(* Test closure score for small range *)
Eval compute in (closure_score 10).
Eval compute in (closure_rate 10).

(* Test invariant summary *)
Eval compute in (invariant_summary 20).

(* Test feature extraction *)
Eval compute in (extract_features 10).

(* Larger test - closure score up to ~n=4004 *)
Eval vm_compute in (closure_score 2000).