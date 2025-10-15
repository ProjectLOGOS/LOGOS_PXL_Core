(** Realistic performance test for invariant scanning *)
Load "modules/iel-math/MathPraxis/Problems/Goldbach/ScanFeatures.v".
Import ScanFeatures.

(* Test individual components *)
Eval compute in (is_prime 17).
Eval compute in (goldbach_witness 20).

(* Test incremental closure scores *)
Eval compute in (closure_score 10).
Eval compute in (closure_score 25).  
Eval compute in (closure_score 100).

(* Test invariant summary for reasonable range *)
Eval compute in (invariant_summary 100).

(* Print closure rate *)
Eval compute in (closure_rate 100).