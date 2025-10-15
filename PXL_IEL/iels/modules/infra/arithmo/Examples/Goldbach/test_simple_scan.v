(** Simple test to isolate the performance issue *)
Load "modules/iel-math/MathPraxis/Problems/Goldbach/ScanFeatures.v".
Import ScanFeatures.

(* Test basic functions first *)
Eval compute in (is_prime 7).
Eval compute in (goldbach_witness 4).
Eval compute in (mk_feat 4).

(* Test very small closure score *)
Eval compute in (closure_score 5).

(* Test slightly larger - this is where it might hang *)
Eval compute in (closure_score 50).