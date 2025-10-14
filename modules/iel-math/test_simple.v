(* Simple test of MathPraxis functionality *)
Load "modules/iel-math/MathPraxis/Problems/Goldbach/Scan.v".
Import GoldbachScan.

(* Test basic primality *)
Eval compute in (is_prime 2).
Eval compute in (is_prime 3).
Eval compute in (is_prime 4).
Eval compute in (is_prime 5).

(* Test Goldbach witness finding *)
Eval compute in (goldbach_witness 4).
Eval compute in (goldbach_witness 6).
Eval compute in (goldbach_witness 8).
Eval compute in (goldbach_witness 10).

(* Test count_ok function for small range *)
Eval compute in (count_ok 2 3).
