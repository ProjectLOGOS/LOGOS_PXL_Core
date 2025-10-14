(* Quick test file for MathPraxis *)
From MathPraxis.Problems.Goldbach Require Import Scan.
Import GoldbachScan.

(* Test a few small cases *)
Eval compute in (goldbach_witness 4).
Eval compute in (goldbach_witness 6).
Eval compute in (goldbach_witness 8).

(* Test count_ok function *)
Eval compute in (count_ok 2 5).
