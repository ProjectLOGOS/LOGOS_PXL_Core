(** ArithmoPraxis Infrastructure Test *)
(* Test domain stubs *)
Load "modules/infra/arithmo/BooleanLogic/Boolean.v".
Load "modules/infra/arithmo/Core/ModalWrap.v".
Load "modules/infra/arithmo/NumberTheory/Number.v".

(* Test Goldbach example functionality *)
Load "modules/infra/arithmo/Examples/Goldbach/ScanFeatures.v".
Import ScanFeatures.

(* Verify basic functionality *)
Eval compute in (is_prime 7).
Eval compute in (goldbach_witness 10).
Eval compute in (closure_score 5).