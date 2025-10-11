From Coq Require Import Program.
From PXLs Require Import PXLv3.
Require Import modules.IEL.ThemiPraxis.subdomains.Truth.Spec.
Module ThemiPraxisTruthTheorems.
  (* Conservativity hook; keep zero admits *)
  Goal True. exact I. Qed.
End ThemiPraxisTruthTheorems.