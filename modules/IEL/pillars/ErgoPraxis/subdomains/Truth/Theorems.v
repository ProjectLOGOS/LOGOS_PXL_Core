From Coq Require Import Program.
From PXLs Require Import PXLv3.
Require Import modules.IEL.ErgoPraxis.subdomains.Truth.Spec.
Module ErgoPraxisTruthTheorems.
  (* Conservativity hook; keep zero admits *)
  Goal True. exact I. Qed.
End ErgoPraxisTruthTheorems.