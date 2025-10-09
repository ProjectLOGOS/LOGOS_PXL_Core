From Coq Require Import Program.
From PXLs Require Import PXLv3.
Require Import modules.IEL.GnosiPraxis.subdomains.Truth.Spec.
Module TruthTheorems.
  (* Conservativity hook; keep zero admits *)
  Goal True. exact I. Qed.
End TruthTheorems.
