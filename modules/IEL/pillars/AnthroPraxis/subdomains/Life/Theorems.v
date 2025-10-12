From Coq Require Import Program.
From PXLs Require Import PXLv3.
Require Import modules.Internal Emergent Logics.AnthroPraxis.subdomains.Life.Spec.
Module LifeTheorems.
  (* Conservativity hook; keep zero admits *)
  Goal True. exact I. Qed.
End LifeTheorems.
