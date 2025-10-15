From Coq Require Import Program.
From PXLs Require Import PXLv3.
Require Import modules.Internal Emergent Logics.Axiopraxis.subdomains.Beauty.Spec.
Module BeautyTheorems.
  (* Conservativity hook; keep zero admits *)
  Goal True. exact I. Qed.
End BeautyTheorems.
