From Coq Require Import Program.
From PXLs Require Import PXLv3.
Require Import modules.Internal Emergent Logics.ChronoPraxis.substrate.ChronoAxioms.
Set Implicit Arguments.

Module CosmoPraxis.
  (* Space–time sketch: pair of temporal mode and spatial region index *)
  Parameter SpaceIndex : Type.
  Record STPoint := { chi_mode : ChronoAxioms.chi; sigma : SpaceIndex }.
  (* Cosmological reachability placeholder *)
  Parameter reaches : STPoint -> STPoint -> Prop.
  Definition BoxCos (φ:form) : form := Box φ.
  Definition DiaCos (φ:form) : form := Dia φ.
End CosmoPraxis.
