(** ExtractCore.v - OCaml Extraction for Verified Slice Only **)

From Coq Require Import Extraction.
Extraction Language OCaml.

(** Require ONLY the coqchk-verified modules **)
Require Import PXLs.PXLv3
               PXLs.Internal Emergent Logics.Source.TheoPraxis.Props.

(** Extract the core syntactic types **)
Extract Inductive form => "pxl_form" [ "PxlAtom" "PxlBot" "PxlNeg" "PxlConj" "PxlDisj" "PxlImpl" "PxlBox" "PxlDia" ].

(** Extract computational definitions **)
Extraction "pxl_core.ml" TheoProps.Truth.
