(* ExtractCore.v - OCaml Extraction for PXL IEL Core *)

From Coq Require Import Extraction.
Extraction Language OCaml.

(* Require the verified modules *)
Require Import PXLs.PXLv3
               PXLs.IEL.Source.TheoPraxis.Props
               PXLs.IEL.Infra.ChronoPraxis.Substrate.ChronoAxioms
               PXLs.IEL.Infra.ChronoPraxis.Substrate.Bijection
               PXLs.IEL.Infra.ChronoPraxis.Substrate.ChronoMappings
               PXLs.IEL.Infra.ChronoPraxis.Tactics.ChronoTactics
               PXLs.IEL.Infra.ChronoPraxis.Theorems.ChronoProofs.

(* Require V4 integration modules *)
Require Import PXLs.V4.Adapters.Knowledge
               PXLs.V4.Adapters.Action
               PXLs.V4.Adapters.Value
               PXLs.V4.Guards.V4_Conservativity.

(* Extract key combinators for runtime verification *)
Extraction "extraction/pxl_core.ml" ChronoProofs.P_chi_identity_preservation ChronoProofs.eternal_identity_preservation.

(* Extract V4 adapter functions for runtime overlay *)
Extraction "extraction/v4_adapters.ml"
  V4_Knowledge_Adapter.v4_knowledge_to_gnosi
  V4_Knowledge_Adapter.v4_knows_sound
  V4_Action_Adapter.v4_action_to_hoare
  V4_Action_Adapter.v4_hoare_sound
  V4_Value_Adapter.v4_value_to_axio
  V4_Value_Adapter.v4_value_mono
  V4_Conservativity.runtime_v4_safe.