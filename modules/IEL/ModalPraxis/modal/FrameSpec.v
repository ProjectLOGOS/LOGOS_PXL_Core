From Coq Require Import Program Setoids.Setoid.

(* TODO: Restore full imports once module path resolution is fixed *)
(* From PXLs Require Import PXLv3. *)
(* Require Import modules.chronopraxis.substrate.ChronoAxioms *)
(*                modules.chronopraxis.theorems.MetaTheorems. *)

(* Standalone definitions for compilation - using PXL canonical model types *)
Parameter form : Type.
Parameter Prov : form -> Prop.
Parameter Box : form -> form.
Parameter Dia : form -> form.
Parameter Impl : form -> form -> form.

(* Reuse PXL canonical model approach *)
Definition set := form -> Prop.
Parameter mct : set -> Prop.  (* maximal consistent theory predicate *)
Definition In_set (G:set) (p:form) : Prop := G p.
Definition can_world := { G : set | mct G }.
Parameter can_R : can_world -> can_world -> Prop.
Parameter forces : can_world -> form -> Prop.

(* Forcing relation parameters *)
Parameter forces_Box : forall w φ, forces w (Box φ) <-> (forall u, can_R w u -> forces u φ).
Parameter forces_Dia : forall w φ, forces w (Dia φ) <-> (exists u, can_R w u /\ forces u φ).
Parameter forces_Impl : forall w φ ψ, forces w (Impl φ ψ) <-> (forces w φ -> forces w ψ).

(* Flags for frame laws - each can be toggled independently *)
Class Serial     : Prop := serial_R     : forall w, exists u, can_R w u.
Class Reflexive  : Prop := reflexive_R  : forall w, can_R w w.
Class Symmetric  : Prop := symmetric_R  : forall w u, can_R w u -> can_R u w.
Class Transitive : Prop := transitive_R : forall w u v, can_R w u -> can_R u v -> can_R w v.
Class Euclidean  : Prop := euclid_R     : forall w u v, can_R w u -> can_R w v -> can_R u v.

(* Completeness bridge from kernel (proven in PXL repository) *)
Parameter completeness_from_truth : forall φ, (forall w, forces w φ) -> Prov φ.

Set Implicit Arguments.