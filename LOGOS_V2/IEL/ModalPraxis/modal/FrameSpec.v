From Coq Require Import Program Setoids.Setoid.

(* TODO: Restore full imports once module path resolution is fixed *)
(* From PXLs Require Import PXLv3. *)
(* Require Import PXLs.Internal Emergent Logics.Infra.substrate.ChronoAxioms *)
(*                PXLs.Internal Emergent Logics.Infra.theorems.MetaTheorems. *)

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

(* Forcing relation axioms *)
Parameter forces_Box : forall w φ, forces w (Box φ) <-> (forall u, can_R w u -> forces u φ).
Parameter forces_Dia : forall w φ, forces w (Dia φ) <-> (exists u, can_R w u /\ forces u φ).
Parameter forces_Impl : forall w φ ψ, forces w (Impl φ ψ) <-> (forces w φ -> forces w ψ).

(* Modal operator capabilities *)
Class Cap_ForcesBox (W:Type) (R:W->W->Prop) (forces: W->form->Prop) : Prop :=
  { forces_box : forall w φ, forces w (Box φ) <-> (forall u, R w u -> forces u φ) }.

Class Cap_ForcesDia (W:Type) (R:W->W->Prop) (forces: W->form->Prop) : Prop :=
  { forces_dia : forall w φ, forces w (Dia φ) <-> (exists u, R w u /\ forces u φ) }.

Class Cap_ForcesImpl (W:Type) (R:W->W->Prop) (forces: W->form->Prop) : Prop :=
  { forces_impl : forall w φ ψ, forces w (Impl φ ψ) <-> (forces w φ -> forces w ψ) }.

(* Forcing relation parameters - replaced by instances *)
Global Instance CapForcesBox_param : Cap_ForcesBox can_world can_R forces :=
  { forces_box := fun w φ => forces_Box w φ }.

Global Instance CapForcesDia_param : Cap_ForcesDia can_world can_R forces :=
  { forces_dia := fun w φ => forces_Dia w φ }.

Global Instance CapForcesImpl_param : Cap_ForcesImpl can_world can_R forces :=
  { forces_impl := fun w φ ψ => forces_Impl w φ ψ }.

(* Parameter forces_Box : forall w φ, forces w (Box φ) <-> (forall u, can_R w u -> forces u φ). *)
(* Parameter forces_Dia : forall w φ, forces w (Dia φ) <-> (exists u, can_R w u /\ forces u φ). *)
(* Parameter forces_Impl : forall w φ ψ, forces w (Impl φ ψ) <-> (forces w φ -> forces w ψ). *)

(* Flags for frame laws - each can be toggled independently *)
Class Serial     : Prop := serial_R     : forall w, exists u, can_R w u.
Class Reflexive  : Prop := reflexive_R  : forall w, can_R w w.
Class Symmetric  : Prop := symmetric_R  : forall w u, can_R w u -> can_R u w.
Class Transitive : Prop := transitive_R : forall w u v, can_R w u -> can_R u v -> can_R w v.
Class Euclidean  : Prop := euclid_R     : forall w u v, can_R w u -> can_R w v -> can_R u v.

(* Completeness bridge from kernel (proven in PXL repository) *)
Parameter completeness_from_truth : forall φ, (forall w, forces w φ) -> Prov φ.

Set Implicit Arguments.
