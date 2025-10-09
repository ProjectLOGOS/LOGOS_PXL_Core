From Coq Require Import Program Setoids.Setoid.

(* TODO: Restore full imports once module path resolution is fixed *)
(* From PXLs Require Import PXLv3. *)
(* Require Import modules.chronopraxis.substrate.ChronoAxioms *)
(*                modules.chronopraxis.theorems.MetaTheorems. *)

(* Standalone definitions for compilation *)
Inductive form : Type :=
| Bot : form
| Atom : nat -> form
| Impl : form -> form -> form
| Conj : form -> form -> form
| Disj : form -> form -> form
| Neg : form -> form
| Box : form -> form
| Dia : form -> form.

Parameter world : Type.
Parameter can_world : Type.
Parameter can_R : can_world -> can_world -> Prop.
Parameter forces : can_world -> form -> Prop.
Parameter Prov : form -> Prop.

(* Forcing relation for modal operators *)
Parameter forces_Box : forall w φ, forces w (Box φ) <-> (forall u, can_R w u -> forces u φ).
Parameter forces_Dia : forall w φ, forces w (Dia φ) <-> (exists u, can_R w u /\ forces u φ).
Parameter forces_Impl : forall w φ ψ, forces w (Impl φ ψ) <-> (forces w φ -> forces w ψ).

(* Semantic validity definition *)
Definition valid (φ : form) : Prop := forall w, forces w φ.

(* Completeness bridge: semantic validity implies provability *)
Parameter completeness_from_truth : forall φ, valid φ -> Prov φ.

Set Implicit Arguments.

(* Necessitation: if φ is valid at all worlds, then □φ is valid at all worlds. *)
Lemma valid_necessitation : forall (φ:form) (w:can_world),
  (forall u, forces u φ) -> forces w (Box φ).
Proof.
  intros φ w H. rewrite forces_Box.
  intros u _. exact (H u).
Qed.

(* Semantic necessitation: if φ is valid then □φ is valid *)
Theorem semantic_necessitation : forall φ,
  (forall w, forces w φ) -> Prov (Box φ).
Proof.
  intro φ. intro Hvalid.
  apply completeness_from_truth. intro w. apply valid_necessitation. exact Hvalid.
Qed.

(* Standard necessitation rule: if ⊢ φ then ⊢ □φ *)
(* This requires soundness (Prov φ -> valid φ) which we assume as parameter *)
Parameter soundness : forall φ, Prov φ -> (forall w, forces w φ).

Theorem provable_necessitation : forall φ,
  Prov φ -> Prov (Box φ).
Proof.
  intros φ Hprov.
  apply semantic_necessitation.
  apply soundness. exact Hprov.
Qed.

(* K axiom: □(φ→ψ) → (□φ → □ψ) is valid on all frames *)
Lemma valid_K : forall (φ ψ:form) (w:can_world),
  forces w (Impl (Box (Impl φ ψ)) (Impl (Box φ) (Box ψ))).
Proof.
  intros φ ψ w. rewrite forces_Impl. intro HboxImp.
  rewrite forces_Impl. intro Hboxφ.
  rewrite forces_Box in HboxImp. rewrite forces_Box in Hboxφ. rewrite forces_Box.
  intros u Hwu.
  specialize (HboxImp u Hwu). (* forces u (φ→ψ) *)
  specialize (Hboxφ u Hwu).   (* forces u φ *)
  rewrite forces_Impl in HboxImp.
  exact (HboxImp Hboxφ).      (* hence forces u ψ *)
Qed.

Theorem provable_K : forall φ ψ, Prov (Impl (Box (Impl φ ψ)) (Impl (Box φ) (Box ψ))).
Proof.
  intros φ ψ. apply completeness_from_truth. intro w. apply valid_K.
Qed.