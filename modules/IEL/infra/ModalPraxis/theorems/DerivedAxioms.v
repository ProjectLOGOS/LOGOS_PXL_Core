From Coq Require Import Program Setoids.Setoid.

(* TODO: Restore full imports once module path resolution is fixed *)
(* From PXLs Require Import PXLv3. *)
(* Require Import modules.IEL.UM.modal.FrameSpec. *)

(* Standalone loading - reuse parameters from FrameSpec *)
Parameter form : Type.
Parameter Prov : form -> Prop.
Parameter Box : form -> form.
Parameter Dia : form -> form.
Parameter Impl : form -> form -> form.

Definition set := form -> Prop.
Parameter mct : set -> Prop.
Definition can_world := { G : set | mct G }.
Parameter can_R : can_world -> can_world -> Prop.
Parameter forces : can_world -> form -> Prop.

Parameter forces_Box : forall w φ, forces w (Box φ) <-> (forall u, can_R w u -> forces u φ).
Parameter forces_Dia : forall w φ, forces w (Dia φ) <-> (exists u, can_R w u /\ forces u φ).
Parameter forces_Impl : forall w φ ψ, forces w (Impl φ ψ) <-> (forces w φ -> forces w ψ).

Parameter completeness_from_truth : forall φ, (forall w, forces w φ) -> Prov φ.

(* Frame law classes *)
Class Serial     : Prop := serial_R     : forall w, exists u, can_R w u.
Class Reflexive  : Prop := reflexive_R  : forall w, can_R w w.
Class Symmetric  : Prop := symmetric_R  : forall w u, can_R w u -> can_R u w.
Class Transitive : Prop := transitive_R : forall w u v, can_R w u -> can_R u v -> can_R w v.
Class Euclidean  : Prop := euclid_R     : forall w u v, can_R w u -> can_R w v -> can_R u v.

Set Implicit Arguments.

(* T and 4 axioms under reflexive and transitive frames *)
Section T_4.
  Context (Hrefl: Reflexive) (Htran: Transitive).

  (* T: □φ → φ on reflexive frames *)
  Lemma valid_T : forall φ w, forces w (Impl (Box φ) φ).
  Proof. 
    intros φ w. rewrite forces_Impl. intro Hbox.
    rewrite forces_Box in Hbox.
    apply Hbox. apply reflexive_R.
  Qed.
  
  Theorem provable_T : forall φ, Prov (Impl (Box φ) φ).
  Proof. 
    intro φ. apply completeness_from_truth. 
    intro w. apply valid_T. 
  Qed.

  (* 4: □φ → □□φ on transitive frames *)
  Lemma valid_4 : forall φ w, forces w (Impl (Box φ) (Box (Box φ))).
  Proof. 
    intros φ w. rewrite forces_Impl. intro Hbox.
    rewrite forces_Box in Hbox. rewrite forces_Box.
    intros u Hwu. rewrite forces_Box.
    intros v Huv.
    apply Hbox. apply (transitive_R w u v Hwu Huv).
  Qed.
  
  Theorem provable_4 : forall φ, Prov (Impl (Box φ) (Box (Box φ))).
  Proof. 
    intro φ. apply completeness_from_truth. 
    intro w. apply valid_4. 
  Qed.
End T_4.

(* B and 5 axioms under symmetric and equivalence frames *)
Section B_5.
  Context (Hsym: Symmetric) (Htran: Transitive) (Hrefl: Reflexive).

  (* B: φ → □◇φ on symmetric frames *)
  Lemma valid_B : forall φ w, forces w (Impl φ (Box (Dia φ))).
  Proof.
    intros φ w. rewrite forces_Impl. intro Hφ.
    rewrite forces_Box. intros u Hwu.
    rewrite forces_Dia.
    exists w. split.
    - apply symmetric_R. exact Hwu.
    - exact Hφ.
  Qed.
  
  Theorem provable_B : forall φ, Prov (Impl φ (Box (Dia φ))).
  Proof. 
    intro φ. apply completeness_from_truth. 
    intro w. apply valid_B. 
  Qed.

  (* 5: ◇φ → □◇φ on equivalence frames (reflexive + symmetric + transitive) *)
  Lemma valid_5 : forall φ w, forces w (Impl (Dia φ) (Box (Dia φ))).
  Proof.
    intros φ w. rewrite forces_Impl. intro Hdia.
    rewrite forces_Dia in Hdia. destruct Hdia as [u [Hwu Hφu]].
    rewrite forces_Box. intros v Hwv.
    rewrite forces_Dia.
    exists u. split.
    - apply (transitive_R v w u).
      + apply symmetric_R. exact Hwv.
      + exact Hwu.
    - exact Hφu.
  Qed.
  
  Theorem provable_5 : forall φ, Prov (Impl (Dia φ) (Box (Dia φ))).
  Proof. 
    intro φ. apply completeness_from_truth. 
    intro w. apply valid_5. 
  Qed.
End B_5.

(* D axiom under serial frames *)
Section D.
  Context (Hser: Serial).

  (* D: □φ → ◇φ on serial frames *)
  Lemma valid_D : forall φ w, forces w (Impl (Box φ) (Dia φ)).
  Proof. 
    intros φ w. rewrite forces_Impl. intro Hbox.
    rewrite forces_Box in Hbox. rewrite forces_Dia.
    destruct (serial_R w) as [u Hwu].
    exists u. split.
    - exact Hwu.
    - apply Hbox. exact Hwu.
  Qed.
  
  Theorem provable_D : forall φ, Prov (Impl (Box φ) (Dia φ)).
  Proof. 
    intro φ. apply completeness_from_truth. 
    intro w. apply valid_D. 
  Qed.
End D.
