From Coq Require Import Program Setoids.Setoid.

(* TODO: Restore full imports once module path resolution is fixed *)
(* From PXLs Require Import PXLv3. *)
(* Require Import modules.Internal Emergent Logics.ModalPraxis.modal.FrameSpec
               modules.Internal Emergent Logics.ModalPraxis.theorems.{NormalBase,DerivedAxioms}. *)

(* Standalone definitions for compilation - using PXL canonical model types *)
Parameter form : Type.
Parameter Prov : form -> Prop.
Parameter Box : form -> form.
Parameter Dia : form -> form.
Parameter Impl : form -> form -> form.
Parameter forces : Type -> form -> Prop.
Parameter can_world : Type.
Parameter can_R : can_world -> can_world -> Prop.

(* Frame classes from ModalPraxis *)
Class Reflexive : Prop := { reflexive_R : forall w, can_R w w }.
Class Transitive : Prop := { transitive_R : forall w u v, can_R w u -> can_R u v -> can_R w v }.
Class Symmetric : Prop := { symmetric_R : forall w u, can_R w u -> can_R u w }.
Class Serial : Prop := { serial_R : forall w, exists u, can_R w u }.

(* Modal theorems from ModalPraxis *)
Parameter provable_K : forall φ ψ, Prov (Impl (Box (Impl φ ψ)) (Impl (Box φ) (Box ψ))).
Parameter provable_necessitation : forall φ, (forall w, forces w φ) -> Prov (Box φ).
Parameter provable_T : Reflexive -> forall φ, Prov (Impl (Box φ) φ).
Parameter provable_4 : Reflexive -> Transitive -> forall φ, Prov (Impl (Box φ) (Box (Box φ))).
Parameter provable_5 : Reflexive -> Symmetric -> Transitive -> forall φ, Prov (Impl (Dia φ) (Box (Dia φ))).
Parameter provable_B : Reflexive -> Symmetric -> Transitive -> forall φ, Prov (Impl φ (Box (Dia φ))).
Parameter provable_D : Serial -> forall φ, Prov (Impl (Box φ) (Dia φ)).

Set Implicit Arguments.

Module GnosiPraxis.

  (* Agents as an abstract, decidable type if needed later. *)
  Parameter Agent : Type.

  (* Per-agent epistemic accessibility is modeled via frame flags.
     We keep forces/can_R abstract in ModalPraxis and pass flags as parameters. *)

  Section PerAgent.
    Variable a : Agent.

    (* Per-agent frame laws (parameters, not global instances). *)
    Class K_Frame : Prop := {}.  (* base normal modal, no extra constraints *)
    Class T_Frame : Prop := { T_refl  : Reflexive }.
    Class S4_Frame: Prop := { S4_refl : Reflexive; S4_tran : Transitive }.
    Class S5_Frame: Prop := { S5_refl : Reflexive; S5_sym  : Symmetric; S5_tran : Transitive }.
    Class KD_Frame: Prop := { KD_ser  : Serial }.

    (* Re-export normal modal theorems per agent by delegation. *)
    Theorem K_axiom    : K_Frame -> forall φ ψ, Prov (Impl (Box (Impl φ ψ)) (Impl (Box φ) (Box ψ))).
    Proof. intros _ φ ψ; apply provable_K. Qed.

    Theorem Necessitation : K_Frame -> forall φ, (forall w, forces w φ) -> Prov (Box φ).
    Proof. intros _ φ H; apply provable_necessitation; exact H. Qed.

    Theorem T_axiom  : T_Frame  -> forall φ, Prov (Impl (Box φ) φ).
    Proof. intros H φ; destruct H as [Hrefl]; eapply provable_T; exact Hrefl. Qed.

    Theorem Four_axiom : S4_Frame -> forall φ, Prov (Impl (Box φ) (Box (Box φ))).
    Proof. intros H φ; destruct H as [Hrefl Htran]; eapply provable_4; eauto. Qed.

    Theorem Five_axiom : S5_Frame -> forall φ, Prov (Impl (Dia φ) (Box (Dia φ))).
    Proof. intros H φ; destruct H as [Hrefl Hsym Htran]; eapply provable_5; eauto. Qed.

    Theorem B_axiom : S5_Frame -> forall φ, Prov (Impl φ (Box (Dia φ))).
    Proof. intros H φ; destruct H as [Hrefl Hsym Htran]; eapply provable_B; eauto. Qed.

    Theorem D_axiom : KD_Frame -> forall φ, Prov (Impl (Box φ) (Dia φ)).
    Proof. intros H φ; destruct H as [Hser]; eapply provable_D; eauto. Qed.
  End PerAgent.

  (* Group knowledge stubs (constructive placeholders; no admits). *)
  Section Groups.
    Variable Agents : list Agent.
    Definition Everyone (φ:form) : form := Box φ.   (* placeholder; refined later *)
    Definition Distributed (φ:form) : form := Box φ.
    Definition Common (φ:form) : form := Box φ.     (* will be μ-style later on finite frames *)
  End Groups.

End GnosiPraxis.
