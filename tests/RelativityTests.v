From Coq Require Import Program.

(* TODO: Restore full imports once module path resolution is fixed *)
(* Require Import PXLs.IEL.Infra.substrate.ChronoAxioms *)
(*                PXLs.IEL.Infra.substrate.ChronoMappings *)
(*                PXLs.IEL.Infra.domains.Empiricism.UnifiedFieldLogic *)
(*                PXLs.IEL.Infra.domains.Empiricism.Relativity. *)

Require Import PXLs.IEL.Infra.ChronoPraxis.domains.Empiricism.Relativity.

Module RelTests.
  (* Minimal model: take Inv = B_to_C (projection-only model). *)
  Definition M0 : Relativity.MetricB := {| Relativity.Inv := B_to_C |}.

  Instance M0_pc : Relativity.ProjectionCompatible M0.
  Proof. intros pB; reflexivity. Qed.

  (* Use identity transform as minimal lorentz for testing *)
  Definition lor_fwd (p:PB) := p.
  Definition lor_bwd (p:PB) := p.

  Lemma lor_fg : forall x, lor_bwd (lor_fwd x) = x. 
  Proof. intro; unfold lor_bwd, lor_fwd; reflexivity. Qed.
  
  Lemma lor_gf : forall y, lor_fwd (lor_bwd y) = y. 
  Proof. intro; unfold lor_fwd, lor_bwd; reflexivity. Qed.
  
  Lemma lor_pres : forall pB, Relativity.Inv M0 (lor_fwd pB) = Relativity.Inv M0 pB.
  Proof. intro; unfold lor_fwd; cbn; reflexivity. Qed.

  (* Test the core isometry theorem directly *)
  Lemma isometry_preserves_projection :
    forall (M:Relativity.MetricB) (Hpc:Relativity.ProjectionCompatible M) (T:Relativity.Isometry M) (pB:PB),
      B_to_C (Relativity.forward (Relativity.iso T) pB) = B_to_C pB.
  Proof.
    intros. apply Relativity.frame_independence_isometry; assumption.
  Qed.

  (* Show that the identity transform is indeed an isometry for any metric *)
  Definition identity_isometry (M:Relativity.MetricB) : Relativity.Isometry M.
  Proof.
    refine {| Relativity.iso := {| Relativity.forward := fun x => x; 
                                   Relativity.backward := fun x => x; 
                                   Relativity.fb := fun x => eq_refl; 
                                   Relativity.bf := fun x => eq_refl |} |}.
    intro pB; reflexivity.
  Defined.

End RelTests.
