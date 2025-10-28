(*
Defines semantic frames, symbol grounding, and allowable transforms.
Ties into adaptive modal probability structures in ModalProbabilistic.v
and type-theoretic bases in /infra/arithmo/TypeTheory/Types.v
*)
From IEL.pillars.TropoPraxis Require Import Core.
From infra.arithmo.TypeTheory Require Import Types.
From infra.adaptive Require Import ModalProbabilistic.

Module TropoPraxis_SemanticsSpec.

  (* Symbol: concrete lexical / structural token. *)
  Parameter Symbol : Type.

  (* Lexicon: mapping from Symbols into Concepts, restricted by Frame. *)
  Parameter Lexicon : Frame -> Symbol -> Concept.

  (* Register a Symbol in a Frame with explicit normative load. *)
  Parameter NormativeTag : Symbol -> Prop.

  (* Some symbols carry embedded obligation ("I consent", "halt",
     "unsafe"). We must not erase that in translation. *)
  Parameter CarriesBindingForce : Symbol -> Prop.

  (* FrameCompatibility: whether semantic import from Frame A to Frame B
     is even meaningful. Some cross-frame projections are undefined. *)
  Parameter FrameCompatible : Frame -> Frame -> Prop.

  (* ModalConfidence: probabilistic confidence that a particular
     Concept in Frame A maps to target Concept in Frame B without
     violating Anthro/Cosmo/Telo constraints. *)
  Parameter ModalConfidence : Frame -> Frame -> Concept -> R.

  (* Guarantee: if FrameCompatible A B and ModalConfidence high,
     we may form Mapping A B. Otherwise translation should be refused. *)
  Axiom SafeToMapCondition :
    forall (A B:Frame) (c:Concept),
      FrameCompatible A B ->
      ModalConfidence A B c >= ConfidenceThreshold ->
      exists m:Mapping A B, Distortion c (ApplyMapping m c) <= DistortionBudget A B.

  Parameter ConfidenceThreshold : R.

End TropoPraxis_SemanticsSpec.