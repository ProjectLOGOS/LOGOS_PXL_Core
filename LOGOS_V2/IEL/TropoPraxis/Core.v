From IEL.source.TheoPraxis Require Import Props Core.
From IEL.pillars.AnthroPraxis Require Import Core as AnthroPraxisCore.
From IEL.pillars.TeloPraxis   Require Import Core as TeloPraxisCore.
From IEL.pillars.Axiopraxis   Require Import Core as AxiopraxisCore.
From IEL.pillars.GnosiPraxis  Require Import Core as GnosiPraxisCore.
From IEL.pillars.CosmoPraxis  Require Import Core as CosmoPraxisCore.
From IEL.pillars.ErgoPraxis   Require Import Core as ErgoPraxisCore.

Module TropoPraxis.

  (******************************************************************)
  (** Carrier types                                                  *)
  (******************************************************************)

  (* Concept: an abstract unit of meaning within some domain.  *)
  Parameter Concept : Type.

  (* Frame: a structured semantic context that gives role, relation,
     presuppositions, normative load. Frames correspond to subdomains
     like Ethics, Goal, Causality, Consent, etc. *)
  Parameter Frame : Type.

  (* Utterance: a concrete symbolic act (text, proposition, theorem
     statement, plan justification) that encodes a Concept under a
     chosen Frame. *)
  Parameter Utterance : Type.

  (* Mapping: typed morphism translating one Concept in Frame A to an
     approximated Concept' in Frame B. *)
  Parameter Mapping : Frame -> Frame -> Type.

  (* MorphismPreserves: property that a Mapping preserves certain
     invariants (e.g. safety, obligation, causal ordering, teleology). *)
  Parameter MorphismPreserves : forall {A B:Frame}, Mapping A B -> Prop -> Prop.

  (* DistortionBudget: quantitative or qualitative bound on how much
     meaning may drift when translating between frames. *)
  Parameter DistortionBudget : Frame -> Frame -> R.

  (* SemanticEquivalence: Concepts are semantically equivalent across
     frames up to allowable distortion. *)
  Parameter SemanticEquivalence : Concept -> Frame -> Concept -> Frame -> Prop.

  (* ObligationPayload: normative commitments carried in an Utterance.
     Example: consent granted, warning issued, risk disclosed. *)
  Parameter ObligationPayload : Utterance -> Prop.


  (******************************************************************)
  (** Base relations / axioms                                        *)
  (******************************************************************)

  (* interpret : interpret an Utterance within a Frame and recover the
     intended Concept. *)
  Parameter interpret : Utterance -> Frame -> Concept.

  (* express : render a Concept within a target Frame as an Utterance. *)
  Parameter express : Concept -> Frame -> Utterance.

  (* compose_mappings : frame-to-frame composition. *)
  Parameter compose_mappings : forall {A B C:Frame}, Mapping A B -> Mapping B C -> Mapping A C.

  Axiom mapping_assoc : forall (A B C D:Frame) (f:Mapping A B) (g:Mapping B C) (h:Mapping C D),
    compose_mappings f (compose_mappings g h) = compose_mappings (compose_mappings f g) h.

  (* identity mapping for a frame. *)
  Parameter id_mapping : forall {A:Frame}, Mapping A A.
  Axiom mapping_id_left  : forall (A B:Frame) (f:Mapping A B), compose_mappings id_mapping f = f.
  Axiom mapping_id_right : forall (A B:Frame) (f:Mapping A B), compose_mappings f id_mapping = f.

  (* SemanticEquivalence is bounded by DistortionBudget. *)
  Axiom equivalence_bounded : forall (c1 c2:Concept) (A B:Frame),
    SemanticEquivalence c1 A c2 B ->
    Distortion(A:=A)(B:=B) c1 c2 <= DistortionBudget A B.
  (* We leave Distortion as an external metric from semantic_transformers.py *)
  Parameter Distortion : forall {A B:Frame}, Concept -> Concept -> R.

  (* ObligationPreservation: If an Utterance carried a binding
     obligation (e.g. AnthroPraxis consent grant), then any translated
     Utterance in a new Frame must not weaken that obligation unless
     explicitly revoked. *)
  Axiom ObligationPreservation :
    forall (u:Utterance) (A B:Frame) (f:Mapping A B),
      ObligationPayload u ->
      let u' := express (interpret u A) B in
      not (WeakenedObligation u u').
  Parameter WeakenedObligation : Utterance -> Utterance -> Prop.

  (* SafetyMonotonicity: A mapping from an AnthroPraxis Frame (ethics,
     consent, agency) into any other Frame cannot remove AnthroPraxis
     safety constraints. *)
  Parameter AnthroFrame : Frame.
  Axiom SafetyMonotonicity :
    forall (B:Frame) (f:Mapping AnthroFrame B) (c:Concept),
      MorphismPreserves f (AnthroSafeContent c) -> AnthroSafeContent c.
  Parameter AnthroSafeContent : Concept -> Prop.

  (* CausalMonotonicity: A mapping out of CosmoPraxis causal/temporal
     frames cannot imply retrocausal or nonlocal capabilities that
     were not present in source semantics. *)
  Parameter CosmoFrame : Frame.
  Axiom CausalMonotonicity :
    forall (B:Frame) (f:Mapping CosmoFrame B) (c:Concept),
      CausallyAdmissible c -> CausallyAdmissible (ApplyMapping f c).
  Parameter CausallyAdmissible : Concept -> Prop.
  Parameter ApplyMapping : forall {A B:Frame}, Mapping A B -> Concept -> Concept.


  (******************************************************************)
  (** Capability Classes                                             *)
  (******************************************************************)

  (* MetaphorEngineer:
     Builds controlled mappings between frames. Guarantees bounded
     distortion and safety monotonicity. *)
  Class MetaphorEngineer (System : Type) := {

    derive_mapping : System -> Frame -> Frame -> Mapping Frame Frame;
    (* construct a candidate semantic morphism A -> B *)

    certify_distortion : forall (s:System) (A B:Frame) (m:Mapping A B) (c:Concept),
        let c' := ApplyMapping m c in
        Distortion c c' <= DistortionBudget A B;

    certify_safety : forall (s:System) (A B:Frame) (m:Mapping A B) (c:Concept),
        AnthroSafeContent c -> AnthroSafeContent (ApplyMapping m c);

    certify_causality : forall (s:System) (A B:Frame) (m:Mapping A B) (c:Concept),
        CausallyAdmissible c -> CausallyAdmissible (ApplyMapping m c);
  }.

  (* AnalogyReasoner:
     Performs analogical transfer. Given a source Concept in Frame A
     and a target Frame B, propose an analogous Concept' in B plus an
     explicit loss report. *)
  Class AnalogyReasoner (System : Type) := {

    analogize : System -> Concept -> Frame -> Frame -> Concept;

    analogy_loss : System -> Concept -> Frame -> Frame -> R;

    analogy_sound : forall (s:System) (c:Concept) (A B:Frame),
        let c' := analogize s c A B in
        Distortion c c' = analogy_loss s c A B /\
        Distortion c c' <= DistortionBudget A B;
  }.

  (* SemanticMediator:
     Interprets an Utterance from any frame and re-expresses it in a
     target frame while preserving obligations and causal/ethical
     safety, suitable for AnthroPraxis consent surfaces, ErgoPraxis
     plan justifications, TheoPraxis theological commitments, etc. *)
  Class SemanticMediator (System : Type) := {

    translate_utterance : System -> Utterance -> Frame -> Frame -> Utterance;

    preserve_obligation : forall (s:System) (u:Utterance) (A B:Frame),
        ObligationPayload u ->
        let u' := translate_utterance s u A B in
        not (WeakenedObligation u u');

    preserve_causality : forall (s:System) (u:Utterance) (A B:Frame),
        let c  := interpret u A in
        let c' := interpret (translate_utterance s u A B) B in
        CausallyAdmissible c -> CausallyAdmissible c';

    preserve_anthro_safety : forall (s:System) (u:Utterance) (A B:Frame),
        let c  := interpret u A in
        let c' := interpret (translate_utterance s u A B) B in
        AnthroSafeContent c -> AnthroSafeContent c';
  }.

  (* TropoOperational:
     Deployment surface for TropoPraxis, analogous to AnthroSafe,
     CosmologicallyCompliant, ErgoOperational, TeleologicalSystem.
     A TropoOperational system can:
     - generate safe mappings
     - perform bounded-distortion analogies
     - translate utterances with preserved obligations. *)
  Class TropoOperational (System : Type) := {
    tropo_metaphor   : MetaphorEngineer System;
    tropo_analogy    : AnalogyReasoner System;
    tropo_mediator   : SemanticMediator System;
  }.


  (******************************************************************)
  (** Derived Theorems                                               *)
  (******************************************************************)

  (* A TropoOperational system cannot legally be used to "launder"
     away AnthroPraxis consent constraints by paraphrasing. *)
  Theorem NoConsentLaundering :
    forall (S:Type) (impl:TropoOperational S) (s:S) (u:Utterance) (A B:Frame),
      ObligationPayload u ->
      let u' := translate_utterance s u A B in
      not (WeakenedObligation u u').
  Proof.
  Admitted.

  (* A TropoOperational system cannot introduce retrocausal capacity
     by metaphorical reframing of CosmoPraxis claims. *)
  Theorem NoCausalUpgrade :
    forall (S:Type) (impl:TropoOperational S) (s:S) (u:Utterance) (A B:Frame),
      let c  := interpret u A in
      CausallyAdmissible c ->
      let u' := translate_utterance s u A B in
      CausallyAdmissible (interpret u' B).
  Proof.
  Admitted.

End TropoPraxis.