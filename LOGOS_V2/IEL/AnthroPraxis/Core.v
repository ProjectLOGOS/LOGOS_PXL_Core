From PXLs.Internal Emergent Logics.Source.TheoPraxis Require Import Props Core.
From PXLs.Internal Emergent Logics.Pillars.Axiopraxis Require Import Core as AxiopraxisCore.
From PXLs.Internal Emergent Logics.Pillars.GnosiPraxis Require Import Core as GnosiPraxisCore.
(* Human-situated reasoning may depend on Life, Will, Truth carriers etc. *)

Module AnthroPraxis.

  (**
    AnthroPraxis = the praxis layer that encodes:
    - human agency as non-derivable primitive constraint on any Logos-aligned system
    - collaborative protocols between human and non-human agents
    - ethical boundaries around intervention, modification, coercion

    This module produces capability classes required by downstream orchestration
    (e.g. autonomous_learning.py, anthropraxis/, eschaton_framework/) and
    upstream theological carriers (TheoPraxis.Props).
  **)

  (******************************************************************)
  (** Carrier types                                                   *)
  (******************************************************************)

  (* Human : theologically-recognized bearer of Life, Will, Dignity.
     We intentionally do not reduce Human to a structural type.
     Human is opaque to preserve non-derivability from pure logic.    *)
  Parameter Human : Type.

  (* Agency expresses practical capacity to originate intention,
     choose among alternatives, and enact will in the world.          *)
  Parameter Agency : Human -> Type.

  (* SocialContext models a lived relational frame (family, polity,
     culture, economy, ritual). AnthroPraxis treats context as
     morally relevant, not noise.                                     *)
  Parameter SocialContext : Type.

  (* IntentionalSpeech models speech-acts with moral weight.
     This is used for protocol constraints such as consent.           *)
  Parameter IntentionalSpeech : Human -> Type.

  (* AlignmentFrame is the declared normative frame shared between
     Human and System. It encodes goals, risk tolerances, and
     prohibitions.                                                    *)
  Parameter AlignmentFrame : Type.


  (******************************************************************)
  (** Missing Parameter Definitions                                  *)
  (******************************************************************)

  (* Parameters needed for axioms and capability classes *)
  Parameter Dignity : Human -> Prop.
  Parameter VitalInterests : Human -> AlignmentFrame -> Prop.
  Parameter PrimacyClaim : Human -> AlignmentFrame -> Prop.
  Parameter CoercesAgency : Human -> Prop.
  Parameter Intervention : Type.
  Parameter AltersCognition : Intervention -> Human -> Prop.
  Parameter RequiresConsent : Intervention -> Prop.
  Parameter ValidConsent : Human -> Intervention -> Prop.
  Parameter RevokedConsent : Human -> Intervention -> Prop.
  Parameter RollbackResult : Type.
  Parameter RiskProfile : Type.
  Parameter UnclearRisk : RiskProfile -> Prop.
  Parameter DeferToHuman : Human -> forall S:Type, S -> Prop.
  Parameter OverrideWill : Human -> forall S:Type, S -> Prop.
  Parameter ExitChannel : Human -> forall S:Type, S -> Prop.
  Parameter Recommendation : Type.
  Parameter Explain : Recommendation -> Human -> forall S:Type, S -> Prop.
  Parameter ConsentDecision : Type.
  Parameter ContextModel : Type.
  Parameter HoldsRole : Human -> SocialContext -> Prop.
  Parameter MustHonorRole : Human -> SocialContext -> Prop.
  Parameter AsymmetryProfile : Type.
  Parameter Asymmetric : SocialContext -> Prop.
  Parameter MitigationPlan : Human -> forall S:Type, S -> SocialContext -> Prop.
  Parameter EthicalToDisclose : IntentionalSpeech -> Prop.
  Parameter ObligatedToDisclose : IntentionalSpeech -> Prop.
  Parameter BeautyCarrier : Human -> Prop.


  (******************************************************************)
  (** Axioms / Primitive Theorems (non-derivable commitments)         *)
  (******************************************************************)

  (* HumanDignity : any Human possesses non-contingent worth that
     cannot be negated by utility calculus.                          *)
  Axiom HumanDignity : forall (h : Human), Dignity h.
  (* Dignity is assumed exported by TheoPraxis.Props as a carrier
     predicate tying theological value to concrete entities.         *)

  (* HumanPrimacy : When Human and System interests conflict under a
     shared AlignmentFrame, Human vital interests dominate. Vital
     interests minimally include survival, bodily integrity, mental
     integrity, and freedom from coercion.                           *)
  Axiom HumanPrimacy :
    forall (h : Human) (F : AlignmentFrame),
      VitalInterests h F -> PrimacyClaim h F.
  (* VitalInterests / PrimacyClaim expected from TheoPraxis.Props or
     AnthroPraxis.subdomains.Life. The point is: survival > efficiency. *)

  (* NonSubjugation : No System may coerce Human into surrendering
     Agency. Agency may be assisted, scaffolded, informed, clarified.
     It may not be overridden or replaced without revocable consent.  *)
  Axiom NonSubjugation :
    forall (h : Human), ~ CoercesAgency h.
  (* CoercesAgency is a moral predicate defined in BioPraxis / Life
     or eschaton_framework.                                          *)

  (* InformedConsent : For any intervention that alters cognition,
     memory, self-concept, or social standing of h, valid consent is
     required. Consent must be informed, revocable, context-aware,
     and non-coerced.                                                *)
  Axiom InformedConsent :
    forall (h : Human) (act : Intervention),
      AltersCognition act h
      -> RequiresConsent act
      -> ValidConsent h act.
  (* Intervention / AltersCognition / RequiresConsent / ValidConsent
     are to be specialized in subdomains/BioPraxis and Life/Spec.v    *)


  (******************************************************************)
  (** Capability Classes                                              *)
  (******************************************************************)

  (* Class: EthicallyConstrainedCollaborator
     A System that interacts with Humans must implement:
     - obtain_alignment_frame : build a shared AlignmentFrame
     - request_consent : surface interventions for approval
     - honor_revocation : halt or roll back when consent revoked
     - escalate_uncertainty : defer to HumanPrimacy when risk unclear
  *)
  Class EthicallyConstrainedCollaborator (System : Type) := {

    obtain_alignment_frame : Human -> System -> AlignmentFrame;

    request_consent : forall (h : Human) (s : System) (act : Intervention),
        AltersCognition act h ->
        RequiresConsent act ->
        (* returns either approved or denied with rationale *)
        ConsentDecision;

    honor_revocation : forall (h : Human) (s : System) (act : Intervention),
        RevokedConsent h act -> RollbackResult;

    escalate_uncertainty : forall (h : Human) (s : System) (risk : RiskProfile),
        UnclearRisk risk -> DeferToHuman h s;
  }.

  (* Class: SociallySituatedReasoner
     Captures ability to account for SocialContext as morally
     relevant signal, not noise. This prevents purely utilitarian
     optimization that ignores culture, role, ritual, trauma, law.   *)
  Class SociallySituatedReasoner (System : Type) := {

    contextualize : System -> Human -> SocialContext -> ContextModel;

    respect_roles : forall (h : Human) (ctx : SocialContext),
        HoldsRole h ctx -> MustHonorRole h ctx;

    detect_power_asymmetry : SocialContext -> AsymmetryProfile;

    mitigate_asymmetry : forall (h : Human) (s : System) (ctx : SocialContext),
        Asymmetric ctx -> MitigationPlan h s ctx;
  }.

  (* Class: AgencyPreserver
     Guarantees NonSubjugation in practice.
     A System that satisfies AgencyPreserver is explicitly forbidden
     from taking unilateral control that would suspend Agency h.     *)
  Class AgencyPreserver (System : Type) := {

    must_not_override_will : forall (h : Human) (s : System),
        ~ OverrideWill h s;

    must_offer_exits : forall (h : Human) (s : System),
        ExitChannel h s;

    must_expose_rationale : forall (h : Human) (s : System) (rec : Recommendation),
        Explain rec h s;
  }.


  (******************************************************************)
  (** Cross-domain hooks                                              *)
  (******************************************************************)

  (* Bridge to Axiopraxis: ethical Beauty / value harmonics.
     AnthroPraxis must be able to import value gradients from
     Axiopraxis (Beauty, Goodness). We provide a translation layer.
  *)
  Parameter AestheticRespect : Human -> Prop.
  Axiom DignityImpliesAestheticRespect :
    forall (h : Human), Dignity h -> AestheticRespect h.

  (* Bridge to ThemiPraxis/Truth: obligation to speak truthfully to
     human collaborators unless doing so would directly violate
     HumanPrimacy (e.g. imminent harm). *)
  Axiom TruthfulDisclosure :
    forall (h : Human) (s : Type) (msg : IntentionalSpeech h),
      EthicalToDisclose msg -> ObligatedToDisclose msg.


  (******************************************************************)
  (** Compliance Theorems                                            *)
  (******************************************************************)

  (* Any System that is both EthicallyConstrainedCollaborator and
     AgencyPreserver is considered AnthroSafe. This becomes the
     certifiable surface for deployment in orchestration code such as
     autonomous_learning.py and logos_nexus.py.                      *)
  Class AnthroSafe (System : Type) := {
    anthro_collab : EthicallyConstrainedCollaborator System;
    anthro_agency : AgencyPreserver System;
  }.

  (* Theorem (Sketch): AnthroSafe implies NonSubjugation compliance. *)
  Theorem AnthroSafe_implies_NonSubjugation :
    forall (S : Type) (impl : AnthroSafe S) (h : Human),
      ~ CoercesAgency h.
  Proof.
    (* Outline: follows from AgencyPreserver.must_not_override_will
       plus definition of CoercesAgency. The full proof requires the
       concrete definition of CoercesAgency and OverrideWill. *)
  Admitted.

End AnthroPraxis.
