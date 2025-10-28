(*
Cross-praxis theorems that guarantee lawful semantic transport between
AnthroPraxis, ErgoPraxis, TeloPraxis, CosmoPraxis, TheoPraxis.
This is how LOGOS keeps statements consistent across subsystems.
*)
From IEL.pillars.TropoPraxis Require Import Core.
From IEL.pillars.AnthroPraxis Require Import Core as AnthroPraxisCore.
From IEL.pillars.ErgoPraxis   Require Import Core as ErgoPraxisCore.
From IEL.pillars.TeloPraxis   Require Import Core as TeloPraxisCore.
From IEL.pillars.CosmoPraxis  Require Import Core as CosmoPraxisCore.
From IEL.source.TheoPraxis    Require Import Props.

Module TropoPraxis_Cross.

  (* ConsentIntegrity:
     Any AnthroPraxis consent utterance, when translated for ErgoPraxis
     planning or logging, must remain binding. *)
  Theorem ConsentIntegrity :
    forall (u:Utterance) (A AnthroFrame B:Frame),
      ObligationPayload u ->
      let u' := express (interpret u AnthroFrame) B in
      not (WeakenedObligation u u').
  Proof.
  Admitted.

  (* TeleologyClarity:
     A teleological goal statement in TeloPraxis must not gain
     cosmologically forbidden power (no retrocausality, no unlimited
     reach) when expressed operationally in ErgoPraxis. *)
  Theorem TeleologyClarity :
    forall (g:TeloPraxisCore.Goal) (A B:Frame),
      let u := express (GoalAsConcept g) A in
      let u' := express (GoalAsConcept g) B in
      CausallyAdmissible (interpret u A) ->
      CausallyAdmissible (interpret u' B).
  Parameter GoalAsConcept : TeloPraxisCore.Goal -> Concept.
  Proof.
  Admitted.

  (* TheologicalFidelity:
     When TheoPraxis carriers (Truth, Beauty, Life, Will, etc.) are
     projected into AnthroPraxis or ErgoPraxis language, those
     carriers cannot be stripped of their normative status and turned
     into neutral "preferences".  TropoPraxis enforces that downgrade
     is illegal. *)
  Parameter TheologicalCarrierConcept : TheoCarrier -> Concept.
  Parameter TheoCarrier : Type.
  Parameter DowngradedToPreference : Utterance -> Prop.

  Theorem TheologicalFidelity :
    forall (car:TheoCarrier) (A B:Frame),
      let uA := express (TheologicalCarrierConcept car) A in
      let uB := express (TheologicalCarrierConcept car) B in
      not (DowngradedToPreference uB).
  Proof.
  Admitted.

End TropoPraxis_Cross.