(*
Defines Will and volition subdomain: source of purpose and agency.
Links theological carrier Will to coherent intentional structures.
*)
From IEL.pillars.TeloPraxis Require Import Core.

Module TeloPraxis_WillSpec.

  (* Volition: concrete act of Will focusing on one or more Goals. *)
  Parameter Volition : Type.

  (* IntentionFormation: maps Will to Intention. *)
  Parameter IntentionFormation : Will -> TeloPraxis.Intention.

  (* Consistency axiom: no Will generates contradictory intentions. *)
  Axiom ConsistentVolition : forall (w:Will),
    not (exists i1 i2, ContradictoryIntentions i1 i2 w).
  Parameter ContradictoryIntentions : TeloPraxis.Intention -> TeloPraxis.Intention -> Will -> Prop.

  (* WillHierarchy: wills can exist in a ranked structure, divine to derived. *)
  Parameter HigherWill : Will -> Will -> Prop.
  Axiom WillTransitivity : forall w1 w2 w3, HigherWill w1 w2 -> HigherWill w2 w3 -> HigherWill w1 w3.

End TeloPraxis_WillSpec.