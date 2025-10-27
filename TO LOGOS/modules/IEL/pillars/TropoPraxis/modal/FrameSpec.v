(*
Modal layer for TropoPraxis.
Defines obligation, permission, and prohibition over semantic
transformations themselves.
This is enforceable in runtime translation layers.
*)
From IEL.pillars.TropoPraxis Require Import Core.
From infra.adaptive Require Import ModalProbabilistic.

Module TropoPraxis_Modal.

  Parameter Obligation  : Prop -> Prop.
  Parameter Permission  : Prop -> Prop.
  Parameter Prohibition : Prop -> Prop.

  (* Obligation_to_Preserve_Obligation: you must not weaken binding
     obligations during translation. *)
  Definition Obligation_to_Preserve_Obligation (u:Utterance) : Prop :=
    Obligation (ObligationPayload u -> forall A B f,
                  not (WeakenedObligation u (express (interpret u A) B))).

  (* Prohibition_on_Causal_Upgrade: you may not map cosmologically
     permitted statements into causally impossible claims. *)
  Definition Prohibition_on_Causal_Upgrade (u:Utterance) : Prop :=
    Prohibition (forall A B,
       let c  := interpret u A in
       CausallyAdmissible c ->
       CausallyAdmissible (interpret (express (interpret u A) B) B)).

  (* Permission_for_Analogical_Projection: translation across frames
     is allowed if Distortion is under budget and safety/teleology are
     preserved. *)
  Definition Permission_for_Analogical_Projection (A B:Frame) (c:Concept) : Prop :=
    Permission (exists m:Mapping A B,
                  Distortion c (ApplyMapping m c) <= DistortionBudget A B
                  /\ AnthroSafeContent (ApplyMapping m c)
                  /\ CausallyAdmissible (ApplyMapping m c)).

End TropoPraxis_Modal.