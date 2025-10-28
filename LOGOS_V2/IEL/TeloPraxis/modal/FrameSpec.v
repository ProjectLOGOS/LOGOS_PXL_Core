(*
Modal frame for Teleological Praxis.
Defines modalities of purpose: obligation, permission, prohibition.
Integrates with adaptive modal logic in infra/adaptive/ModalProbabilistic.v
*)
From infra.adaptive Require Import ModalProbabilistic.
From IEL.pillars.TeloPraxis Require Import Core.

Module TeloPraxis_Modal.

  Parameter Obligation  : Prop -> Prop.
  Parameter Permission  : Prop -> Prop.
  Parameter Prohibition : Prop -> Prop.

  (* Obligation_to_Pursue_Consistent_Goals: only pursue goals that are
     both valid and coherent. *)
  Definition Obligation_to_Pursue_Consistent_Goals (g:Goal) : Prop :=
    Obligation (Valid g /\ ConsistentWithTheo g /\ ConsistentWithCosmo g).

  (* Prohibition_on_Contradictory_Goals: forbids goals that would
     negate parent Will. *)
  Definition Prohibition_on_Contradictory_Goals (g:Goal) : Prop :=
    Prohibition (exists w, OriginatesFrom g w /\ ContradictsWillPurpose g w).
  Parameter ContradictsWillPurpose : Goal -> Will -> Prop.

  (* Permission_for_Goal_Decomposition: allows derivation of subgoals
     when hierarchy integrity holds. *)
  Definition Permission_for_Goal_Decomposition (g:Goal) : Prop :=
    Permission (exists subs, DecomposesTo g subs /\ Forall (fun sg => DerivedFrom sg g) subs).

End TeloPraxis_Modal.