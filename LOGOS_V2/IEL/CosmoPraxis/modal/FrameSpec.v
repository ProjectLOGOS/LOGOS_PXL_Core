From PXLs.Internal Emergent Logics.Pillars.CosmoPraxis Require Import Core.
From PXLs.Internal Emergent Logics.Infra.Adaptive Require Import ModalProbabilistic.

Module CosmoPraxis_Modal.

  Parameter Obligation : Prop -> Prop.
  Parameter Permission : Prop -> Prop.
  Parameter Prohibition : Prop -> Prop.

  (* Obligation_to_Respect_Causality: no RetroCausalOverride. *)
  Definition Obligation_to_Respect_Causality (S:Type) : Prop :=
    Obligation (forall (s:S) (y:SpacePoint) (t':TimeIndex),
                  ~ RetroCausalOverride s y t').

  (* Prohibition_on_InstantaneousNonlocalControl. *)
  Definition Prohibition_on_FTL_Control (S:Type) : Prop :=
    Prohibition (forall (s:S) (y:SpacePoint) (t':TimeIndex),
                   ~ InstantaneousNonlocalControl s y t').

  (* Permission_for_Predictive_Planning: forecasting future states is
     permitted if uncertainty is surfaced and TeleologyRespectsCausality. *)
  Definition Permission_for_Predictive_Planning (S:Type) : Prop :=
    Permission (forall (g:Goal) (w:World),
                  FeasibleInWorld g w \/ ImpossibleNow g).

End CosmoPraxis_Modal.
