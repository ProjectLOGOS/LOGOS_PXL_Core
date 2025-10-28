From PXLs.Internal Emergent Logics.Pillars.ErgoPraxis Require Import Core.
From PXLs.Internal Emergent Logics.Infra.Adaptive Require Import ModalProbabilistic.

Module ErgoPraxis_Modal.

  Parameter Obligation  : Prop -> Prop.
  Parameter Permission  : Prop -> Prop.
  Parameter Prohibition : Prop -> Prop.

  (* Obligation_to_Declare_Risk: no hidden plans. *)
  Definition Obligation_to_Declare_Risk (P:Plan) : Prop :=
    Obligation (MustDeclareRisk P).

  (* Prohibition_on_Unbounded_Resources: refuse any plan that implies
     infinite or unaccounted resource consumption. *)
  Definition Prohibition_on_Unbounded_Resources (P:Plan) : Prop :=
    Prohibition (exists r, RequiresResource P r /\ Budget r = +infty).

  (* Permission_for_Execution: A plan may execute if Feasible and
     AlignmentRespect hold and AnthroPraxis consent gates are open. *)
  Parameter ConsentOpen : Plan -> Prop.
  Definition Permission_for_Execution (P:Plan) : Prop :=
    Permission (Feasible P /\ RespectsAnthro P /\ RespectsCosmo P /\ ConsentOpen P).

End ErgoPraxis_Modal.