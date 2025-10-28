From PXLs.Internal Emergent Logics.Pillars.ErgoPraxis Require Import Core.

Module ErgoPraxis_TruthSpec.

  Parameter ConstraintSet : Type.
  Parameter SatisfiedConstraints : Outcome -> ConstraintSet -> Prop.

  (* ActionSuccess: an outcome met the key acceptance criteria. *)
  Parameter ActionSuccess : Outcome -> Goal -> Prop.

  (* PragmaticTruth is true if:
     - Acceptance criteria satisfied for Goal g
     - Constraints respected (including Anthro/Cosmo safety)
     - Resource budgets not violated
  *)
  Definition PragmaticTruthHolds (o:Outcome) (g:Goal) (C:ConstraintSet) : Prop :=
    ActionSuccess o g
    /\ SatisfiedConstraints o C
    /\ (forall r, ResourceWithinBudget o r).

  Parameter ResourceWithinBudget : Outcome -> Resource -> Prop.

End ErgoPraxis_TruthSpec.