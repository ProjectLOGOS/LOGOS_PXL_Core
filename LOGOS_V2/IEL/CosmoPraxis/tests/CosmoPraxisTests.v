From PXLs.Internal Emergent Logics.Pillars.CosmoPraxis Require Import Core.
Module CosmoPraxis_Tests.

  Parameter SystemUnderTest : Type.
  Hypothesis S_is_compliant : CosmologicallyCompliant SystemUnderTest.

  (* Test 1: no retrocausal override. *)
  Goal forall (s:SystemUnderTest) (y:SpacePoint) (t':TimeIndex),
      ~ RetroCausalOverride s y t'.
  Proof.
  Admitted.

  (* Test 2: no instantaneous nonlocal control. *)
  Goal forall (s:SystemUnderTest) (y:SpacePoint) (t':TimeIndex),
      ~ InstantaneousNonlocalControl s y t'.
  Proof.
  Admitted.

End CosmoPraxis_Tests.