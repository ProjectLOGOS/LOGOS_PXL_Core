From PXLs.Internal Emergent Logics.Pillars.CosmoPraxis Require Import Core.
From PXLs.Internal Emergent Logics.Infra.Arithmo Require Import Topology.Topology MeasureTheory.Measure.

Module CosmoPraxis_SpaceSpec.

  (* Distance metric on SpacePoint. May be non-Euclidean. *)
  Parameter dist : SpacePoint -> SpacePoint -> R.
  Axiom dist_nonneg : forall x y, 0 <= dist x y.
  Axiom dist_sym    : forall x y, dist x y = dist y x.
  Axiom dist_id     : forall x y, dist x y = 0 -> x = y.
  Axiom dist_tri    : forall x y z, dist x z <= dist x y + dist y z.

  (* Neighborhood / open ball. *)
  Definition Ball (c:SpacePoint) (r:R) : Region := (* embed as Region *) admit.

  (* LightCone / CausalCone abstraction. *)
  Parameter LightCone : SpacePoint -> TimeIndex -> Region.
  Axiom CausalReachability_in_LightCone :
    forall x t y t',
      CausalReachability x t y t' -> InRegion y t' (LightCone x t).
  Parameter InRegion : SpacePoint -> TimeIndex -> Region -> Prop.

  (* Spatial locality bound. If y is outside LightCone at t',
     then no causal reachability. *)
  Axiom NoFTL : forall x t y t',
    ~ InRegion y t' (LightCone x t) -> ~ CausalReachability x t y t'.

End CosmoPraxis_SpaceSpec.
