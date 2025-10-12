From PXLs.Internal Emergent Logics.Infra.TopoPraxis Require Import Core.
From PXLs.Internal Emergent Logics.Pillars.CosmoPraxis.subdomains.Space Require Import Spec.
Module CosmoPraxis.
  Definition V := PXLs.Internal Emergent Logics.Source.TheoPraxis.Props.Space.
  Theorem ChronoTopoInterface : forall p, V p -> V (Box p).
  Proof. apply SpaceSub.chrono_topo_interface. Qed.
End CosmoPraxis.
