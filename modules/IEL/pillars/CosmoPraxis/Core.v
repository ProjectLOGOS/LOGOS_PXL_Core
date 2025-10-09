From PXLs.IEL.Infra.TopoPraxis Require Import Core.
From PXLs.IEL.Pillars.CosmoPraxis.subdomains.Space Require Import Spec.
Module CosmoPraxis.
  Definition V := PXLs.IEL.Source.TheoPraxis.Props.Space.
  Theorem ChronoTopoInterface : forall p, V p -> V (Box p).
  Proof. apply SpaceSub.chrono_topo_interface. Qed.
End CosmoPraxis.
