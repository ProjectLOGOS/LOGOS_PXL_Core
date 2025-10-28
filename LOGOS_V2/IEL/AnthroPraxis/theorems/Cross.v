From PXLs.Internal Emergent Logics.Pillars.AnthroPraxis Require Import Core.
From PXLs.Internal Emergent Logics.Pillars.Axiopraxis Require Import Core as AxiopraxisCore.
From PXLs.Internal Emergent Logics.Pillars.ThemiPraxis.subdomains.Truth Require Import Spec as TruthSpec.

Module AnthroPraxis_Cross.

  (* Beauty implies Respect. Respect implies NonSubjugation duties. *)
  Theorem Beauty_implies_Respect_implies_NonSubjugation :
    forall (h : AnthroPraxis.Human),
      BeautyCarrier h -> AestheticRespect h -> ~ CoercesAgency h.
  Proof.
    (* Sketch: requires BeautyCarrier from Axiopraxis, AestheticRespect
       from AnthroPraxis.Core, and NonSubjugation axiom. *)
  Admitted.

  (* Truth-telling as default interaction primitive. *)
  Theorem TruthBias :
    forall (h : AnthroPraxis.Human) (msg : IntentionalSpeech h),
      TruthSpec.Truthful msg -> EthicalToDisclose msg.
  Proof.
  Admitted.

End AnthroPraxis_Cross.