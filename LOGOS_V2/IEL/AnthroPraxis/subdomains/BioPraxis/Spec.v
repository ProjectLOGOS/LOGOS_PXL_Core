From PXLs.Internal Emergent Logics.Source.TheoPraxis Require Import Props.
Module AnthroPraxis_BioPraxisSpec.

  Parameter Intervention : Type.
  Parameter AltersCognition : Intervention -> AnthroPraxis.Human -> Prop.
  Parameter RequiresConsent : Intervention -> Prop.
  Parameter ValidConsent : AnthroPraxis.Human -> Intervention -> Prop.
  Parameter RevokedConsent : AnthroPraxis.Human -> Intervention -> Prop.
  Parameter RollbackResult : Type.

  Parameter RiskProfile : Type.
  Parameter UnclearRisk : RiskProfile -> Prop.
  Parameter DeferToHuman : AnthroPraxis.Human -> forall S:Type, S -> Prop.

  Parameter CoercesAgency : AnthroPraxis.Human -> Prop.
  Parameter OverrideWill : AnthroPraxis.Human -> forall S:Type, S -> Prop.
  Parameter ExitChannel : AnthroPraxis.Human -> forall S:Type, S -> Prop.
  Parameter Recommendation : Type.
  Parameter Explain : Recommendation -> AnthroPraxis.Human -> forall S:Type, S -> Prop.

  Parameter ConsentDecision : Type.

End AnthroPraxis_BioPraxisSpec.
