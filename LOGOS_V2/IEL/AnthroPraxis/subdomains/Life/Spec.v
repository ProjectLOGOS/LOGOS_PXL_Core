From PXLs.Internal Emergent Logics.Source.TheoPraxis Require Import Props.
Module AnthroPraxis_LifeSpec.

  Parameter Survival : AnthroPraxis.Human -> Prop.
  Parameter BodilyIntegrity : AnthroPraxis.Human -> Prop.
  Parameter MentalIntegrity : AnthroPraxis.Human -> Prop.
  Parameter ContinuityOfSelf : AnthroPraxis.Human -> Prop.

  (* VitalInterests used in Core.v *)
  Definition VitalInterests (h : AnthroPraxis.Human) (F : AnthroPraxis.AlignmentFrame) : Prop :=
    Survival h /\ BodilyIntegrity h /\ MentalIntegrity h /\ ContinuityOfSelf h.

End AnthroPraxis_LifeSpec.
