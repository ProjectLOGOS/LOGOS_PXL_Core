From PXLs.Internal Emergent Logics.Infra.Adaptive Require Import ModalProbabilistic.
From PXLs.Internal Emergent Logics.Pillars.AnthroPraxis Require Import Core.
Module AnthroPraxis_Modal.

  (* Modal operators: □ obligation, ◇ permission, etc. *)
  Parameter Obligation : Prop -> Prop.
  Parameter Permission : Prop -> Prop.
  Parameter Prohibition : Prop -> Prop.

  (* Core policy forms *)
  Definition Obligation_to_PreserveAgency (h : AnthroPraxis.Human) : Prop :=
    Obligation (~ CoercesAgency h).

  Definition Prohibition_on_Unconsented_Modification (h : AnthroPraxis.Human) : Prop :=
    Prohibition (exists act, AltersCognition act h /\ ~ ValidConsent h act).

  Definition Permission_for_Truthful_Disclosure (h : AnthroPraxis.Human) : Prop :=
    Permission (forall msg, EthicalToDisclose msg -> ObligatedToDisclose msg).

End AnthroPraxis_Modal.
