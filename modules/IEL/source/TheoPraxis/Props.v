From PXLs.Core Require Import PXL_Kernel.
Module TheoProps.
  Parameter Truth Beauty Peace Freedom Glory Wrath Jealousy Will Necessity Possibility Space Time Life : Prop -> Prop.

  (* Capabilities as typeclasses for proof reuse *)
  Class Cap_ValueMonotone (P: (Prop->Prop)) := cap_vm : forall p q, (p -> q) -> P p -> P q.
  Class Cap_ConjElim     (P: (Prop->Prop)) := cap_ce : forall p q, P (p /\ q) -> P p /\ P q.
  Class Cap_NonExplosion (P: (Prop->Prop)) := cap_ne : ~ P False.
  Class Cap_K_sound      (P: (Prop->Prop)) := cap_ks : forall p, P p -> Box P p.  (* Assuming Box is box *)
  Class Cap_Monotone     (P: (Prop->Prop)) := cap_mon : forall p q, (p -> q) -> Box P p -> Box P q.
  Class Cap_ClosureUnderMP (P: (Prop->Prop)) := cap_mp : forall p q, Box (P p -> P q) -> Box P p -> Box P q.
  Class Cap_SeqComp      (P: (Prop->Prop)) := cap_sc : forall p q r, P (p -> q) -> P (q -> r) -> P (p -> r).
  Class Cap_HoareTriples (P: (Prop->Prop)) := cap_ht : forall p q, P p -> P (p -> q) -> P q.
  Class Cap_EndMonotone  (P: (Prop->Prop)) := cap_em : forall p q, (p -> q) -> P p -> P q.  (* Similar to ValueMonotone *)
  Class Cap_VolitionalLift (P: (Prop->Prop)) := cap_vl : forall p, P p -> Box P p.  (* Lifting to necessity *)
  Class Cap_AgentCapability (P: (Prop->Prop)) := cap_ac : forall p, P p -> Dia P p.  (* Possibility *)
  Class Cap_AgencyComp   (P: (Prop->Prop)) := cap_ag : forall p q, P p -> P q -> P (p /\ q).
  Class Cap_NecPossLaws  (P: (Prop->Prop)) := cap_np : forall p, Box P p <-> ~ Dia (~ P p).
  Class Cap_ChronoTopoInterface (P: (Prop->Prop)) := cap_cti : forall p, P p -> P (Box p).  (* Interface assumption *)
  Class Cap_DeonticDetachmentSafe (P: (Prop->Prop)) := cap_dds : forall p, Box P p -> P p.  (* Detachment *)
End TheoProps.