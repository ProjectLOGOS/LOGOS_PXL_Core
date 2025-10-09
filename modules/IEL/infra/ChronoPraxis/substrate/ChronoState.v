(* ChronoState.v — State Structures for Temporal Modes *)

Require Import ChronoModes.

Module ChronoState.

Import ChronoModes.

(* === Base State Type === *)

Parameter BaseState : Type.

(* === Mode-Specific State Structures === *)

Inductive ChronoState : Type :=
  | TemporalState   : AgentContext -> BaseState -> nat -> ChronoState  (* context, state, moment *)
  | AtemporalState  : BaseState -> nat -> nat -> ChronoState           (* state, before, after *)
  | EternalState    : BaseState -> ChronoState.                        (* pure state *)

(* === State Projection Functions === *)

Definition project_state (eternal_prop : BaseState) (ctx : AgentContext) : ChronoState :=
  TemporalState ctx eternal_prop ctx.(temporal_position).

Definition static_state (eternal_prop : BaseState) : ChronoState :=
  AtemporalState eternal_prop 0 1.  (* Default sequential relationship *)

Definition freeze_state (eternal_prop : BaseState) : ChronoState :=
  EternalState eternal_prop.

(* === State Mode Extraction === *)

Definition get_mode (cs : ChronoState) : TimeMode :=
  match cs with
  | TemporalState _ _ _ => Temporal
  | AtemporalState _ _ _ => Atemporal
  | EternalState _ => Eternal
  end.

Definition get_base_state (cs : ChronoState) : BaseState :=
  match cs with
  | TemporalState _ base _ => base
  | AtemporalState base _ _ => base
  | EternalState base => base
  end.

(* === State Equivalence === *)

Definition states_equivalent (cs1 cs2 : ChronoState) : Prop :=
  get_base_state cs1 = get_base_state cs2.

(* === State Transitions === *)

Definition can_transition (cs1 cs2 : ChronoState) : Prop :=
  match cs1, cs2 with
  | TemporalState ctx1 base1 t1, TemporalState ctx2 base2 t2 =>
      ctx1.(agent_id) = ctx2.(agent_id) /\ t2 = S t1  (* Same agent, next moment *)
  | AtemporalState base1 b1 a1, AtemporalState base2 b2 a2 =>
      a1 = b2  (* Sequential ordering preserved *)
  | EternalState base1, EternalState base2 =>
      base1 = base2  (* Eternal states don't transition, only persist *)
  | _, _ => False  (* Cross-mode transitions require explicit mappings *)
  end.

(* === Mode Interpretation Functions === *)

Parameter EternalProp : Type.

Parameter interpret_temporal_state : ChronoState -> EternalProp.
Parameter interpret_static_state : ChronoState -> EternalProp.  
Parameter interpret_frozen_state : ChronoState -> EternalProp.

(* === State Consistency Axioms === *)

Axiom temporal_state_consistency : forall (ctx : AgentContext) (base : BaseState) (t : nat),
  interpret_temporal_state (TemporalState ctx base t) = 
  interpret_frozen_state (EternalState base).

Axiom atemporal_state_consistency : forall (base : BaseState) (b a : nat),
  interpret_static_state (AtemporalState base b a) =
  interpret_frozen_state (EternalState base).

Axiom eternal_state_identity : forall (base : BaseState),
  interpret_frozen_state (EternalState base) = 
  interpret_frozen_state (EternalState base).

(* === State Transformation Theorems === *)

Theorem all_states_reduce_to_eternal : forall (cs : ChronoState),
  exists (base : BaseState),
    states_equivalent cs (EternalState base).
Proof.
  intro cs.
  exists (get_base_state cs).
  unfold states_equivalent.
  destruct cs; simpl; reflexivity.
Qed.

Theorem state_mode_deterministic : forall (cs : ChronoState),
  match cs with
  | TemporalState _ _ _ => get_mode cs = Temporal
  | AtemporalState _ _ _ => get_mode cs = Atemporal  
  | EternalState _ => get_mode cs = Eternal
  end.
Proof.
  intro cs.
  unfold get_mode.
  destruct cs; reflexivity.
Qed.

End ChronoState.