(* ChronoModes.v - Temporal Mode Definitions *)

Module ChronoModes.

(* Base types for temporal reasoning *)
Parameter Agent : Type.
Parameter Context : Type.

(* Time as natural numbers for temporal positions *)
Definition Time := nat.

(* Temporal modes *)
Inductive TimeMode :=
  | Temporal : TimeMode
  | Atemporal : TimeMode
  | Eternal : TimeMode.

(* Agent context with temporal position *)
Record AgentContext := {
  agent : Agent;
  agent_id : Agent;  (* For identity comparisons *)
  temporal_position : Time;
  context : Context
}.

(* Accessor functions for record fields *)
Definition get_agent_id (ctx : AgentContext) : Agent := ctx.(agent_id).
Definition get_temporal_position (ctx : AgentContext) : Time := ctx.(temporal_position).

End ChronoModes.
