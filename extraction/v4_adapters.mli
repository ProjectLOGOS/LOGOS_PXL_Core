
type __ = Obj.t

type nat =
| O
| S of nat

module V4_Action_Adapter :
 sig
  val v4_hoare_sound : __
 end

module Axiopraxis_Placeholder :
 sig
  type value = nat

  val neutral : value
 end

module V4_Knowledge_Adapter :
 sig
  type v4_knowledge_to_gnosi = __

  val v4_knows_sound : __
 end

module Coq_V4_Action_Adapter :
 sig
  type v4_action_to_hoare = __
 end

module V4_Value_Adapter :
 sig
  type coq_V4_Value (* AXIOM TO BE REALIZED *)

  val v4_value_to_axio : coq_V4_Value -> Axiopraxis_Placeholder.value

  val v4_value_mono : __
 end

module V4_Conservativity :
 sig
  val runtime_v4_safe : __
 end
