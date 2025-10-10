
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type nat =
| O
| S of nat

module V4_Action_Adapter =
 struct
  (** val v4_hoare_sound : __ **)

  let v4_hoare_sound =
    __
 end

module Axiopraxis_Placeholder =
 struct
  type value = nat

  (** val neutral : value **)

  let neutral =
    O
 end

module V4_Knowledge_Adapter =
 struct
  type v4_knowledge_to_gnosi = __

  (** val v4_knows_sound : __ **)

  let v4_knows_sound =
    __
 end

module Coq_V4_Action_Adapter =
 struct
  type v4_action_to_hoare = __
 end

module V4_Value_Adapter =
 struct
  type coq_V4_Value (* AXIOM TO BE REALIZED *)

  (** val v4_value_to_axio : coq_V4_Value -> Axiopraxis_Placeholder.value **)

  let v4_value_to_axio _ =
    Axiopraxis_Placeholder.neutral

  (** val v4_value_mono : __ **)

  let v4_value_mono =
    __
 end

module V4_Conservativity =
 struct
  (** val runtime_v4_safe : __ **)

  let runtime_v4_safe =
    __
 end
