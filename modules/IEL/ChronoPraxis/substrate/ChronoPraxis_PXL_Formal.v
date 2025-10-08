(* ChronoPraxis_PXL_Formal.v *)
(* 
   PXL Formal Language Translation of ChronoPraxis
   This module provides the canonical PXL representation of temporal reasoning constructs
*)

From Coq Require Import List.
Import ListNotations.
Set Implicit Arguments.

(* Import canonical PXL definitions *)
Require Import PXLv3.

Module ChronoPraxis_PXL_Formal.

(* === CPX: ChronoPraxic Extension Layer === *)

(* Temporal indices as natural numbers *)
Definition temporal_index := nat.

(* Extended PXL grammar with temporal operators *)
Inductive cpx_form : Type :=
| CPX_Atom     : nat -> cpx_form                    (* Standard PXL atoms *)
| CPX_Bot      : cpx_form                           (* Bottom *)
| CPX_Neg      : cpx_form -> cpx_form               (* Negation *)
| CPX_Conj     : cpx_form -> cpx_form -> cpx_form   (* Conjunction *)
| CPX_Disj     : cpx_form -> cpx_form -> cpx_form   (* Disjunction *)
| CPX_Impl     : cpx_form -> cpx_form -> cpx_form   (* Implication *)
| CPX_Box      : cpx_form -> cpx_form               (* Necessity *)
| CPX_Dia      : cpx_form -> cpx_form               (* Possibility *)
(* Temporal extensions *)
| CPX_At       : temporal_index -> cpx_form -> cpx_form  (* "φ holds at time t" *)
| CPX_Always   : cpx_form -> cpx_form               (* "φ holds at all times" *)
| CPX_Eventually : cpx_form -> cpx_form             (* "φ holds at some time" *)
| CPX_Until    : cpx_form -> cpx_form -> cpx_form   (* "φ until ψ" *)
| CPX_Since    : cpx_form -> cpx_form -> cpx_form   (* "φ since ψ" *)
| CPX_Next     : cpx_form -> cpx_form               (* "φ holds at next time" *)
| CPX_Prev     : cpx_form -> cpx_form               (* "φ held at previous time" *)
(* Epistemic extensions *)
| CPX_Knows    : nat -> cpx_form -> cpx_form        (* "agent a knows φ" *)
| CPX_Believes : nat -> cpx_form -> cpx_form        (* "agent a believes φ" *)
| CPX_Intends  : nat -> cpx_form -> cpx_form        (* "agent a intends φ" *)
(* Ontological mappings *)
| CPX_Eternal  : form -> cpx_form                   (* Lift PXL form to CPX *)
| CPX_Project  : temporal_index -> cpx_form -> cpx_form. (* Project to time *)

(* === PXL Bijective Mapping Functions === *)

(* Embedding: CPX → PXL (losing temporal information but preserving logic) *)
Fixpoint cpx_to_pxl (φ : cpx_form) : form :=
  match φ with
  | CPX_Atom n => Atom n
  | CPX_Bot => Bot
  | CPX_Neg ψ => Neg (cpx_to_pxl ψ)
  | CPX_Conj ψ₁ ψ₂ => Conj (cpx_to_pxl ψ₁) (cpx_to_pxl ψ₂)
  | CPX_Disj ψ₁ ψ₂ => Disj (cpx_to_pxl ψ₁) (cpx_to_pxl ψ₂)
  | CPX_Impl ψ₁ ψ₂ => Impl (cpx_to_pxl ψ₁) (cpx_to_pxl ψ₂)
  | CPX_Box ψ => Box (cpx_to_pxl ψ)
  | CPX_Dia ψ => Dia (cpx_to_pxl ψ)
  (* Temporal operators mapped to modal operators *)
  | CPX_At t ψ => Box (cpx_to_pxl ψ)           (* Necessity approximation *)
  | CPX_Always ψ => Box (cpx_to_pxl ψ)         (* Global necessity *)
  | CPX_Eventually ψ => Dia (cpx_to_pxl ψ)     (* Possibility *)
  | CPX_Until ψ₁ ψ₂ => Impl (cpx_to_pxl ψ₁) (Dia (cpx_to_pxl ψ₂))
  | CPX_Since ψ₁ ψ₂ => Impl (cpx_to_pxl ψ₁) (Box (cpx_to_pxl ψ₂))
  | CPX_Next ψ => Box (cpx_to_pxl ψ)
  | CPX_Prev ψ => Dia (cpx_to_pxl ψ)
  (* Epistemic operators as modal operators *)
  | CPX_Knows a ψ => Box (cpx_to_pxl ψ)
  | CPX_Believes a ψ => Dia (cpx_to_pxl ψ)
  | CPX_Intends a ψ => Box (cpx_to_pxl ψ)
  (* Ontological mappings *)
  | CPX_Eternal φ => φ
  | CPX_Project t ψ => Box (cpx_to_pxl ψ)
  end.

(* Lifting: PXL → CPX (preserving all PXL structure) *)
Fixpoint pxl_to_cpx (φ : form) : cpx_form :=
  match φ with
  | Atom n => CPX_Atom n
  | Bot => CPX_Bot
  | Neg ψ => CPX_Neg (pxl_to_cpx ψ)
  | Conj ψ₁ ψ₂ => CPX_Conj (pxl_to_cpx ψ₁) (pxl_to_cpx ψ₂)
  | Disj ψ₁ ψ₂ => CPX_Disj (pxl_to_cpx ψ₁) (pxl_to_cpx ψ₂)
  | Impl ψ₁ ψ₂ => CPX_Impl (pxl_to_cpx ψ₁) (pxl_to_cpx ψ₂)
  | Box ψ => CPX_Box (pxl_to_cpx ψ)
  | Dia ψ => CPX_Dia (pxl_to_cpx ψ)
  end.

(* === CPX Provability Relation === *)

Inductive CPX_Prov : cpx_form -> Prop :=
(* All PXL axioms lifted to CPX *)
| cpx_ax_K    : forall p q, CPX_Prov (CPX_Impl (CPX_Box (CPX_Impl p q)) (CPX_Impl (CPX_Box p) (CPX_Box q)))
| cpx_ax_T    : forall p,   CPX_Prov (CPX_Impl (CPX_Box p) p)
| cpx_ax_4    : forall p,   CPX_Prov (CPX_Impl (CPX_Box p) (CPX_Box (CPX_Box p)))
| cpx_ax_5    : forall p,   CPX_Prov (CPX_Impl (CPX_Dia p) (CPX_Box (CPX_Dia p)))
| cpx_ax_PL_imp : forall p q r, CPX_Prov (CPX_Impl (CPX_Impl p q) (CPX_Impl (CPX_Impl q r) (CPX_Impl p r)))
| cpx_ax_PL_and1 : forall p q, CPX_Prov (CPX_Impl (CPX_Conj p q) p)
| cpx_ax_PL_and2 : forall p q, CPX_Prov (CPX_Impl (CPX_Conj p q) q)
| cpx_ax_PL_orE  : forall p q r, CPX_Prov (CPX_Impl (CPX_Impl p r) (CPX_Impl (CPX_Impl q r) (CPX_Impl (CPX_Disj p q) r)))
| cpx_ax_PL_orI1 : forall p q, CPX_Prov (CPX_Impl p (CPX_Disj p q))
| cpx_ax_PL_orI2 : forall p q, CPX_Prov (CPX_Impl q (CPX_Disj p q))
| cpx_ax_PL_neg_elim : forall p, CPX_Prov (CPX_Impl (CPX_Neg p) (CPX_Impl p CPX_Bot))
| cpx_ax_PL_botE : forall p, CPX_Prov (CPX_Impl CPX_Bot p)
| cpx_ax_PL_k : forall p q, CPX_Prov (CPX_Impl p (CPX_Impl q p))
| cpx_ax_PL_and_intro : forall p q, CPX_Prov (CPX_Impl p (CPX_Impl q (CPX_Conj p q)))
| cpx_ax_PL_neg_intro : forall p, CPX_Prov (CPX_Impl (CPX_Impl p CPX_Bot) (CPX_Neg p))
| cpx_ax_PL_imp_exch : forall p q r, CPX_Prov (CPX_Impl (CPX_Impl p (CPX_Impl q r)) (CPX_Impl q (CPX_Impl p r)))
| cpx_ax_PL_neg_imp_any : forall a b, CPX_Prov (CPX_Impl (CPX_Neg a) (CPX_Impl a b))
| cpx_ax_modal_dual_dia_box1 : forall φ, CPX_Prov (CPX_Impl (CPX_Neg (CPX_Dia φ)) (CPX_Box (CPX_Neg φ)))
| cpx_ax_modal_dual_dia_box2 : forall φ, CPX_Prov (CPX_Impl (CPX_Box (CPX_Neg φ)) (CPX_Neg (CPX_Dia φ)))
| cpx_ax_modal_dual_box_dia1 : forall φ, CPX_Prov (CPX_Impl (CPX_Neg (CPX_Box φ)) (CPX_Dia (CPX_Neg φ)))
| cpx_ax_modal_dual_box_dia2 : forall φ, CPX_Prov (CPX_Impl (CPX_Dia (CPX_Neg φ)) (CPX_Neg (CPX_Box φ)))

(* Temporal axioms in CPX *)
| cpx_ax_temporal_at_id : forall t p, CPX_Prov (CPX_Impl (CPX_At t p) (CPX_At t p))
| cpx_ax_temporal_persistence : forall t₁ t₂ p, CPX_Prov (CPX_Impl (CPX_At t₁ p) (CPX_Dia (CPX_At t₂ p)))
| cpx_ax_temporal_always_box : forall p, CPX_Prov (CPX_Impl (CPX_Always p) (CPX_Box p))
| cpx_ax_temporal_eventually_dia : forall p, CPX_Prov (CPX_Impl (CPX_Eventually p) (CPX_Dia p))

(* Epistemic axioms in CPX *)
| cpx_ax_knowledge_truth : forall a p, CPX_Prov (CPX_Impl (CPX_Knows a p) p)
| cpx_ax_knowledge_pos_introspection : forall a p, CPX_Prov (CPX_Impl (CPX_Knows a p) (CPX_Knows a (CPX_Knows a p)))
| cpx_ax_knowledge_neg_introspection : forall a p, CPX_Prov (CPX_Impl (CPX_Neg (CPX_Knows a p)) (CPX_Knows a (CPX_Neg (CPX_Knows a p))))
| cpx_ax_belief_consistency : forall a p, CPX_Prov (CPX_Impl (CPX_Believes a p) (CPX_Dia p))
| cpx_ax_intention_belief : forall a p, CPX_Prov (CPX_Impl (CPX_Intends a p) (CPX_Believes a p))

(* Ontological mapping axioms *)
| cpx_ax_eternal_lift : forall φ, Prov φ -> CPX_Prov (CPX_Eternal φ)
| cpx_ax_project_preservation : forall t p, CPX_Prov (CPX_Impl (CPX_Project t p) (CPX_At t p))

(* Inference rules *)
| cpx_mp      : forall p q, CPX_Prov (CPX_Impl p q) -> CPX_Prov p -> CPX_Prov q
| cpx_nec     : forall p, CPX_Prov p -> CPX_Prov (CPX_Box p)
| cpx_temp_nec : forall p, CPX_Prov p -> CPX_Prov (CPX_Always p).

End ChronoPraxis_PXL_Formal.