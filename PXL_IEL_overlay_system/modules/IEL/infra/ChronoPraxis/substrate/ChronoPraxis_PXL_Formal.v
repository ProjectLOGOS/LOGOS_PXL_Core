(* ChronoPraxis_PXL_Formal.v - Stub for compilation *)(* ChronoPraxis_PXL_Formal.v *)(* ChronoPraxis_PXL_Formal.v *)(* ChronoPraxis_PXL_Formal.v *)



From PXLs Require Import PXLv3.(* Formal definitions for PXL↔CPX bijection *)



Module ChronoPraxis_PXL_Formal.(* Formal definitions for PXL↔CPX bijection *)(* 



Notation form := PXLv3.form.From PXLs Require Import PXLv3.

Notation Prov := PXLv3.Prov.

   PXL Formal Language Translation of ChronoPraxis

Inductive cpx_form : Type :=

  | CPX_Atom : nat -> cpx_formModule ChronoPraxis_PXL_Formal.

  | CPX_Bot : cpx_form

  | CPX_Neg : cpx_form -> cpx_formModule ChronoPraxis_PXL_Formal.   This module provides the canonical PXL representation of temporal reasoning constructs

  | CPX_Conj : cpx_form -> cpx_form -> cpx_form

  | CPX_Disj : cpx_form -> cpx_form -> cpx_form(* === PXL Formula Type === *)

  | CPX_Impl : cpx_form -> cpx_form -> cpx_form

  | CPX_Box : cpx_form -> cpx_formNotation form := PXLv3.form.*)

  | CPX_Dia : cpx_form -> cpx_form.



Inductive CPX_Prov : cpx_form -> Type :=

  | cpx_ax_K : forall p q, CPX_Prov (CPX_Impl (CPX_Box (CPX_Impl p q)) (CPX_Impl (CPX_Box p) (CPX_Box q)))(* === PXL Proof System === *)(* === PXL Formula Type === *)

  | cpx_ax_T : forall p, CPX_Prov (CPX_Impl (CPX_Box p) p)

  | cpx_ax_4 : forall p, CPX_Prov (CPX_Impl (CPX_Box p) (CPX_Box (CPX_Box p)))Notation Prov := PXLv3.Prov.

  | cpx_ax_5 : forall p, CPX_Prov (CPX_Impl (CPX_Dia p) (CPX_Box (CPX_Dia p)))

  | cpx_ax_PL_imp : forall p q, CPX_Prov (CPX_Impl p (CPX_Impl q p))(* Import PXL formula type from PXLv3 *)From Coq Require Import List.

  | cpx_ax_PL_and1 : forall p q, CPX_Prov (CPX_Impl (CPX_Conj p q) p)

  | cpx_ax_PL_and2 : forall p q, CPX_Prov (CPX_Impl (CPX_Conj p q) q)(* === CPX Formula Type === *)

  | cpx_ax_PL_orE : forall p q r, CPX_Prov (CPX_Impl (CPX_Disj p q) (CPX_Impl (CPX_Impl p r) (CPX_Impl (CPX_Impl q r) r)))

  | cpx_ax_PL_orI1 : forall p q, CPX_Prov (CPX_Impl p (CPX_Disj p q))(* ChronoPraxis extended modal logic formulas *)From PXLs Require Import PXLv3.Import ListNotations.

  | cpx_ax_PL_orI2 : forall p q, CPX_Prov (CPX_Impl q (CPX_Disj p q))

  | cpx_ax_PL_neg_elim : forall p, CPX_Prov (CPX_Impl (CPX_Neg (CPX_Neg p)) p)Inductive cpx_form : Type :=

  | cpx_ax_PL_botE : forall p, CPX_Prov (CPX_Impl CPX_Bot p)

  | cpx_ax_PL_k : forall p q, CPX_Prov (CPX_Impl (CPX_Box (CPX_Impl p q)) (CPX_Impl (CPX_Box p) (CPX_Box q)))  | CPX_Atom : nat -> cpx_formNotation form := PXLv3.form.Set Implicit Arguments.

  | cpx_ax_PL_and_intro : forall p q, CPX_Prov (CPX_Impl p (CPX_Impl q (CPX_Conj p q)))

  | cpx_ax_PL_neg_intro : forall p, CPX_Prov (CPX_Impl (CPX_Impl p CPX_Bot) (CPX_Neg p))  | CPX_Bot : cpx_form

  | cpx_ax_PL_imp_exch : forall p q r, CPX_Prov (CPX_Impl (CPX_Impl p (CPX_Impl q r)) (CPX_Impl (CPX_Conj p q) r))

  | cpx_ax_PL_neg_imp_any : forall p q, CPX_Prov (CPX_Impl (CPX_Neg p) (CPX_Impl p q))  | CPX_Neg : cpx_form -> cpx_form

  | cpx_modal_dual_dia_box1 : forall p, CPX_Prov (CPX_Impl (CPX_Neg (CPX_Box p)) (CPX_Dia (CPX_Neg p)))

  | cpx_modal_dual_dia_box2 : forall p, CPX_Prov (CPX_Impl (CPX_Dia (CPX_Neg p)) (CPX_Neg (CPX_Box p)))  | CPX_Conj : cpx_form -> cpx_form -> cpx_form

  | cpx_modal_dual_box_dia1 : forall p, CPX_Prov (CPX_Impl (CPX_Neg (CPX_Dia p)) (CPX_Box (CPX_Neg p)))

  | cpx_modal_dual_box_dia2 : forall p, CPX_Prov (CPX_Impl (CPX_Box (CPX_Neg p)) (CPX_Neg (CPX_Dia p)))  | CPX_Disj : cpx_form -> cpx_form -> cpx_form(* === PXL Proof System === *)(* Import canonical PXL definitions *)

  | cpx_mp : forall p q, CPX_Prov p -> CPX_Prov (CPX_Impl p q) -> CPX_Prov q

  | cpx_nec : forall p, CPX_Prov p -> CPX_Prov (CPX_Box p).  | CPX_Impl : cpx_form -> cpx_form -> cpx_form



Fixpoint pxl_to_cpx (φ : form) : cpx_form :=  | CPX_Box : cpx_form -> cpx_form(* Import PXL proof system *)Require Import PXLs.PXLv3.

  match φ with

  | PXLv3.Atom n => CPX_Atom n  | CPX_Dia : cpx_form -> cpx_form.

  | PXLv3.Bot => CPX_Bot

  | PXLv3.Neg ψ => CPX_Neg (pxl_to_cpx ψ)Notation Prov := PXLv3.Prov.

  | PXLv3.Conj ψ₁ ψ₂ => CPX_Conj (pxl_to_cpx ψ₁) (pxl_to_cpx ψ₂)

  | PXLv3.Disj ψ₁ ψ₂ => CPX_Disj (pxl_to_cpx ψ₁) (pxl_to_cpx ψ₂)(* === CPX Proof System === *)

  | PXLv3.Impl ψ₁ ψ₂ => CPX_Impl (pxl_to_cpx ψ₁) (pxl_to_cpx ψ₂)

  | PXLv3.Box ψ => CPX_Box (pxl_to_cpx ψ)(* ChronoPraxis proof system - simplified for compilation *)Module ChronoPraxis_PXL_Formal.

  | PXLv3.Dia ψ => CPX_Dia (pxl_to_cpx ψ)

  end.Inductive CPX_Prov : cpx_form -> Type :=



End ChronoPraxis_PXL_Formal.  | cpx_ax_K : forall p q, CPX_Prov (CPX_Impl (CPX_Box (CPX_Impl p q)) (CPX_Impl (CPX_Box p) (CPX_Box q)))(* === CPX Formula Type === *)

  | cpx_ax_T : forall p, CPX_Prov (CPX_Impl (CPX_Box p) p)

  | cpx_ax_4 : forall p, CPX_Prov (CPX_Impl (CPX_Box p) (CPX_Box (CPX_Box p)))(* ChronoPraxis extended modal logic formulas *)(* === CPX: ChronoPraxic Extension Layer === *)

  | cpx_ax_5 : forall p, CPX_Prov (CPX_Impl (CPX_Dia p) (CPX_Box (CPX_Dia p)))

  | cpx_ax_PL_imp : forall p q, CPX_Prov (CPX_Impl p (CPX_Impl q p))Inductive cpx_form : Type :=

  | cpx_ax_PL_and1 : forall p q, CPX_Prov (CPX_Impl (CPX_Conj p q) p)

  | cpx_ax_PL_and2 : forall p q, CPX_Prov (CPX_Impl (CPX_Conj p q) q)  | CPX_Atom : nat -> cpx_form(* Temporal indices as natural numbers *)

  | cpx_ax_PL_orE : forall p q r, CPX_Prov (CPX_Impl (CPX_Disj p q) (CPX_Impl (CPX_Impl p r) (CPX_Impl (CPX_Impl q r) r)))

  | cpx_ax_PL_orI1 : forall p q, CPX_Prov (CPX_Impl p (CPX_Disj p q))  | CPX_Bot : cpx_formDefinition temporal_index := nat.

  | cpx_ax_PL_orI2 : forall p q, CPX_Prov (CPX_Impl q (CPX_Disj p q))

  | cpx_ax_PL_neg_elim : forall p, CPX_Prov (CPX_Impl (CPX_Neg (CPX_Neg p)) p)  | CPX_Neg : cpx_form -> cpx_form

  | cpx_ax_PL_botE : forall p, CPX_Prov (CPX_Impl CPX_Bot p)

  | cpx_ax_PL_k : forall p q, CPX_Prov (CPX_Impl (CPX_Box (CPX_Impl p q)) (CPX_Impl (CPX_Box p) (CPX_Box q)))  | CPX_Conj : cpx_form -> cpx_form -> cpx_form(* Extended PXL grammar with temporal operators *)

  | cpx_ax_PL_and_intro : forall p q, CPX_Prov (CPX_Impl p (CPX_Impl q (CPX_Conj p q)))

  | cpx_ax_PL_neg_intro : forall p, CPX_Prov (CPX_Impl (CPX_Impl p CPX_Bot) (CPX_Neg p))  | CPX_Disj : cpx_form -> cpx_form -> cpx_formInductive cpx_form : Type :=

  | cpx_ax_PL_imp_exch : forall p q r, CPX_Prov (CPX_Impl (CPX_Impl p (CPX_Impl q r)) (CPX_Impl (CPX_Conj p q) r))

  | cpx_ax_PL_neg_imp_any : forall p q, CPX_Prov (CPX_Impl (CPX_Neg p) (CPX_Impl p q))  | CPX_Impl : cpx_form -> cpx_form -> cpx_form| CPX_Atom     : nat -> cpx_form                    (* Standard PXL atoms *)

  | cpx_modal_dual_dia_box1 : forall p, CPX_Prov (CPX_Impl (CPX_Neg (CPX_Box p)) (CPX_Dia (CPX_Neg p)))

  | cpx_modal_dual_dia_box2 : forall p, CPX_Prov (CPX_Impl (CPX_Dia (CPX_Neg p)) (CPX_Neg (CPX_Box p)))  | CPX_Box : cpx_form -> cpx_form| CPX_Bot      : cpx_form                           (* Bottom *)

  | cpx_modal_dual_box_dia1 : forall p, CPX_Prov (CPX_Impl (CPX_Neg (CPX_Dia p)) (CPX_Box (CPX_Neg p)))

  | cpx_modal_dual_box_dia2 : forall p, CPX_Prov (CPX_Impl (CPX_Box (CPX_Neg p)) (CPX_Neg (CPX_Dia p)))  | CPX_Dia : cpx_form -> cpx_form.| CPX_Neg      : cpx_form -> cpx_form               (* Negation *)

  | cpx_mp : forall p q, CPX_Prov p -> CPX_Prov (CPX_Impl p q) -> CPX_Prov q

  | cpx_nec : forall p, CPX_Prov p -> CPX_Prov (CPX_Box p).| CPX_Conj     : cpx_form -> cpx_form -> cpx_form   (* Conjunction *)



(* === PXL to CPX Translation === *)(* === CPX Proof System === *)| CPX_Disj     : cpx_form -> cpx_form -> cpx_form   (* Disjunction *)

Fixpoint pxl_to_cpx (φ : form) : cpx_form :=

  match φ with(* ChronoPraxis proof system - simplified for compilation *)| CPX_Impl     : cpx_form -> cpx_form -> cpx_form   (* Implication *)

  | PXLv3.Atom n => CPX_Atom n

  | PXLv3.Bot => CPX_BotInductive CPX_Prov : cpx_form -> Type :=| CPX_Box      : cpx_form -> cpx_form               (* Necessity *)

  | PXLv3.Neg ψ => CPX_Neg (pxl_to_cpx ψ)

  | PXLv3.Conj ψ₁ ψ₂ => CPX_Conj (pxl_to_cpx ψ₁) (pxl_to_cpx ψ₂)  | cpx_ax_K : forall p q, CPX_Prov (CPX_Impl (CPX_Box (CPX_Impl p q)) (CPX_Impl (CPX_Box p) (CPX_Box q)))| CPX_Dia      : cpx_form -> cpx_form               (* Possibility *)

  | PXLv3.Disj ψ₁ ψ₂ => CPX_Disj (pxl_to_cpx ψ₁) (pxl_to_cpx ψ₂)

  | PXLv3.Impl ψ₁ ψ₂ => CPX_Impl (pxl_to_cpx ψ₁) (pxl_to_cpx ψ₂)  | cpx_ax_T : forall p, CPX_Prov (CPX_Impl (CPX_Box p) p)(* Temporal extensions *)

  | PXLv3.Box ψ => CPX_Box (pxl_to_cpx ψ)

  | PXLv3.Dia ψ => CPX_Dia (pxl_to_cpx ψ)  | cpx_ax_4 : forall p, CPX_Prov (CPX_Impl (CPX_Box p) (CPX_Box (CPX_Box p)))| CPX_At       : temporal_index -> cpx_form -> cpx_form  (* "φ holds at time t" *)

  end.

  | cpx_ax_5 : forall p, CPX_Prov (CPX_Impl (CPX_Dia p) (CPX_Box (CPX_Dia p)))| CPX_Always   : cpx_form -> cpx_form               (* "φ holds at all times" *)

End ChronoPraxis_PXL_Formal.
  | cpx_ax_PL_imp : forall p q, CPX_Prov (CPX_Impl p (CPX_Impl q p))| CPX_Eventually : cpx_form -> cpx_form             (* "φ holds at some time" *)

  | cpx_ax_PL_and1 : forall p q, CPX_Prov (CPX_Impl (CPX_Conj p q) p)| CPX_Until    : cpx_form -> cpx_form -> cpx_form   (* "φ until ψ" *)

  | cpx_ax_PL_and2 : forall p q, CPX_Prov (CPX_Impl (CPX_Conj p q) q)| CPX_Since    : cpx_form -> cpx_form -> cpx_form   (* "φ since ψ" *)

  | cpx_ax_PL_orE : forall p q r, CPX_Prov (CPX_Impl (CPX_Disj p q) (CPX_Impl (CPX_Impl p r) (CPX_Impl (CPX_Impl q r) r)))| CPX_Next     : cpx_form -> cpx_form               (* "φ holds at next time" *)

  | cpx_ax_PL_orI1 : forall p q, CPX_Prov (CPX_Impl p (CPX_Disj p q))| CPX_Prev     : cpx_form -> cpx_form               (* "φ held at previous time" *)

  | cpx_ax_PL_orI2 : forall p q, CPX_Prov (CPX_Impl q (CPX_Disj p q))(* Epistemic extensions *)

  | cpx_ax_PL_neg_elim : forall p, CPX_Prov (CPX_Impl (CPX_Neg (CPX_Neg p)) p)| CPX_Knows    : nat -> cpx_form -> cpx_form        (* "agent a knows φ" *)

  | cpx_ax_PL_botE : forall p, CPX_Prov (CPX_Impl CPX_Bot p)| CPX_Believes : nat -> cpx_form -> cpx_form        (* "agent a believes φ" *)

  | cpx_ax_PL_k : forall p q, CPX_Prov (CPX_Impl (CPX_Box (CPX_Impl p q)) (CPX_Impl (CPX_Box p) (CPX_Box q)))| CPX_Intends  : nat -> cpx_form -> cpx_form        (* "agent a intends φ" *)

  | cpx_ax_PL_and_intro : forall p q, CPX_Prov (CPX_Impl p (CPX_Impl q (CPX_Conj p q)))(* Ontological mappings *)

  | cpx_ax_PL_neg_intro : forall p, CPX_Prov (CPX_Impl (CPX_Impl p CPX_Bot) (CPX_Neg p))| CPX_Eternal  : form -> cpx_form                   (* Lift PXL form to CPX *)

  | cpx_ax_PL_imp_exch : forall p q r, CPX_Prov (CPX_Impl (CPX_Impl p (CPX_Impl q r)) (CPX_Impl (CPX_Conj p q) r))| CPX_Project  : temporal_index -> cpx_form -> cpx_form. (* Project to time *)

  | cpx_ax_PL_neg_imp_any : forall p q, CPX_Prov (CPX_Impl (CPX_Neg p) (CPX_Impl p q))

  | cpx_modal_dual_dia_box1 : forall p, CPX_Prov (CPX_Impl (CPX_Neg (CPX_Box p)) (CPX_Dia (CPX_Neg p)))(* === PXL Bijective Mapping Functions === *)

  | cpx_modal_dual_dia_box2 : forall p, CPX_Prov (CPX_Impl (CPX_Dia (CPX_Neg p)) (CPX_Neg (CPX_Box p)))

  | cpx_modal_dual_box_dia1 : forall p, CPX_Prov (CPX_Impl (CPX_Neg (CPX_Dia p)) (CPX_Box (CPX_Neg p)))(* Embedding: CPX → PXL (losing temporal information but preserving logic) *)

  | cpx_modal_dual_box_dia2 : forall p, CPX_Prov (CPX_Impl (CPX_Box (CPX_Neg p)) (CPX_Neg (CPX_Dia p)))Fixpoint cpx_to_pxl (φ : cpx_form) : form :=

  | cpx_mp : forall p q, CPX_Prov p -> CPX_Prov (CPX_Impl p q) -> CPX_Prov q  match φ with

  | cpx_nec : forall p, CPX_Prov p -> CPX_Prov (CPX_Box p).  | CPX_Atom n => Atom n

  | CPX_Bot => Bot

(* === PXL to CPX Translation === *)  | CPX_Neg ψ => Neg (cpx_to_pxl ψ)

Fixpoint pxl_to_cpx (φ : form) : cpx_form :=  | CPX_Conj ψ₁ ψ₂ => Conj (cpx_to_pxl ψ₁) (cpx_to_pxl ψ₂)

  match φ with  | CPX_Disj ψ₁ ψ₂ => Disj (cpx_to_pxl ψ₁) (cpx_to_pxl ψ₂)

  | PXLv3.Atom n => CPX_Atom n  | CPX_Impl ψ₁ ψ₂ => Impl (cpx_to_pxl ψ₁) (cpx_to_pxl ψ₂)

  | PXLv3.Bot => CPX_Bot  | CPX_Box ψ => Box (cpx_to_pxl ψ)

  | PXLv3.Neg ψ => CPX_Neg (pxl_to_cpx ψ)  | CPX_Dia ψ => Dia (cpx_to_pxl ψ)

  | PXLv3.Conj ψ₁ ψ₂ => CPX_Conj (pxl_to_cpx ψ₁) (pxl_to_cpx ψ₂)  (* Temporal operators mapped to modal operators *)

  | PXLv3.Disj ψ₁ ψ₂ => CPX_Disj (pxl_to_cpx ψ₁) (pxl_to_cpx ψ₂)  | CPX_At t ψ => Box (cpx_to_pxl ψ)           (* Necessity approximation *)

  | PXLv3.Impl ψ₁ ψ₂ => CPX_Impl (pxl_to_cpx ψ₁) (pxl_to_cpx ψ₂)  | CPX_Always ψ => Box (cpx_to_pxl ψ)         (* Global necessity *)

  | PXLv3.Box ψ => CPX_Box (pxl_to_cpx ψ)  | CPX_Eventually ψ => Dia (cpx_to_pxl ψ)     (* Possibility *)

  | PXLv3.Dia ψ => CPX_Dia (pxl_to_cpx ψ)  | CPX_Until ψ₁ ψ₂ => Impl (cpx_to_pxl ψ₁) (Dia (cpx_to_pxl ψ₂))

  end.  | CPX_Since ψ₁ ψ₂ => Impl (cpx_to_pxl ψ₁) (Box (cpx_to_pxl ψ₂))

  | CPX_Next ψ => Box (cpx_to_pxl ψ)

End ChronoPraxis_PXL_Formal.  | CPX_Prev ψ => Dia (cpx_to_pxl ψ)
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
