From Coq Require Import Logic.Classical.

(* Small, self-contained countermodel file showing failures of 4 and 5.
   Uses a tiny deep embedding of propositional modal formulas with
   local `model` and `satisfies` semantics so it doesn't depend on
   the rest of the packet. *)

Inductive form := atom (n: nat) | box (φ: form) | dia (φ: form).

Record model := {
  world : Type;
  R : world -> world -> Prop;
  D : world -> Type; (* constant domain allowed *)
  V : world -> nat -> Prop
}.

Fixpoint satisfies (M: model) (w: world M) (φ: form) : Prop :=
  match φ with
  | atom n => V M w n
  | box ψ => forall u, R M w u -> satisfies M u ψ
  | dia ψ => exists u, R M w u /\ satisfies M u ψ
  end.

Section CounterModels.

(* Three-worlds used by both countermodels *)
Inductive W := w0 | w1 | w2.

(* ---------- Four_fails model ---------- *)
Definition R4 (x y: W) : Prop :=
  match x, y with
  | w0, w1 => True
  | w1, w2 => True
  | _, _   => False
  end.

Definition Dconst (w:W) : Type := unit.

(* We'll use atom 0 as the propositional p *)
Definition V4 (w: W) (n: nat) : Prop :=
  match n, w with
  | 0, w1 => True
  | 0, w2 => False
  | 0, w0 => True
  | _, _ => False
  end.

Definition M4 : model := {| world := W; R := R4; D := Dconst; V := V4 |}.

Lemma Four_fails : exists w: W, satisfies M4 w (box (atom 0)) /\ ~ satisfies M4 w (box (box (atom 0))).
Proof.
  exists w0. split.
  - unfold satisfies. intros u Hru. destruct u; simpl in Hru; try inversion Hru; simpl; auto.
  - unfold not. intro H.
    assert (H01: R4 w0 w1) by (simpl; auto).
    specialize (H w1 H01).
    assert (H12: R4 w1 w2) by (simpl; auto).
    specialize (H w2 H12). simpl in H. exact H.
Qed.

(* ---------- Five_fails model ---------- *)
Definition R5 (x y: W) : Prop :=
  match x, y with
  | w0, w1 => True
  | w0, w2 => True
  | _, _   => False
  end.

Definition V5 (w: W) (n: nat) : Prop :=
  match n, w with
  | 0, w1 => True
  | 0, w2 => False
  | 0, w0 => False
  | _, _ => False
  end.

Definition M5 : model := {| world := W; R := R5; D := Dconst; V := V5 |}.

Lemma Five_fails : exists w:W, satisfies M5 w (dia (atom 0)) /\ ~ satisfies M5 w (box (dia (atom 0))).
Proof.
  exists w0. split.
  - unfold satisfies. exists w1. split; [simpl; auto | simpl; auto].
  - unfold not. intro H.
    assert (H02: R5 w0 w2) by (simpl; auto).
    specialize (H w2 H02). simpl in H.
    destruct H as [u [Hru Hsat]]. destruct u; simpl in Hru; inversion Hru.
Qed.

End CounterModels.
