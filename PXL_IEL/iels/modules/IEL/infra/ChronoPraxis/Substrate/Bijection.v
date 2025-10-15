(* Bijection.v - Constructive Bijection Interface *)

Set Implicit Arguments.
Set Primitive Projections.

From Coq Require Import Program.

(* === Constructive Bijection Record === *)

Record Bijection (X Y : Type) := {
  f : X -> Y;
  g : Y -> X;
  fg : forall x : X, g (f x) = x;
  gf : forall y : Y, f (g y) = y
}.

(* === Identity Bijection === *)

Definition id_bij (X : Type) : Bijection X X := {|
  f := fun x => x;
  g := fun x => x;
  fg := fun x => eq_refl;
  gf := fun x => eq_refl
|}.

(* === Inverse Bijection === *)

Definition inverse_bij {X Y : Type} (bij : Bijection X Y) : Bijection Y X := {|
  f := g bij;
  g := f bij;
  fg := gf bij;
  gf := fg bij
|}.

(* === Bijection Equality Lemmas === *)

Lemma bij_injective_f {X Y : Type} (bij : Bijection X Y) :
  forall x1 x2 : X, f bij x1 = f bij x2 -> x1 = x2.
Proof.
  intros x1 x2 H.
  rewrite <- (fg bij x1).
  rewrite <- (fg bij x2).
  rewrite H.
  reflexivity.
Qed.

Lemma bij_injective_g {X Y : Type} (bij : Bijection X Y) :
  forall y1 y2 : Y, g bij y1 = g bij y2 -> y1 = y2.
Proof.
  intros y1 y2 H.
  rewrite <- (gf bij y1).
  rewrite <- (gf bij y2).
  rewrite H.
  reflexivity.
Qed.

(* === Bijection Composition === *)

Definition compose_bij {X Y Z : Type} (bij1 : Bijection X Y) (bij2 : Bijection Y Z) : Bijection X Z := {|
  f := fun x => f bij2 (f bij1 x);
  g := fun z => g bij1 (g bij2 z);
  fg := fun x =>
    eq_trans (f_equal (g bij1) (fg bij2 (f bij1 x)))
             (fg bij1 x);
  gf := fun z =>
    eq_trans (f_equal (f bij2) (gf bij1 (g bij2 z)))
             (gf bij2 z)
|}.

(* === Forward and Backward Accessors === *)

Definition forward {X Y : Type} (bij : Bijection X Y) : X -> Y := f bij.
Definition backward {X Y : Type} (bij : Bijection X Y) : Y -> X := g bij.

(* === Rewrite Lemmas === *)

Lemma fg_rewrite {X Y : Type} (bij : Bijection X Y) : 
  forall x : X, backward bij (forward bij x) = x.
Proof. intro x. unfold backward, forward. apply fg. Qed.

Lemma gf_rewrite {X Y : Type} (bij : Bijection X Y) : 
  forall y : Y, forward bij (backward bij y) = y.
Proof. intro y. unfold forward, backward. apply gf. Qed.
