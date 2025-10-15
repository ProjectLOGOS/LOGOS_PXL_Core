From Coq Require Import Logic.Classical.

(*
  S5_Independence_Barcan.v
  Independence tests for T, 4, 5 via counter-frames, and Barcan/Converse-Barcan
  under constant domains.
  Explicit proofs only.
*)

Record frame := { W : Type; R : W -> W -> Prop }.

Definition box {F:frame} (p:W F -> Prop) : W F -> Prop := fun w => forall u, R F w u -> p u.
Definition dia {F:frame} (p:W F -> Prop) : W F -> Prop := fun w => exists u, R F w u /\ p u.

Module NonReflexive_T.
  Inductive Wt := w0 | w1.
  Definition Rt (x y:Wt) : Prop := match x, y with | w0, w1 => True | w1, w1 => True | _, _ => False end.
  Definition Ft : frame := {| W := Wt; R := Rt |}.

  Definition p (w:Wt) : Prop := match w with | w0 => False | w1 => True end.

  Lemma T_fails : exists w, box (F:=Ft) p w /\ ~ p w.
  Proof.
    exists w0. split.
    - intros u Hu. destruct u; simpl in *.
      + inversion Hu.
      + exact I.
    - simpl. intro H. inversion H.
  Qed.
End NonReflexive_T.

(* The constructive countermodels for failure of 4 and 5 live in
   `S5_CounterModels.v`. That file is self-contained and contains
   verified lemmas `Four_fails` and `Five_fails` demonstrating the
   countermodels. Import that module if you want to use those lemmas
   here. *)

From PXLs Require Import S5_CounterModels.

(* See `S5_CounterModels.v` for a self-contained proof of Five_fails. *)

Section Barcan_Constant.

Variable W : Type.
Variable R : W -> W -> Prop.

Definition box_const (p:W->Prop) : W->Prop := fun w => forall u, R w u -> p u.

Variable D : Type.
Variable P : W -> D -> Prop.

Lemma Barcan_constant : forall w,
  (forall x:D, box_const (fun w => P w x) w) ->
  box_const (fun w => forall x:D, P w x) w.
Proof.
  intros w H u Hwu x. apply (H x u Hwu).
Qed.

Lemma Converse_Barcan_constant : forall w,
  box_const (fun w => forall x:D, P w x) w ->
  forall x:D, box_const (fun w => P w x) w.
Proof.
  intros w H x u Hwu. apply (H u Hwu).
Qed.

End Barcan_Constant.
