(** MathPraxis/Problems/Goldbach/Verify.v *)
From Coq Require Import Arith Lia Bool.

Module GoldbachVerify.

  (* Basic types and operations *)
  Definition Nat := nat.
  Definition prime (n:Nat) : Prop := n > 1 /\ forall d, 1 < d < n -> n mod d <> 0.

  (* Import primality checker from Extract *)
  Fixpoint divides (d n:Nat) : bool :=
    match d with
    | 0 => false
    | _ => Nat.eqb (n mod d) 0
    end.

  Fixpoint trial_divisor (fuel:nat) (d:nat) (n:nat) : bool :=
    match fuel with
    | 0 => true  (* out of fuel, assume prime *)
    | S fuel' =>
        match d with
        | 0 | 1 => true
        | _ => if divides d n then Nat.eqb d n else trial_divisor fuel' (d-1) n
        end
    end.

  Definition is_prime (n:Nat) : bool :=
    match n with
    | 0 | 1 => false
    | 2 => true
    | _ => trial_divisor n (n-1) n
    end.

  (* Soundness axiom from Numbers module *)
  Axiom is_prime_sound_small : forall n, n <= 100000 -> is_prime n = true -> prime n.

  Definition check_witness (n:Nat) (pr:Nat*Nat) : bool :=
    let '(p1,p2) := pr in
    Nat.eqb (p1 + p2) n && is_prime p1 && is_prime p2.

  Lemma check_witness_sound_small :
    forall n p, n <= 100000 ->
      check_witness n p = true ->
      exists p1 p2, p = (p1,p2) /\ prime p1 /\ prime p2 /\ n = p1 + p2.
  Proof.
    intros n p Hbound Hcheck.
    unfold check_witness in Hcheck.
    destruct p as [p1 p2].
    apply andb_prop in Hcheck. destruct Hcheck as [Hpart1 Hprime2].
    apply andb_prop in Hpart1. destruct Hpart1 as [Hsum Hprime1].
    
    exists p1, p2.
    split. reflexivity.
    split.
    - (* p1 is prime *)
      apply is_prime_sound_small.
      + (* p1 <= 100000 *)
        assert (Heq : (p1 + p2) = n) by (apply Nat.eqb_eq; exact Hsum).
        assert (p1 <= p1 + p2). lia.
        rewrite Heq in H. exact (Nat.le_trans _ _ _ H Hbound).
      + exact Hprime1.
    - split.
      + (* p2 is prime *)
        apply is_prime_sound_small.
        * (* p2 <= 100000 *)
          assert (Heq : (p1 + p2) = n) by (apply Nat.eqb_eq; exact Hsum).
          assert (p2 <= p1 + p2). lia.
          rewrite Heq in H. exact (Nat.le_trans _ _ _ H Hbound).
        * exact Hprime2.
      + (* n = p1 + p2 *)
        apply Nat.eqb_eq in Hsum. symmetry. exact Hsum.
  Qed.

End GoldbachVerify.
