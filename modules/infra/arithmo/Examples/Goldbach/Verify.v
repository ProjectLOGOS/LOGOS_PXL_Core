(** MathPraxis/Problems/Goldbach/Verify.v *)
From Coq Require Import Arith Lia.

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

  Fixpoint is_prime (n:Nat) : bool :=
    match n with
    | 0 | 1 => false
    | 2 => true
    | _ =>
      let fix trial d :=
          match d with
          | 0 | 1 => true
          | _ => if divides d n then Nat.eqb d n else trial (d-1)
          end
      in trial (n-1)
    end.

  Definition check_witness (n:Nat) (pr:Nat*Nat) : bool :=
    let '(p1,p2) := pr in
    Nat.eqb (p1 + p2) n && is_prime p1 && is_prime p2.

  Lemma check_witness_sound_small :
    forall n p, n <= 100000 ->
      check_witness n p = true ->
      exists p1 p2, p = (p1,p2) /\ prime p1 /\ prime p2 /\ n = p1 + p2.
  Proof. (* TODO: connect to is_prime_sound_small; small-range guarantee *)
  Admitted.

End GoldbachVerify.
