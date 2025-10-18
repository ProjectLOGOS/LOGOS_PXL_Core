(** ArithmoPraxis/Core/Numbers.v *)
From Coq Require Import Arith PeanoNat.
From Coq Require Import Lists.List.
Import ListNotations.

Module ArithmoPraxis_Numbers.
  (* Canonical types/defs from Coq stdlib *)
  Definition Nat := nat.
  Definition even (n:Nat) : Prop := Nat.Even n.

  (* Simple prime definition for now - can be upgraded later *)
  Definition prime (n:Nat) : Prop := n > 1 /\ forall d, 1 < d < n -> n mod d <> 0.

  (* Fast enough determinism for small scans; can upgrade later. *)
  Fixpoint divides (d n:Nat) : bool :=
    match d with
    | 0 => false
    | _ => Nat.eqb (n mod d) 0
    end.

  (* Helper for primality testing with proper structural recursion *)
  Fixpoint trial_divisor (fuel d n : nat) : bool :=
    match fuel with
    | 0 => true  (* out of fuel, assume prime *)
    | S fuel' =>
      match d with
      | 0 | 1 => true
      | S (S _) =>
        if divides d n
        then Nat.eqb d n
        else trial_divisor fuel' (d-1) n
      end
    end.

  (* Very naive primality test (placeholder); swap for Pocklington or MR with proof later. *)
  Definition is_prime (n:Nat) : bool :=
    match n with
    | 0 | 1 => false
    | 2 => true
    | _ => trial_divisor n (n-1) n
    end.

  Lemma is_prime_sound_small :
    forall n, n <= 100000 -> is_prime n = true -> prime n.
  Proof.
    (* TODO: prove or replace checker; keep lemma name stable. *)
  Admitted.
End ArithmoPraxis_Numbers.
