(** MathPraxis/Core/Numbers.v *)
From Coq Require Import Arith PeanoNat.
From Coq Require Import Lists.List.
Import ListNotations.

Module Numbers.
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

  (* Very naive primality test (placeholder); swap for Pocklington or MR with proof later. *)
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

  Lemma is_prime_sound_small :
    forall n, n <= 100000 -> is_prime n = true -> prime n.
  Proof.
    (* TODO: prove or replace checker; keep lemma name stable. *)
  Admitted.
End Numbers.
