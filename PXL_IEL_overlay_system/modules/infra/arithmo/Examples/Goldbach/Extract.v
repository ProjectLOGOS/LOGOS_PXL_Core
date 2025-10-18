(** MathPraxis/Problems/Goldbach/Extract.v *)
From Coq Require Import Arith Lia.

Module GoldbachExtract.

  (* Basic number theory definitions *)
  Definition Nat := nat.

  (* Redefine prime check locally *)
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

  (* Try primes p <= n/2; if n-p is prime, return pair *)
  Fixpoint first_prime_pair_upto (n p:Nat) : option (Nat*Nat) :=
    match p with
    | 0 | 1 => None
    | S p' =>
        let p0 := S p' in
        if Nat.leb (2*p0) n then
          if andb (is_prime p0) (is_prime (n - p0))
          then Some (p0, n - p0)
          else first_prime_pair_upto n p'
        else None
    end.

  Definition goldbach_witness (n:Nat) : option (Nat*Nat) :=
    match Nat.even n with
    | true  => first_prime_pair_upto n (n/2)
    | false => None
    end.

End GoldbachExtract.
