(** MathPraxis/Problems/Goldbach/Scan.v *)
From Coq Require Import Arith String Ascii.

Module GoldbachScan.

  (* Basic types *)
  Definition Nat := nat.

  (* Import the witness finder and verifier *)
  Fixpoint divides (d n:Nat) : bool :=
    match d with
    | 0 => false
    | _ => Nat.eqb (n mod d) 0
    end.

  Fixpoint trial_prime (n d:Nat) : bool :=
    match d with
    | 0 | 1 => true
    | S d' => if divides d n then Nat.eqb d n else trial_prime n d'
    end.

  Definition is_prime (n:Nat) : bool :=
    match n with
    | 0 | 1 => false
    | 2 => true
    | S (S (S _)) => trial_prime n (n-1)
    end.

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

  Definition check_witness (n:Nat) (pr:Nat*Nat) : bool :=
    let '(p1,p2) := pr in
    Nat.eqb (p1 + p2) n && is_prime p1 && is_prime p2.

  (* Helper function to convert nat to string - simplified version *)
  Fixpoint nat_to_string (n : nat) : string :=
    match n with
    | 0 => "0"
    | S n' => "S(" ++ (nat_to_string n') ++ ")"
    end.

  (* Pure log line as string; extraction will stringify to file via driver. *)
  Definition log_line (n:Nat) : string :=
    match goldbach_witness n with
    | Some (p1,p2) =>
        if check_witness n (p1,p2)
        then ("ok," ++ (nat_to_string n) ++ "," ++
                     (nat_to_string p1) ++ "," ++
                     (nat_to_string p2))
        else ("bad," ++ (nat_to_string n))
    | None => ("none," ++ (nat_to_string n))
    end.

  (* For quick in-Coq testing via vm_compute, not file I/O. *)
  Fixpoint count_ok (n k:Nat) : Nat :=
    match k with
    | 0 => 0
    | S k' =>
        let e := 2*(n + k') in
        match goldbach_witness e with
        | Some (p1,p2) =>
            if check_witness e (p1,p2) then S (count_ok n k') else (count_ok n k')
        | None => count_ok n k'
        end
    end.

End GoldbachScan.
