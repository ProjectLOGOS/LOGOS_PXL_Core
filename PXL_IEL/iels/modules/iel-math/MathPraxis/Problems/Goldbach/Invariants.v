(** MathPraxis/Problems/Goldbach/Invariants.v *)
From Coq Require Import Arith Lia Bool.
From MathPraxis.Core Require Import Numbers.
From MathPraxis.Problems.Goldbach Require Import Extract Verify.
Import Numbers GoldbachExtract GoldbachVerify.

Module Invariants.

  Definition Nat := nat.

  (* Helper: simple log2 surrogate *)
  Fixpoint log2_approx (n : Nat) : Nat :=
    match n with
    | 0 | 1 => 1
    | S (S n') => S (log2_approx (n / 2))
    end.

  (* Window size function: w(n) = (log2(max(2,n)))^2 *)
  Definition window_size (n : Nat) : Nat :=
    let logn := log2_approx (max 2 n) in
    logn * logn.

  (* NW invariant: narrow-window prime near n/2 *)
  Definition NW (n : Nat) : bool :=
    let w := window_size n in
    let half := n / 2 in
    match goldbach_witness n with
    | Some (p1, p2) =>
        let gap1 := if Nat.leb p1 half then half - p1 else p1 - half in
        let gap2 := if Nat.leb p2 half then half - p2 else p2 - half in
        let mingap := min gap1 gap2 in
        Nat.leb mingap w
    | None => false
    end.

  (* Helper: check if n has a witness that shares an addend with n+2 *)
  Definition shares_addend (n : Nat) : bool :=
    match goldbach_witness n, goldbach_witness (n + 2) with
    | Some (p1, p2), Some (q1, q2) =>
        Nat.eqb p1 q1 || Nat.eqb p1 q2 || Nat.eqb p2 q1 || Nat.eqb p2 q2
    | _, _ => false
    end.

  (* Helper: check if n+2 can be covered by adjusting n's witness by ±2 *)
  Definition adjust_witness (n : Nat) : bool :=
    match goldbach_witness n with
    | Some (p1, p2) =>
        let candidates := [(p1+2, p2); (p1, p2+2); (p1-2, p2+2); (p1+2, p2-2)] in
        let check_candidate '(a, b) :=
            Nat.eqb (a + b) (n + 2) && is_prime a && is_prime b in
        existsb check_candidate candidates
    | None => false
    end.

  (* CF invariant: carry-forward (reuse addend or ±2 adjust) *)
  Definition CF (n : Nat) : bool :=
    shares_addend n || adjust_witness n.

  (* Helper: check if there's a ±2 step from n to n+2 *)
  Definition step_by_two (n : Nat) : bool :=
    match goldbach_witness n, goldbach_witness (n + 2) with
    | Some (p1, p2), Some (q1, q2) =>
        let diff1 := if Nat.leb p1 q1 then q1 - p1 else p1 - q1 in
        let diff2 := if Nat.leb p2 q2 then q2 - p2 else p2 - q2 in
        (Nat.eqb diff1 2 && Nat.eqb p2 q2) || (Nat.eqb diff2 2 && Nat.eqb p1 q1) ||
        (Nat.eqb diff1 2 && Nat.eqb diff2 0) || (Nat.eqb diff1 0 && Nat.eqb diff2 2)
    | _, _ => false
    end.

  (* BL invariant: balanced ladder (local ±2 step) *)
  Definition BL (n : Nat) : bool :=
    step_by_two n.

  (* Gap constraint: min(|p−n/2|, |q−n/2|) ≤ K *)
  Definition gap_le (n K : Nat) : bool :=
    let half := n / 2 in
    match goldbach_witness n with
    | Some (p1, p2) =>
        let gap1 := if Nat.leb p1 half then half - p1 else p1 - half in
        let gap2 := if Nat.leb p2 half then half - p2 else p2 - half in
        let mingap := min gap1 gap2 in
        Nat.leb mingap K
    | None => false
    end.

End Invariants.
