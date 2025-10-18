(** MathPraxis/Problems/Goldbach/ScanFeatures.v *)
From Coq Require Import Arith Lia Bool Lists.List.
Import ListNotations.

Module ScanFeatures.

  Definition Nat := nat.

  (* Redefine essential functions locally *)
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

  (* Simple sqrt approximation for primality bound *)
  Definition sqrt_approx (n:Nat) : Nat :=
    if Nat.leb n 4 then 2
    else if Nat.leb n 9 then 3
    else if Nat.leb n 16 then 4
    else if Nat.leb n 25 then 5
    else if Nat.leb n 36 then 6
    else if Nat.leb n 49 then 7
    else if Nat.leb n 64 then 8
    else if Nat.leb n 81 then 9
    else if Nat.leb n 100 then 10
    else if Nat.leb n 121 then 11
    else if Nat.leb n 144 then 12
    else 15.

  Definition is_prime (n:Nat) : bool :=
    match n with
    | 0 | 1 => false
    | 2 => true
    | S (S (S _)) => 
        if Nat.even n then false  (* even numbers > 2 are not prime *)
        else trial_prime n (sqrt_approx n)
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

  (* Invariant implementations - simple log2 approximation *)
  Definition log2_approx (n : Nat) : Nat :=
    if Nat.leb n 1 then 1
    else if Nat.leb n 3 then 2
    else if Nat.leb n 7 then 3
    else if Nat.leb n 15 then 4
    else if Nat.leb n 31 then 5
    else if Nat.leb n 63 then 6
    else if Nat.leb n 127 then 7
    else 8.

  Definition window_size (n : Nat) : Nat :=
    let logn := log2_approx (max 2 n) in
    logn * logn.

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

  Definition shares_addend (n : Nat) : bool :=
    match goldbach_witness n, goldbach_witness (n + 2) with
    | Some (p1, p2), Some (q1, q2) =>
        Nat.eqb p1 q1 || Nat.eqb p1 q2 || Nat.eqb p2 q1 || Nat.eqb p2 q2
    | _, _ => false
    end.

  Definition adjust_witness (n : Nat) : bool :=
    match goldbach_witness n with
    | Some (p1, p2) =>
        let check_pair (a b : Nat) := 
            Nat.eqb (a + b) (n + 2) && is_prime a && is_prime b in
        check_pair (p1+2) p2 || check_pair p1 (p2+2) || 
        check_pair (p1-2) (p2+2) || check_pair (p1+2) (p2-2)
    | None => false
    end.

  Definition CF (n : Nat) : bool :=
    shares_addend n || adjust_witness n.

  Definition step_by_two (n : Nat) : bool :=
    match goldbach_witness n, goldbach_witness (n + 2) with
    | Some (p1, p2), Some (q1, q2) =>
        let diff1 := if Nat.leb p1 q1 then q1 - p1 else p1 - q1 in
        let diff2 := if Nat.leb p2 q2 then q2 - p2 else p2 - q2 in
        (Nat.eqb diff1 2 && Nat.eqb p2 q2) || (Nat.eqb diff2 2 && Nat.eqb p1 q1)
    | _, _ => false
    end.

  Definition BL (n : Nat) : bool :=
    step_by_two n.

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

  (* Feature record for a given even number *)
  Record feat := mkFeat {
    n_even : Nat;           (* the even number *)
    has_pair : bool;        (* goldbach witness exists *)
    nw_win : bool;          (* NW invariant holds *)
    cf_next : bool;         (* CF invariant for n->n+2 *)
    bl_next : bool;         (* BL invariant for n->n+2 *)
    gapK2 : bool;           (* gap_le n 2 *)
    gapK4 : bool;           (* gap_le n 4 *)
  }.

  (* Create feature record for even number n *)
  Definition mk_feat (n : Nat) : feat :=
    let witness := goldbach_witness n in
    let has_w := match witness with Some _ => true | None => false end in
    let verified := match witness with
                    | Some p => check_witness n p
                    | None => false
                    end in
    mkFeat n 
           (has_w && verified)
           (NW n)
           (CF n)
           (BL n)
           (gap_le n 2)
           (gap_le n 4).

  (* Step validation rule: satisfies one of the closure conditions *)
  Definition step_ok (f : feat) : bool :=
    (has_pair f && cf_next f) || (has_pair f && bl_next f) || (nw_win f && gapK4 f).

  (* Closure score: count valid steps in range [4, 2*(k+2)] *)
  Fixpoint closure_score (k : Nat) : Nat :=
    match k with
    | 0 => 0
    | S k' => 
        let n := 2 * (k' + 2) in  (* even numbers starting from 4 *)
        let f := mk_feat n in
        let score_rest := closure_score k' in
        if step_ok f then S score_rest else score_rest
    end.

  (* Helper: count total evens in range for rate calculation *)
  Definition total_evens (k : Nat) : Nat := k.

  (* Closure rate calculation *)
  Definition closure_rate (k : Nat) : Nat * Nat :=
    (closure_score k, total_evens k).

  (* Feature extraction for a single number (useful for CSV generation) *)
  Definition extract_features (n : Nat) : list bool :=
    let f := mk_feat n in
    (has_pair f) :: (nw_win f) :: (cf_next f) :: (bl_next f) :: (gapK2 f) :: (gapK4 f) :: nil.

  (* Best candidate analysis - which invariant performs best *)
  Fixpoint count_nw_gap (k : Nat) : Nat :=
    match k with
    | 0 => 0
    | S k' =>
        let n := 2 * (k' + 2) in
        let f := mk_feat n in
        let rest := count_nw_gap k' in
        if nw_win f && gapK4 f then S rest else rest
    end.

  Fixpoint count_cf (k : Nat) : Nat :=
    match k with
    | 0 => 0
    | S k' =>
        let n := 2 * (k' + 2) in
        let f := mk_feat n in
        let rest := count_cf k' in
        if has_pair f && cf_next f then S rest else rest
    end.

  Fixpoint count_bl (k : Nat) : Nat :=
    match k with
    | 0 => 0
    | S k' =>
        let n := 2 * (k' + 2) in
        let f := mk_feat n in
        let rest := count_bl k' in
        if has_pair f && bl_next f then S rest else rest
    end.

  (* Summary statistics *)
  Definition invariant_summary (k : Nat) : (Nat * Nat * Nat) :=
    (count_nw_gap k, count_cf k, count_bl k).

End ScanFeatures.