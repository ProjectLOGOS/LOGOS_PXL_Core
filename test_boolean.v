(** Test file for Boolean logic compilation *)
From Coq Require Import Arith Bool String Lists.List.
From IEL.ArithmoPraxis.Core Require Import ModalWrap Numbers.

Module TestBoolean.
  (** Propositional formulas *)
  Inductive prop : Type :=
  | T : prop                    (* True *)
  | F : prop                    (* False *)
  | Var : nat -> prop           (* Propositional variable *)
  | Not : prop -> prop          (* Negation *)
  | And : prop -> prop -> prop  (* Conjunction *)
  | Or : prop -> prop -> prop   (* Disjunction *)
  | Imp : prop -> prop -> prop. (* Implication *)

  (** CNF types *)
  Definition lit : Type := (nat * bool).
  Definition clause : Type := list lit.
  Definition cnf : Type := list clause.

  (** Simple test function *)
  Definition test_cnf (phi : prop) : cnf :=
    match phi with
    | T => nil
    | _ => ((nil) :: nil)
    end.

End TestBoolean.