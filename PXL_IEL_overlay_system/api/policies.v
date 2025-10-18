From PXLs.API Require Import ProofToken ToolGate.

Module Policies.

  (* Themi: consent, scope, rate-limit *)
  Module Themi.
    Definition Consent := Prop.
    Definition Scope := Prop.
    Definition RateLimit := nat.

    Definition check_consent (c : Consent) : bool := true.
    Definition check_scope (s : Scope) : bool := true.
    Definition check_rate (r : RateLimit) : bool := true.
  End Themi.

  (* Gnosi: evidence threshold *)
  Module Gnosi.
    Definition EvidenceThreshold := nat.

    Definition check_evidence (e : EvidenceThreshold) : bool := true.
  End Gnosi.

  (* Ergo: side-effect class gates *)
  Module Ergo.
    Inductive SideEffectClass := ReadOnly | WriteLocal | Network | System.

    Definition gate_side_effect (c : SideEffectClass) : bool :=
      match c with
      | ReadOnly => true
      | WriteLocal => true
      | Network => false
      | System => false
      end.
  End Ergo.

End Policies.
