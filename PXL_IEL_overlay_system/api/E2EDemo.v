From PXLs.API Require Import ProofToken ToolGate PolicyDemo.

Module E2EDemo.
  (* E2E runtime exercise: gate a read-only tool *)

  Definition read_only_tool : unit :=
    Print "Read-only tool executed: displaying system info".

  Definition demo :=
    let token := ProofToken.create_token "conservative_theorem" "b39a8d8" "coqchk_passed" in
    let _ := PolicyDemo.run token in
    read_only_tool.

End E2EDemo.
