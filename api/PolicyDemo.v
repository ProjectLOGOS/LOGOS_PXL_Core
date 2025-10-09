From PXLs.API Require Import ProofToken ToolGate.
Module PolicyDemo.
  Definition Policy := True.
  Definition run (t:ProofToken.Token Policy) := ToolGate.allow _ t.
End PolicyDemo.