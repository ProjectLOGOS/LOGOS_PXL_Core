From PXLs.API Require Import ProofToken ToolGate.
Module PolicyDemo.
  Definition Policy := True.
  Definition run (t:ProofToken.Token Policy) :=
    let _ := Print t.(ProofToken.lemma_id) in
    let _ := Print t.(ProofToken.commit) in
    let _ := Print t.(ProofToken.coqchk_stamp) in
    let _ := ToolGate.emit_attestation t.(ProofToken.commit) t.(ProofToken.lemma_id) "placeholder_hash" t.(ProofToken.coqchk_stamp) in
    ToolGate.allow _ I.
End PolicyDemo.
