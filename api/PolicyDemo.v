From PXLs.IEL.Pillars.ThemiPraxis Require Import Core.
From PXLs.IEL.Pillars.GnosiPraxis Require Import Core.
From PXLs.API Require Import ProofToken ToolGate.
Module PolicyDemo.
  Definition Policy := True.                 (* replace with Oφ ∧ Kφ form *)
  Definition run (t:ProofToken.Token Policy) := ToolGate.allow _ t.
End PolicyDemo.