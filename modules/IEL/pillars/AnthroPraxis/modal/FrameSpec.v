From Coq Require Import Program.
From PXLs Require Import PXLv3.
Set Implicit Arguments.

Module AnthroPraxis.
  (* Agents, roles, norms (abstract) *)
  Parameter Agent : Type.
  Parameter Role  : Type.
  Parameter plays : Agent -> Role -> Prop.
  (* Social accessibility *)
  Parameter R_soc : form -> form -> Prop.
End AnthroPraxis.
