From Coq Require Import Program.
From PXLs Require Import PXLv3.
Set Implicit Arguments.
Module BioPraxis.
  Parameter Organism : Type.
  Parameter Evolves : Organism -> Organism -> Prop.
End BioPraxis.
