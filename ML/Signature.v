Require Import Ensembles.
Record Signature := {
  symbols : Type;
}.

Definition Power (Sigma : Type) := Ensemble Sigma.
