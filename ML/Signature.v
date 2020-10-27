Require Import Ensembles.

Record MLVariables := {
  somethingtodo : Type;
}.

Record Signature := {
  symbols : Type;
}.

Definition Power (Sigma : Type) := Ensemble Sigma.
