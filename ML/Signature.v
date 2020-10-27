Require Import Ensembles.

Record MLVariables := {
  evar : Type;
  svar : Type;
  evar_eq : forall (v1 v2 : evar), {v1 = v2} + {v1 <> v2};
  svar_eq : forall (v1 v2 : svar), {v1 = v2} + {v1 <> v2};
  (* TODO fresh generator *)
}.

Record Signature := {
  variables : MLVariables;
  symbols : Type;
  sym_eq : forall (s1 s2 : symbols), {s1 = s2} + {s1 <> s2};
}.

Definition Power (Sigma : Type) := Ensemble Sigma.
