Require Import List.
Require Import Ensembles.

(*Definition or2bool*)
Definition or2bool {A}{B}(x : {A} + {B}) :=
  match x with
  | left _ => true
  | right _ => false
  end.

  
Record MLVariables := {
  evar : Type;
  svar : Type;
  evar_eq : forall (v1 v2 : evar), {v1 = v2} + {v1 <> v2};
  svar_eq : forall (v1 v2 : svar), {v1 = v2} + {v1 <> v2};
  (* TODO fresh generator *)
  evar_fresh : list evar -> evar;
  svar_fresh : list svar -> svar;
  evar_fresh_is_fresh : forall l,
      ~List.In (evar_fresh l) l;
  svar_fresh_is_fresh : forall l,
      ~List.In (svar_fresh l) l
}.

Record Signature := {
  variables : MLVariables;
  symbols : Type;
  sym_eq : forall (s1 s2 : symbols), {s1 = s2} + {s1 <> s2};
}.

Definition Power (Sigma : Type) := Ensemble Sigma.
