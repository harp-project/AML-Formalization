Require Import List.
Require Import Ensembles.
Require Import Coq.Strings.String.
From stdpp Require Import countable.

(*Definition or2bool*)
Definition or2bool {A}{B}(x : {A} + {B}) :=
  match x with
  | left _ => true
  | right _ => false
  end.

  
Class MLVariables := {
  evar : Type;
  svar : Type;
  (* TODO remove _eq, use _eqdec instead *)
  evar_eq : forall (v1 v2 : evar), {v1 = v2} + {v1 <> v2};
  svar_eq : forall (v1 v2 : svar), {v1 = v2} + {v1 <> v2};
  evar_eqdec : EqDecision evar;
  evar_countable : Countable evar;
  svar_eqdec : EqDecision svar;
  svar_countable : Countable svar;
  (* TODO fresh generator *)
  evar_fresh : list evar -> evar;
  svar_fresh : list svar -> svar;
  evar_fresh_is_fresh : forall l,
      ~List.In (evar_fresh l) l;
  svar_fresh_is_fresh : forall l,
      ~List.In (svar_fresh l) l;
  (* We need a way to build named variables from strings *)
  nevar : string -> evar;
  nsvar : string -> svar;
  nevar_inj : forall (s1 s2 : string), nevar s1 = nevar s2 -> s1 = s2;
  nsvar_inj : forall (s1 s2 : string), nsvar s1 = nsvar s2 -> s1 = s2;
}.

Class Signature := {
  variables : MLVariables;
  symbols : Type;
  sym_eq : forall (s1 s2 : symbols), {s1 = s2} + {s1 <> s2};
}.

Definition Power (Sigma : Type) := Ensemble Sigma.
