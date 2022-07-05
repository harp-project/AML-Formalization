From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From stdpp Require Import countable infinite.
From stdpp Require Import pmap gmap mapset fin_sets propset.

Class MLVariables := {
  evar : Set;
  svar : Set;
  evar_eqdec :> EqDecision evar;
  evar_countable :> Countable evar;
  evar_infinite :> Infinite evar;
  svar_eqdec :> EqDecision svar;
  svar_countable :> Countable svar;
  svar_infinite :> Infinite svar;
}.

Class Signature := {
  variables :> MLVariables;
  symbols : Set;
  sym_eqdec :> EqDecision symbols;
  sym_countable :> Countable symbols;
}.

(* Later we will define signature morphisms in some file *)
