From Coq Require Import ssreflect ssrfun ssrbool.

From Coq Require Import String.

From stdpp Require Import
  countable
  infinite
.

Class MLVariables := {
  evar : Set;
  svar : Set;
  evar_eqdec :> EqDecision evar;
  evar_countable :> Countable evar;
  evar_infinite :> Infinite evar;
  svar_eqdec :> EqDecision svar;
  svar_countable :> Countable svar;
  svar_infinite :> Infinite svar;

  string2evar : string -> evar ;
  string2evar_inj : Inj (=) (=) string2evar ;
  string2svar : string -> svar ;
  string2svar_inj : Inj (=) (=) string2svar ;

}.

Class MLSymbols := {
  symbols : Set;
  sym_eqdec :> EqDecision symbols;
  sym_countable :> Countable symbols;
}.

Class Signature := {
  variables :> MLVariables;
  ml_symbols :> MLSymbols;
}.

(* Later we will define signature morphisms in some file *)
