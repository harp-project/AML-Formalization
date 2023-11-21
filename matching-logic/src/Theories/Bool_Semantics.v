From Coq Require Import ssreflect ssrfun ssrbool.

Require Import Setoid.
From Coq Require Import Unicode.Utf8.
From Coq.Logic Require Import Classical_Prop FunctionalExtensionality.
From Coq.Classes Require Import Morphisms_Prop.

From stdpp Require Import base sets.

From MatchingLogic Require Export
    Logic
    Utils.extralibrary
    Theories.Bool_Syntax
    Theories.ModelExtension.

Import MatchingLogic.Theories.Definedness_Syntax.Notations.
Import MatchingLogic.Theories.Bool_Syntax.Notations.
Import BoundVarSugar.
Import MatchingLogic.Semantics.Notations.

Section with_model.
  Context
    {Σ : Signature}
    {syntax : Bool_Syntax.Syntax}
    {M : Model}.
  Open Scope ml_scope.

  Hypothesis M_satisfies_theory : M ⊨ᵀ Bool_Syntax.theory.

End with_model.

(* Section bool_model.

  Instance default_boolΣ : Signature := {
    variables := StringMLVariables;
    ml_symbols := Build_MLSymbols Symbols _ _;
  }.

  Instance default_bool_syntax : Bool_Syntax.Syntax := {
     inj := id;
     imported_sorts := 
  }.

End bool_model. *)