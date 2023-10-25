From Coq Require Import ssreflect ssrfun ssrbool.

Require Import Setoid.
From Coq Require Import Unicode.Utf8.
From Coq.Logic Require Import Classical_Prop FunctionalExtensionality.
From Coq.Classes Require Import Morphisms_Prop.

From stdpp Require Import base sets.

From MatchingLogic Require Export
    Logic
    Utils.extralibrary
    Theories.Bool_Syntax.

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