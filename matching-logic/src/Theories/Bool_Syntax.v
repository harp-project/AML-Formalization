From Coq Require Import ssreflect ssrfun ssrbool.

Require Import Setoid.
From Coq Require Import Unicode.Utf8.
From Coq.Logic Require Import Classical_Prop FunctionalExtensionality.
From Coq.Classes Require Import Morphisms_Prop.

From stdpp Require Import base sets.

From MatchingLogic Require Export Logic.
Require Export MatchingLogic.Theories.Sorts_Syntax.

Inductive Symbols : Set :=
| sBool
| sTrue
| sFalse
| sAnd
| sNeg.

Global Instance Symbols_eqdec : EqDecision Symbols.
Proof. unfold EqDecision. intros x y. unfold Decision. destruct x; decide equality. (*solve_decision.*) Defined.

Import MatchingLogic.Logic.Notations.
Import MatchingLogic.Theories.Definedness_Syntax.Notations.
Import MatchingLogic.Theories.Sorts_Syntax.Notations.
Import BoundVarSugar.

Section bool_syntax.
  Open Scope ml_scope.
  Context {Σ : Signature}.

  Class Syntax :=
    { inj : Symbols -> symbols;
      imported_sorts : Sorts_Syntax.Syntax;
    }.

  #[global] Existing Instance imported_definedness.
  #[global] Existing Instance imported_sorts.

  Context {self : Syntax}.

  Definition mlBool := patt_sym (inj sBool).
  Definition mlTrue := patt_sym (inj sTrue).
  Definition mlFalse := patt_sym (inj sFalse).
  Definition mlsBAnd := patt_sym (inj sAnd).
  Definition mlsBNeg := patt_sym (inj sNeg).

  Definition mlBAnd (φ1 φ2 : Pattern) : Pattern :=
    (mlsBAnd $ φ1) $ φ2.
  Definition mlBNeg (φ : Pattern) : Pattern :=
    mlsBNeg $ φ.

End bool_syntax.

Section bools.
  Context {Σ : Signature}.
  Context {self : Syntax}.
  Open Scope ml_scope.

  Obligation Tactic := idtac.

  #[global]
  Program Instance Unary_inhabitant_set : Unary mlBNeg := {}.
  Next Obligation.
    intros. repeat rewrite pm_correctness. reflexivity.
  Defined.
  Next Obligation.
    wf_auto2.
  Qed.
  Next Obligation.
    wf_auto2.
  Qed.
  Next Obligation.
    wf_auto2.
  Qed.

  #[global]
  Program Instance Binary_sorted_neg : Binary mlBAnd := {}.
  Next Obligation.
    intros. repeat rewrite pm_correctness. reflexivity.
  Defined.
  Next Obligation.
    intros. wf_auto2.
  Qed.
  Next Obligation.
    intros. wf_auto2.
  Qed.
  Next Obligation.
    intros. wf_auto2.
  Qed.

End bools.

Module Notations.
  Notation "phi '&&ml' psi" := (mlBAnd phi psi) (at level 40, left associativity) : ml_scope.
  Notation "'!b' phi" := (mlBNeg phi) (at level 60) : ml_scope.
End Notations.

Section axioms.
  Import Notations.
  Open Scope ml_scope.
  Context
    {Σ : Signature}
    {syntax : Syntax}.

  Inductive AxiomName := 
  | AxFunTrue
  | AxFunFalse
  | AxFunAnd
  | AxFunNeg
  | AxNoConfusion
  | AxInductiveDomain
  (* TODO: extend this with the DEFINITION axioms from "ML explained" *)
  | AxDefNegTrue
  | AxDefNegFalse
  | AxDefAndRightTrue
  | AxDefAndRightFalse
  | AxDefAndLeftTrue
  | AxDefAndLeftFalse
  .

  Definition axiom (name : AxiomName) : Pattern :=
    match name with
    | AxFunTrue => ex mlBool , mlTrue =ml b0
    | AxFunFalse => ex mlBool , mlFalse =ml b0
    | AxFunAnd =>
      all mlBool , all mlBool , ex mlBool , b1 &&ml b2 =ml b0
    | AxFunNeg => all mlBool , ex mlBool , !b b1 =ml b0
    | AxNoConfusion => all mlBool, !(mlTrue =ml mlFalse)
    | AxInductiveDomain => 〚 mlBool 〛 =ml mlTrue or mlFalse
    (* TODO: extend this with the DEFINITION axioms from "ML explained" *)
    | AxDefNegTrue =>  !b mlTrue =ml mlFalse
    | AxDefNegFalse => !b mlFalse =ml mlTrue 
    
    | AxDefAndRightTrue =>  
      all mlBool, b0 &&ml mlTrue =ml b0 
    | AxDefAndRightFalse =>
      all mlBool, b0 &&ml mlFalse =ml mlFalse
    | AxDefAndLeftTrue =>
      all mlBool, mlTrue &&ml b0 =ml b0
    | AxDefAndLeftFalse =>
      all mlBool, mlFalse &&ml b0 =ml mlFalse
    end.

  Program Definition named_axioms : NamedAxioms :=
    {|
      NAName := AxiomName;
      NAAxiom := axiom;
    |}.
  Next Obligation.
    destruct name; simpl; wf_auto2.
  Qed.

  Definition theory := Definedness_Syntax.theory ∪
                       theory_of_NamedAxioms named_axioms.


End axioms.