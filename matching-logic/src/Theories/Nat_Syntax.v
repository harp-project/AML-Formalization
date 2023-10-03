From Coq Require Import ssreflect ssrfun ssrbool.

From Ltac2 Require Import Ltac2.

From Coq Require Import String Ensembles Setoid.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.Classical_Prop.
From Coq.Logic Require Import FunctionalExtensionality Eqdep_dec.
From Coq.Classes Require Import Morphisms_Prop.
From Coq.Unicode Require Import Utf8.
From Coq.micromega Require Import Lia.

From MatchingLogic Require Import Logic.
From MatchingLogic.Theories Require Import Definedness_Syntax Definedness_ProofSystem.
From MatchingLogic.Utils Require Import stdpp_ext.

Require Import MatchingLogic.wftactics.

From stdpp Require Import base fin_sets sets propset proof_irrel option list.

Import extralibrary.

Import MatchingLogic.Logic.Notations.
Import MatchingLogic.Theories.Definedness_Syntax.Notations.

Set Default Proof Mode "Classic".

From MatchingLogic Require Import
  Theories.DeductionTheorem
  Theories.Sorts_Syntax
  FOEquality_ProofSystem
  Sorts_ProofSystem
.

Import MatchingLogic.Theories.Sorts_Syntax.Notations.

Open Scope ml_scope.
Open Scope string_scope.
Open Scope list_scope.


Section nat_syntax.

  Context {Σ : Signature}.

  Inductive Symbols := sNat | sZero | sSucc.

  Class Syntax :=
    { inj : Symbols -> symbols;
      imported_sorts : Sorts_Syntax.Syntax;
    }.
  
  #[global] Existing Instance imported_sorts.

  Context {self : Syntax}.

  Definition Nat := patt_sym (inj sNat).
  Definition Zero := patt_sym (inj sZero).
  Definition Succ := patt_sym (inj sSucc).

End nat_syntax.


Section nat.
  Context
    {Σ : Signature}
    {syntax : Syntax}
  .

  Inductive AxiomName := 
  | AxFun1
  | AxFun2
  | AxNoConfusion1
  | AxNoConfusion2
  | AxInductiveDomain.

  Definition axiom (name : AxiomName) : Pattern :=
    match name with
    | AxFun1 => ex Nat , Zero =ml b0
    | AxFun2 => all Nat, ex Nat, Succ $ b1 =ml b0
    | AxNoConfusion1 => all Nat, !(Zero =ml Succ $ b0)
    | AxNoConfusion2 => all Nat, all Nat, (Succ $ b1 =ml Succ $ b0 ---> b1 =ml b0)
    | AxInductiveDomain => 〚 Nat 〛 =ml mu , Zero or Succ $ B0
    end.

  Program Definition named_axioms : NamedAxioms :=
    {|
      NAName := AxiomName;
      NAAxiom := axiom;
    |}.
  Next Obligation.
    destruct name; simpl; wf_auto2.
  Qed.

  Definition theory := Definedness_Syntax.theory ∪ theory_of_NamedAxioms named_axioms.

End nat.