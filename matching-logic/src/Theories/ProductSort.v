From Coq Require Import ssreflect ssrfun ssrbool.

From Coq Require Import Unicode.Utf8.
From stdpp Require Import base sets.

From MatchingLogic Require Import
    Logic
    Theories.Sorts_Syntax
.

Inductive Symbols {Σ : Signature} (s1 s2 : symbols) :=
| ml_prod
| ml_pair
| ml_proj1
| ml_proj2
.

#[global]
Instance Symbols_eqdec {Σ : Signature} s1 s2 : EqDecision (Symbols s1 s2).
Proof. solve_decision. Defined.

Class Syntax {Σ : Signature} (s1 s2 : symbols) :=
{
    imported_sorts :: Sorts_Syntax.Syntax;
    inj: Symbols s1 s2 -> symbols;
    inj_inj: Inj (=) (=) inj;
}.



Section sorts.
    Context
      {Σ : Signature}
      (s1 s2 : symbols)
      {syntax : Syntax s1 s2}
    .
    Import Notations.
    Open Scope ml_scope.



    Inductive AxiomName :=
    | AxPair
    | AxProjLeft
    | AxProjRight
    | AxInj
    | InversePairProj1
    | InversePairProj2
    .

    Definition axiom (name : AxiomName) : Pattern :=
    match name with
    | AxPair =>
        patt_total_binary_function
            (patt_sym (inj (ml_pair s1 s2)))
            (patt_sym s1)
            (patt_sym s2)
            (patt_sym (inj (ml_prod s1 s2)))
    end.

    Program Definition named_axioms : NamedAxioms :=
    {| NAName := AxiomName;
        NAAxiom := axiom;
    |}.
    Next Obligation.
    destruct name; simpl; wf_auto2.
    Qed.

Definition theory := theory_of_NamedAxioms named_axioms.

End sorts.