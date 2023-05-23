From Coq Require Import ssreflect ssrfun ssrbool.

From Coq Require Import Unicode.Utf8.
From stdpp Require Import base sets.

From MatchingLogic Require Import
    Logic
    Theories.Sorts_Syntax
.

Import BoundVarSugar.
Import Definedness_Syntax.Notations.

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
    Delimit Scope ml_scope with ml. (* TODO move this somewhere else *)

    Local Notation "'(' phi1 ',ml' phi2 ')'" := 
        (patt_app (patt_app (patt_sym (inj (ml_pair s1 s2))) phi1) phi2)
        : ml_scope
    .

    Inductive AxiomName :=
    | AxPair
    | AxProjLeft
    | AxProjRight
    | AxInj
    | InversePairProj1
    | InversePairProj2
    .

    Arguments patt_forall_of_sort {Σ self} sort phi%ml_scope.

    Definition axiom (name : AxiomName) : Pattern :=
    match name with
    | AxPair =>
        patt_total_binary_function
            (patt_sym (inj (ml_pair s1 s2)))
            (patt_sym s1)
            (patt_sym s2)
            (patt_sym (inj (ml_prod s1 s2)))
    | AxProjLeft =>
        patt_total_function
            (patt_sym (inj (ml_proj1 s1 s2)))
            (patt_sym (inj (ml_prod s1 s2)))
            (patt_sym s1)
    | AxProjRight =>
        patt_total_function
            (patt_sym (inj (ml_proj1 s1 s2)))
            (patt_sym (inj (ml_prod s1 s2)))
            (patt_sym s2)
    | AxInj =>
        patt_forall_of_sort (patt_sym s1) (
            patt_forall_of_sort (patt_sym s1) (
                patt_forall_of_sort (patt_sym s2) (
                    patt_forall_of_sort (patt_sym s2) (
                        patt_imp (
                            ( b3 ,ml b1 ) =ml ( b2 ,ml b0 )%ml
                        ) (
                            patt_and (
                                b3 =ml b2
                            ) (
                                b1 =ml b0
                            )
                        )
                    )
                )
            )
        )
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