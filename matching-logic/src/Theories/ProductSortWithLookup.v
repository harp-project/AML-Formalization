From Coq Require Import ssreflect ssrfun ssrbool.

From Coq Require Import Unicode.Utf8.
From stdpp Require Import base sets list.

From MatchingLogic Require Import
    Logic
    Theories.Sorts_Syntax
    Theories.ProductSort
.

Import BoundVarSugar.
Import Definedness_Syntax.Notations.
Import Sorts_Syntax.Notations.
Import ProductSort.Notations.

Inductive Symbols {Σ : Signature} (s1 s2 : symbols) :=
| ml_sym_lookup
.


#[global]
Instance Symbols_eqdec {Σ : Signature} s1 s2 : EqDecision (Symbols s1 s2).
Proof. unfold EqDecision. intros x y. unfold Decision. destruct x. decide equality. (*solve_decision. -- crashes*) Defined.

Class Syntax {Σ : Signature} (s1 s2 : symbols) :=
{
    imported_product :: ProductSort.Syntax s1 s2;
    inj: Symbols s1 s2 -> symbols;
    inj_inj: Inj (=) (=) inj;
}.

#[global] Existing Instance imported_product.

Section pswl.
    Context
      {Σ : Signature}
      (s1 s2 : symbols)
      {syntax : Syntax s1 s2}
    .
    Import Notations.
    Open Scope ml_scope.
    Delimit Scope ml_scope with ml. (* TODO move this somewhere else *)

    Definition ml_lookup (ϕ k : Pattern)
        := patt_app (patt_app (patt_sym (inj (ml_sym_lookup s1 s2))) ϕ) k
    .

    Inductive AxiomName :=
    | AxKeyValue
    .

    Definition axiom (name : AxiomName) : Pattern :=
    match name with
    | AxKeyValue =>
        all (patt_sym s1), (
            all (patt_sym s2), (
                all (patt_sym s1), (
                    ml_lookup (mlPair { s1 , s2 } (b2 , b1)) b0 =ml (patt_and (b2 =ml b0) b1)
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

    Definition Γprodl := theory_of_NamedAxioms named_axioms.

End pswl.