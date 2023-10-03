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

Inductive Symbols {Σ : Signature} (s1 s2 : Pattern) :=
| ml_sym_lookup
| ml_sym_product_symbols (s : ProductSort.Symbols s1 s2)
.


#[global]
Instance Symbols_eqdec {Σ : Signature} s1 s2 : EqDecision (Symbols s1 s2).
Proof. solve_decision. Defined.

Class Syntax {Σ : Signature} (s1 s2 : Pattern) :=
{
    (* imported_product :: ProductSort.Syntax s1 s2; *)
    imported_sorts : Sorts_Syntax.Syntax ;
    sym_inj: Symbols s1 s2 -> symbols;
    sym_inj_inj: Inj (=) (=) sym_inj;
}.

(*#[global] Existing Instance imported_product.*)
#[global] Existing Instance imported_sorts.
#[global] Existing Instance sym_inj_inj.

Section pswl.
    Context
      {Σ : Signature}
      (s1 s2 : Pattern)
      (wfs1 : well_formed s1 = true)
      (wfs2 : well_formed s2 = true)
      {syntax : Syntax s1 s2}
    .
    Import Notations.
    Open Scope ml_scope.
    Delimit Scope ml_scope with ml. (* TODO move this somewhere else *)

    (* Typelass resolution does not terminate on this input.
       TODO: figure out why.
       So I will just define the instance via ltac.
    *)
    (*
    #[global]
    Instance imported_product
        : (ProductSort.Syntax s1 s2)
    := {|
        ProductSort.imported_sorts := @imported_sorts Σ s1 s2 syntax;
    |}.
    *)
    #[global]
    Instance product_syntax
        : (ProductSort.Syntax s1 s2)
    .
    Proof.
        unshelve(econstructor).
        {
            intros s.
            exact (sym_inj (ml_sym_product_symbols s1 s2 s)).
        }
        {
            exact imported_sorts.
        }
        {
            abstract(
                intros x y Hxy;
                apply sym_inj_inj in Hxy;
                inversion Hxy;
                subst; reflexivity
            ).
        }
    Defined.

    Definition ml_lookup (ϕ k : Pattern)
        := patt_app (patt_app (patt_sym (sym_inj (ml_sym_lookup s1 s2))) ϕ) k
    .

    Inductive AxiomName :=
    | AxKeyValue
    .

    Definition axiom (name : AxiomName) : Pattern :=
    match name with
    | AxKeyValue =>
        all s1, (
            all s2, (
                all s1, (
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