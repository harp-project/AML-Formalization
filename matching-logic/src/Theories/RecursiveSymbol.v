From Coq Require Import ssreflect ssrfun ssrbool.

From Coq Require Import Unicode.Utf8.
From stdpp Require Import base sets list.

From MatchingLogic Require Import
    Logic
    Theories.Sorts_Syntax
    Theories.ProductSort
    Theories.ProductSortWithLookup
.

Import BoundVarSugar.
Import Definedness_Syntax.Notations.
Import ProductSort.Notations.

Delimit Scope ml_scope with ml. (* TODO move this somewhere else *)

Section rs.
    Context
        {Σ : Signature}
        {sorts_syntax : Sorts_Syntax.Syntax} 
        (param_sort : list symbols)
        (ret_sort : symbols)
    .

    Inductive Intermediate :=
    | i_leaf
        (s_right : symbols)
    | i_step
        (s_left : symbols)
        (s_right : Pattern)
        (syntax: ProductSortWithLookup.Syntax s_left s_right)
        (next : Intermediate)
    .

    Definition im_right (im : Intermediate) : Pattern :=
        match im with
        | i_leaf s_right => patt_sym s_right
        | i_step s_left s_right syntax next =>
            (mlProd(s_left, s_right))%ml    
        end
    .

    Fixpoint im_valid (im : Intermediate) : Prop :=
        match im with
        | i_leaf _ => True
        | i_step s_left s_right syntax next =>
            s_right = im_right next
        end
    .



    Definition combine (im : Intermediate) (psort : symbol) :=
        i_
    .
    
    (*
      This is going to be tricky.
      We need to define those three operations on lists of things:
      (1) s1 ⊗ · · · ⊗ sn ⊗ t ≡ s1 ⊗ (s2 ⊗ (· · · ⊗ (sn ⊗ t) . . . ))
      (2) ⟨ϕ1, . . . , ϕn, ϕ⟩ ≡ ⟨ϕ1, ⟨. . . , ⟨ϕn, ϕ⟩ . . .⟩⟩
      (3) ψ(ϕ1, . . . , ϕn ) ≡ ψ(ϕ1 ) . . . (ϕn ).
      However, for these we need to have an instance of
      `ProductSort.Syntax s1 s2` but for any consecutive s1 s2 from the list.

    
    *)

(*

    Fixpoint im_valid (im : Intermediate) : Prop :=
        match im with

    Check fold_right.
    Definition prod_chain
        := fold_right (*...*)
    *)


End rs.