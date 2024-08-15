From Coq Require Import ssreflect ssrfun ssrbool.

From Coq Require Import Unicode.Utf8.
From stdpp Require Import base sets list.

From MatchingLogic Require Import
    Logic
    Theories.Sorts_Syntax
    Theories.ProductSort
    Theories.ProductSortWithLookup
.

Import Logic.Notations.
Import BoundVarSugar.
Import Definedness_Syntax.Notations.
Import ProductSort.Notations.

Delimit Scope ml_scope with ml. (* TODO move this somewhere else *)

Section rs.
    Context
        {Σ : Signature}
        {sorts_syntax : Sorts_Syntax.Syntax} 
    .

    Definition apply_connective (connective arg1 arg2 : Pattern) : Pattern
    := (connective ⋅ arg1 ⋅ arg2)%ml.

    Definition chain_patterns
        (connective : Pattern)
        (ps : list Pattern)
        (last : Pattern)
        : Pattern
    :=
        fold_right
            (apply_connective connective)
            last
            ps
    .

    #[local] Example chain_1_patterns:
        chain_patterns
            (⊥%ml)
            []
            (b0)
        = b0
    .
    Proof. reflexivity. Qed.

    #[local] Example chain_2_patterns:
        chain_patterns
            (⊥%ml)
            [b0]
            (b1)
        = (⊥ ⋅ b0 ⋅ b1)%ml
    .
    Proof. reflexivity. Qed.

    #[local] Example chain_3_patterns:
        chain_patterns
            (⊥%ml)
            [b0;b1]
            (b2)
        = (⊥ ⋅ b0 ⋅ (⊥ ⋅ b1 ⋅ b2))%ml
    .
    Proof. reflexivity. Qed.

    #[local] Example chain_4_patterns:
        chain_patterns
            (⊥%ml)
            [b0;b1;b2]
            (b3)
        = (⊥ ⋅ b0 ⋅ (⊥ ⋅ b1 ⋅ (⊥ ⋅ b2 ⋅ b3)))%ml
    .
    Proof. reflexivity. Qed.

    Context
        (param_sort : list Pattern)
        (ret_sort : Pattern)
    .

    (*
      This is going to be tricky.
      We need to define those three operations on lists of things:
      (1) s1 ⊗ · · · ⊗ sn ⊗ t ≡ s1 ⊗ (s2 ⊗ (· · · ⊗ (sn ⊗ t) . . . ))
      (2) ⟨ϕ1, . . . , ϕn, ϕ⟩ ≡ ⟨ϕ1, ⟨. . . , ⟨ϕn, ϕ⟩ . . .⟩⟩
      (3) ψ(ϕ1, . . . , ϕn ) ≡ ψ(ϕ1 ) . . . (ϕn ).
      
      Therefore, we need to have syntax for
      sn ⊗ t, sn-1 ⊗ sn ⊗ t, etc.
      By "syntax", we mean
      `ProductSort.Syntax s1 s2`.

      What sorts do we need?

      Case length(param_sort)=0:
        `ret_sort`

      Case length(param_sort)=1:        
        `ret_sort`
        `param_sort!!0 ⊗ ret_sort`

      Case length(param_sort)=2:        
        `ret_sort`
        `param_sort!!1 ⊗ ret_sort`
        `param_sort!!0 ⊗ (param_sort!!1 ⊗ ret_sort)`

      Case length(param_sort)=3:        
        `ret_sort`
        `param_sort!!2 ⊗ ret_sort`
        `param_sort!!1 ⊗ (param_sort!!2 ⊗ ret_sort)`
        `param_sort!!0 ⊗ (param_sort!!1 ⊗ (param_sort!!2 ⊗ ret_sort))`

      Let n=3. We need the user to provide us with something like
    *)

    
    (*
    Definition partial_sort_applications : list Pattern :=
        fold_right (fun b a => a) ret_sort param_sort
    .
    Print fold_right.

    Inductive Syntaxes :=
    | sxs_leaf
        (s_right : Pattern)
    | sxs_step
        (s_left : Pattern)
        (s_right : Pattern)
        (syntax: ProductSortWithLookup.Syntax s_left s_right)
        (next : Syntaxes)
    .

    Definition sxs_right (sxs : Syntaxes) : Pattern :=
        match sxs with
        | sxs_leaf s_right => s_right
        | sxs_step s_left s_right syntax next =>
            (mlProd(s_left, s_right))%ml    
        end
    .

    Fixpoint sxs_valid (sxs : Syntaxes) : Prop :=
        match sxs with
        | sxs_leaf _ => True
        | sxs_step s_left s_right syntax next =>
            s_right = sxs_right next /\ sxs_valid next
        end
    .

        *)
End rs.