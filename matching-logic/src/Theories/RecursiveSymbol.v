From Coq Require Import ssreflect ssrfun ssrbool.

From Coq Require Import Unicode.Utf8.
From stdpp Require Import base sets list.

From MatchingLogic Require Import
    Logic
    Theories.ProductSortWithLookup
.

Import BoundVarSugar.
Import Definedness_Syntax.Notations.

Section rs.
    Context
        {Σ : Signature}
        (*{pswl_syntax : ProductSort.Syntax} *)
    .

    (*
    Check fold_right.
    Definition prod_chain (ss : list symbols) (t : symbol)
        := fold_right (*...*)
    *)

    (*
      This is going to be tricky.
      We need to define those three operations on lists of things:
      (1) s1 ⊗ · · · ⊗ sn ⊗ t ≡ s1 ⊗ (s2 ⊗ (· · · ⊗ (sn ⊗ t) . . . ))
      (2) ⟨ϕ1, . . . , ϕn, ϕ⟩ ≡ ⟨ϕ1, ⟨. . . , ⟨ϕn, ϕ⟩ . . .⟩⟩
      (3) ψ(ϕ1, . . . , ϕn ) ≡ ψ(ϕ1 ) . . . (ϕn ).
      However, for these we need to have an instance of
      `ProductSort.Syntax s1 s2` but for any consecutive s1 s2 from the list.

    
    *)

End rs.