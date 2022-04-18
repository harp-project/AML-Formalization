From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Logic.Classical_Prop Coq.Logic.FunctionalExtensionality.

From stdpp
Require Import
    base
    decidable
    propset
    fin_maps
    fin_sets
.

From MatchingLogic
Require Import
    Utils.extralibrary
    Pattern
    Syntax
    Semantics
    monotonic
.


Record ModelIsomorphism {Σ : Signature} (M₁ M₂ : Model) : Set := mkModelIsomorphism
    {
        mi_f : (Domain M₁) -> (Domain M₂) ;
        mi_inj :> Inj (=) (=) mi_f ;
        mi_surj :> Surj (=) mi_f ;
        mi_sym : ∀ (s : symbols),
            mi_f <$> (sym_interp M₁ s) = sym_interp M₂ s ;
        mi_app : ∀ (x y : Domain M₁),
            mi_f <$> (@app_interp Σ M₁ x y) = @app_interp Σ M₂ (mi_f x) (mi_f y) ;
    }.