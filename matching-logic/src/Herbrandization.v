From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


From stdpp Require Import base.
From MatchingLogic Require Import Syntax ProofSystem extralibrary.

Fixpoint subst_evar_for_symbol {Σ : Signature} (σ : symbols) (x : evar) (ϕ : Pattern) :=
  match ϕ with
  | patt_bott => patt_bott
  | patt_free_evar y => patt_free_evar y
  | patt_free_svar Y => patt_free_svar Y
  | patt_bound_evar n => patt_bound_evar n
  | patt_bound_svar N => patt_bound_svar N
  | patt_sym σ' => if (decide (σ = σ')) is left _ then patt_free_evar x else patt_sym σ'
  | patt_app ϕ₁ ϕ₂ => patt_app (subst_evar_for_symbol σ x ϕ₁) (subst_evar_for_symbol σ x ϕ₂)
  | patt_imp ϕ₁ ϕ₂ => patt_imp (subst_evar_for_symbol σ x ϕ₁) (subst_evar_for_symbol σ x ϕ₂)
  | patt_exists ϕ' => patt_exists (subst_evar_for_symbol σ x ϕ')
  | patt_mu ϕ' => patt_mu (subst_evar_for_symbol σ x ϕ')
  end.
