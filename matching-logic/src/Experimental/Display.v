From Coq Require Import ssreflect ssrfun ssrbool.

From stdpp Require Import base gmap natmap option.
From MatchingLogic Require Import
    Signature
    Syntax
.

Require Import String.

Inductive DisplayedPattern {Sym : MLSymbols} : Set :=
| dpatt_evar (x : string)
| dpatt_svar (X : string)
| dpatt_sym (sigma : symbols)
| dpatt_app (phi1 phi2 : DisplayedPattern)
| dpatt_bott
| dpatt_imp (phi1 phi2 : DisplayedPattern)
| dpatt_exists (x : string) (phi : DisplayedPattern)
| dpatt_mu (X : string) (phi : DisplayedPattern)
.

Fixpoint display_aux
  {Σ : Signature}
  (bevmap : list string)
  (bsvmap : list string)
  (fevmap : gmap evar string)
  (fsvmap : gmap svar string)
  (default_name : string)
  (names_supply : list string)
  (ϕ : Pattern)
  : DisplayedPattern :=
  match ϕ with
  | patt_bound_evar n
    => dpatt_evar (default default_name (bevmap !! n))
  | patt_bound_svar n
    => dpatt_svar (default default_name (bsvmap !! n))
  | patt_free_evar x
    => dpatt_evar (default default_name (fevmap !! x))
  | patt_free_svar x
    => dpatt_svar (default default_name (fsvmap !! x))
  | patt_sym s => dpatt_sym s
  | patt_bott => dpatt_bott
  | patt_imp ϕ₁ ϕ₂
    => dpatt_imp
        (display_aux bevmap bsvmap fevmap fsvmap default_name names_supply ϕ₁)
        (display_aux bevmap bsvmap fevmap fsvmap default_name names_supply ϕ₂)
  | patt_app ϕ₁ ϕ₂
    => dpatt_app
        (display_aux bevmap bsvmap fevmap fsvmap default_name names_supply ϕ₁)
        (display_aux bevmap bsvmap fevmap fsvmap default_name names_supply ϕ₂)
  | patt_exists ϕ'
    => let name := (default default_name (head names_supply)) in
      dpatt_exists
        name
        (display_aux (name::bevmap) bsvmap fevmap fsvmap default_name (tail names_supply) ϕ')
  | patt_mu ϕ'
    => let name := (default default_name (head names_supply)) in
      dpatt_mu
        name
        (display_aux bevmap (name::bsvmap) fevmap fsvmap default_name (tail names_supply) ϕ')
  end
  .

Definition display
  {Σ : Signature}
  (fevmap : gmap evar string)
  (fsvmap : gmap svar string)
  (names_supply : list string)
  (ϕ : Pattern)
  : DisplayedPattern :=
  display_aux [] [] fevmap fsvmap "" names_supply ϕ
.