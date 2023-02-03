From Coq Require Import ssreflect ssrfun ssrbool.

From stdpp Require Import base pmap gmap fin_maps finite.
From MatchingLogic Require Import Syntax.

Require Import String.

Inductive DisplayedPattern {Sym : MLSymbols} : Set :=
| npatt_evar (x : evar)
| npatt_svar (X : svar)
| npatt_sym (sigma : symbols)
| npatt_app (phi1 phi2 : DisplayedPattern)
| npatt_bott
| npatt_imp (phi1 phi2 : DisplayedPattern)
| npatt_exists (x : evar) (phi : DisplayedPattern)
| npatt_mu (X : svar) (phi : DisplayedPattern)
.
