From Coq Require Import ssreflect ssrfun ssrbool.

From stdpp Require Import base tactics sets.

From MatchingLogic.Utils
Require Import
    extralibrary
.

From MatchingLogic
Require Import
    Signature
    Pattern
    Substitution
.

Import MatchingLogic.Substitution.Notations.

Section with_signature.
    Context {Σ : Signature}.

    Record PatternCtx : Type :=
    { pcEvar : evar ;
      pcPattern : Pattern;
    }.

  Definition is_linear_context (C : PatternCtx) := count_evar_occurrences (pcEvar C) (pcPattern C) = 1.

  Definition PC_wf C := well_formed (pcPattern C).

  Open Scope ml_scope.
  Definition emplace (ctx : PatternCtx) (p : Pattern) : Pattern :=
    (pcPattern ctx)^[[evar: (pcEvar ctx) ↦ p]].

  Fixpoint variable_occurs_positively (x : evar) (phi : Pattern) : bool :=
    match phi with
    | patt_free_evar y => match decide (x = y) with left _ => true | right _ => false end
    | patt_free_svar X => false
    | patt_bound_evar _ => false
    | patt_bound_svar _ => false                             
    | patt_bott => false
    | patt_sym _ => false
    | patt_imp phi1 phi2 => (variable_occurs_negatively x phi1) || (variable_occurs_positively x phi2)
    | patt_app phi1 phi2 => (variable_occurs_positively x phi1) || (variable_occurs_positively x phi2)
    | patt_exists phi' => variable_occurs_positively x phi'
    | patt_mu phi' => variable_occurs_positively x phi'
    end
  with variable_occurs_negatively (x : evar) (phi : Pattern) : bool :=
         match phi with
         | patt_free_evar y => false
         | patt_free_svar X => false
         | patt_bound_evar _ => false
         | patt_bound_svar _ => false                             
         | patt_bott => false
         | patt_sym _ => false
         | patt_imp phi1 phi2 => (variable_occurs_positively x phi1) || (variable_occurs_negatively x phi2)
         | patt_app phi1 phi2 => (variable_occurs_negatively x phi1) || (variable_occurs_negatively x phi2)
         | patt_exists phi' => variable_occurs_negatively x phi'
         | patt_mu phi' => variable_occurs_negatively x phi'         
    end.

  Definition is_positive_context (C : PatternCtx) := ~~ variable_occurs_negatively (pcEvar C) (pcPattern C).

  Definition is_negative_context (C : PatternCtx) := ~~ variable_occurs_positively (pcEvar C) (pcPattern C).
  
  
End with_signature.
