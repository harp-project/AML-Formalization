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

  Definition is_positive_context (C : PatternCtx) := ~~ evar_has_negative_occurrence (pcEvar C) (pcPattern C).

  Definition is_negative_context (C : PatternCtx) := ~~ evar_has_positive_occurrence (pcEvar C) (pcPattern C).

End with_signature.