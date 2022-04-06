From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From stdpp Require Import base tactics sets.

From MatchingLogic.Utils
Require Import
    extralibrary
    stdpp_ext
.

From MatchingLogic
Require Import
    Signature
    Pattern
    ApplicationContext
    Substitution
.


  Lemma free_evar_subst_subst_ctx_independent {Σ : Signature} AC ϕ Xfr1 Xfr2:
  Xfr1 ∉ free_evars_ctx AC ->
  Xfr2 ∉ free_evars_ctx AC ->
  free_evar_subst (subst_ctx AC (patt_free_evar Xfr1)) ϕ Xfr1 =
  free_evar_subst (subst_ctx AC (patt_free_evar Xfr2)) ϕ Xfr2.
Proof.
  intros HXfr1 HXfr2.
  induction AC.
  - simpl.
    destruct (decide (Xfr1 = Xfr1)), (decide (Xfr2 = Xfr2)); simpl; try contradiction.
    reflexivity.
  - simpl in HXfr1. simpl in HXfr2.
    feed specialize IHAC.
    { set_solver. }
    { set_solver. }
    simpl. rewrite IHAC.
    rewrite [free_evar_subst p ϕ Xfr1]free_evar_subst_no_occurrence.
    { apply count_evar_occurrences_0. set_solver. }
    rewrite [free_evar_subst p ϕ Xfr2]free_evar_subst_no_occurrence.
    { apply count_evar_occurrences_0. set_solver. }
    reflexivity.
  - simpl in HXfr1. simpl in HXfr2.
    feed specialize IHAC.
    { set_solver. }
    { set_solver. }
    simpl. rewrite IHAC.
    rewrite [free_evar_subst p ϕ Xfr1]free_evar_subst_no_occurrence.
    { apply count_evar_occurrences_0. set_solver. }
    rewrite [free_evar_subst p ϕ Xfr2]free_evar_subst_no_occurrence.
    { apply count_evar_occurrences_0. set_solver. }
    reflexivity.
Qed.
