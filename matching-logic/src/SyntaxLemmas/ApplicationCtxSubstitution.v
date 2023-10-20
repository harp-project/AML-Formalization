From Coq Require Import ssreflect ssrfun ssrbool.

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

Import MatchingLogic.Substitution.Notations.

Section with_signature.
  Open Scope ml_scope.
  Context {Σ : Signature}.

  Lemma free_evar_subst_subst_ctx_independent AC ϕ Xfr1 Xfr2:
  Xfr1 ∉ free_evars_ctx AC ->
  Xfr2 ∉ free_evars_ctx AC ->
  (subst_ctx AC (patt_free_evar Xfr1))^[[evar: Xfr1 ↦ ϕ]] =
  (subst_ctx AC (patt_free_evar Xfr2))^[[evar: Xfr2 ↦ ϕ]].
Proof.
  intros HXfr1 HXfr2.
  induction AC.
  - simpl.
    destruct (decide (Xfr1 = Xfr1)), (decide (Xfr2 = Xfr2)); simpl; try contradiction.
    reflexivity.
  - simpl in HXfr1. simpl in HXfr2.
    ospecialize* IHAC.
    { set_solver. }
    { set_solver. }
    simpl. rewrite IHAC.
    rewrite [p^[[evar: Xfr1 ↦ ϕ]]]free_evar_subst_no_occurrence.
    { set_solver. }
    rewrite [p^[[evar: Xfr2 ↦ ϕ]]]free_evar_subst_no_occurrence.
    { set_solver. }
    reflexivity.
  - simpl in HXfr1. simpl in HXfr2.
    ospecialize* IHAC.
    { set_solver. }
    { set_solver. }
    simpl. rewrite IHAC.
    rewrite [p^[[evar: Xfr1 ↦ ϕ]]]free_evar_subst_no_occurrence.
    { set_solver. }
    rewrite [p^[[evar: Xfr2 ↦ ϕ]]]free_evar_subst_no_occurrence.
    { set_solver. }
    reflexivity.
Qed.

End with_signature.
