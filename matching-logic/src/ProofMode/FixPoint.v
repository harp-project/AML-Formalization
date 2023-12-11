From Coq Require Import ssreflect ssrfun ssrbool.

From Ltac2 Require Import Ltac2.

From Coq Require Import Ensembles Bool.
From Coq.Logic Require Import FunctionalExtensionality Eqdep_dec.
From Equations Require Import Equations.

Require Import Coq.Program.Tactics.

From MatchingLogic Require Import
    ProofSystem
    Syntax
    DerivedOperators_Syntax
    ProofSystem
    IndexManipulation
    wftactics
    ProofInfo
    BasicProofSystemLemmas
.
From MatchingLogic.ProofMode Require Import Basics
                                            Propositional
                                            Firstorder.

From stdpp Require Import list tactics fin_sets coGset gmap sets.

From MatchingLogic.Utils Require Import stdpp_ext.

Import extralibrary.

Import
  MatchingLogic.Syntax.Notations
  MatchingLogic.Substitution.Notations
  MatchingLogic.DerivedOperators_Syntax.Notations
  MatchingLogic.ProofInfo.Notations
.

Set Default Proof Mode "Classic".

Open Scope ml_scope.
Open Scope string_scope.
Open Scope list_scope.


Lemma mu_monotone {Σ : Signature} Γ ϕ₁ ϕ₂ X (i : ProofInfo):
  ProofInfoLe ( (ExGen := ∅, SVSubst := {[X]}, KT := true, AKT := ~~ bound_svar_is_banned_under_mus ϕ₁^{{svar:X↦0}} 0 0)) i ->
  svar_has_negative_occurrence X ϕ₁ = false ->
  svar_has_negative_occurrence X ϕ₂ = false ->
  Γ ⊢i ϕ₁ ---> ϕ₂ using i->
  Γ ⊢i (patt_mu (ϕ₁^{{svar: X ↦ 0}})) ---> (patt_mu (ϕ₂^{{svar: X ↦ 0}}))
  using i.
Proof.
  intros pile nonegϕ₁ nonegϕ₂ Himp.
  pose proof (wfϕ12 := proved_impl_wf _ _ (proj1_sig Himp)).
  assert(wfϕ₁ : well_formed ϕ₁) by wf_auto2.
  assert(wfϕ₂ : well_formed ϕ₂) by wf_auto2.

  apply Knaster_tarski.
  { try_solve_pile. }
  { 
    wf_auto2.
  }

  pose proof (Htmp := @Svar_subst Σ Γ (ϕ₁ ---> ϕ₂) (mu, ϕ₂^{{svar: X ↦ 0}}) X i).
  ospecialize* Htmp.
  { try_solve_pile. }
  { wf_auto2. }
  { exact Himp. }
  unfold free_svar_subst in Htmp.
  simpl in Htmp.
  fold free_svar_subst in Htmp.

  pose proof (Hpf := Pre_fixp Γ (ϕ₂^{{svar: X ↦ 0}})).
  simpl in Hpf.

  unshelve (eapply (cast_proof' Γ _ _) in Hpf).
  3: { 
  erewrite bound_to_free_set_variable_subst.
    5: { apply svar_quantify_not_free. }
    4: {
     apply svar_quantify_closed_mu.
     unfold well_formed, well_formed_closed in *. destruct_and!. auto.
    }
    3: {
       apply svar_quantify_closed_mu.
       unfold well_formed, well_formed_closed in *. destruct_and!. auto.
    }
    2: lia.
    reflexivity.
  }

  2: abstract (wf_auto2).

  eapply (cast_proof' Γ) in Hpf.
  2: {
    rewrite svar_open_svar_quantify.
    { unfold well_formed, well_formed_closed in *. destruct_and!. auto. }
    reflexivity.
  }


  assert(well_formed_positive (ϕ₂^[[svar: X ↦ mu , ϕ₂^{{svar: X ↦ 0}}]]) = true).
  {
    unfold well_formed, well_formed_closed in *. destruct_and!. simpl; split_and?.
    apply wfp_free_svar_subst; auto.
    { apply svar_quantify_closed_mu. auto. }
    { simpl. split_and!.
      2: apply well_formed_positive_svar_quantify; assumption.
      apply no_negative_occurrence_svar_quantify; auto.
    }
  }

  assert(well_formed_closed_mu_aux (ϕ₂^[[svar: X ↦ mu , ϕ₂^{{svar: X ↦ 0}}]]) 0 = true).
  {
    unfold well_formed, well_formed_closed in *. destruct_and!. simpl; split_and?; auto.
    replace 0 with (0 + 0) at 3 by lia.
    apply wfc_mu_free_svar_subst; auto.
    simpl.
    apply svar_quantify_closed_mu. assumption.
  }

  assert(well_formed_closed_ex_aux (ϕ₂^[[svar: X ↦ mu , ϕ₂^{{svar: X ↦ 0}}]]) 0 = true).
  {
    unfold well_formed, well_formed_closed in *. destruct_and!. simpl; split_and?; auto.
    replace 0 with (0 + 0) at 3 by lia.
    apply wfc_ex_free_svar_subst; auto.
    simpl.
    apply svar_quantify_closed_ex. assumption.
  }

  assert(well_formed_positive (ϕ₁^[[svar: X ↦ mu , ϕ₂^{{svar: X ↦ 0}}]]) = true).
  {
    unfold well_formed, well_formed_closed in *. destruct_and!. simpl; split_and?.
    apply wfp_free_svar_subst; auto.
    { apply svar_quantify_closed_mu. auto. }
    { simpl. split_and!.
      2: apply well_formed_positive_svar_quantify; assumption.
      apply no_negative_occurrence_svar_quantify; auto.
    }
  }

  assert(well_formed_closed_mu_aux (ϕ₁^[[svar: X ↦ mu , ϕ₂^{{svar: X ↦ 0}}]]) 0 = true).
  {
    unfold well_formed, well_formed_closed in *. destruct_and!. simpl; split_and?; auto.
    replace 0 with (0 + 0) at 3 by lia.
    apply wfc_mu_free_svar_subst; auto.
    simpl.
    apply svar_quantify_closed_mu. assumption.
  }

  assert(well_formed_closed_ex_aux (ϕ₁^[[svar: X ↦ mu , ϕ₂^{{svar: X ↦ 0}}]]) 0 = true).
  {
    unfold well_formed, well_formed_closed in *. destruct_and!. simpl; split_and?; auto.
    replace 0 with (0 + 0) at 3 by lia.
    apply wfc_ex_free_svar_subst; auto.
    simpl.
    apply svar_quantify_closed_ex. assumption.
  }

  apply useBasicReasoning with (i := i) in Hpf.
  epose proof (Hsi := syllogism_meta _ _ _ Htmp Hpf).
  simpl.

  eapply (@cast_proof' Σ Γ).
  1: {
    erewrite bound_to_free_set_variable_subst with (X := X).
    5: { apply svar_quantify_not_free. }
    4: {
         apply svar_quantify_closed_mu.
         unfold well_formed, well_formed_closed in *. destruct_and!. auto.
    }
    3: {
         apply svar_quantify_closed_mu.
         unfold well_formed, well_formed_closed in *. destruct_and!. auto.
    }
    2: lia.
    reflexivity.
  }

  eapply (cast_proof' Γ).
  1: {
    rewrite svar_open_svar_quantify.
    { unfold well_formed, well_formed_closed in *. destruct_and!. auto. }
    reflexivity.
  }
  apply Hsi.
  Unshelve.
  all: abstract(wf_auto2).
Defined.

Lemma mu_iff {Σ : Signature} Γ ϕ₁ ϕ₂ X (i : ProofInfo):
  ProofInfoLe ( (ExGen := ∅, SVSubst := {[X]}, KT := true, AKT := true)) i ->
  svar_has_negative_occurrence X ϕ₁ = false ->
  svar_has_negative_occurrence X ϕ₂ = false ->
  Γ ⊢i ϕ₁ <---> ϕ₂ using i->
  Γ ⊢i (patt_mu (ϕ₁^{{svar: X ↦ 0}})) <---> (patt_mu (ϕ₂^{{svar: X ↦ 0}}))
  using i.
Proof.
  intros.
  
  apply pf_iff_split.
  { wf_auto2. }
  { wf_auto2. }
  {
    apply mu_monotone; try assumption.
    { try_solve_pile. }
    { 
      apply pf_iff_proj1 in H2.
      { exact H2. }
      { wf_auto2. }
      { wf_auto2. }
    }
  }
  {
    apply mu_monotone; try assumption.
    { try_solve_pile. }
    { 
      apply pf_iff_proj2 in H2.
      { exact H2. }
      { wf_auto2. }
      { wf_auto2. }
    }
  }
Defined.

Close Scope ml_scope.
Close Scope string_scope.
Close Scope list_scope.
