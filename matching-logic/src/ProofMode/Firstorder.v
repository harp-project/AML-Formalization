From Coq Require Import ssreflect ssrfun ssrbool.

From Ltac2 Require Import Ltac2 Control.

From Coq Require Import Ensembles Bool String.
From Coq.Logic Require Import FunctionalExtensionality Eqdep_dec.
From Equations Require Import Equations.

Require Import Coq.Program.Tactics.

From MatchingLogic Require Import
    Syntax
    DerivedOperators_Syntax
    ProofSystem
    IndexManipulation
    wftactics
    ProofInfo
    BasicProofSystemLemmas
    FreshnessManager
.
From MatchingLogic.ProofMode Require Import Basics
                                            Propositional.

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

Section with_signature.
  Context {Σ : Signature}.
  Open Scope ml_scope.
  Open Scope string_scope.
  Open Scope list_scope.

  (*
    Γ ⊢ φ₁ → φ₂
    -------------------- (x ∉ FV(φ₂))
    Γ ⊢ (∃x. φ₁) → φ₂
  *)
  Lemma Ex_gen (Γ : Theory) (ϕ₁ ϕ₂ : Pattern) (x : evar) (i : ProofInfo)
      {pile : ProofInfoLe (
              {| pi_generalized_evars := {[x]};
                 pi_substituted_svars := ∅;
                 pi_uses_kt := false ;
                 pi_uses_advanced_kt := false ;
              |}) i} :
    x ∉ free_evars ϕ₂ ->
    Γ ⊢i ϕ₁ ---> ϕ₂ using i ->
    Γ ⊢i (exists_quantify x ϕ₁ ---> ϕ₂) using i.
  Proof.
    intros Hfev [pf Hpf].
    unshelve (eexists).
    {
      apply ProofSystem.Ex_gen.
      { pose proof (pf' := pf). apply proved_impl_wf in pf'.  wf_auto2. }
      { pose proof (pf' := pf). apply proved_impl_wf in pf'.  wf_auto2. }
      { exact pf. }
      { exact Hfev. }
    }
    {
      simpl.
      constructor; simpl.
      {
        rewrite elem_of_subseteq. intros x0 Hx0.
        rewrite elem_of_gset_to_coGset in Hx0.
        rewrite elem_of_union in Hx0.
        destruct Hx0.
        {
          rewrite elem_of_singleton in H. subst.
          eapply pile_impl_allows_gen_x.
          apply pile.
        }
        {
          inversion Hpf.
          apply pwi_pf_ge.
          rewrite elem_of_gset_to_coGset.
          assumption.
        }
      }
      {
        inversion Hpf.
        apply pwi_pf_svs.
      }
      {
        inversion Hpf.
        apply pwi_pf_kt.
      }
      {
        inversion Hpf.
        apply pwi_pf_kta.
      }
    }
  Defined.

  (*
     Γ ⊢ φ[y/x] → ∃x. φ
   *)
  Lemma Ex_quan (Γ : Theory) (ϕ : Pattern) (y : evar) :
    well_formed (patt_exists ϕ) ->
    Γ ⊢i (instantiate (patt_exists ϕ) (patt_free_evar y) ---> (patt_exists ϕ))
    using BasicReasoning.
  Proof.
    intros Hwf.
    unshelve (eexists).
    {
      apply ProofSystem.Ex_quan. apply Hwf.
    }
    {
      abstract (solve_pim_simple).
    }
  Defined.

  (*
    Γ ⊢ φ
    --------------
    Γ ⊢ ∀x. φ
  *)
  Lemma universal_generalization Γ ϕ x (i : ProofInfo) :
    ProofInfoLe ( (ExGen := {[x]}, SVSubst := ∅, KT := false, AKT := false)) i ->
    well_formed ϕ ->
    Γ ⊢i ϕ using i ->
    Γ ⊢i patt_forall (ϕ^{{evar: x ↦ 0}}) using i.
  Proof.
    intros pile wfϕ Hϕ.
    unfold patt_forall.
    unfold patt_not at 1.
    replace (! ϕ^{{evar: x ↦ 0}})
      with ((! ϕ)^{{evar: x ↦ 0}})
      by reflexivity.
    apply Ex_gen.
    { exact pile. }
    { simpl. set_solver. }
    toMLGoal.
    { wf_auto2. }
    mlIntro. mlAdd Hϕ.
    mlApply "0". mlExactn 0.
  Defined.

  (*
   Γ ⊢ (∀x. φ) → φ
   DO NOT use quantification here instead of opening
  *)
  Lemma forall_variable_substitution Γ ϕ x:
    well_formed (ex, ϕ) ->
    Γ ⊢i (all, ϕ) ---> ϕ^{evar:0 ↦ x} using BasicReasoning.
  Proof.
    intros wfϕ.

    unfold patt_forall.
    apply double_neg_elim_meta.
    { wf_auto2. }
    { wf_auto2. }
    toMLGoal.
    { wf_auto2. }
    mlIntro.
    mlIntro.
    mlApply "0".
    mlIntro.
    mlApply "2".
    pose proof (Htmp := Ex_quan Γ (!ϕ) x ltac:(wf_auto2)).
    rewrite /instantiate in Htmp.
    useBasicReasoning.
    mlAdd Htmp.
    mlApply "3". mlSimpl.
    mlIntro.
    mlApply "1".
    mlExactn 4.
  Defined.

  Lemma forall_variable_substitution_meta Γ ϕ x i:
    well_formed (ex, ϕ) ->
    Γ ⊢i (all, ϕ) using i -> Γ ⊢i ϕ^{evar:0 ↦ x} using i.
  Proof.
    intros WF H. eapply MP.
    2: gapply forall_variable_substitution.
    assumption.
    try_solve_pile.
    wf_auto2.
  Defined.

  (*
    Γ ⊢ φ₁ → φ₂
    -----------------------
    Γ ⊢ (∃x. φ₁) → (∃x. φ₂)
  *)
  Lemma ex_quan_monotone Γ x ϕ₁ ϕ₂ (i : ProofInfo)
    (pile : ProofInfoLe ( (ExGen := {[x]}, SVSubst := ∅, KT := false, AKT := false)) i) :
    Γ ⊢i ϕ₁ ---> ϕ₂ using i ->
    Γ ⊢i (exists_quantify x ϕ₁) ---> (exists_quantify x ϕ₂) using i.
  Proof.
    intros H.
    pose proof (Hwf := proved_impl_wf Γ _ (proj1_sig H)).
    assert (wfϕ₁: well_formed ϕ₁ = true) by wf_auto2.
    assert (wfϕ₂: well_formed ϕ₂ = true) by wf_auto2.
    apply Ex_gen.
    { exact pile. }
    { simpl. rewrite free_evars_evar_quantify. clear. set_solver. }

    unfold exists_quantify.
    eapply syllogism_meta. 4: apply H.
    { wf_auto2. }
    { wf_auto2. }
    { wf_auto2. }
    clear H wfϕ₁ ϕ₁ Hwf.

    (* We no longer need to use [cast_proof] to avoid to ugly eq_sym terms;
       however, without [cast_proof'] the [replace] tactics does not work,
       maybe because of implicit parameters.
     *)
    eapply (cast_proof').
    {
      replace ϕ₂ with (instantiate (ex, ϕ₂^{{evar: x ↦ 0}}) (patt_free_evar x)) at 1.
      2: { unfold instantiate.
         rewrite bevar_subst_evar_quantify_free_evar.
         now do 2 apply andb_true_iff in wfϕ₂ as [_ wfϕ₂].
         reflexivity.
      }
      reflexivity.
    }
          (* i =  gpi *)
    useBasicReasoning.
    apply Ex_quan.
    abstract (wf_auto2).
  Defined.

  (*
     Γ ⊢ (∃x. φ₁ /\ φ₂) -> (∃x. φ₁)
  *)
  Lemma ex_quan_and_proj1 Γ x ϕ₁ ϕ₂:
    well_formed ϕ₁ = true ->
    well_formed ϕ₂ = true ->
    Γ ⊢i (exists_quantify x (ϕ₁ and ϕ₂)) ---> (exists_quantify x ϕ₁)
    using ( (ExGen := {[x]}, SVSubst := ∅, KT := false, AKT := false)).
  Proof.
    intros wfϕ₁ wfϕ₂.
    apply ex_quan_monotone.
    { apply pile_refl. }
    toMLGoal.
    { wf_auto2. }
    mlIntro.
    mlDestructAnd "0". mlExactn 0.
  Defined.

  (*
     Γ ⊢ (∃x. φ₁ /\ φ₂) -> (∃x. φ₂)
  *)
  Lemma ex_quan_and_proj2 Γ x ϕ₁ ϕ₂:
    well_formed ϕ₁ = true ->
    well_formed ϕ₂ = true ->
    Γ ⊢i (exists_quantify x (ϕ₁ and ϕ₂)) ---> (exists_quantify x ϕ₂)
    using ( (ExGen := {[x]}, SVSubst := ∅, KT := false, AKT := false)).
  Proof.
    intros wfϕ₁ wfϕ₂.
    apply ex_quan_monotone.
    { apply pile_refl. }
    toMLGoal.
    { wf_auto2. }
    mlIntro.
    mlDestructAnd "0".
    mlExactn 1.
  Defined.

  (*
   Γ ⊢ φ₁ → φ₂
   ----------------------------
   Γ ⊢ φ₁ → ∀x. φ₂
  *)
  (* identity *)
  Lemma strip_exists_quantify_l Γ x P Q i :
    x ∉ free_evars P ->
    well_formed_closed_ex_aux P 1 ->
    Γ ⊢i (exists_quantify x (P^{evar: 0 ↦ x}) ---> Q) using i ->
    Γ ⊢i (ex , P) ---> Q using i.
  Proof.
  intros Hx HwfcP H.
  unshelve (eapply (cast_proof' Γ _ _ _ _ H)).
  abstract (
    unfold exists_quantify;
    rewrite -> evar_quantify_evar_open by assumption;
    reflexivity
  ).
  Defined.

  (* identity *)
  Lemma strip_exists_quantify_r Γ x P Q i :
    x ∉ free_evars Q ->
    well_formed_closed_ex_aux Q 1 ->
    Γ ⊢i P ---> (exists_quantify x (Q^{evar: 0 ↦ x})) using i ->
    Γ ⊢i P ---> ex, Q using i.
  Proof.
  intros Hx HwfcP H.
  unshelve (eapply (cast_proof' Γ _ _ _ _ H)).
  abstract (
    unfold exists_quantify;
    rewrite -> evar_quantify_evar_open by assumption;
    reflexivity
  ).
  Defined.


  (* prenex-exists-and-left *)
  (*
   Γ ⊢ ((∃x. φ₁) /\ φ₂) → (∃x. (φ₁ /\ φ₂))
   *)
  Lemma prenex_exists_and_1 (Γ : Theory) ϕ₁ ϕ₂:
    well_formed (ex, ϕ₁) ->
    well_formed ϕ₂ ->
    Γ ⊢i ((ex, ϕ₁) and ϕ₂) ---> (ex, (ϕ₁ and ϕ₂))
    using ( (ExGen := {[fresh_evar (ϕ₂ ---> ex , (ϕ₁ and ϕ₂))]}, SVSubst := ∅, KT := false, AKT := false)).
  Proof.
    intros wfϕ₁ wfϕ₂.
    toMLGoal.
    { wf_auto2. }
    mlIntro. mlDestructAnd "0".
    fromMLGoal.

    remember (fresh_evar (ϕ₂ ---> (ex, (ϕ₁ and ϕ₂)))) as x.
    apply strip_exists_quantify_l with (x := x).
    { subst x. eapply evar_is_fresh_in_richer'.
      2: { apply set_evar_fresh_is_fresh'. }
      simpl. clear. set_solver.
    }
    { wf_auto2. }
    apply Ex_gen.
    { apply pile_refl. }
    { subst x. apply set_evar_fresh_is_fresh. }

    apply lhs_to_and.
    { wf_auto2. }
    { wf_auto2. }
    { wf_auto2. }

    eapply cast_proof'.
    {
      replace (ϕ₁^{evar: 0 ↦ x} and ϕ₂)
              with ((ϕ₁ and ϕ₂)^{evar: 0 ↦ x}).
      2: {
        unfold evar_open. mlSimpl.
        rewrite [bevar_subst _ _ ϕ₂]bevar_subst_not_occur.
        {
          wf_auto2.
        }
        reflexivity.
      }
      reflexivity.
    }
    useBasicReasoning.
    apply Ex_quan.
    wf_auto2.
  Defined.

  (* prenex-exists-and-right *)
  (*
     Γ ⊢ (∃x. (φ₁ /\ φ₂)) → ((∃x. φ₁) /\ φ₂)
  *)
  Lemma prenex_exists_and_2 (Γ : Theory) ϕ₁ ϕ₂:
    well_formed (ex, ϕ₁) ->
    well_formed ϕ₂ ->
    Γ ⊢i (ex, (ϕ₁ and ϕ₂)) ---> ((ex, ϕ₁) and ϕ₂)
    using ( (ExGen := {[fresh_evar ((ϕ₁ and ϕ₂))]}, SVSubst := ∅, KT := false, AKT := false)).
  Proof.
    intros wfϕ₁ wfϕ₂.
    toMLGoal.
    { wf_auto2. }
    mlIntro.
    mlSplitAnd.
    - fromMLGoal.
      remember (fresh_evar (ϕ₁ and ϕ₂)) as x.
      apply strip_exists_quantify_l with (x := x).
      { subst x. apply set_evar_fresh_is_fresh. }
      (* TODO: make wf_auto2 solve this *)
      { simpl. rewrite !andbT. split_and!.
        + wf_auto2.
        + wf_auto2.
      }
      apply strip_exists_quantify_r with (x := x).
      { subst x. eapply evar_is_fresh_in_richer'.
        2: { apply set_evar_fresh_is_fresh'. }
        simpl. clear. set_solver.
      }
      { wf_auto2. }
      apply ex_quan_monotone.
      { apply pile_refl. }

      unfold evar_open. mlSimpl.
      rewrite [bevar_subst _ _ ϕ₂]bevar_subst_not_occur.
      {
        wf_auto2.
      }
      toMLGoal.
      { wf_auto2. }
      mlIntro. mlDestructAnd "0". mlExactn 0.
    - fromMLGoal.
      remember (fresh_evar (ϕ₁ and ϕ₂)) as x.
      eapply cast_proof'.
      {
        rewrite -[ϕ₁ and ϕ₂](evar_quantify_evar_open x 0).
        { subst x. apply set_evar_fresh_is_fresh. }
        { wf_auto2. }
        reflexivity.
      }
      apply Ex_gen.
      { apply pile_refl. }
      { eapply evar_is_fresh_in_richer. 2: { subst x. apply set_evar_fresh_is_fresh'. }
        simpl. clear. set_solver.
      }

      unfold evar_open. mlSimpl.
      rewrite [bevar_subst _ _ ϕ₂]bevar_subst_not_occur.
      {
        wf_auto2.
      }
      toMLGoal.
      { wf_auto2. }
      mlIntro.
      mlDestructAnd "0".
      mlExactn 1.
  Defined.

  (*
     Γ ⊢ (∃x. (φ₁ /\ φ₂)) ↔ ((∃x. φ₁) /\ φ₂)
  *)
  Lemma prenex_exists_and_iff (Γ : Theory) ϕ₁ ϕ₂:
    well_formed (ex, ϕ₁) ->
    well_formed ϕ₂ ->
    Γ ⊢i (ex, (ϕ₁ and ϕ₂)) <---> ((ex, ϕ₁) and ϕ₂)
    using ( (ExGen := {[fresh_evar ((ϕ₁ and ϕ₂))]}, SVSubst := ∅, KT := false, AKT := false)).
  Proof.
    intros wfϕ₁ wfϕ₂.
    apply conj_intro_meta.
    { wf_auto2. }
    { wf_auto2. }
    - apply prenex_exists_and_2; assumption.
    - (* TODO we need a tactic to automate this change *)
      replace (fresh_evar (ϕ₁ and ϕ₂))
      with (fresh_evar (ϕ₂ ---> ex , (ϕ₁ and ϕ₂))).
      2: { cbn. unfold fresh_evar. apply f_equal. simpl. set_solver. }
     apply prenex_exists_and_1; assumption.
  Defined.


  (*
     This is basically [universal_generalization]
    but under an implication.
    I wonder if we could get an iterative version [forall_gen_iter]?
    Like,
    Γ ⊢ φ₁ → ... → φₖ → ψ
    ----------------------------
    Γ ⊢ φ₁ → ... → φₖ → ∀x. ψ
  *)
  Lemma forall_gen Γ ϕ₁ ϕ₂ x (i : ProofInfo):
    evar_is_fresh_in x ϕ₁ ->
    ProofInfoLe ( (ExGen := {[x]}, SVSubst := ∅, KT := false, AKT := false)) i ->
    Γ ⊢i ϕ₁ ---> ϕ₂ using i ->
    Γ ⊢i ϕ₁ ---> all, (ϕ₂^{{evar: x ↦ 0}}) using i.
  Proof.
    intros Hfr pile Himp.
    pose proof (Hwf := proved_impl_wf _ _ (proj1_sig Himp)).
    pose proof (wfϕ₁ := well_formed_imp_proj1 _ _ Hwf).
    pose proof (wfϕ₂ := well_formed_imp_proj2 _ _ Hwf).
    toMLGoal.
    { wf_auto2. }
    mlIntro.
    mlApplyMetaRaw (useBasicReasoning i (not_not_intro Γ ϕ₁ ltac:(wf_auto2))) in "0".
    fromMLGoal.
    apply modus_tollens.

    eapply cast_proof'.
    {
      replace (! ϕ₂^{{evar: x ↦ 0}})
              with ((! ϕ₂)^{{evar: x ↦ 0}})
                   by reflexivity.
      reflexivity.
    }
    apply Ex_gen.
    { exact pile. }
    { simpl. unfold evar_is_fresh_in in Hfr. clear -Hfr. set_solver. }
    apply modus_tollens; assumption.
  Defined.

  (*
   Γ ⊢ (∀x. φ) → φ

   This is the same as [forall_variable_substitution]
   except that here we have a ProofInfoLe assumption
   instead of a concrete [using] clause.
  *)
  Lemma forall_variable_substitution' Γ ϕ x (i : ProofInfo):
    well_formed (ex, ϕ) ->
    Γ ⊢i (all, ϕ) ---> ϕ^{evar:0 ↦ x} using i.
  Proof.
    intros wfϕ.
    pose proof (Htmp := forall_variable_substitution Γ ϕ x wfϕ).
    eapply useGenericReasoning. 2: apply Htmp. try_solve_pile.
  Defined.

  (*
    Γ ⊢ ∀x. φ
    ----------
    Γ ⊢ φ
  *)
  Lemma forall_elim Γ ϕ x (i : ProofInfo):
    well_formed (ex, ϕ) ->
    Γ ⊢i (all, ϕ) using i ->
    Γ ⊢i (ϕ^{evar: 0 ↦ x}) using i.
  Proof.
    intros wfϕ H.
    destruct i.
    eapply MP.
    2: eapply forall_variable_substitution'.
    2: wf_auto2.
    apply H.
  Defined.

  (*
   Γ ⊢ ∀x. (φ₁ → φ₂)
   ------------------
   Γ ⊢ (∃x. φ₁) → φ₂

  When applied backwards,
  turns an existential quantification on the LHS of an implication
  into an universal quantification on top.
  I wonder if we can get an iterative version, saying that
   Γ ⊢ ∀ x. (φ₁ → ... → φᵢ → ... → φₖ → ψ)
   ------------------
   Γ ⊢ φ₁ → ... → (∃x. φᵢ) → ... → φₖ → ψ

  Even better, I would like to have a version which says that
   Γ ⊢ ∀ x₁,...,xₘ,x. (φ₁ → ... → φᵢ → ... → φₖ → ψ)
   ------------------
   Γ ⊢ ∀ x₁,...,xₘ. (φ₁ → ... → (∃x. φᵢ) → ... → φₖ → ψ)

  because that would basically implement [mgDestructEx],
  assuming we hide the leading universal quantifiers.

  TODO: parameterize this lemma with a variable which is fresh in (ϕ₁ ---> ϕ₂),
  instead of hard-coding the fresh generation.
  *)
  Lemma prenex_forall_imp Γ ϕ₁ ϕ₂ i:
    well_formed (ex, ϕ₁) ->
    well_formed ϕ₂ ->
    ProofInfoLe ( (ExGen := {[fresh_evar (ϕ₁ ---> ϕ₂)]}, SVSubst := ∅, KT := false, AKT := false)) i ->
    Γ ⊢i (all, (ϕ₁ ---> ϕ₂)) using i ->
    Γ ⊢i (ex, ϕ₁) ---> (ϕ₂) using i.
  Proof.
    intros wfϕ₁ wfϕ₂ pile H.
    remember (fresh_evar (ϕ₁ ---> ϕ₂)) as x.
    apply (strip_exists_quantify_l Γ x).
    { subst x.
      eapply evar_is_fresh_in_richer'.
      2: { apply set_evar_fresh_is_fresh'. }
      simpl. set_solver.
    }
    { wf_auto2. }
    apply Ex_gen.
    { apply pile. }
    1: {
      subst x.
      eapply evar_is_fresh_in_richer'.
      2: { apply set_evar_fresh_is_fresh'. }
      simpl. set_solver.
    }

    eapply cast_proof'.
    {
      rewrite -[HERE in evar_open _ _ _ ---> HERE](evar_open_not_occur 0 x ϕ₂).
      {
        wf_auto2.
      }
      reflexivity.
    }
    eapply forall_elim with (x := x) in H.
    2: wf_auto2.
    unfold evar_open in *. simpl in *. exact H.
  Defined.

  Lemma Ex_gen_lifted (Γ : Theory) (ϕ₁ : Pattern) (l : hypotheses) (n : string) (g : Pattern) (x : evar)
    (i : ProofInfo) :
    evar_is_fresh_in x g ->
    evar_is_fresh_in_list x (patterns_of l) ->
    ProofInfoLe ( (ExGen := {[x]}, SVSubst := ∅, KT := false, AKT := false)) i ->
    bevar_occur ϕ₁ 0 = false ->
    mkMLGoal Σ Γ (mkNH _ n ϕ₁::l) g i -> 
    mkMLGoal Σ Γ (mkNH _ n (exists_quantify x ϕ₁)::l) g i.
  Proof.
    intros xfrg xfrl pile Hno0 H.
    mlExtractWF H1 H2.
    fromMLGoal.
    pose proof (H1' := H1).
    unfold Pattern.wf in H1. simpl in H1. apply andb_prop in H1. destruct H1 as [H11 H12].
    apply wf_ex_quan_impl_wf in H11. 2: assumption.
    unfold of_MLGoal in H. simpl in H.
    specialize (H H2).
    ospecialize* H.
    {
      unfold Pattern.wf. simpl. rewrite H11 H12. reflexivity.
    }
    apply Ex_gen.
    { apply pile. }
    2: { assumption. }
    simpl.
    apply evar_fresh_in_foldr.
    split; assumption.
  Defined.



  (* Weakening under existential *)
  Local Example ex_exists Γ ϕ₁ ϕ₂ ϕ₃ i:
    well_formed (ex, ϕ₁) ->
    well_formed (ex, ϕ₂) ->
    well_formed ϕ₃ ->
    ProofInfoLe ( (ExGen := {[(evar_fresh (elements (free_evars ϕ₁ ∪ free_evars ϕ₂ ∪ free_evars (ex, ϕ₃))))]}, SVSubst := ∅, KT := false, AKT := false)) i ->
    Γ ⊢i (all, (ϕ₁ and ϕ₃ ---> ϕ₂)) using i ->
    Γ ⊢i (ex, ϕ₁) ---> ϕ₃ ---> (ex, ϕ₂) using i.
  Proof.
    intros wfϕ₁ wfϕ₂ wfϕ₃ pile H.
    toMLGoal.
    { wf_auto2. }
    mlIntro.
    remember (evar_fresh (elements (free_evars ϕ₁ ∪ free_evars ϕ₂ ∪ free_evars (ex, ϕ₃)))) as x.
    rewrite -[ϕ₁](evar_quantify_evar_open x 0).
    { subst x.
      eapply evar_is_fresh_in_richer'. 2: apply set_evar_fresh_is_fresh'. clear. set_solver.
    }
    wf_auto2.
    mlIntro.
    apply Ex_gen_lifted.
    { subst x. eapply evar_is_fresh_in_richer'. 2: apply set_evar_fresh_is_fresh'. clear. set_solver. }
    { constructor. 2: apply Forall_nil; exact I.
      subst x.
      eapply evar_is_fresh_in_richer'. 2: apply set_evar_fresh_is_fresh'. clear. set_solver.
    }
    { assumption. }
  Abort.

  Lemma existential_instantiation :
    forall Γ (φ : Pattern) x y, well_formed φ -> x <> y ->  y ∉ free_evars φ ->
      Γ ⊢i exists_quantify x φ ---> φ^[[evar: x ↦ patt_free_evar y]]
      using (ExGen := {[x]}, SVSubst := ∅, KT := false, AKT := false).
  Proof.
    intros Γ φ x y WF xNy Hy.
    apply Ex_gen. apply pile_refl.
    apply evar_is_fresh_in_free_evar_subst. unfold evar_is_fresh_in. set_solver.
    toMLGoal.
    { wf_auto2. }
    mlIntro "H".
    mlAssert ("H0" : (all , φ^{{evar: x ↦ 0}})). wf_auto2.
  Abort.

  Lemma MLGoal_IntroVar : forall Γ l g i x,
    x ∉ free_evars g ->
    ProofInfoLe ( (ExGen := {[x]}, SVSubst := ∅, KT := false, AKT := false)) i ->
    mkMLGoal Σ Γ l (g^{evar: 0 ↦ x}) i ->
    mkMLGoal Σ Γ l (all , g) i.
  Proof.
    unfold of_MLGoal. simpl. intros Γ l g i x xN PI H wf1 wf2.
    eapply prf_weaken_conclusion_iter_meta_meta. 5: apply H.
    all: try solve[wf_auto2].
    toMLGoal. wf_auto2. mlIntro "H". mlIntro "H0".
    epose proof (Ex_gen Γ (! g^{evar: 0 ↦ x}) ⊥ x i _ _).
    mlApplyMeta H0. unfold exists_quantify. simpl.
    rewrite evar_quantify_evar_open; auto.
    apply andb_true_iff in wf1 as [_ wf1].
    apply andb_true_iff in wf1 as [_ wf1]. simpl in wf1.
    now do 2 rewrite andb_true_r in wf1. mlExact "H0".
   Unshelve.
     set_solver.
  Abort.

  Lemma propagate_forall (Γ : Theory):
    forall ϕ₁ ϕ₂ x,
    well_formed ϕ₁ ->
    well_formed ϕ₂ ->
    x ∉ free_evars ϕ₁ ->
    Γ ⊢i ((all, (ϕ₁ ---> ϕ₂^{{evar:x↦0}})) ---> (ϕ₁ ---> all, ϕ₂^{{evar:x↦0}}))
      using (ExGen := {[x]}, SVSubst := ∅, KT := false, AKT := false).
  Proof.
    intros ϕ₁ ϕ₂ x Wf1 Wf2 Hx. mlIntro "H". mlIntro "H0".
    mlAssert ("H1" : ((all, ϕ₁ ---> ϕ₂^{{evar:x↦0}}) and ϕ₁)). wf_auto2.
    { mlSplitAnd; mlAssumption. }
    mlClear "H". mlClear "H0".
    fromMLGoal.
    apply forall_gen.
    unfold evar_is_fresh_in. cbn.
    pose proof (evar_quantify_no_occurrence ϕ₂ x 0) as H. set_solver.
    try_solve_pile.
    mlIntro "H".
    mlDestructAnd "H".
    pose proof (forall_variable_substitution Γ (ϕ₁ ---> ϕ₂^{{evar: x↦0}}) x ltac:(wf_auto2)) as H0.
    cbn in H0. fold (evar_open x 0 ϕ₂^{{evar:x ↦ 0}}) in H0.
    rewrite evar_open_evar_quantify in H0. wf_auto2.
    rewrite bevar_subst_not_occur in H0. wf_auto2.
    mlRevertLast.
    mlApplyMeta H0. mlAssumption.
  Defined.

  Lemma universal_generalization_iter (Γ : Theory):
    forall (l : list Pattern) (ϕ : Pattern) x i,
    Pattern.wf l ->
    well_formed ϕ ->
    x ∉ free_evars_of_list l ->
    ProofInfoLe (ExGen := {[x]}, SVSubst := ∅, KT := false, AKT := false) i ->
    Γ ⊢i foldr patt_imp ϕ l using i ->
    Γ ⊢i foldr patt_imp (all , ϕ^{{evar: x ↦ 0}}) l using i.
  Proof.
    induction l; intros ϕ x i Wfl Wfϕ Hx Hle H.
    - by apply universal_generalization.
    - apply reorder_last_to_head_meta in H. 2-4: wf_auto2.
      rewrite foldr_snoc in H. apply (IHl _ x) in H. 2-3: wf_auto2.
      2: { solve_free_evars 5. }
      simpl in H. rewrite evar_quantify_fresh in H.
      1: { solve_free_evars 5. }
      eapply prf_weaken_conclusion_iter_meta_meta in H.
      5: gapply propagate_forall.
      5,9: try_solve_pile.
      2-7: try by wf_auto2.
      2: solve_free_evars 5.
      apply reorder_head_to_last_meta. 1-3: wf_auto2.
      by rewrite foldr_snoc.
    Defined.

  Lemma MLGoal_forallIntro Γ l g (x : evar) i :
    x ∉ free_evars_of_list (patterns_of l) ->
    x ∉ free_evars g ->
    ProofInfoLe (ExGen := {[x]}, SVSubst := ∅, KT := false, AKT := false) i ->
    mkMLGoal _ Γ l (g^{evar: 0 ↦ x}) i ->
    mkMLGoal _ Γ l (all, g) i.
  Proof.
    unfold of_MLGoal in *. simpl in *. intros Hx1 Hx2 Hi H Hwf1 Hwfl.
    rewrite <- (evar_quantify_evar_open x 0 g). 3: wf_auto2. 2: assumption.
    apply universal_generalization_iter. 1-2: wf_auto2.
    assumption. try_solve_pile.
    apply H; wf_auto2. 
  Defined.

  (* NOTE: this is not too good with quantification in the concusion.
           Opening is better, when there is no condition about the
           freshness of variables (i.e. Ex_gen is not used). *)
  Lemma specialize_forall (Γ : Theory) :
    forall (l₁ l₂ : list Pattern) (ϕ ψ : Pattern) x i,
      well_formed ϕ -> well_formed (ex, ψ) -> Pattern.wf l₁ -> Pattern.wf l₂ ->
      Γ ⊢i foldr patt_imp ϕ (l₁ ++ ψ^{evar:0 ↦ x} :: l₂) using i ->
      Γ ⊢i foldr patt_imp ϕ (l₁ ++ (all, ψ) :: l₂) using i.
  Proof.
    intros.
    eapply prf_strenghten_premise_iter_meta_meta. 7: eassumption.
    1-5: wf_auto2.
    apply forall_variable_substitution'.
    wf_auto2.
  Defined.

  Lemma MLGoal_specializeAll Γ l₁ l₂ (g ψ : Pattern) x i name :
    mkMLGoal _ Γ (l₁ ++ (mkNH _ name (ψ^{evar:0 ↦ x})) :: l₂) g i ->
    mkMLGoal _ Γ (l₁ ++ (mkNH _ name (all, ψ)) :: l₂) g i.
  Proof.
    unfold of_MLGoal in *. simpl in *. intros H Hwf Hwfl.
    unfold patterns_of in *. rewrite map_app. rewrite map_app in Hwfl.
    simpl in *.
    eapply (specialize_forall Γ _ _ _ _ x).
    1-4: wf_auto2.
    rewrite map_app in H. simpl in H.
    apply H; wf_auto2.
  Defined.

  (* This is more efficient in proof term size, than the version below based on specialize: *)
  Lemma revert_forall_iter (Γ : Theory) :
    forall (l : list Pattern) (ϕ : Pattern) x,
    Pattern.wf l ->
    well_formed (ex, ϕ) ->
    Γ ⊢i foldr patt_imp (all , ϕ) l ---> foldr patt_imp ϕ^{evar: 0 ↦ x} l
      using BasicReasoning.
  Proof.
    intros l ϕ x Wfl Wfϕ. apply prf_weaken_conclusion_iter_meta. 1-3: wf_auto2.
    apply forall_variable_substitution. wf_auto2.
  Defined.

  Lemma revert_forall_iter_meta (Γ : Theory) :
    forall (l : list Pattern) (ϕ : Pattern) x i,
    Pattern.wf l ->
    well_formed (ex, ϕ) ->
    Γ ⊢i foldr patt_imp (all , ϕ) l using i ->
    Γ ⊢i foldr patt_imp (ϕ^{evar: 0 ↦ x}) l using i.
  Proof.
    intros l ϕ x i Wfl Wfϕ H.
    eapply MP. 2: gapply revert_forall_iter. 3-4: wf_auto2. 2: try_solve_pile.
    exact H.
  Defined.

  (* Here, we change opening in the conclusion to quantification in the premise
     to simplify pattern matching for the tactic *)
  Lemma MLGoal_revertAll Γ l g (x : evar) i :
    mkMLGoal _ Γ l (all, g^{{evar:x ↦ 0}}) i ->
    mkMLGoal _ Γ l g i.
  Proof.
    unfold of_MLGoal in *. simpl in *. intros H Hwf1 Hwfl.
    specialize (H ltac:(wf_auto2) ltac:(wf_auto2)).
    apply revert_forall_iter_meta with (x := x) in H. 2-3: wf_auto2.
    rewrite evar_open_evar_quantify in H. wf_auto2.
    assumption.
  Defined.

  Lemma ex_quan_iter (Γ : Theory) :
    forall (l : list Pattern) (ϕ : Pattern) x,
    Pattern.wf l ->
      well_formed (ex, ϕ) ->
      Γ ⊢i foldr patt_imp ϕ^{evar:0 ↦ x} l ---> foldr patt_imp (ex, ϕ) l
        using BasicReasoning.
  Proof.
    intros l ϕ x Wfl Wfϕ. apply prf_weaken_conclusion_iter_meta.
    1-3: wf_auto2.
    apply Ex_quan.
    wf_auto2.
  Defined.

  Lemma ex_quan_iter_meta (Γ : Theory) :
    forall (l : list Pattern) (ϕ : Pattern) x i,
    Pattern.wf l ->
      well_formed (ex, ϕ) ->
      Γ ⊢i foldr patt_imp ϕ^{evar:0 ↦ x} l using i ->
      Γ ⊢i foldr patt_imp (ex, ϕ) l using i.
  Proof.
    intros l ϕ x i Wfl Wfϕ H.
    eapply MP. exact H.
    gapply ex_quan_iter.
    1: try_solve_pile.
    all: wf_auto2.
  Defined.

  Lemma MLGoal_exists Γ l g (x : evar) i :
    mkMLGoal _ Γ l (g^{evar: 0 ↦ x}) i ->
    mkMLGoal _ Γ l (ex, g) i.
  Proof.
    unfold of_MLGoal in *. simpl in *. intros H Hwf1 Hwfl.
    eapply ex_quan_iter_meta.
    1-2: wf_auto2.
    apply H.
    1-2: wf_auto2.
  Defined.

  Lemma exists_elim Γ : forall l₁ l₂ g ϕ i x,
    well_formed (ex, ϕ) -> Pattern.wf l₁ -> Pattern.wf l₂ ->
    ProofInfoLe (ExGen := {[x]}, SVSubst := ∅, KT := false, AKT := false) i ->
    x ∉ free_evars ϕ ->
    x ∉ free_evars g ->
    x ∉ free_evars_of_list l₁ ->
    x ∉ free_evars_of_list l₂ ->
    Γ ⊢i foldr patt_imp g (l₁ ++ ϕ^{evar:0 ↦ x} :: l₂) using i ->
    Γ ⊢i foldr patt_imp g (l₁ ++ (ex, ϕ) :: l₂) using i.
  Proof.
    intros l₁ l₂ g ϕ i x Hwf Hwfl1 Hwfl2 Hi Hin1 Hin2 Hin3 Hin4 H.
    apply reorder_middle_to_head_meta. 1-4: wf_auto2.
    apply reorder_head_to_middle_meta in H. 2-5: wf_auto2.
    pose proof (EG := Ex_gen Γ (ϕ^{evar:0↦x}) (foldr patt_imp g (l₁ ++ l₂)) x).
    simpl in *. unfold exists_quantify in EG.
    apply EG in H. 2: try_solve_pile.
    2: { clear EG H Hi. solve_free_evars 1. }
    clear EG.
    rewrite evar_quantify_evar_open in H. assumption. wf_auto2.
    assumption.
  Defined.

  Lemma MLGoal_destructEx Γ l₁ l₂ g (x : evar) name ϕ i :
    ProofInfoLe (ExGen := {[x]}, SVSubst := ∅, KT := false, AKT := false) i ->
    x ∉ free_evars_of_list (map nh_patt l₁) ->
    x ∉ free_evars_of_list (map nh_patt l₂) ->
    x ∉ free_evars ϕ ->
    x ∉ free_evars g ->
    mkMLGoal _ Γ (l₁ ++ (mkNH _ name ϕ^{evar:0 ↦ x}) :: l₂) g i ->
    mkMLGoal _ Γ (l₁ ++ (mkNH _ name (ex, ϕ)) :: l₂) g i.
  Proof.
    unfold of_MLGoal in *. simpl in *. intros Hi Hf1 Hf2 Hf3 Hf4 H Hwf Hwfl.
    unfold patterns_of in *. rewrite map_app. rewrite map_app in Hwfl.
    simpl in *.
    eapply exists_elim with (x := x).
    1-3: wf_auto2.
    try_solve_pile.
    1-4: solve_free_evars 5.
    rewrite map_app in H. simpl in H.
    apply H; wf_auto2.
  Defined.

End with_signature.


Open Scope ml_scope.
Open Scope string_scope.

(* TODO: reformulate in Ltac2 - depends on the Freshness Manager *)
Tactic Notation "mlIntroAll" ident(x) :=
_ensureProofMode;
mlFreshEvar as x;
tryif apply (MLGoal_forallIntro _ _ _ x);
[   try fm_solve
  | try fm_solve
  | try subst x; try_solve_pile
  | unfold evar_open; mlSimpl;
    repeat (rewrite bevar_subst_not_occur; [by wf_auto2|])
]
then idtac
else fail "mlIntroAll: matching logic goal is not a universally quantified pattern".

Tactic Notation "mlIntroAllManual" constr(x) :=
_ensureProofMode;
tryif apply (MLGoal_forallIntro _ _ _ x);
[   try fm_solve; try subst x; try solve_fresh; try solve_free_evars 10
  | try fm_solve; try subst x; try solve_fresh; try solve_free_evars 10
  | try subst x; try_solve_pile
  | unfold evar_open; mlSimpl;
    repeat (rewrite bevar_subst_not_occur; [by wf_auto2|])
]
then idtac
else fail "mlIntroAll: matching logic goal is not a universally quantified pattern".

Local Example forall_test_1 {Σ : Signature} Γ ϕ:
  well_formed ϕ ->
  Γ ⊢ all , (ϕ ---> ϕ and ϕ).
Proof.
  intro.
  toMLGoal. wf_auto2.
  mlIntroAll x.
Restart.
  intros.
  toMLGoal. wf_auto2.
  mlFreshEvar as x.
  mlIntroAllManual x.
  Fail mlIntroAll y.
  mlIntro "A". mlSplitAnd; mlAssumption.
Qed.

(* The FreshMan does not handle this case yet
Local Example forall_test_2 {Σ : Signature} Γ ϕ ψ x:
  well_formed ϕ -> well_formed (ex, ψ) ->
  x ∉ free_evars ϕ ->
  x ∉ free_evars ψ ->
  Γ ⊢ ϕ ---> ψ^{evar:0 ↦ x} ->
  Γ ⊢ (ϕ ---> all, ψ).
Proof.
  intros.
  toMLGoal. wf_auto2.
  mlIntro. mlIntroAll x.
  by fromMLGoal.
Qed.
*)

Tactic Notation "mlRevertAll" constr(x) :=
  _ensureProofMode;
  apply (MLGoal_revertAll _ _ _ x).

Local Example revert_test {Σ : Signature} Γ ϕ ψ x:
  well_formed ϕ -> well_formed (ex, ψ) ->
  x ∉ free_evars ϕ ->
  x ∉ free_evars ψ ->
  Γ ⊢ (ϕ ---> all, ψ) ->
  Γ ⊢ ϕ ---> ψ^{evar:0 ↦ x}.
Proof.
  intros.
  toMLGoal. wf_auto2.
  mlIntro. mlRevertAll x.
  rewrite evar_quantify_evar_open. 2: wf_auto2. assumption.
  by fromMLGoal.
Qed.

Local Example forall_revert_test_1 {Σ : Signature} Γ ϕ ψ:
  well_formed ϕ -> well_formed (ex, ψ) ->
  Γ ⊢ (ϕ ---> all, ψ) ->
  Γ ⊢ all, ϕ ---> ψ.
Proof.
  intros.
  toMLGoal. wf_auto2.
  mlIntroAll x.
  mlIntro. mlRevertAll x.
  fold (evar_open x 0 ψ).
  rewrite evar_quantify_evar_open.
  { fm_solve. }
  1: wf_auto2.
  by fromMLGoal.
Qed.

Local Example forall_revert_test_2 {Σ : Signature} Γ ϕ ψ ξ:
  well_formed ξ -> well_formed ϕ -> well_formed (ex, ψ) ->
  Γ ⊢ (ξ ---> ϕ ---> all, ψ) ->
  Γ ⊢ all, ξ ---> ϕ ---> ψ.
Proof.
  intros.
  toMLGoal. wf_auto2.
  mlIntroAll x.
  do 2 mlIntro. mlRevertAll x.
  fold (evar_open x 0 ψ).
  rewrite evar_quantify_evar_open.
  { fm_solve. }
  1: wf_auto2.
  by fromMLGoal.
Qed.

Local Example destruct_or_f {Σ : Signature} Γ ϕ₁ ϕ₂ ψ:
  well_formed (ex, ϕ₁) -> well_formed (ex, ϕ₂) -> well_formed (ex, ψ) ->
  Γ ⊢ all, ϕ₁ ---> ψ -> Γ ⊢ all, ϕ₂ ---> ψ ->
  Γ ⊢ all, ϕ₁ or ϕ₂ ---> ψ.
Proof.
  intros.
  toMLGoal. wf_auto2.
  mlIntroAll x.
  mlIntro. mlDestructOr "0".
  * mlRevertLast. mlRevertAll x. simpl.
    fold (evar_open x 0 ψ).
    rewrite evar_quantify_evar_open.
    { fm_solve. }
    1: wf_auto2.
    fold (evar_open x 0 ϕ₁).
    rewrite evar_quantify_evar_open.
    { fm_solve. }
    1: wf_auto2.
    by fromMLGoal.
  * mlAdd H3.
    mlRevertLast. mlRevertAll x. simpl.
    fold (evar_open x 0 ψ).
    rewrite evar_quantify_evar_open.
    { fm_solve. }
    1: wf_auto2.
    fold (evar_open x 0 ϕ₁).
    rewrite evar_quantify_evar_open.
    { fm_solve. }
    1: wf_auto2.
    mlAssumption.
Qed.

Tactic Notation "mlSpecialize" constr(name') "with" constr(var) :=
_ensureProofMode;
_mlReshapeHypsByName name';
tryif apply (MLGoal_specializeAll _ _ _ _ _ var);
_mlReshapeHypsBack
then idtac
else fail "mlSpecialize: given local hypothesis is not a universally quantified pattern".

(* revert is a corollary of specialize: *)
Local Lemma Private_revert_forall_iter {Σ : Signature} (Γ : Theory) :
  forall (l : list Pattern) (ϕ : Pattern) x,
  Pattern.wf l ->
  well_formed ϕ ->
  Γ ⊢i foldr patt_imp (all , ϕ^{{evar: x ↦ 0}}) l ---> foldr patt_imp ϕ l
    using BasicReasoning.
Proof.
  intros l ϕ x Wfl Wfϕ. apply prf_weaken_conclusion_iter_meta. 1-3: wf_auto2.
  mlIntro "H".
  mlSpecialize "H" with x.
  Fail mlSpecialize "H" with x.
  rewrite evar_open_evar_quantify. wf_auto2.
  mlAssumption.
Qed.

Tactic Notation "mlExists" constr(var) :=
_ensureProofMode;
tryif apply (MLGoal_exists _ _ _ var);
try (rewrite evar_open_evar_quantify;[by wf_auto2|])
then idtac
else fail "mlExists: matching logic goal is not an existentially quantified pattern".

Local Lemma exists_test_1 {Σ : Signature} Γ ϕ :
  well_formed (ex, ϕ) ->
  Γ ⊢ (all, ϕ) ---> (ex, ϕ).
Proof.
  intro WF.
  mlIntro "H".
  mlFreshEvar as y.
  (* we can prove this with a y which is not necessarily equal to x too, but it is tricky. *)
  mlSpecialize "H" with y.
  mlExists y.
  Fail mlExists y.
  mlAssumption.
Qed.

(*(* The order of these two tactics matter! Do not exchange them! *)
Tactic Notation "mlDestructEx" constr(name') "as" constr(x) :=
  _ensureProofMode;
  _mlReshapeHypsByName name';
  apply (MLGoal_destructEx _ _ _ _ x name');[
    try subst x; try_solve_pile
  | try subst x; try solve_fresh; try solve_free_evars 10
  | try subst x; try solve_fresh; try solve_free_evars 10
  | try subst x; try solve_fresh; try solve_free_evars 10
  | try subst x; try solve_fresh; try solve_free_evars 10
  | _mlReshapeHypsBack]
.
(* The order of this and the previous tactic matter! *)
Tactic Notation "mlDestructEx" constr(name') "as" ident(x) :=
  tryif ltac2:(hyp ident:(x))
  then mlDestructEx name' as (constr:(x))
  else  
    _ensureProofMode;
    _mlReshapeHypsByName name';
    mlFreshEvar as x;
    apply (MLGoal_destructEx _ _ _ _ x name');[
      try subst x; try_solve_pile
    | fm_solve
    | fm_solve
    | fm_solve
    | fm_solve
    | _mlReshapeHypsBack]
.*)

Ltac _mlDestructExManual name' x :=
  _ensureProofMode;
  _mlReshapeHypsByName name';
  tryif apply (MLGoal_destructEx _ _ _ _ x name');[
    try subst x; simpl; try_solve_pile
  | try fm_solve; try subst x; simpl; try solve_fresh; try solve_free_evars 10
  | try fm_solve; try subst x; simpl; try solve_fresh; try solve_free_evars 10
  | try fm_solve; try subst x; simpl; try solve_fresh; try solve_free_evars 10
  | try fm_solve; try subst x; simpl; try solve_fresh; try solve_free_evars 10
  | _mlReshapeHypsBack]
  then idtac
  else fail "_mlDestructExManual: given local hypothesis is not existentially quantified".

Ltac _mlDestructExFresh name' x :=
    _ensureProofMode;
    _mlReshapeHypsByName name';
    mlFreshEvar as x;
    tryif apply (MLGoal_destructEx _ _ _ _ x name');[
      try subst x; try_solve_pile
    | fm_solve
    | fm_solve
    | fm_solve
    | fm_solve
    | _mlReshapeHypsBack]
    then idtac
    else fail "_mlDestructExFresh: given local hypothesis is not existentially quantified".

Tactic Notation "mlDestructEx" constr(name') "as" constr(x) :=
  _mlDestructExManual name' x.

Tactic Notation "mlDestructEx" constr(name') "as" ident(x) :=
  tryif is_var x (* we need to check whether x is a used ident! *)
  then
    _mlDestructExManual name' x (* Do not use idtac here, because it breaks tryif for some reason *)
  else
    _mlDestructExFresh name' x (* Do not use idtac here, because it breaks tryif for some reason *)
  .

(* Ltac mlDestructEx name' x :=
  tryif
    match type of x with
    | evar => idtac
    | _ => fail 1
    end
  then _mlDestructExManual name' as x
  else _mlDestructExFresh name' as x
. *)

From Ltac2 Require Import Ltac2 Control.

Set Default Proof Mode "Classic".

Local Lemma destructExDouble_Test {Σ : Signature} Γ ϕ ψ :
  well_formed (ex, ϕ) -> well_formed (ex, ψ) ->
  Γ ⊢ (ex, ϕ and ψ) ---> (ex, ϕ and ψ) ---> ex, ϕ.
Proof.
  intros.
  mlIntro "H". mlIntro "H0".
  mlDestructEx "H" as (fresh_evar (ϕ $ ψ)). { cbn. solve_fresh. }
  Fail mlDestructEx "H" as x.
  mlClear "H". mlDestructEx "H0" as x.
  Fail mlDestructEx "H0" as x.
  mlSimpl. mlDestructAnd "H0" as "H" "H1".
  mlExists x. mlAssumption.
Qed.


Local Lemma destructEx_Test {Σ : Signature} Γ ϕ ψ :
  well_formed (ex, ϕ) -> well_formed (ex, ψ) ->
  Γ ⊢ (ex, ϕ and ψ) ---> ex, ϕ.
Proof.
  intros WF1 WF2.
  mlIntro "H".
  
  remember (fresh_evar (ϕ and ψ)) as x0.
  mlDestructEx "H" as x0.
  Undo. Undo.
  
  mlDestructEx "H" as x.
  mlSimpl.
  mlDestructAnd "H".
  mlExists x.
  mlAssumption.
Qed.
