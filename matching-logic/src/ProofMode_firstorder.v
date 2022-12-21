From Coq Require Import ssreflect ssrfun ssrbool.

From Ltac2 Require Import Ltac2.

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
    ProofMode_base
    ProofMode_propositional
    BasicProofSystemLemmas
.

From stdpp Require Import list tactics fin_sets coGset gmap sets.

From MatchingLogic.Utils Require Import stdpp_ext.

Import extralibrary.

Import
  MatchingLogic.Syntax.Notations
  MatchingLogic.Substitution.Notations
  MatchingLogic.DerivedOperators_Syntax.Notations
  MatchingLogic.ProofSystem.Notations
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
    ProofInfoLe ( (ExGen := {[x]}, SVSubst := ∅, KT := false)) i ->
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
  *)
  Lemma forall_variable_substitution Γ ϕ x:
    well_formed ϕ ->
    Γ ⊢i (all, ϕ^{{evar: x ↦ 0}}) ---> ϕ
    using ( (ExGen := {[x]}, SVSubst := ∅, KT := false)).
  Proof.
    intros wfϕ.

    unfold patt_forall.
    replace (! ϕ^{{evar: x ↦ 0}})
      with ((! ϕ)^{{evar: x ↦ 0}})
      by reflexivity.
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
    pose proof (Htmp := Ex_quan Γ ((!ϕ)^{{evar: x ↦ 0}}) x).
    rewrite /instantiate in Htmp.
    rewrite bevar_subst_evar_quantify_free_evar in Htmp.
    {
      simpl. split_and!. now do 2 apply andb_true_iff in wfϕ as [_ wfϕ]. reflexivity.
    }
    specialize (Htmp ltac:(wf_auto2)).
    useBasicReasoning.
    mlAdd Htmp.
    mlApply "3".
    mlIntro.
    mlApply "1".
    mlExactn 4.
  Defined.


  (*
    Γ ⊢ φ₁ → φ₂
    -----------------------
    Γ ⊢ (∃x. φ₁) → (∃x. φ₂)
  *)
  Lemma ex_quan_monotone Γ x ϕ₁ ϕ₂ (i : ProofInfo)
    (pile : ProofInfoLe ( (ExGen := {[x]}, SVSubst := ∅, KT := false)) i) :
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
    using ( (ExGen := {[x]}, SVSubst := ∅, KT := false)).
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
    using ( (ExGen := {[x]}, SVSubst := ∅, KT := false)).
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
    using ( (ExGen := {[fresh_evar (ϕ₂ ---> ex , (ϕ₁ and ϕ₂))]}, SVSubst := ∅, KT := false)).
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
    using ( (ExGen := {[fresh_evar ((ϕ₁ and ϕ₂))]}, SVSubst := ∅, KT := false)).
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
    using ( (ExGen := {[fresh_evar ((ϕ₁ and ϕ₂))]}, SVSubst := ∅, KT := false)).
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
    ProofInfoLe ( (ExGen := {[x]}, SVSubst := ∅, KT := false)) i ->
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
    mlApplyMetaRaw (useBasicReasoning _ (not_not_intro Γ ϕ₁ ltac:(wf_auto2))) in "0".
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
    well_formed ϕ ->
    (ProofInfoLe ( (ExGen := {[x]}, SVSubst := ∅, KT := false)) i) ->
    Γ ⊢i (all, ϕ^{{evar: x ↦ 0}}) ---> ϕ using i.
  Proof.
    intros wfϕ pile.
    pose proof (Htmp := forall_variable_substitution Γ ϕ x wfϕ).
    eapply useGenericReasoning. apply pile. apply Htmp.
  Defined.

  (*
    Γ ⊢ ∀x. φ
    ----------
    Γ ⊢ φ
  *)
  Lemma forall_elim Γ ϕ x (i : ProofInfo):
    well_formed (ex, ϕ) ->
    evar_is_fresh_in x ϕ ->
    ProofInfoLe ( (ExGen := {[x]}, SVSubst := ∅, KT := false)) i ->
    Γ ⊢i (all, ϕ) using i ->
    Γ ⊢i (ϕ^{evar: 0 ↦ x}) using i.
  Proof.
    intros wfϕ frϕ pile H.
    destruct i.
    eapply MP.
    2: eapply forall_variable_substitution'.
    2: wf_auto2.
    2: apply pile.
    eapply cast_proof'.
    {
      rewrite evar_quantify_evar_open.
      { apply frϕ. }
      { wf_auto2. }
      reflexivity.
    }
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
    ProofInfoLe ( (ExGen := {[fresh_evar (ϕ₁ ---> ϕ₂)]}, SVSubst := ∅, KT := false)) i ->
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
    4: { apply pile. }
    2: wf_auto2.
    2: { subst x. apply set_evar_fresh_is_fresh. }
    unfold evar_open in *. simpl in *. exact H.
  Defined.

  Lemma Ex_gen_lifted (Γ : Theory) (ϕ₁ : Pattern) (l : hypotheses) (n : string) (g : Pattern) (x : evar)
    (i : ProofInfo) :
    evar_is_fresh_in x g ->
    evar_is_fresh_in_list x (patterns_of l) ->
    ProofInfoLe ( (ExGen := {[x]}, SVSubst := ∅, KT := false)) i ->
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
    feed specialize H.
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
    ProofInfoLe ( (ExGen := {[(evar_fresh (elements (free_evars ϕ₁ ∪ free_evars ϕ₂ ∪ free_evars (ex, ϕ₃))))]}, SVSubst := ∅, KT := false)) i ->
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
      using (ExGen := {[x]}, SVSubst := ∅, KT := false).
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
    ProofInfoLe ( (ExGen := {[x]}, SVSubst := ∅, KT := false)) i ->
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

End with_signature.
