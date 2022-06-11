From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Setoid.
From Coq Require Import Unicode.Utf8.
From Coq.Logic Require Import Classical_Prop FunctionalExtensionality.
From Coq.Classes Require Import Morphisms_Prop.

From stdpp Require Import base sets.

From MatchingLogic Require Import
    Syntax
    Semantics
    DerivedOperators_Syntax
    DerivedOperators_Semantics
    Utils.extralibrary
    Theories.Definedness_Syntax
    Theories.Definedness_Semantics
    Theories.Sorts_Syntax.

Import MatchingLogic.Syntax.Notations.
Import MatchingLogic.Syntax.BoundVarSugar.
Import MatchingLogic.Semantics.Notations.
Import MatchingLogic.IndexManipulation.
Import MatchingLogic.DerivedOperators_Syntax.Notations.

Section with_model.
    Context
      {Σ : Signature}
      {syntax : Sorts_Syntax.Syntax}
      {M : Model}.
    Hypothesis M_satisfies_theory : M ⊨ᵀ Definedness_Syntax.theory.

    Local Definition sym (s : Symbols) : Pattern :=
    patt_sym (inj s).

    Definition Mpatt_inhabitant_set m := app_ext (sym_interp M (inj inhabitant)) {[m]}.

    (* ϕ is expected to be a sort pattern *)
    Definition Minterp_inhabitant (ϕ : Pattern) (ρ : @Valuation Σ M)
      := @eval Σ M ρ (patt_app (sym inhabitant) ϕ).
    
    Lemma eval_forall_of_sort_predicate s ϕ ρ:
      let x := fresh_evar ϕ in
      M_predicate M (evar_open 0 x ϕ) ->
      eval ρ (patt_forall_of_sort s ϕ) = ⊤
      <-> (∀ m : Domain M, m ∈ Minterp_inhabitant s ρ ->
                           eval (update_evar_val x m ρ) (evar_open 0 x ϕ) = ⊤).
    Proof.
      intros x Hpred.
      unfold patt_forall_of_sort.
      assert (Hsub: is_subformula_of_ind ϕ (patt_in b0 (patt_inhabitant_set (nest_ex s)) ---> ϕ)).
      { apply sub_imp_r. apply sub_eq. reflexivity.  }
      rewrite eval_forall_predicate.
      {
        unfold evar_open. simpl_bevar_subst. simpl.
        apply M_predicate_impl.
        - apply T_predicate_in.
          apply M_satisfies_theory.
        - subst x.
          apply M_predicate_evar_open_fresh_evar_2.
          2: apply Hpred.
          eapply evar_fresh_in_subformula. apply Hsub. apply set_evar_fresh_is_fresh.
      }
      subst x.
      remember (patt_in b0 (patt_inhabitant_set (nest_ex s)) ---> ϕ) as Bigϕ.
      assert (Hfresh: fresh_evar Bigϕ ∉ free_evars (patt_sym (inj inhabitant) $ (nest_ex s))).
      { rewrite HeqBigϕ.
        unfold patt_inhabitant_set.
        fold (evar_is_fresh_in (fresh_evar (patt_in b0 (sym inhabitant $ s) ---> ϕ)) (patt_sym (inj inhabitant) $ s)).
        unfold sym.
        eapply evar_fresh_in_subformula.
        2: apply set_evar_fresh_is_fresh.
        (* TODO automation *)
        apply sub_imp_l. unfold patt_in. unfold patt_defined.
        apply sub_app_r. unfold patt_and.
        unfold patt_not. unfold patt_or.
        apply sub_imp_l. apply sub_imp_r.
        apply sub_imp_l. apply sub_eq. reflexivity.
      }

      remember (patt_in b0 (patt_inhabitant_set s) ---> ϕ) as Bigϕ'.
      assert (HfreeBigϕ: free_evars Bigϕ = free_evars Bigϕ').
      { subst. simpl. unfold nest_ex. rewrite free_evars_nest_ex_aux. reflexivity. }
      assert (HfreshBigϕ: fresh_evar Bigϕ = fresh_evar Bigϕ').
      { unfold fresh_evar. rewrite HfreeBigϕ. reflexivity. }
      clear HfreeBigϕ.

      assert (Hfrs: evar_is_fresh_in (fresh_evar Bigϕ) s).
      { unfold evar_is_fresh_in.
        rewrite HfreshBigϕ. fold (evar_is_fresh_in (fresh_evar Bigϕ') s).
        eapply evar_fresh_in_subformula'. 2: apply set_evar_fresh_is_fresh.
        rewrite HeqBigϕ'. simpl. rewrite is_subformula_of_refl. simpl.
        rewrite !orb_true_r. auto.
      }
            
      split.
      - intros H m H'.
        specialize (H m).
        (*rewrite -eval_fresh_evar_subterm.*)
        rewrite -(@eval_fresh_evar_subterm _ _ _ Bigϕ).
        rewrite HeqBigϕ in H.
        rewrite evar_open_imp in H.
        rewrite -HeqBigϕ in H.
        assumption.
        rewrite {3}HeqBigϕ in H.
        eapply eval_impl_MP.
        apply H.
        simpl. fold evar_open.
  
        unfold Minterp_inhabitant in H'.
        pose proof (Hfeip := @free_evar_in_patt _ _ M M_satisfies_theory (fresh_evar Bigϕ) (patt_sym (inj inhabitant) $ evar_open 0 (fresh_evar Bigϕ) (nest_ex s)) (update_evar_val (fresh_evar Bigϕ) m ρ)).
        destruct Hfeip as [Hfeip1 _]. apply Hfeip1. clear Hfeip1.
        rewrite update_evar_val_same.
        clear H. unfold sym in H'.
        unfold Ensembles.In.
        
        rewrite eval_app_simpl.
        unfold evar_open. rewrite nest_ex_same.
        rewrite eval_sym_simpl.

        rewrite eval_app_simpl in H'.
        rewrite eval_sym_simpl in H'.
        rewrite eval_free_evar_independent.
        {
          solve_free_evars_inclusion 5.
        }
        apply H'.

      - intros H m.
        pose proof (Hfeip := @free_evar_in_patt _ _ M M_satisfies_theory (fresh_evar Bigϕ) (patt_sym (inj inhabitant) $ evar_open 0 (fresh_evar Bigϕ) (nest_ex s)) (update_evar_val (fresh_evar Bigϕ) m ρ)).
        destruct Hfeip as [_ Hfeip2].
        rewrite {3}HeqBigϕ.
        unfold evar_open. simpl_bevar_subst. simpl.
        apply eval_predicate_impl.
        apply T_predicate_in. apply M_satisfies_theory.
        intros H1.
        specialize (Hfeip2 H1). clear H1.
        specialize (H m).
        rewrite -(@eval_fresh_evar_subterm _ _ _ Bigϕ) in H.
        apply Hsub. apply H. clear H.

        unfold Minterp_inhabitant.
        unfold Ensembles.In in Hfeip2. unfold sym.


        rewrite eval_app_simpl in Hfeip2.
        unfold evar_open in Hfeip2. rewrite nest_ex_same in Hfeip2.
        rewrite eval_sym_simpl in Hfeip2.

        rewrite eval_app_simpl.
        rewrite eval_sym_simpl.
        rewrite update_evar_val_same in Hfeip2.
        rewrite eval_free_evar_independent in Hfeip2.
        {
          solve_free_evars_inclusion 5.
        }
        apply Hfeip2.
    Qed.

    Lemma eval_exists_of_sort_predicate s ϕ ρ:
      let x := fresh_evar ϕ in
      M_predicate M (evar_open 0 x ϕ) ->
      eval ρ (patt_exists_of_sort s ϕ) = ⊤
      <-> (∃ m : Domain M, m ∈ Minterp_inhabitant s ρ /\
                           eval (update_evar_val x m ρ) (evar_open 0 x ϕ) = ⊤).
    Proof.
      intros x Hpred.
      unfold patt_exists_of_sort.
      assert (Hsub: is_subformula_of_ind ϕ (patt_in b0 (patt_inhabitant_set (nest_ex s)) and ϕ)).
      { unfold patt_and. unfold patt_or.  apply sub_imp_l. apply sub_imp_r. apply sub_imp_l. apply sub_eq. reflexivity. }
      rewrite eval_exists_predicate_full.
      {
        unfold evar_open. simpl_bevar_subst. simpl.
        apply M_predicate_and.
        - apply T_predicate_in.
          apply M_satisfies_theory.
        - subst x.
          apply M_predicate_evar_open_fresh_evar_2.
          2: apply Hpred.
          eapply evar_fresh_in_subformula. apply Hsub. apply set_evar_fresh_is_fresh.
      }
      subst x.
      remember (patt_in b0 (patt_inhabitant_set (nest_ex s)) and ϕ) as Bigϕ.
      assert (Hfresh: fresh_evar Bigϕ ∉ free_evars (patt_sym (inj inhabitant) $ (nest_ex s))).
      { rewrite HeqBigϕ.
        unfold patt_inhabitant_set.
        fold (evar_is_fresh_in (fresh_evar (patt_in b0 (sym inhabitant $ s) and ϕ)) (patt_sym (inj inhabitant) $ s)).
        unfold sym.
        eapply evar_fresh_in_subformula.
        2: apply set_evar_fresh_is_fresh.
        (* TODO automation *)
        unfold patt_and. unfold patt_not. unfold patt_or.
        apply sub_imp_l. apply sub_imp_l. apply sub_imp_l.
        apply sub_imp_l. unfold patt_in. unfold patt_defined.
        apply sub_app_r. unfold patt_and.
        unfold patt_not. unfold patt_or.
        apply sub_imp_l. apply sub_imp_r.
        apply sub_imp_l. apply sub_eq. reflexivity.
      }

      remember (patt_in b0 (patt_inhabitant_set s) and ϕ) as Bigϕ'.
      assert (HfreeBigϕ: free_evars Bigϕ = free_evars Bigϕ').
      { subst. simpl. unfold nest_ex. rewrite free_evars_nest_ex_aux. reflexivity. }
      assert (HfreshBigϕ: fresh_evar Bigϕ = fresh_evar Bigϕ').
      { unfold fresh_evar. rewrite HfreeBigϕ. reflexivity. }
      clear HfreeBigϕ.

      assert (Hfrs: evar_is_fresh_in (fresh_evar Bigϕ) s).
      { unfold evar_is_fresh_in.
        rewrite HfreshBigϕ. fold (evar_is_fresh_in (fresh_evar Bigϕ') s).
        eapply evar_fresh_in_subformula'. 2: apply set_evar_fresh_is_fresh.
        rewrite HeqBigϕ'. simpl. rewrite is_subformula_of_refl. simpl.
        rewrite !orb_true_r. auto.
      }
      
      split.
      - intros [m H].
        exists m.
        rewrite -(@eval_fresh_evar_subterm _ _ _ Bigϕ).
        assumption.
        rewrite {3}HeqBigϕ in H.

        apply eval_and_full in H.
        fold evar_open in H.
        destruct H as [H1 H2].
        split. 2: apply H2. clear H2.
        unfold Minterp_inhabitant.
        pose proof (Hfeip := @free_evar_in_patt _ _ M M_satisfies_theory (fresh_evar Bigϕ) (patt_sym (inj inhabitant) $ evar_open 0 (fresh_evar Bigϕ) (nest_ex s)) (update_evar_val (fresh_evar Bigϕ) m ρ)).
        destruct Hfeip as [_ Hfeip2].

        apply Hfeip2 in H1. clear Hfeip2.
        rewrite update_evar_val_same in H1.
        unfold sym.
        unfold Ensembles.In in H1.

        rewrite eval_app_simpl in H1.
        unfold evar_open in H1.
        rewrite nest_ex_same in H1.
        rewrite eval_sym_simpl in H1.

        rewrite eval_app_simpl.
        rewrite eval_sym_simpl.
        rewrite eval_free_evar_independent in H1.
        {
          solve_free_evars_inclusion 5.
        }
        apply H1.

      - intros [m [H1 H2] ]. exists m.
        pose proof (Hfeip := @free_evar_in_patt _ _ M M_satisfies_theory (fresh_evar Bigϕ) (patt_sym (inj inhabitant) $ evar_open 0 (fresh_evar Bigϕ) (nest_ex s)) (update_evar_val (fresh_evar Bigϕ) m ρ)).
        destruct Hfeip as [Hfeip1 _].
        rewrite {3}HeqBigϕ.
        apply eval_and_full. fold evar_open.
        split.
        + apply Hfeip1. clear Hfeip1.
          unfold Ensembles.In.
          rewrite -> update_evar_val_same.
          unfold Minterp_inhabitant in H1. unfold sym in H1.

          rewrite eval_app_simpl in H1.
          rewrite eval_sym_simpl in H1.

          rewrite eval_app_simpl.
          unfold evar_open. rewrite nest_ex_same.
          rewrite eval_sym_simpl.
          rewrite eval_free_evar_independent.
          {
            solve_free_evars_inclusion 5.
          }
          apply H1.
        + rewrite -(@eval_fresh_evar_subterm _ _ _ Bigϕ) in H2.
          apply Hsub.
          apply H2.
    Qed.


    Lemma M_predicate_exists_of_sort s ϕ :
      let x := fresh_evar ϕ in
      M_predicate M (evar_open 0 x ϕ) -> M_predicate M (patt_exists_of_sort s ϕ).
    Proof.
      intros x Hpred.
      unfold patt_exists_of_sort.
      apply M_predicate_exists.
      unfold evar_open. simpl_bevar_subst.
      rewrite {1}[bevar_subst _ _ _]/=.
      apply M_predicate_and.
      - apply T_predicate_in.
        apply M_satisfies_theory.
      - subst x.
        apply M_predicate_evar_open_fresh_evar_2.
        2: apply Hpred.
        eapply evar_fresh_in_subformula.
        2: apply set_evar_fresh_is_fresh.
        unfold patt_and. unfold patt_not. unfold patt_or.
        apply sub_imp_l.
        apply sub_imp_r. apply sub_imp_l. apply sub_eq. reflexivity.
    Qed.

    Hint Resolve M_predicate_exists_of_sort : core.

    Lemma M_predicate_forall_of_sort s ϕ :
      let x := fresh_evar ϕ in
      M_predicate M (evar_open 0 x ϕ) -> M_predicate M (patt_forall_of_sort s ϕ).
    Proof.
      intros x Hpred.
      unfold patt_forall_of_sort.
      apply M_predicate_forall.
      unfold evar_open. simpl_bevar_subst.
      apply M_predicate_impl.
      - apply T_predicate_in.
        apply M_satisfies_theory.
      - subst x.
        apply M_predicate_evar_open_fresh_evar_2.
        2: apply Hpred.
        eapply evar_fresh_in_subformula. 2: apply set_evar_fresh_is_fresh.
        apply sub_imp_r. apply sub_eq. reflexivity.
    Qed.

    Hint Resolve M_predicate_forall_of_sort : core.

    Lemma interp_total_function f s₁ s₂ ρ :
      @eval Σ M ρ (patt_total_function f s₁ s₂) = ⊤ <->
      @is_total_function Σ M f (Minterp_inhabitant s₁ ρ) (Minterp_inhabitant s₂ ρ) ρ.
    Proof.
      unfold is_total_function.
      rewrite eval_forall_of_sort_predicate.
      1: { eauto. }

      unfold evar_open. simpl_bevar_subst.
      remember (fresh_evar (patt_exists_of_sort (nest_ex s₂) (patt_equal ((nest_ex (nest_ex f)) $ b1) b0))) as x'.
      rewrite [nest_ex s₂]/nest_ex.
      unfold nest_ex. repeat rewrite nest_ex_same.
      rewrite fuse_nest_ex_same. rewrite nest_ex_same_general. 1-2: lia. simpl.
      rewrite -/(nest_ex s₂).

      apply all_iff_morphism.
      unfold pointwise_relation. intros m₁.
      apply all_iff_morphism. unfold pointwise_relation. intros Hinh1.

      rewrite eval_exists_of_sort_predicate.
      1: {
        unfold evar_open. simpl_bevar_subst.
        apply T_predicate_equals; apply M_satisfies_theory.
      }
      apply ex_iff_morphism. unfold pointwise_relation. intros m₂.

      unfold Minterp_inhabitant.
      rewrite 2!eval_app_simpl.
      rewrite 2!eval_sym_simpl.
      rewrite eval_free_evar_independent.
      (* two subgoals *)
      fold (evar_is_fresh_in x' (nest_ex s₂)).

      assert (Hfreq: x' = fresh_evar (patt_imp s₂ (nest_ex (nest_ex f)))).
      { rewrite Heqx'. unfold fresh_evar. apply f_equal. simpl.
        rewrite 2!free_evars_nest_ex_aux.
        rewrite !(left_id_L ∅ union). rewrite !(right_id_L ∅ union).
        rewrite (idemp_L union). reflexivity.
      }
      {
        rewrite Hfreq.
        unfold evar_is_fresh_in.
        eapply evar_is_fresh_in_richer'.
        2: apply set_evar_fresh_is_fresh'. solve_free_evars_inclusion 5.
      }

      apply and_iff_morphism; auto.

      unfold nest_ex.
      unfold evar_open. simpl_bevar_subst.
      repeat rewrite nest_ex_same.


      remember (fresh_evar (patt_equal (nest_ex_aux 0 1 f $ patt_free_evar x') b0)) as x''.

      rewrite equal_iff_interpr_same. 1: apply M_satisfies_theory.
      simpl. rewrite eval_free_evar_simpl.
      rewrite update_evar_val_same.
      rewrite eval_app_simpl.
      rewrite eval_free_evar_simpl.

      (*  Hx''neqx' : x'' ≠ x'
          Hx''freeinf : x'' ∉ free_evars f
       *)
      rewrite {2}update_evar_val_comm.
      {
        solve_fresh_neq.
      }
      rewrite update_evar_val_same.
      rewrite eval_free_evar_independent.
      {
         rewrite Heqx''. unfold evar_is_fresh_in.
         eapply evar_is_fresh_in_richer'.
         2: apply set_evar_fresh_is_fresh'. cbn.
         solve_free_evars_inclusion 5.
      }
      rewrite eval_free_evar_independent.
      {
         rewrite Heqx'. unfold evar_is_fresh_in.
         eapply evar_is_fresh_in_richer'.
         2: apply set_evar_fresh_is_fresh'. cbn.
         solve_free_evars_inclusion 5.
      }
      auto.
    Qed.

    Lemma interp_partial_function f s₁ s₂ ρ :
      @eval Σ M ρ (patt_partial_function f s₁ s₂) = ⊤ <->
      ∀ (m₁ : Domain M),
        m₁ ∈ Minterp_inhabitant s₁ ρ ->
        ∃ (m₂ : Domain M),
          m₂ ∈ Minterp_inhabitant s₂ ρ /\
          (app_ext (@eval Σ M ρ f) {[m₁]})
            ⊆ {[m₂]}.
    Proof.
      rewrite eval_forall_of_sort_predicate.
      1: { eauto. }

      unfold evar_open. simpl_bevar_subst.
      remember (fresh_evar (patt_exists_of_sort (nest_ex s₂) (patt_subseteq ((nest_ex (nest_ex f)) $ b1) b0))) as x'.
      rewrite [nest_ex s₂]/nest_ex.
      rewrite nest_ex_same.
      unfold nest_ex.
      rewrite fuse_nest_ex_same. rewrite nest_ex_same_general. 1-2: lia. simpl.

      apply all_iff_morphism.
      unfold pointwise_relation. intros m₁.
      apply all_iff_morphism. unfold pointwise_relation. intros Hinh1.

      rewrite eval_exists_of_sort_predicate.
      1: {
        unfold evar_open. simpl_bevar_subst.
        apply T_predicate_subseteq; apply M_satisfies_theory.
      }

      apply ex_iff_morphism. unfold pointwise_relation. intros m₂.

      unfold Minterp_inhabitant.
      rewrite 2!eval_app_simpl.
      rewrite 2!eval_sym_simpl.
      rewrite eval_free_evar_independent.
      {
        fold (evar_is_fresh_in x' (nest_ex s₂)).

        assert (Hfreq: x' = fresh_evar (patt_imp s₂ (nest_ex (nest_ex f)))).
        { rewrite Heqx'. unfold fresh_evar. apply f_equal. simpl.
          rewrite 2!free_evars_nest_ex_aux.
          rewrite !(left_id_L ∅ union). rewrite !(right_id_L ∅ union).
          reflexivity.
        }

        rewrite Hfreq.
        unfold nest_ex.
        unfold evar_is_fresh_in.
        eapply evar_is_fresh_in_richer'.
         2: apply set_evar_fresh_is_fresh'. cbn.
         solve_free_evars_inclusion 5.
      }

      apply and_iff_morphism; auto.

      unfold evar_open. simpl_bevar_subst.
      rewrite nest_ex_same.
      simpl.
      remember (fresh_evar (patt_subseteq (nest_ex_aux 0 1 f $ patt_free_evar x') b0)) as x''.

      rewrite subseteq_iff_interpr_subseteq. 1: apply M_satisfies_theory.
      simpl. rewrite eval_free_evar_simpl.
      rewrite update_evar_val_same.
      rewrite eval_app_simpl.
      rewrite eval_free_evar_simpl.

      (*  Hx''neqx' : x'' ≠ x'
          Hx''freeinf : x'' ∉ free_evars f
       *)

      rewrite {2}update_evar_val_comm.
      {
        solve_fresh_neq.
      }
      rewrite update_evar_val_same.
      unfold nest_ex.

      rewrite eval_free_evar_independent.
      {
         rewrite Heqx''. unfold evar_is_fresh_in.
         eapply evar_is_fresh_in_richer'.
         2: apply set_evar_fresh_is_fresh'. cbn.
         solve_free_evars_inclusion 5.
      }
      rewrite eval_free_evar_independent.
      {
         rewrite Heqx'. unfold evar_is_fresh_in.
         eapply evar_is_fresh_in_richer'.
         2: apply set_evar_fresh_is_fresh'. cbn.
         solve_free_evars_inclusion 5.
      }
      tauto.
    Qed.

    Lemma Minterp_inhabitant_evar_open_update_evar_val ρ x e s m:
      evar_is_fresh_in x s ->
      m ∈ Minterp_inhabitant (evar_open 0 x (nest_ex s)) (update_evar_val x e ρ)
      <-> m ∈ Minterp_inhabitant s ρ.
    Proof.
      intros Hfr.
      unfold Minterp_inhabitant.
      rewrite 2!eval_app_simpl.
      rewrite 2!eval_sym_simpl.
      unfold nest_ex, evar_open. rewrite nest_ex_same.
      rewrite eval_free_evar_independent; auto.
   Qed.

    Lemma interp_partial_function_injective f s ρ :
      @eval Σ M ρ (patt_partial_function_injective f s) = ⊤ <->
      ∀ (m₁ : Domain M),
        m₁ ∈ Minterp_inhabitant s ρ ->
        ∀ (m₂ : Domain M),
          m₂ ∈ Minterp_inhabitant s ρ ->
          (rel_of ρ f) m₁ ≠ ∅ ->
          (rel_of ρ f) m₁ = (rel_of ρ f) m₂ ->
          m₁ = m₂.
    Proof.
      unfold patt_partial_function_injective.
      rewrite eval_forall_of_sort_predicate.
      1: {
        match goal with
        | [ |- M_predicate _ (evar_open _ ?x _) ] => remember x
        end.
        unfold evar_open. simpl_bevar_subst. simpl.
        apply M_predicate_forall_of_sort.
        match goal with
        | [ |- M_predicate _ (evar_open _ ?x _) ] => remember x
        end.
        unfold evar_open. simpl_bevar_subst. simpl.
        eauto.
      }
      remember
      (fresh_evar
             (patt_forall_of_sort (nest_ex s)
                (! patt_equal (nest_ex (nest_ex f) $ b1) ⊥ --->
                 patt_equal (nest_ex (nest_ex f) $ b1) (nest_ex (nest_ex f) $ b0) --->
                 patt_equal b1 b0)))
      as x₁.
      apply all_iff_morphism. intros m₁.
      apply all_iff_morphism. intros Hm₁s.

      unfold evar_open. simpl_bevar_subst.
      rewrite eval_forall_of_sort_predicate.
      1: { eauto 8. (* TODO be more explicit. Have a tactic for this kind of goals. *) }
      remember
      (fresh_evar
             (! patt_equal
                  ((nest_ex (nest_ex f)).[evar:1↦patt_free_evar x₁] $ b1.[evar:1↦patt_free_evar x₁])
                  ⊥ --->
              patt_equal
                ((nest_ex (nest_ex f)).[evar:1↦patt_free_evar x₁] $ b1.[evar:1↦patt_free_evar x₁])
                ((nest_ex (nest_ex f)).[evar:1↦patt_free_evar x₁] $ b0.[evar:1↦patt_free_evar x₁]) --->
              patt_equal b1.[evar:1↦patt_free_evar x₁] b0.[evar:1↦patt_free_evar x₁]))
      as x₂.

      apply all_iff_morphism. intros m₂.
      rewrite Minterp_inhabitant_evar_open_update_evar_val.
      1: {
        eapply evar_is_fresh_in_richer.
        2: { subst x₁.
             apply set_evar_fresh_is_fresh.
        }
        solve_free_evars_inclusion 5.
      }
      apply all_iff_morphism. intros Hm₂s.
      unfold evar_open. simpl_bevar_subst.
      unfold nest_ex in *.
      rewrite fuse_nest_ex_same in Heqx₂, Heqx₁. rewrite nest_ex_same_general in Heqx₁, Heqx₂.
      1-2: lia.
      rewrite fuse_nest_ex_same. rewrite nest_ex_same_general. 1-2: lia. simpl.
      rewrite nest_ex_same.
      simpl in Heqx₁, Heqx₂.

      rewrite eval_predicate_impl. 1: { eauto. }
      simpl.
      rewrite eval_predicate_not. 1: { eauto. }
      rewrite equal_iff_interpr_same.
      1: apply M_satisfies_theory.
      rewrite eval_bott_simpl.
      rewrite eval_app_simpl.
      rewrite eval_free_evar_simpl.
      rewrite update_evar_val_neq.
      { solve_fresh_neq. }
      rewrite update_evar_val_same.
      rewrite eval_free_evar_independent.
      {
         rewrite Heqx₂. unfold evar_is_fresh_in.
         eapply evar_is_fresh_in_richer'.
         2: apply set_evar_fresh_is_fresh'. cbn.
         solve_free_evars_inclusion 5.
      }
      rewrite eval_free_evar_independent.
      {
         rewrite Heqx₁. unfold evar_is_fresh_in.
         eapply evar_is_fresh_in_richer'.
         2: apply set_evar_fresh_is_fresh'. cbn.
         solve_free_evars_inclusion 5.
      }
      fold (rel_of ρ f m₁).
      apply all_iff_morphism. unfold pointwise_relation. intros Hnonempty.

      rewrite eval_predicate_impl. 1: { eauto. }
      (*rewrite simpl_evar_open.*)
      rewrite equal_iff_interpr_same. 1: apply M_satisfies_theory.
      rewrite 2!eval_app_simpl.
      rewrite equal_iff_interpr_same. 1: { apply M_satisfies_theory. }
      rewrite !eval_free_evar_simpl.
      rewrite update_evar_val_same.
      rewrite update_evar_val_neq.
      { solve_fresh_neq. }
      rewrite update_evar_val_same.
      unfold rel_of.
      rewrite eval_free_evar_independent.
      {
         rewrite Heqx₂. unfold evar_is_fresh_in.
         eapply evar_is_fresh_in_richer'.
         2: apply set_evar_fresh_is_fresh'. cbn.
         solve_free_evars_inclusion 5.
      }
      rewrite eval_free_evar_independent.
      {
         rewrite Heqx₁. unfold evar_is_fresh_in.
         eapply evar_is_fresh_in_richer'.
         2: apply set_evar_fresh_is_fresh'. cbn.
         solve_free_evars_inclusion 5.
      }
      apply all_iff_morphism. intros Hfm1eqfm2.
      clear.
      set_solver.
    Qed.

    Lemma interp_total_function_injective f s ρ :
      @eval Σ M ρ (patt_total_function_injective f s) = ⊤ <->
      total_function_is_injective f (Minterp_inhabitant s ρ) ρ.
    Proof.
      unfold total_function_is_injective.
      unfold patt_partial_function_injective.
      rewrite eval_forall_of_sort_predicate.
      1: {
        match goal with
        | [ |- M_predicate _ (evar_open _ ?x _) ] => remember x
        end.
        unfold evar_open. simpl_bevar_subst. simpl.
        apply M_predicate_forall_of_sort.
        match goal with
        | [ |- M_predicate _ (evar_open _ ?x _) ] => remember x
        end.
        unfold evar_open. simpl_bevar_subst. simpl.
        eauto.
      }
      remember
      (fresh_evar
               (patt_forall_of_sort (nest_ex s)
                  (patt_equal (nest_ex (nest_ex f) $ b1) (nest_ex (nest_ex f) $ b0) ---> patt_equal b1 b0)))
      as x₁.
      apply all_iff_morphism. intros m₁.
      apply all_iff_morphism. intros Hm₁s.

      unfold evar_open. simpl_bevar_subst.
      rewrite eval_forall_of_sort_predicate.
      1: {
                match goal with
        | [ |- M_predicate _ (evar_open _ ?x _) ] => remember x
        end.
        unfold evar_open. simpl_bevar_subst. simpl.
        eauto.
      }
      remember
      (fresh_evar
             (patt_equal
                ((nest_ex (nest_ex f)).[evar:1↦patt_free_evar x₁] $ b1.[evar:1↦patt_free_evar x₁])
                ((nest_ex (nest_ex f)).[evar:1↦patt_free_evar x₁] $ b0.[evar:1↦patt_free_evar x₁]) --->
              patt_equal b1.[evar:1↦patt_free_evar x₁] b0.[evar:1↦patt_free_evar x₁]))
      as x₂.

      apply all_iff_morphism. intros m₂.
      rewrite Minterp_inhabitant_evar_open_update_evar_val.
      1: {
        eapply evar_is_fresh_in_richer.
        2: { subst. apply set_evar_fresh_is_fresh. }
        solve_free_evars_inclusion 5.
      }
      apply all_iff_morphism. intros Hm₂s.
      unfold nest_ex, evar_open in *.
      rewrite fuse_nest_ex_same in Heqx₂, Heqx₁. rewrite nest_ex_same_general in Heqx₁, Heqx₂.
      1-2: lia.
      rewrite fuse_nest_ex_same. rewrite nest_ex_same_general. 1-2: lia. simpl pred.
      simpl_bevar_subst.

      rewrite eval_predicate_impl.
      1: { eauto. }
      simpl.
      
      rewrite equal_iff_interpr_same.
      1: { apply M_satisfies_theory. }
      rewrite 2!eval_app_simpl.
      rewrite eval_free_evar_simpl.
      rewrite update_evar_val_neq.
      { solve_fresh_neq. }
      rewrite update_evar_val_same.

      rewrite eval_free_evar_simpl.
      rewrite update_evar_val_same.
      rewrite nest_ex_same.
      rewrite eval_free_evar_independent.
      {
         rewrite Heqx₂. unfold evar_is_fresh_in.
         eapply evar_is_fresh_in_richer'.
         2: apply set_evar_fresh_is_fresh'. cbn.
         solve_free_evars_inclusion 5.
      }
      rewrite eval_free_evar_independent.
      {
         rewrite Heqx₁. unfold evar_is_fresh_in.
         eapply evar_is_fresh_in_richer'.
         2: apply set_evar_fresh_is_fresh'. cbn.
         solve_free_evars_inclusion 5.
      }
      fold (rel_of ρ f m₁). fold (rel_of ρ f m₂).
      apply all_iff_morphism. intros Hfm1eqfm2.


      rewrite equal_iff_interpr_same.
      1: apply M_satisfies_theory.
      rewrite 2!eval_free_evar_simpl.
      rewrite update_evar_val_same.
      rewrite update_evar_val_neq.
      { solve_fresh_neq. }
      rewrite update_evar_val_same.
      clear. set_solver.
    Qed.

    

    Lemma eval_exists_of_sort
      (s : Pattern)
      (ρ : Valuation)
      (indec : forall (m : Domain M), Decision (m ∈ Minterp_inhabitant s ρ))
      (ϕ : Pattern):
    eval ρ (patt_exists_of_sort s ϕ)
    = stdpp_ext.propset_fa_union (λ (m : Domain M),
      match (indec m) with
      | left _ => eval (update_evar_val (fresh_evar ϕ) m ρ) (evar_open 0 (fresh_evar ϕ) ϕ)
      | right _ => ∅
      end
    ).
    Proof.
      unfold patt_exists_of_sort.
      rewrite eval_ex_simpl. simpl.
      f_equal. apply functional_extensionality.
      intros m.
      remember (fresh_evar (patt_in b0 (patt_inhabitant_set (nest_ex s)) and ϕ)) as x.
      case_match.
      {
        clear Heqd.
        rename e into Hinh.
        unfold evar_open. simpl_bevar_subst. simpl.
        unfold nest_ex. rewrite nest_ex_same.
        rewrite eval_and_simpl.
        unfold Minterp_inhabitant in Hinh.
        replace m with (evar_valuation (update_evar_val x m ρ) x) in Hinh.
        2: { apply update_evar_val_same. }
        rewrite -(@eval_free_evar_independent _ _ ρ x m) in Hinh.
        {
          eapply evar_is_fresh_in_richer.
          2: { subst. apply set_evar_fresh_is_fresh. }
          simpl. clear. unfold nest_ex. rewrite free_evars_nest_ex_aux. set_solver.
        }
        rewrite free_evar_in_patt  in Hinh.
        1: { apply M_satisfies_theory. }
        rewrite Hinh.
        remember (fresh_evar ϕ) as x'.
        assert (Htmp: eval (update_evar_val x m ρ)
          ϕ.[evar:0↦patt_free_evar x] =
          eval (update_evar_val x' m ρ)
          ϕ.[evar:0↦patt_free_evar x']).
        {
          apply eval_fresh_evar_open.
          { subst x.
            eapply evar_is_fresh_in_richer.
            2: { apply set_evar_fresh_is_fresh. }
            simpl. clear. set_solver.
          }
          {
            subst. apply set_evar_fresh_is_fresh.
          }
        }
        rewrite Htmp. clear. unfold_leibniz. set_solver.
      }
      {
        clear Heqd.
        rename n into Hinh.
        unfold evar_open. simpl_bevar_subst.
        rewrite eval_and_simpl. simpl.
        replace m with (evar_valuation (update_evar_val x m ρ) x) in Hinh.
        2: { apply update_evar_val_same. }
        unfold nest_ex. rewrite nest_ex_same.
        unfold Minterp_inhabitant in Hinh.
        rewrite -(@eval_free_evar_independent _ _ ρ x m) in Hinh.
        {
          eapply evar_is_fresh_in_richer.
          2: { subst. apply set_evar_fresh_is_fresh. }
          simpl. clear. unfold nest_ex. rewrite free_evars_nest_ex_aux. set_solver.
        }
        rewrite free_evar_in_patt  in Hinh.
        1:{ apply M_satisfies_theory. }
        rewrite predicate_not_full_iff_empty in Hinh.
        1: { apply T_predicate_in. apply M_satisfies_theory. }
        rewrite Hinh. clear. set_solver.
      }
    Qed.



    Lemma eval_forall_of_sort
      (s : Pattern)
      (ρ : Valuation)
      (indec : forall (m : Domain M), Decision (m ∈ Minterp_inhabitant s ρ))
      (ϕ : Pattern):
    eval ρ (patt_forall_of_sort s ϕ)
    = stdpp_ext.propset_fa_intersection (λ (m : Domain M),
      match (indec m) with
      | left _ => eval (update_evar_val (fresh_evar ϕ) m ρ) (evar_open 0 (fresh_evar ϕ) ϕ)
      | right _ => ⊤
      end
    ).
    Proof.
      unfold patt_forall_of_sort.
      rewrite eval_all_simpl.
      simpl.
      f_equal. apply functional_extensionality.
      intros m.
      remember (fresh_evar
      (patt_in b0 (patt_inhabitant_set (nest_ex s)) ---> ϕ)) as x.
      case_match.
      {
        clear Heqd.
        rename e into Hinh.
        unfold evar_open. simpl_bevar_subst. simpl.
        unfold nest_ex. rewrite nest_ex_same.
        unfold Minterp_inhabitant in Hinh.
        replace m with (evar_valuation (update_evar_val x m ρ) x) in Hinh.
        2: { apply update_evar_val_same. }
        rewrite -(@eval_free_evar_independent _ _ ρ x m) in Hinh.
        {
          eapply evar_is_fresh_in_richer.
          2: { subst. apply set_evar_fresh_is_fresh. }
          simpl. clear. unfold nest_ex. rewrite free_evars_nest_ex_aux. set_solver.
        }
        rewrite free_evar_in_patt in Hinh.
        1: { apply M_satisfies_theory. }
        unfold patt_inhabitant_set.
        unfold Sorts_Syntax.sym.
        unfold sym in Hinh.
        rewrite eval_imp_simpl.
        rewrite Hinh.
        remember (fresh_evar ϕ) as x'.
        assert (Htmp: eval (update_evar_val x m ρ)
          ϕ.[evar:0↦patt_free_evar x] =
          eval (update_evar_val x' m ρ)
          ϕ.[evar:0↦patt_free_evar x']).
        {
          apply eval_fresh_evar_open.
          { subst x.
            eapply evar_is_fresh_in_richer.
            2: { apply set_evar_fresh_is_fresh. }
            simpl. clear. set_solver.
          }
          {
            subst. apply set_evar_fresh_is_fresh.
          }
        }
        rewrite Htmp. clear. unfold_leibniz. set_solver.
      }
      {
        clear Heqd.
        rename n into Hinh.
        unfold evar_open. simpl_bevar_subst.
        rewrite eval_imp_simpl. simpl.
        replace m with (evar_valuation (update_evar_val x m ρ) x) in Hinh.
        2: { apply update_evar_val_same. }
        unfold nest_ex. rewrite nest_ex_same.
        unfold Minterp_inhabitant in Hinh.
        rewrite -(@eval_free_evar_independent _ _ ρ x m) in Hinh.
        {
          eapply evar_is_fresh_in_richer.
          2: { subst. apply set_evar_fresh_is_fresh. }
          simpl. clear. unfold nest_ex. rewrite free_evars_nest_ex_aux. set_solver.
        }
        rewrite free_evar_in_patt  in Hinh.
        1:{ apply M_satisfies_theory. }
        rewrite predicate_not_full_iff_empty in Hinh.
        1: { apply T_predicate_in. apply M_satisfies_theory. }
        rewrite Hinh. clear. set_solver.
      }
    Qed.
    

  End with_model.
    

  #[export]
  Hint Resolve M_predicate_exists_of_sort : core.

  #[export]
  Hint Resolve M_predicate_forall_of_sort : core.

