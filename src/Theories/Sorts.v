From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Coq Require Import Unicode.Utf8.
From Coq.Logic Require Import Classical_Prop FunctionalExtensionality.

From stdpp Require Import base.

From MatchingLogic Require Import Syntax Semantics.
Require Import MatchingLogic.Theories.Definedness.

Import MatchingLogic.Syntax.Notations.
Import MatchingLogic.Syntax.BoundVarSugar.
Import MatchingLogic.Semantics.Notations.

Section sorts.

  Inductive Symbols := inhabitant.

  Context {sig : Signature}.

  Class Syntax :=
    { inj: Symbols -> symbols;
      imported_definedness: @Definedness.Syntax sig;
    }.

  Context {self : Syntax}.

  Existing Instance imported_definedness.

  Local Definition sym (s : Symbols) : @Pattern sig :=
    @patt_sym sig (inj s).
  
  Example test_pattern_1 := patt_equal (sym inhabitant) (sym inhabitant).
  Definition patt_inhabitant_set(phi : Pattern) : Pattern := sym inhabitant $ phi.


  Lemma evar_open_inhabitant_set db x ϕ :
    evar_open db x (patt_inhabitant_set ϕ) = patt_inhabitant_set (evar_open db x ϕ).
  Proof. unfold patt_inhabitant_set. rewrite !simpl_evar_open. reflexivity. Qed.
  
  Lemma svar_open_inhabitant_set db x ϕ :
    svar_open db x (patt_inhabitant_set ϕ) = patt_inhabitant_set (svar_open db x ϕ).
  Proof. unfold patt_inhabitant_set. rewrite !simpl_svar_open. reflexivity. Qed.
  
  #[global]
   Instance Unary_inhabitant_set : Unary patt_inhabitant_set :=
    {| unary_evar_open := evar_open_inhabitant_set ;
       unary_svar_open := svar_open_inhabitant_set ;
    |}.

  (* A pattern representing sort that can be quantified over *)
  (* TODO some instances for automation *)
  Class QSort (patt_sort : Pattern) :=
    { qsort_closed : free_evars patt_sort = ∅ ;
      qsort_not_occur_0 : bevar_occur patt_sort 0 = false;
    }.

  Definition patt_forall_of_sort (sort phi : Pattern) : Pattern :=
    patt_forall ((patt_in (patt_bound_evar 0) (patt_inhabitant_set sort)) ---> phi).

  Definition patt_exists_of_sort (sort phi : Pattern) : Pattern :=
    patt_exists ((patt_in (patt_bound_evar 0) (patt_inhabitant_set sort)) and phi).

  Lemma evar_open_forall_of_sort db x s ϕ :
    bevar_occur s 0 = false ->
    evar_open db x (patt_forall_of_sort s ϕ) = patt_forall_of_sort s (evar_open (db+1) x ϕ).
  Proof.
    unfold patt_forall_of_sort.
    rewrite !simpl_evar_open.
    Check unit. Check id. Check (id 0).
    simpl.
  Abort.
  

    (*
  #[global]
   Instance EBinder_forall_of_sort s (QS : QSort s) : EBinder (patt_forall_of_sort s) :=
    {|
    |}.*)

  
  (* TODO patt_forall_of_sort and patt_exists_of_sorts are duals - a lemma *)

  (* TODO a lemma about patt_forall_of_sort *)
  
  Definition patt_total_function(phi from to : Pattern) : Pattern :=
    patt_forall_of_sort from (patt_exists_of_sort to (patt_equal (patt_app phi b1) b0)).

  Definition patt_partial_function(phi from to : Pattern) : Pattern :=
    patt_forall_of_sort from (patt_exists_of_sort to (patt_subseteq (patt_app phi b1) b0)).

  Section with_model.
    Context {M : Model}.
    Hypothesis M_satisfies_theory : M ⊨ᵀ Definedness.theory.

    Definition Mpatt_inhabitant_set m := app_ext (sym_interp (inj inhabitant)) (Ensembles.Singleton (Domain M) m).

    (* ϕ is expected to be a sort pattern *)
    Definition Minterp_inhabitant ϕ ρₑ ρₛ := @pattern_interpretation sig M ρₑ ρₛ (patt_app (sym inhabitant) ϕ).    
    
    Lemma pattern_interpretation_forall_of_sort_predicate s (Hpss : QSort s) ϕ ρₑ ρₛ:
      let x := fresh_evar ϕ in
      M_predicate M (evar_open 0 x ϕ) ->
      wfc_body_ex ϕ ->
      pattern_interpretation ρₑ ρₛ (patt_forall_of_sort s ϕ) = Full
      <-> (∀ m : Domain M, Minterp_inhabitant s ρₑ ρₛ m ->
                           pattern_interpretation (update_evar_val x m ρₑ) ρₛ (evar_open 0 x ϕ) = Full).
    Proof.
      intros x Hpred Hwfc.
      unfold patt_forall_of_sort.
      assert (Hsub: is_subformula_of_ind ϕ (patt_in b0 (patt_inhabitant_set s) ---> ϕ)).
      { apply sub_imp_r. apply sub_eq. reflexivity.  }
      rewrite pattern_interpretation_forall_predicate.
      2: {
        (*rewrite !simpl_evar_open.*)
        autorewrite with ml_db.
        simpl.
        apply M_predicate_impl.
        - apply T_predicate_in.
          apply M_satisfies_theory.
        - subst x.
          apply M_predicate_evar_open_fresh_evar_2.
          3: apply Hpred. 2: apply Hwfc.
          eapply evar_fresh_in_subformula. eauto. apply set_evar_fresh_is_fresh.
      }
      subst x.
      remember (patt_in b0 (patt_inhabitant_set s) ---> ϕ) as Bigϕ.
      assert (Hfresh: fresh_evar Bigϕ ∉ free_evars (patt_sym (inj inhabitant) $ s)).
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
      
      split.
      - intros H m H'.
        specialize (H m).
        rewrite -(@interpretation_fresh_evar_subterm_2 _ _ _ Bigϕ).
        assumption. assumption.
        rewrite HeqBigϕ in H.
        rewrite evar_open_imp in H.
        rewrite -HeqBigϕ in H.
        
        eapply pattern_interpretation_impl_MP.
        apply H.
        autorewrite with ml_db. simpl.
  
        unfold Minterp_inhabitant in H'.
        pose proof (Hfeip := @free_evar_in_patt _ _ M M_satisfies_theory (fresh_evar Bigϕ) (patt_sym (inj inhabitant) $ evar_open 0 (fresh_evar Bigϕ) s) (update_evar_val (fresh_evar Bigϕ) m ρₑ) ρₛ).
        destruct Hfeip as [Hfeip1 _]. apply Hfeip1. clear Hfeip1.
        rewrite update_evar_val_same.
        clear H. unfold sym in H'.
        unfold Ensembles.In.
        rewrite -> evar_open_not_occur. 2: apply qsort_not_occur_0.

        rewrite -> pattern_interpretation_free_evar_independent.
        2: apply Hfresh.
        apply H'.
        
      - intros H m.
        pose proof (Hfeip := @free_evar_in_patt _ _ M M_satisfies_theory (fresh_evar Bigϕ) (patt_sym (inj inhabitant) $ evar_open 0 (fresh_evar Bigϕ) s) (update_evar_val (fresh_evar Bigϕ) m ρₑ) ρₛ).
        destruct Hfeip as [_ Hfeip2].
        rewrite {3}HeqBigϕ.
        apply pattern_interpretation_predicate_impl.
        2: fold evar_open.
        fold evar_open.
        rewrite evar_open_in. apply T_predicate_in. apply M_satisfies_theory.
        intros H1.
        specialize (Hfeip2 H1). clear H1.
        specialize (H m).
        rewrite -(@interpretation_fresh_evar_subterm_2 _ _ _ Bigϕ) in H.
        apply Hwfc. apply Hsub. apply H. clear H.
        
        unfold Minterp_inhabitant.
        unfold Ensembles.In in Hfeip2. unfold sym.
        rewrite -> evar_open_not_occur in Hfeip2. 2: apply qsort_not_occur_0.
        rewrite -> update_evar_val_same in Hfeip2.
        rewrite -> pattern_interpretation_free_evar_independent in Hfeip2.
        2: apply Hfresh.
        apply Hfeip2.
    Qed.

    Lemma pattern_interpretation_exists_of_sort_predicate s (Hpss : QSort s) ϕ ρₑ ρₛ:
      let x := fresh_evar ϕ in
      M_predicate M (evar_open 0 x ϕ) ->
      wfc_body_ex ϕ ->
      pattern_interpretation ρₑ ρₛ (patt_exists_of_sort s ϕ) = Full
      <-> (∃ m : Domain M, Minterp_inhabitant s ρₑ ρₛ m /\
                           pattern_interpretation (update_evar_val x m ρₑ) ρₛ (evar_open 0 x ϕ) = Full).
    Proof.
      intros x Hpred Hwfc.
      unfold patt_exists_of_sort.
      assert (Hsub: is_subformula_of_ind ϕ (patt_in b0 (patt_inhabitant_set s) and ϕ)).
      { unfold patt_and. unfold patt_or.  apply sub_imp_l. apply sub_imp_r. apply sub_imp_l. apply sub_eq. reflexivity. }
      rewrite -> pattern_interpretation_exists_predicate_full.
      2: {
        autorewrite with ml_db.
        simpl.
        apply M_predicate_and.
        - apply T_predicate_in.
          apply M_satisfies_theory.
        - subst x.
          apply M_predicate_evar_open_fresh_evar_2.
          3: apply Hpred. 2: apply Hwfc.
          eapply evar_fresh_in_subformula. eauto. apply set_evar_fresh_is_fresh.
      }
      subst x.
      remember (patt_in b0 (patt_inhabitant_set s) and ϕ) as Bigϕ.
      assert (Hfresh: fresh_evar Bigϕ ∉ free_evars (patt_sym (inj inhabitant) $ s)).
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
      split.
      - intros [m H].
        exists m.
        rewrite -(@interpretation_fresh_evar_subterm_2 _ _ _ Bigϕ).
        assumption. assumption.
        rewrite {3}HeqBigϕ in H.

        apply pattern_interpretation_and_full in H.
        fold evar_open in H.
        destruct H as [H1 H2].
        split. 2: apply H2. clear H2.
        unfold Minterp_inhabitant.
        pose proof (Hfeip := @free_evar_in_patt _ _ M M_satisfies_theory (fresh_evar Bigϕ) (patt_sym (inj inhabitant) $ evar_open 0 (fresh_evar Bigϕ) s) (update_evar_val (fresh_evar Bigϕ) m ρₑ) ρₛ).
        destruct Hfeip as [_ Hfeip2].

        apply Hfeip2 in H1. clear Hfeip2.
        rewrite update_evar_val_same in H1.
        unfold sym.
        unfold Ensembles.In in H1.
        rewrite -> evar_open_not_occur in H1. 2: apply qsort_not_occur_0.
        rewrite -> pattern_interpretation_free_evar_independent in H1.
        2: apply Hfresh.
        apply H1.
      - intros [m [H1 H2]]. exists m.
        pose proof (Hfeip := @free_evar_in_patt _ _ M M_satisfies_theory (fresh_evar Bigϕ) (patt_sym (inj inhabitant) $ evar_open 0 (fresh_evar Bigϕ) s) (update_evar_val (fresh_evar Bigϕ) m ρₑ) ρₛ).
        destruct Hfeip as [Hfeip1 _].
        rewrite {3}HeqBigϕ.
        apply pattern_interpretation_and_full. fold evar_open.
        split.
        + apply Hfeip1. clear Hfeip1.
          unfold Ensembles.In.
          rewrite -> update_evar_val_same.
          unfold Minterp_inhabitant in H1. unfold sym in H1.
          rewrite -> evar_open_not_occur. 2: apply qsort_not_occur_0.
          rewrite -> pattern_interpretation_free_evar_independent.
          2: apply Hfresh.
          apply H1.
        + rewrite -(@interpretation_fresh_evar_subterm_2 _ _ _ Bigϕ) in H2.
          apply Hwfc. apply Hsub.
          apply H2.
    Qed.


    Lemma M_predicate_exists_of_sort s (Hpss : QSort s) ϕ :
      let x := fresh_evar ϕ in
      M_predicate M (evar_open 0 x ϕ) -> M_predicate M (patt_exists_of_sort s ϕ).
    Proof.
      intros x Hpred.
      unfold patt_exists_of_sort.
      apply M_predicate_exists.
      autorewrite with ml_db. rewrite [if PeanoNat.Nat.eqb 0 0 then _ else _]/=.
      apply M_predicate_and.
      - apply T_predicate_in.
        apply M_satisfies_theory.
      - simpl.
        rewrite -> qsort_closed.
        repeat rewrite sets.union_empty_r_L.
        repeat rewrite sets.union_empty_l_L.
        subst x.
        unfold fresh_evar in Hpred.
        apply Hpred.
    Qed.

    Lemma M_predicate_forall_of_sort s (Hpss : QSort s) ϕ :
      let x := fresh_evar ϕ in
      M_predicate M (evar_open 0 x ϕ) -> M_predicate M (patt_forall_of_sort s ϕ).
    Proof.
      intros x Hpred.
      unfold patt_forall_of_sort.
      apply M_predicate_forall.
      autorewrite with ml_db. rewrite [if PeanoNat.Nat.eqb 0 0 then _ else _]/=.
      apply M_predicate_impl.
      - apply T_predicate_in.
        apply M_satisfies_theory.
      - simpl.
        rewrite -> qsort_closed.
        rewrite !(@right_id _ (=) ∅ (∪) ).
        rewrite (@left_id _ (=) ∅).
        subst x.
        unfold fresh_evar in Hpred.
        apply Hpred.
    Qed.

    
    Lemma interp_total_function f s₁ s₂ (Hpss₁ : QSort s₁) (Hpss₂ : QSort s₂) ρₑ ρₛ :
      @pattern_interpretation sig M ρₑ ρₛ (patt_total_function f s₁ s₂) = Full ->
      ∀ (m₁ : Domain M),
        Minterp_inhabitant s₁ ρₑ ρₛ m₁ ->                 
        ∃ (m₂ : Domain M),
          Minterp_inhabitant s₂ ρₑ ρₛ m₂ ->
          app_ext (@pattern_interpretation sig M ρₑ ρₛ f) (Ensembles.Singleton (Domain M) m₁)
          = Ensembles.Singleton (Domain M) m₂.
    Proof.
      intros Hfun m₁ H1.
      unfold patt_total_function in Hfun.
      rewrite -> pattern_interpretation_forall_of_sort_predicate in Hfun.
      specialize (Hfun m₁ H1).
    Abort.

  End with_model.
    
End sorts.
