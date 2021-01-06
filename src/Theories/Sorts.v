From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Setoid.
From Coq Require Import Unicode.Utf8.
From Coq.Logic Require Import Classical_Prop FunctionalExtensionality.
From Coq.Classes Require Import Morphisms_Prop.

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

  Definition patt_forall_of_sort (sort phi : Pattern) : Pattern :=
    patt_forall ((patt_in (patt_bound_evar 0) (patt_inhabitant_set (nest_ex sort))) ---> phi).

  Definition patt_exists_of_sort (sort phi : Pattern) : Pattern :=
    patt_exists ((patt_in (patt_bound_evar 0) (patt_inhabitant_set (nest_ex sort))) and phi).

  Lemma evar_open_forall_of_sort s db x ϕ :
    evar_open db x (patt_forall_of_sort s ϕ) = patt_forall_of_sort (evar_open db x s) (evar_open (db+1) x ϕ).
  Proof.
    unfold patt_forall_of_sort.
    rewrite !simpl_evar_open.
    (* TODO rewrite all _+1 to 1+_ *)
    rewrite PeanoNat.Nat.add_comm. simpl.
    unfold nest_ex.
    rewrite evar_open_nest_ex_aux_comm.
    simpl.
    rewrite PeanoNat.Nat.sub_0_r.
    reflexivity.
  Qed.

  Lemma svar_open_forall_of_sort s db X ϕ :
    svar_open db X (patt_forall_of_sort s ϕ) = patt_forall_of_sort (svar_open db X s) (svar_open db X ϕ).
  Proof.
    unfold patt_forall_of_sort.
    rewrite !simpl_svar_open. simpl.
    rewrite svar_open_nest_ex_comm.
    reflexivity.
  Qed. 

  Lemma evar_open_exists_of_sort s db x ϕ :
    evar_open db x (patt_exists_of_sort s ϕ) = patt_exists_of_sort (evar_open db x s) (evar_open (db+1) x ϕ).
  Proof.
    unfold patt_exists_of_sort.
    rewrite !simpl_evar_open.
    (* TODO rewrite all _+1 to 1+_ *)
    rewrite PeanoNat.Nat.add_comm. simpl.
    unfold nest_ex.
    rewrite evar_open_nest_ex_aux_comm.
    simpl.
    rewrite PeanoNat.Nat.sub_0_r.
    reflexivity.
  Qed.

  Lemma svar_open_exists_of_sort s db X ϕ :
    svar_open db X (patt_exists_of_sort s ϕ) = patt_exists_of_sort (svar_open db X s) (svar_open db X ϕ).
  Proof.
    unfold patt_exists_of_sort.
    rewrite !simpl_svar_open. simpl.
    rewrite svar_open_nest_ex_comm.
    reflexivity.
  Qed.
    
  #[global]
   Instance EBinder_forall_of_sort s : EBinder (patt_forall_of_sort s) _ _:=
    {|
    ebinder_evar_open := evar_open_forall_of_sort s ;
    ebinder_svar_open := svar_open_forall_of_sort s ;
    |}.

  #[global]
   Instance EBinder_exists_of_sort s : EBinder (patt_exists_of_sort s) _ _:=
    {|
    ebinder_evar_open := evar_open_exists_of_sort s ;
    ebinder_svar_open := svar_open_exists_of_sort s ;
    |}.
  
  (* TODO patt_forall_of_sort and patt_exists_of_sorts are duals - a lemma *)

  (* TODO a lemma about patt_forall_of_sort *)
  
  Definition patt_total_function(phi from to : Pattern) : Pattern :=
    patt_forall_of_sort from (patt_exists_of_sort (nest_ex to) (patt_equal (patt_app (nest_ex (nest_ex phi)) b1) b0)).

  Definition patt_partial_function(phi from to : Pattern) : Pattern :=
    patt_forall_of_sort from (patt_exists_of_sort (nest_ex to) (patt_subseteq (patt_app (nest_ex (nest_ex phi)) b1) b0)).

  Section with_model.
    Context {M : Model}.
    Hypothesis M_satisfies_theory : M ⊨ᵀ Definedness.theory.

    Definition Mpatt_inhabitant_set m := app_ext (sym_interp (inj inhabitant)) (Ensembles.Singleton (Domain M) m).

    (* ϕ is expected to be a sort pattern *)
    Definition Minterp_inhabitant ϕ ρₑ ρₛ := @pattern_interpretation sig M ρₑ ρₛ (patt_app (sym inhabitant) ϕ).    
    
    Lemma pattern_interpretation_forall_of_sort_predicate s ϕ ρₑ ρₛ:
      let x := fresh_evar ϕ in
      M_predicate M (evar_open 0 x ϕ) ->
      pattern_interpretation ρₑ ρₛ (patt_forall_of_sort s ϕ) = Full
      <-> (∀ m : Domain M, Minterp_inhabitant s ρₑ ρₛ m ->
                           pattern_interpretation (update_evar_val x m ρₑ) ρₛ (evar_open 0 x ϕ) = Full).
    Proof.
      intros x Hpred.
      unfold patt_forall_of_sort.
      assert (Hsub: is_subformula_of_ind ϕ (patt_in b0 (patt_inhabitant_set (nest_ex s)) ---> ϕ)).
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
        (*rewrite -interpretation_fresh_evar_subterm.*)
        rewrite -(@interpretation_fresh_evar_subterm _ _ _ Bigϕ).
        rewrite HeqBigϕ in H.
        rewrite evar_open_imp in H.
        rewrite -HeqBigϕ in H.
        assumption.
        rewrite {3}HeqBigϕ in H.
        eapply pattern_interpretation_impl_MP.
        apply H.
        autorewrite with ml_db. simpl. fold evar_open.
  
        unfold Minterp_inhabitant in H'.
        pose proof (Hfeip := @free_evar_in_patt _ _ M M_satisfies_theory (fresh_evar Bigϕ) (patt_sym (inj inhabitant) $ evar_open 0 (fresh_evar Bigϕ) (nest_ex s)) (update_evar_val (fresh_evar Bigϕ) m ρₑ) ρₛ).
        destruct Hfeip as [Hfeip1 _]. apply Hfeip1. clear Hfeip1.
        rewrite update_evar_val_same.
        clear H. unfold sym in H'.
        unfold Ensembles.In.
        
        rewrite pattern_interpretation_app_simpl.
        rewrite pattern_interpretation_evar_open_nest_ex. apply Hfrs.
        rewrite pattern_interpretation_sym_simpl.

        rewrite pattern_interpretation_app_simpl in H'.
        rewrite pattern_interpretation_sym_simpl in H'.
        apply H'.

      - intros H m.
        pose proof (Hfeip := @free_evar_in_patt _ _ M M_satisfies_theory (fresh_evar Bigϕ) (patt_sym (inj inhabitant) $ evar_open 0 (fresh_evar Bigϕ) (nest_ex s)) (update_evar_val (fresh_evar Bigϕ) m ρₑ) ρₛ).
        destruct Hfeip as [_ Hfeip2].
        rewrite {3}HeqBigϕ.
        apply pattern_interpretation_predicate_impl.
        2: fold evar_open.
        fold evar_open.
        rewrite evar_open_in. apply T_predicate_in. apply M_satisfies_theory.
        intros H1.
        specialize (Hfeip2 H1). clear H1.
        specialize (H m).
        rewrite -(@interpretation_fresh_evar_subterm _ _ _ Bigϕ) in H.
        apply Hsub. apply H. clear H.
        
        unfold Minterp_inhabitant.
        unfold Ensembles.In in Hfeip2. unfold sym.


        rewrite pattern_interpretation_app_simpl in Hfeip2.
        rewrite pattern_interpretation_evar_open_nest_ex in Hfeip2. apply Hfrs.
        rewrite pattern_interpretation_sym_simpl in Hfeip2.

        rewrite pattern_interpretation_app_simpl.
        rewrite pattern_interpretation_sym_simpl.
        rewrite update_evar_val_same in Hfeip2.
        apply Hfeip2.
    Qed.

    Lemma pattern_interpretation_exists_of_sort_predicate s ϕ ρₑ ρₛ:
      let x := fresh_evar ϕ in
      M_predicate M (evar_open 0 x ϕ) ->
      pattern_interpretation ρₑ ρₛ (patt_exists_of_sort s ϕ) = Full
      <-> (∃ m : Domain M, Minterp_inhabitant s ρₑ ρₛ m /\
                           pattern_interpretation (update_evar_val x m ρₑ) ρₛ (evar_open 0 x ϕ) = Full).
    Proof.
      intros x Hpred.
      unfold patt_exists_of_sort.
      assert (Hsub: is_subformula_of_ind ϕ (patt_in b0 (patt_inhabitant_set (nest_ex s)) and ϕ)).
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
        rewrite -(@interpretation_fresh_evar_subterm _ _ _ Bigϕ).
        assumption.
        rewrite {3}HeqBigϕ in H.

        apply pattern_interpretation_and_full in H.
        fold evar_open in H.
        destruct H as [H1 H2].
        split. 2: apply H2. clear H2.
        unfold Minterp_inhabitant.
        pose proof (Hfeip := @free_evar_in_patt _ _ M M_satisfies_theory (fresh_evar Bigϕ) (patt_sym (inj inhabitant) $ evar_open 0 (fresh_evar Bigϕ) (nest_ex s)) (update_evar_val (fresh_evar Bigϕ) m ρₑ) ρₛ).
        destruct Hfeip as [_ Hfeip2].

        apply Hfeip2 in H1. clear Hfeip2.
        rewrite update_evar_val_same in H1.
        unfold sym.
        unfold Ensembles.In in H1.

        rewrite pattern_interpretation_app_simpl in H1.
        rewrite pattern_interpretation_evar_open_nest_ex in H1. apply Hfrs.
        rewrite pattern_interpretation_sym_simpl in H1.

        rewrite pattern_interpretation_app_simpl.
        rewrite pattern_interpretation_sym_simpl.
        apply H1.
        
      - intros [m [H1 H2]]. exists m.
        pose proof (Hfeip := @free_evar_in_patt _ _ M M_satisfies_theory (fresh_evar Bigϕ) (patt_sym (inj inhabitant) $ evar_open 0 (fresh_evar Bigϕ) (nest_ex s)) (update_evar_val (fresh_evar Bigϕ) m ρₑ) ρₛ).
        destruct Hfeip as [Hfeip1 _].
        rewrite {3}HeqBigϕ.
        apply pattern_interpretation_and_full. fold evar_open.
        split.
        + apply Hfeip1. clear Hfeip1.
          unfold Ensembles.In.
          rewrite -> update_evar_val_same.
          unfold Minterp_inhabitant in H1. unfold sym in H1.

          rewrite pattern_interpretation_app_simpl in H1.
          rewrite pattern_interpretation_sym_simpl in H1.

          rewrite pattern_interpretation_app_simpl.
          rewrite pattern_interpretation_evar_open_nest_ex. apply Hfrs.
          rewrite pattern_interpretation_sym_simpl.
          apply H1.
        + rewrite -(@interpretation_fresh_evar_subterm _ _ _ Bigϕ) in H2.
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
      autorewrite with ml_db. rewrite [if PeanoNat.Nat.eqb 0 0 then _ else _]/=.
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

    Lemma M_predicate_forall_of_sort s ϕ :
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
      - subst x.
        apply M_predicate_evar_open_fresh_evar_2.
        2: apply Hpred.
        eapply evar_fresh_in_subformula. 2: apply set_evar_fresh_is_fresh.
        apply sub_imp_r. apply sub_eq. reflexivity.
    Qed.

    
    Lemma interp_total_function f s₁ s₂ ρₑ ρₛ :
      @pattern_interpretation sig M ρₑ ρₛ (patt_total_function f s₁ s₂) = Full <->
      ∀ (m₁ : Domain M),
        Minterp_inhabitant s₁ ρₑ ρₛ m₁ ->                 
        ∃ (m₂ : Domain M),
          Minterp_inhabitant (nest_ex s₂) ρₑ ρₛ m₂ /\
          app_ext (@pattern_interpretation sig M ρₑ ρₛ f) (Ensembles.Singleton (Domain M) m₁)
          = Ensembles.Singleton (Domain M) m₂.
    Proof.      
      rewrite pattern_interpretation_forall_of_sort_predicate.
      2: rewrite !simpl_evar_open; apply M_predicate_exists_of_sort;
        apply T_predicate_equals; apply M_satisfies_theory.

      rewrite !simpl_evar_open.
      remember (fresh_evar (patt_exists_of_sort (nest_ex s₂) (patt_equal ((nest_ex (nest_ex f)) $ b1) b0))) as x'.
      rewrite [nest_ex s₂]/nest_ex.
      rewrite evar_open_nest_ex_aux_comm. simpl.
      rewrite -/(nest_ex s₂).

      apply all_iff_morphism.
      unfold pointwise_relation. intros m₁.
      apply all_iff_morphism. unfold pointwise_relation. intros Hinh1.
      
      rewrite pattern_interpretation_exists_of_sort_predicate.
      2: rewrite !simpl_evar_open; apply T_predicate_equals; apply M_satisfies_theory.
      apply ex_iff_morphism. unfold pointwise_relation. intros m₂.

      unfold Minterp_inhabitant.
      rewrite 2!pattern_interpretation_app_simpl.
      rewrite 2!pattern_interpretation_sym_simpl.
      rewrite pattern_interpretation_free_evar_independent.
      fold (evar_is_fresh_in x' (nest_ex s₂)).

      assert (Hfreq: x' = fresh_evar (patt_imp s₂ (nest_ex (nest_ex f)))).
      { rewrite Heqx'. unfold fresh_evar. apply f_equal. simpl.
        rewrite 2!free_evars_nest_ex_aux.
        rewrite !(left_id_L ∅ union). rewrite !(right_id_L ∅ union).
        rewrite (idemp_L union). reflexivity.
      }

      rewrite Hfreq.
      unfold nest_ex.
      unfold evar_is_fresh_in.
      rewrite free_evars_nest_ex_aux.
      fold (evar_is_fresh_in (fresh_evar (s₂ ---> f)) s₂).
      eapply evar_fresh_in_subformula'. 2: apply set_evar_fresh_is_fresh.
      simpl. rewrite is_subformula_of_refl. rewrite orb_true_r. auto.

      apply and_iff_morphism. auto.

      unfold nest_ex.      
      rewrite !simpl_evar_open.
      rewrite evar_open_nest_ex_aux_comm. simpl.
      rewrite evar_open_nest_ex_aux_comm. simpl.
      fold (nest_ex f). fold (nest_ex (nest_ex f)).
      
      
      remember (fresh_evar (patt_equal (nest_ex (nest_ex f) $ patt_free_evar x') b0)) as x''.

      rewrite equal_iff_interpr_same. 2: apply M_satisfies_theory.
      simpl. rewrite pattern_interpretation_free_evar_simpl.
      rewrite update_evar_val_same.
      rewrite pattern_interpretation_app_simpl.
      rewrite pattern_interpretation_free_evar_simpl.

      (*  Hx''neqx' : x'' ≠ x'
          Hx''freeinf : x'' ∉ free_evars f
       *)
      pose proof (HB := @set_evar_fresh_is_fresh' _ (free_evars(patt_equal (nest_ex (nest_ex f) $ patt_free_evar x') b0))).
      pose proof (Heqx''2 := Heqx'').
      unfold fresh_evar in Heqx''2.
      rewrite -Heqx''2 in HB.
      simpl in HB.
      rewrite !(left_id_L ∅ union) in HB.
      rewrite !(right_id_L ∅ union) in HB.
      apply sets.not_elem_of_union in HB. destruct HB as [HB _].
      apply sets.not_elem_of_union in HB. destruct HB as [Hx''freeinf Hx''neqx'].
      apply stdpp_ext.not_elem_of_singleton_1 in Hx''neqx'.
      unfold nest_ex in Hx''freeinf.
      rewrite 2!free_evars_nest_ex_aux in Hx''freeinf.

      (* Hx'fr : x' ∉ free_evars f *)
      pose proof (Hx'fr := @set_evar_fresh_is_fresh _ (patt_exists_of_sort (nest_ex s₂) (patt_equal (nest_ex (nest_ex f) $ b1) b0))).
      rewrite -Heqx' in Hx'fr.
      unfold evar_is_fresh_in in Hx'fr. simpl in Hx'fr.
      rewrite !(left_id_L ∅ union) in Hx'fr.
      rewrite !(right_id_L ∅ union) in Hx'fr.
      apply sets.not_elem_of_union in Hx'fr. destruct Hx'fr as [_ Hx'fr].
      apply sets.not_elem_of_union in Hx'fr. destruct Hx'fr as [Hx'fr _].
      rewrite 2!free_evars_nest_ex_aux in Hx'fr.
      
      rewrite {2}update_evar_val_comm. apply Hx''neqx'.
      rewrite update_evar_val_same.
      unfold nest_ex.
      rewrite evar_open_nest_ex_aux_comm. simpl.
      fold (nest_ex f). fold (nest_ex (nest_ex f)).

      unfold nest_ex.
      rewrite 2!pattern_interpretation_nest_ex_aux.

      rewrite pattern_interpretation_free_evar_independent. assumption.
      rewrite pattern_interpretation_free_evar_independent. assumption.
      auto.      
    Qed.

  End with_model.
    
End sorts.
