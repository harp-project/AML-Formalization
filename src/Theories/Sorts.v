From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Coq Require Import Unicode.Utf8.
From Coq.Logic Require Import Classical_Prop FunctionalExtensionality.

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
  Definition inhabitant_set(phi : Pattern) : Pattern := sym inhabitant $ phi.

  Definition patt_forall_of_sort (sort phi : Pattern) : Pattern :=
    patt_forall ((patt_in (patt_bound_evar 0) (inhabitant_set sort)) ---> phi).

  Definition patt_exists_of_sort (sort phi : Pattern) : Pattern :=
    patt_exists ((patt_in (patt_bound_evar 0) (inhabitant_set sort)) and phi).

  (* TODO patt_forall_of_sort and patt_exists_of_sorts are duals - a lemma *)

  (* TODO a lemma about patt_forall_of_sort *)
  
  Definition patt_total_function(phi from to : Pattern) : Pattern :=
    patt_forall_of_sort from (patt_exists_of_sort to (patt_equal (patt_app phi b1) b0)).

  Definition patt_partial_function(phi from to : Pattern) : Pattern :=
    patt_forall_of_sort from (patt_exists_of_sort to (patt_subseteq (patt_app phi b1) b0)).

  Section with_model.
    Context {M : Model}.
    Hypothesis M_satisfies_theory : M ⊨ᵀ Definedness.theory.

    Definition Minhabitant_set m := app_ext (sym_interp (inj inhabitant)) (Ensembles.Singleton (Domain M) m).

    (* ϕ is expected to be a sort pattern *)
    Definition Minterp_inhabitant ϕ ρₑ ρₛ := @pattern_interpretation sig M ρₑ ρₛ (patt_app (sym inhabitant) ϕ).

    Lemma pattern_interpretation_forall_of_sort_predicate s ϕ ρₑ ρₛ:
      (* s is closed *)
      free_evars s = base.empty ->
      well_formed_closed s ->
      let x := fresh_evar ϕ in
      M_predicate M (evar_open 0 x ϕ) ->
      pattern_interpretation ρₑ ρₛ (patt_forall_of_sort s ϕ) = Full
      <-> (∀ m : Domain M, Minterp_inhabitant s ρₑ ρₛ m ->
                           pattern_interpretation (update_evar_val x m ρₑ) ρₛ (evar_open 0 x ϕ) = Full).
    Proof.
      intros Hs Hwfc x Hpred.
      unfold patt_forall_of_sort.
      assert (Hfr: fresh_evar (patt_in b0 (inhabitant_set s) ---> ϕ) = fresh_evar ϕ).
      { unfold fresh_evar. apply f_equal. apply f_equal. simpl.
        rewrite -> Hs.
        repeat rewrite -> sets.union_empty_l_L.
        auto.
      }
      rewrite pattern_interpretation_forall_predicate.
      2: {
        autorewrite with ml_db.
        simpl.
        apply M_predicate_impl.
        - apply T_predicate_in.
          apply M_satisfies_theory.
        - subst x.
          rewrite -> Hfr.
          apply Hpred.
      }
      subst x.
      split.
      - intros H m H'.
        specialize (H m).
        autorewrite with ml_db in H. simpl in H.
        rewrite -> Hfr in H.
        eapply pattern_interpretation_impl_MP. apply H.
        unfold Minterp_inhabitant in H'.
        pose proof (Hfeip := free_evar_in_patt M M_satisfies_theory (fresh_evar ϕ) (patt_sym (inj inhabitant) $ evar_open 0 (fresh_evar ϕ) s) (update_evar_val (fresh_evar ϕ) m ρₑ) ρₛ).
        destruct Hfeip as [Hfeip1 _]. apply Hfeip1. clear Hfeip1.
        rewrite update_evar_val_same.
        clear H. unfold sym in H'.
        unfold Ensembles.In.
        rewrite -> evar_open_wfc. 2: apply Hwfc.
        rewrite -> pattern_interpretation_free_evar_independent.
        3: { intros Contra. simpl in Contra.
             rewrite -> sets.union_empty_l_L in Contra.
             rewrite -> Hs in Contra.
             apply base.not_elem_of_empty in Contra.
             apply Contra.
        }
        2: { apply wfc_ind_wfc.
             constructor.
             constructor.
             apply wfc_wfc_ind.
             apply Hwfc.
        }
        apply H'.
      - intros H m.
        autorewrite with ml_db. simpl.
        pose proof (Hfeip := free_evar_in_patt M M_satisfies_theory (fresh_evar ϕ) (patt_sym (inj inhabitant) $ evar_open 0 (fresh_evar ϕ) s) (update_evar_val (fresh_evar ϕ) m ρₑ) ρₛ).
        destruct Hfeip as [_ Hfeip2].
        apply pattern_interpretation_predicate_impl.
        apply T_predicate_in. apply M_satisfies_theory.
        intros H1. rewrite -> Hfr in *.
        specialize (Hfeip2 H1). clear H1.
        apply H. unfold Minterp_inhabitant.
        unfold Ensembles.In in Hfeip2. unfold sym.
        rewrite -> evar_open_wfc in Hfeip2. 2: apply Hwfc.
        rewrite -> update_evar_val_same in Hfeip2.
        rewrite -> pattern_interpretation_free_evar_independent in Hfeip2.
        3: { intros Contra. simpl in Contra.
             rewrite -> sets.union_empty_l_L in Contra.
             rewrite -> Hs in Contra.
             apply base.not_elem_of_empty in Contra.
             apply Contra.
        }
        2: { apply wfc_ind_wfc.
             constructor.
             constructor.
             apply wfc_wfc_ind.
             apply Hwfc.
        }
        apply Hfeip2.
    Qed.

    Lemma pattern_interpretation_exists_of_sort_predicate s ϕ ρₑ ρₛ:
      (* s is closed *)
      free_evars s = base.empty ->
      well_formed_closed s ->
      let x := fresh_evar ϕ in
      M_predicate M (evar_open 0 x ϕ) ->
      pattern_interpretation ρₑ ρₛ (patt_exists_of_sort s ϕ) = Full
      <-> (∃ m : Domain M, Minterp_inhabitant s ρₑ ρₛ m /\
                           pattern_interpretation (update_evar_val x m ρₑ) ρₛ (evar_open 0 x ϕ) = Full).
    Proof.
      intros Hs Hwfc x Hpred.
      unfold patt_exists_of_sort.
      assert (Hfr: fresh_evar (patt_in b0 (inhabitant_set s) and ϕ) = fresh_evar ϕ).
      { unfold fresh_evar. apply f_equal. apply f_equal. simpl.
        rewrite -> Hs.
        repeat rewrite -> sets.union_empty_r_L.
        rewrite -> sets.union_empty_l_L.
        auto.
      }
      rewrite -> pattern_interpretation_exists_predicate_full.
      2: {
        autorewrite with ml_db.
        simpl.
        apply M_predicate_and.
        - apply T_predicate_in.
          apply M_satisfies_theory.
        - subst x.
          rewrite -> Hfr.
          apply Hpred.
      }
      subst x.
      split.
      - intros [m H].
        autorewrite with ml_db in H. simpl in H.
        rewrite -> Hfr in H.
        apply pattern_interpretation_and_full in H.
        destruct H as [H1 H2].
        exists m. split. 2: apply H2. clear H2.
        unfold Minterp_inhabitant.
        pose proof (Hfeip := free_evar_in_patt M M_satisfies_theory (fresh_evar ϕ) (patt_sym (inj inhabitant) $ evar_open 0 (fresh_evar ϕ) s) (update_evar_val (fresh_evar ϕ) m ρₑ) ρₛ).
        destruct Hfeip as [_ Hfeip2]. apply Hfeip2 in H1. clear Hfeip2.
        rewrite update_evar_val_same in H1.
        unfold sym.
        unfold Ensembles.In in H1.
        rewrite -> evar_open_wfc in H1. 2: apply Hwfc.
        rewrite -> pattern_interpretation_free_evar_independent in H1.
        3: { intros Contra. simpl in Contra.
             rewrite -> sets.union_empty_l_L in Contra.
             rewrite -> Hs in Contra.
             apply base.not_elem_of_empty in Contra.
             apply Contra.
        }
        2: { apply wfc_ind_wfc.
             constructor.
             constructor.
             apply wfc_wfc_ind.
             apply Hwfc.
        }
        apply H1.
      - intros [m [H1 H2]]. exists m.
        autorewrite with ml_db. simpl.
        pose proof (Hfeip := free_evar_in_patt M M_satisfies_theory (fresh_evar ϕ) (patt_sym (inj inhabitant) $ evar_open 0 (fresh_evar ϕ) s) (update_evar_val (fresh_evar ϕ) m ρₑ) ρₛ).
        destruct Hfeip as [Hfeip1 _].
        apply pattern_interpretation_and_full.
        rewrite -> Hfr.
        split.
        + apply Hfeip1. clear Hfeip1.
          unfold Ensembles.In.
          rewrite -> update_evar_val_same.
          unfold Minterp_inhabitant in H1. unfold sym in H1.
          rewrite -> evar_open_wfc. 2: apply Hwfc.
          rewrite -> pattern_interpretation_free_evar_independent.
          3: { intros Contra. simpl in Contra.
               rewrite -> sets.union_empty_l_L in Contra.
               rewrite -> Hs in Contra.
               apply base.not_elem_of_empty in Contra.
               apply Contra.
          }
          2: { apply wfc_ind_wfc.
               constructor.
               constructor.
               apply wfc_wfc_ind.
               apply Hwfc.
          }
          apply H1.
        + apply H2.
    Qed.


    Lemma M_predicate_exists_of_sort s ϕ :
      (* s is closed *)
      free_evars s = base.empty ->
      well_formed_closed s ->
      let x := fresh_evar ϕ in
      M_predicate M (evar_open 0 x ϕ) -> M_predicate M (patt_exists_of_sort s ϕ).
    Proof.
      intros Hclosed Hwfc x Hpred.
      unfold patt_exists_of_sort.
      apply M_predicate_exists.
      autorewrite with ml_db. rewrite [if PeanoNat.Nat.eqb 0 0 then _ else _]/=.
      apply M_predicate_and.
      - apply T_predicate_in.
        apply M_satisfies_theory.
      - simpl.
        rewrite -> Hclosed.
        repeat rewrite sets.union_empty_r_L.
        repeat rewrite sets.union_empty_l_L.
        subst x.
        unfold fresh_evar in Hpred.
        apply Hpred.
    Qed.

    Lemma M_predicate_forall_of_sort s ϕ :
      (* s is closed *)
      free_evars s = base.empty ->
      well_formed_closed s ->
      let x := fresh_evar ϕ in
      M_predicate M (evar_open 0 x ϕ) -> M_predicate M (patt_forall_of_sort s ϕ).
    Proof.
      intros Hclosed Hwfc x Hpred.
      unfold patt_forall_of_sort.
      apply M_predicate_forall.
      autorewrite with ml_db. rewrite [if PeanoNat.Nat.eqb 0 0 then _ else _]/=.
      apply M_predicate_impl.
      - apply T_predicate_in.
        apply M_satisfies_theory.
      - simpl.
        rewrite -> Hclosed.
        repeat rewrite sets.union_empty_r_L.
        repeat rewrite sets.union_empty_l_L.
        subst x.
        unfold fresh_evar in Hpred.
        apply Hpred.
    Qed.
      
    
    Lemma interp_total_function f s₁ s₂ ρₑ ρₛ :
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
      (*Search patt_forall_of_sort.*)
    Abort.

  End with_model.
    
End sorts.
