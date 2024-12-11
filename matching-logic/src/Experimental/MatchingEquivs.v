From Coq Require Import ssreflect ssrfun ssrbool.

Require Import Equations.Prop.Equations.

From Coq Require Import String Setoid.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.Classical_Prop.
From Coq.Logic Require Import FunctionalExtensionality Eqdep_dec.
From Coq.Classes Require Import Morphisms_Prop.
From Coq.Unicode Require Import Utf8.
From Coq.micromega Require Import Lia.

From MatchingLogic Require Import Logic ProofMode.MLPM Substitution DerivedOperators_Semantics.
From MatchingLogic.Theories Require Import Definedness_Syntax Definedness_ProofSystem FOEquality_ProofSystem DeductionTheorem Definedness_Semantics.
From MatchingLogic.Utils Require Import stdpp_ext.

Require Import MatchingLogic.wftactics.

From stdpp Require Import base fin_sets sets propset proof_irrel option list tactics.

Import extralibrary.

Import MatchingLogic.Logic.Notations.
Import MatchingLogic.Theories.Definedness_Syntax.Notations.

Require Import Experimental.Unification.

Set Default Proof Mode "Classic".

Close Scope equations_scope. (* Because of [!] *)

Open Scope ml_scope.
Open Scope string_scope.
Open Scope list_scope.

Section MatchingEquivs.
  Context {Σ : Signature} {syntax : Syntax}.

  Context (Γ : Theory).
  Hypothesis (HΓ : theory ⊆ Γ).

  (* Proof for Γ ⊢ (θ -> (l = ti)) <-> (l /\ θ = ti /\ θ) *) 

  (* Helper lemma for predicate patterns. *)
  Lemma predicate_iff φ₁ φ₂ :
well_formed φ₁ ->
    well_formed φ₂ ->
    Γ ⊢ is_predicate_pattern φ₁ --->
        is_predicate_pattern φ₂ --->
        is_predicate_pattern (φ₁ <---> φ₂).
  Proof.
    intros Hwfφ₁ Hwfφ₂.
    toMLGoal. simpl. unfold is_predicate_pattern. wf_auto2.
    do 2 mlIntro.
    unfold patt_iff.
    opose proof* (predicate_and Γ (φ₁ ---> φ₂) (φ₂ ---> φ₁));
    [auto | wf_auto2 .. |].
    opose proof* (predicate_imp Γ φ₁ φ₂); auto.
    opose proof* (predicate_imp Γ φ₂ φ₁); auto.
mlAdd H. mlAdd H0. mlAdd H1. clear H H0 H1.
    mlAssert ("0dup" : (is_predicate_pattern φ₁)).
    wf_auto2. mlExact "0".
    mlAssert ("1dup" : (is_predicate_pattern φ₂)).
    wf_auto2. mlExact "1".
    mlApply "3" in "0". mlApply "0" in "1".
    mlApply "4" in "1dup". mlApply "1dup" in "0dup".
    mlApply "2" in "1". mlApply "1" in "0dup".
    mlExact "0dup".
  Defined.

  Lemma extract_common_from_equality_r_2 a b p :
    well_formed a -> well_formed b -> well_formed p ->
    Γ ⊢ is_predicate_pattern p --->
    (p ---> a =ml b) <---> (a and p) =ml (b and p).
  Proof.
    intros Hwfa Hwfb Hwfp.
    mlIntro.
    mlSplitAnd; mlIntro.
    - 
      assert (Γ ⊢ is_predicate_pattern (a =ml b)). {
        unfold patt_equal.
        mlFreshEvar as x.
        mlFreshEvar as y.
        mlFreshEvar as z.
        apply (floor_is_predicate Γ (a <---> b) AnyReasoning x y z).
        auto. wf_auto2. fm_solve. fm_solve. fm_solve. try_solve_pile.
      }
      opose proof* (predicate_imp Γ p (a =ml b));
      [auto .. | wf_auto2 |].
      mlAdd H. mlAdd H0. clear H H0.
      mlApply "3" in "0". mlApply "0" in "2". mlClear "0". mlClear "3".
      opose proof* (predicate_equiv Γ (p ---> a =ml b)).
      auto. wf_auto2.
      mlApplyMeta H in "2". mlDestructAnd "2". mlApply "0" in "1".
      mlClear "0". mlClear "3".
      mlFreshEvar as x.
      mlDeduct "1".
      remember (ExGen := _, SVSubst := _, KT:= _, AKT := _) as i.
      remember (_ ∪ _ : Theory) as Γ'.
      opose proof* (hypothesis Γ' (p ---> a =ml b)).
      wf_auto2. set_solver.
      use i in H0.
      opose proof* (total_phi_impl_phi Γ' (a <---> b) x).
      set_solver. fm_solve. wf_auto2.
      use i in H1.
      epose proof syllogism_meta _ _ _ H0 H1.
      pose proof extract_common_from_equivalence_r Γ' _ _ _ i Hwfp Hwfa Hwfb.
      epose proof pf_iff_proj2 _ _ _ _ _ _ H3.
      pose proof MP H2 H4.
      mlRewrite H5 at 1. mlReflexivity.
      Unshelve.
      subst i. simpl.
      admit. (* TODO: revise definedness to make solvable *)
      all: wf_auto2.
    -
      mlIntro.
      mlApplyMeta (predicate_equiv _ _ HΓ Hwfp) in "0".
      mlDestructAnd "0". mlApply "3" in "2".
      mlClear "3". mlClear "4".
      epose proof patt_total_and _ _ _ HΓ _ _.
      use AnyReasoning in H.
      epose proof pf_iff_proj2 _ _ _ _ _ _ H.
      mlConj "1" "2" as "0".
      mlApplyMeta H0 in "0".
      clear H H0. mlClear "1". mlClear "2".
      mlDeduct "0".
      remember (ExGen := _, SVSubst := _, KT:= _, AKT := _) as i.
      remember (_ ∪ _ : Theory) as Γ'.
      opose proof* (hypothesis Γ' (((a and p <---> b and p) and p))).
      wf_auto2. set_solver. use i in H.
      pose proof extract_common_from_equivalence_r Γ' _ _ _ i Hwfp Hwfa Hwfb.
      epose proof pf_iff_proj1 Γ' _ _ i _ _ H0.
      epose proof lhs_from_and Γ' _ _ _ i _ _ _ H1.
      pose proof MP H H2.
      mlRewrite H3 at 1.
      mlReflexivity.
      Unshelve.
      all: wf_auto2.
  Admitted.

  (* Proof for Γ ⊢ (∃. (l = ti)) <-> (ti ∈ ∃. l) *) 

  (* Single exists version. *)
  Goal forall l ti,
    well_formed (ex, l) ->
    well_formed ti ->
    mu_free l ->
    (forall x, Γ ⊢ is_functional l^{evar: 0 ↦ x}) ->
    Γ ⊢ is_functional ti ->
    Γ ⊢ (ex, (l =ml ti)) <---> ti ∈ml (ex, l).
  Proof.
    intros * wfl wfti mfl fpl fpti.
    mlFreshEvar as y.
    assert (y ∉ free_evars l ∪ free_evars ti)
      by (ltac2:(_fm_export_everything ()); set_solver).
    assert (forall x, ti^{evar:0↦x} = ti)
      by (intros; apply evar_open_not_occur; wf_auto2).
    mlSplitAnd; mlIntro.
    1: unshelve mlApplyMeta membership_exists_2; auto.
    2: unshelve mlApplyMeta membership_exists_1 in "0"; auto.
    all: mlDestructEx "0" as x; mlExists x.
    all: mlSimpl; rewrite ! H0.
    -
      mlRewriteBy "0" at 1.
      mlApplyMeta membership_refl.
      mlExactMeta fpti. auto.
    -
      opose proof* (membership_imp_equal Γ ti (l^{evar:0↦x})); auto.
      now apply mu_free_bevar_subst. wf_auto2.
      pose proof (MP fpti H1); clear H1.
      pose proof (MP (fpl x) H2); clear H2.
      mlSymmetry. now fromMLGoal.
  Qed.

  (* Definitions for multiple exists version. *)

  Fixpoint functional_when_applied (n : nat) (φ : Pattern) :=
    match n with
    | 0 => derives Γ (is_functional φ)
    | S m => forall x, functional_when_applied m (evar_open x 0 φ)
    end.

  Fixpoint many_ex (n : nat) (φ : Pattern) :=
    match n with
    | 0 => φ
    | S m => ex, many_ex m φ
    end.

  Lemma many_ex_travels n : forall φ, (ex, many_ex n φ) = many_ex n (ex, φ).
  Proof.
    induction n; simpl; intros.
    reflexivity.
    rewrite IHn. reflexivity.
  Defined. 

  Lemma well_formed_many_ex n : ∀ m φ,
    m <= n ->
    well_formed_closed_ex_aux φ m ->
    well_formed_closed_mu_aux φ 0 ->
    well_formed_positive φ ->
    well_formed (many_ex n φ).
  Proof.
    induction n; simpl; intros.
    inversion H; subst. wf_auto2.
    rewrite many_ex_travels.
    inversion H; subst.
    apply well_formed_closed_ex_all in H0.
    apply (IHn n (ex, φ)); auto. wf_auto2.
    apply (IHn m (ex, φ)); auto. wf_auto2.
  Defined.

  Lemma free_evars_many_ex n φ : free_evars (many_ex n φ) = free_evars φ.
  Proof.
    now induction n.
  Defined.

  Lemma many_ex_subst n x φ : ∀ m, (many_ex n φ)^{evar:m↦x} = many_ex n (φ^{evar:m + n↦x}).
  Proof.
    induction n; simpl; intros.
    f_equal. auto.
    mlSimpl. rewrite (IHn (S m)). do 3 f_equal. auto.
  Defined.

  Lemma membership_many_ex n φ φ' :
    well_formed φ -> well_formed φ' ->
    Γ ⊢ φ ∈ml (many_ex n φ') <---> many_ex n (φ ∈ml φ').
  Proof.
    intros Hwfφ Hwfφ'.
    induction n; simpl.
    aapply pf_iff_equiv_refl. wf_auto2.
    mlFreshEvar as y.
    opose proof (well_formed_many_ex n 0 φ' _ _ _ _). lia. 1-3: wf_auto2.
    opose proof (well_formed_many_ex n 0 (φ ∈ml φ') _ _ _ _). lia. 1-3: wf_auto2.
    opose proof (membership_exists Γ φ y (many_ex n φ') AnyReasoning HΓ _ _ _ _).
    wf_auto2. auto.
    rewrite (free_evars_many_ex n φ'). ltac2:(fm_solve ()).
    try_solve_pile.
    toMLGoal.
    wf_auto2.
    mlRewrite H1 at 1.
    mlRewrite IHn at 1.
    mlReflexivity.
  Defined.

  Lemma fwa_drop_one : forall n m l y,
    m <= n ->
    functional_when_applied (S n) l → functional_when_applied n l^{evar:m↦y}.
  Proof.
    induction n; intros.
    apply Nat.le_0_r in H. subst. apply H0.
    simpl. intro.
    compare m 0; intro.
    subst. simpl in H0. specialize (H0 y x). auto.
    rewrite evar_open_comm_higher. lia.
    apply IHn. lia. exact (H0 x).
  Defined.

  (* In place of inversion for Set. *)
  Tactic Notation "decide_le" hyp(Hle) :=
    apply le_lt_eq_dec in Hle as [Hle%Arith_prebase.lt_n_Sm_le | ->].

  (* Multiple exists version. *)
  Goal forall l ti n m,
    m <= n ->
    well_formed_closed_ex_aux l m ->
    well_formed_closed_mu_aux l 0 ->
    well_formed_positive l ->
    well_formed ti ->
    mu_free l ->
    functional_when_applied m l ->
    Γ ⊢ is_functional ti ->
    Γ ⊢ (many_ex n (l =ml ti)) <---> ti ∈ml (many_ex n l).
  Proof.
    intros * Hmlen Hwfceal Hwfcmal Hwfpl Hwfti Hmfl Hfpl Hfpti.
    generalize dependent l.
    generalize dependent m.
    induction n; simpl; intros.
    -
      apply Nat.le_0_r in Hmlen; subst. simpl in Hfpl.
      epose proof membership_equal_equal Γ ti l HΓ Hmfl Hwfti ltac:(wf_auto2) Hfpti Hfpl.
      toMLGoal. wf_auto2.
      mlAdd H.
      mlRewriteBy "0" at 1.
      mlSplitAnd; mlIntro.
      mlSymmetry; mlAssumption.
      mlSymmetry; mlAssumption.
    -
      mlFreshEvar as y.
      opose proof (membership_exists Γ ti y (many_ex n l) AnyReasoning HΓ _ _ _ _).
      replace (ex, many_ex n l) with (many_ex (S n) l) by reflexivity.
      eapply well_formed_many_ex; eauto.
      auto.
      rewrite free_evars_many_ex.
      ltac2:(fm_solve ()).
      try_solve_pile.
      apply pf_iff_equiv_sym in H.
      eapply pf_iff_equiv_trans with (5 := H).
      4: toMLGoal.
      4: simpl; apply well_formed_iff.
      all: try solve [(eapply extract_wfp + eapply extract_wfq); eauto].
      1,2: rewrite many_ex_travels; eapply well_formed_many_ex; only 1,5: reflexivity; wf_auto2.
      mlSplitAnd; mlIntro;
      apply (MLGoal_destructEx Γ [] [] _ y "0" _ AnyReasoning);
      simpl.
      4,5,10,11: rewrite free_evars_many_ex.
      1,9: try_solve_pile.
      ltac2:(fm_solve ()).
      ltac2:(fm_solve ()).
      ltac2:(fm_solve ()).
      ltac2:(fm_solve ()).
      ltac2:(fm_solve ()).
      ltac2:(fm_solve ()).
      2: ltac2:(fm_solve ()).
      2: ltac2:(fm_solve ()).
      all: mlExists y; mlSimpl;
      rewrite ! many_ex_subst; mlSimpl;
      rewrite ! (evar_open_wfc_aux 0 _ y ti);
      try solve [lia | wf_auto2];
      replace (0 + n) with n by reflexivity;
      decide_le Hmlen.
      1,3: rewrite ! (evar_open_wfc_aux m n); auto; specialize (IHn m Hmlen l Hwfceal Hwfcmal Hwfpl Hmfl Hfpl).
      3,4: ospecialize (IHn n _ l^{evar:n↦y} _ _ _ _ _); auto; [now apply mu_free_evar_open | now apply fwa_drop_one |].
      1,3: apply pf_iff_proj1 in IHn.
      7,8: apply pf_iff_proj2 in IHn.
      all: try solve [(eapply extract_wfp + eapply extract_wfq); eauto]; mlApplyMeta IHn in "0"; mlAssumption.
  Qed.

  (* Proof for Γ ⊢ (⌈l /\ ti⌉) -> (ti ∈ ∃. l) *) 

  (* Single exists version. *)
  Goal forall l ti,
    well_formed (ex, l) ->
    well_formed ti ->
    mu_free ti ->
    (forall x, Γ ⊢ is_functional l^{evar:0↦x}) ->
    Γ ⊢ is_functional ti ->
    Γ ⊢ ⌈l^{evar: 0 ↦ fresh_evar l} and ti⌉ ---> (ex, l =ml ti).
  Proof.
    intros * wfl wfti mfti fpl fpti.
    remember (fresh_evar _) as y.
    pose proof evar_open_not_occur 0 y ti ltac:(wf_auto2).
    mlIntro.
      mlExists y. mlSimpl. rewrite H.
      fold (l^{evar:0↦y} ∈ml ti).
      epose proof membership_imp_equal Γ (l^{evar:0↦y}) ti HΓ mfti ltac:(wf_auto2) ltac:(wf_auto2).
      pose proof (MP (fpl y) H0). clear H0.
      pose proof (MP fpti H1). clear H1.
      now fromMLGoal.
  Defined.

  (* Definitions for multiple exists version. *)

  Fixpoint fully_apply (n : nat) (p : Pattern) :=
    match n with
    | 0 => p
    | S m => fully_apply m (p^{evar:m↦fresh_evar p})
    end.

  Lemma well_formed_fully_apply : forall n m p,
    m <= n ->
    well_formed_closed_ex_aux p m ->
    well_formed_closed_mu_aux p 0 ->
    well_formed_positive p ->
    well_formed (fully_apply n p).
  Proof.
    induction n; intros; simpl.
    apply Nat.le_0_r in H. subst. wf_auto2.
    decide_le H.
    apply (IHn m); auto.
    rewrite (evar_open_wfc_aux m n); auto.
    apply (IHn n); auto.
  Defined.

  (* Multiple exists version. *)
  Goal forall n m l ti,
    m <= n ->
    well_formed_closed_ex_aux l m ->
    well_formed_closed_mu_aux l 0 ->
    well_formed_positive l ->
    well_formed ti ->
    mu_free ti ->
    functional_when_applied m l ->
    Γ ⊢ is_functional ti ->
    Γ ⊢ ⌈fully_apply n l and ti⌉ ---> (many_ex n (l =ml ti)).
  Proof.
    intros * Hmlen Hwfceal Hwfcmal Hwfpl Hwfti Hmfti Hfpl Hfpti.
    generalize dependent l.
    generalize dependent m .
    induction n; intros.
    simpl. fold (l ∈ml ti).
    apply Nat.le_0_r in Hmlen; subst.
    apply membership_imp_equal_meta; auto. wf_auto2.
    simpl.
    toMLGoal. simpl. clear Halmost. shelve.
    mlIntro.
    remember (fresh_evar l) as y.
    mlExists y. rewrite many_ex_subst. mlSimpl.
    rewrite (evar_open_wfc_aux 0 n y ti). lia. wf_auto2.
    replace (0 + n) with n by auto.
    decide_le Hmlen.
    ospecialize (IHn m Hmlen l^{evar:n↦y} _ _ _ _);
    only 1,4: rewrite (evar_open_wfc_aux m n y l); auto.
    mlApplyMeta IHn. mlAssumption.
    ospecialize (IHn n _ l^{evar:n↦y} _ _ _ _); auto.
    now apply fwa_drop_one.
    mlApplyMeta IHn. mlAssumption.
    Unshelve.
    apply well_formed_imp.
    apply well_formed_defined, well_formed_and.
    2: auto.
    2: {
      replace (ex , many_ex n (l =ml ti)) with (many_ex (S n) (l =ml ti)) by reflexivity.
      eapply well_formed_many_ex; eauto.
      (* TODO: I should not have to do this. *)
      assert (well_formed_closed_ex_aux ti m). {
        clear dependent l n Hfpti.
        induction ti; simpl; auto.
        1,2: simpl in Hmfti; apply andb_true_iff in Hmfti as [];
        apply andb_true_iff; split.
        apply IHti1. eapply well_formed_app_proj1. eauto. auto.
        apply IHti2. eapply well_formed_app_proj2. eauto. auto.
        apply IHti1. eapply well_formed_imp_proj1. eauto. auto.
        apply IHti2. eapply well_formed_imp_proj2. eauto. auto.
        apply well_formed_closed_ex_all. wf_auto2.
      }
      1-3: wf_auto2.
    }
    decide_le Hmlen.
    rewrite (evar_open_wfc_aux m n); auto.
    eapply well_formed_fully_apply; eauto.
    eapply well_formed_fully_apply. reflexivity.
    all: wf_auto2.
  Qed.

  (* Counter-proof for Γ ⊢ (ti ∈ ∃. l) -> (⌈l /\ ti⌉) *) 
  Goal forall y (sy : symbols), exists (M : Model), forall (ρ' : @Valuation _ M), exists ρ l ti,
    well_formed ti ->
    @eval _ M ρ ((ex, l =ml ti) ---> ⌈l^{evar: 0 ↦ y} and ti⌉) ≠ ⊤.
  Proof.
    intros.
    pose {| Domain := bool; sym_interp _ := {[true]}; app_interp _ _ := ⊤ |} as M.
    eexists M.
    intros.
    pose (false : M).
    exists (update_evar_val y d ρ'), b0, (patt_sym sy).
    intros wfti *.
    rewrite ! eval_simpl. simpl.
    remember (fresh_evar _) as y'.
    mlSimpl.
    remember (λ e : bool, eval _ _) as f.
    epose proof propset_fa_union_full f as [_ ?]. rewrite H.
    intros.
    pose (true : Domain M) as c.
    exists c. subst f.
    unfold evar_open. simpl.
    epose proof equal_iff_interpr_same M _ (patt_free_evar y') (patt_sym sy) (update_evar_val y' c (update_evar_val y d ρ')) as [_ ->].
    set_solver. clear _H.
    rewrite ! eval_simpl. simpl. rewrite decide_eq_same. subst c. auto.
    epose proof @difference_diag_L bool (propset M) _ _ _ _ _ _ _ _ ⊤.
    rewrite H0. rewrite (@union_empty_l_L bool (propset M)).
    rewrite decide_eq_same.
    assert (LeibnizEquiv (propset bool)). apply (@propset_leibniz_equiv _ M).
    rewrite ! union_empty_r_L.
    rewrite ! Compl_Compl_propset.
    rewrite Compl_Union_Compl_Inters_propset_alt.
    replace ({[d]} ∩ {[true]}) with (@empty (propset (@Domain Σ M)) (@propset_empty (@Domain Σ M))) by set_solver.
    unfold app_ext. simpl.
    remember (λ e, exists le re, _) as f'.
    epose proof set_eq (PropSet f') ⊤.
    apply not_iff_compat in H2. apply H2.
    intro. specialize (H3 false).
    pose proof elem_of_PropSet f' false.
    apply iff_sym in H4.
    apply (iff_trans H4) in H3. clear H4.
    epose proof elem_of_top false.
    apply (iff_trans H3) in H4. clear H3.
    destruct H4 as [_ ?]. specialize (H3 I).
    rewrite Heqf' in H3. decompose record H3.
    set_solver.
    Unshelve.
    1: {
      unfold satisfies_theory, satisfies_model. intros.
      inversion H0. subst. simpl. unfold axiom. case_match.
      rewrite ! eval_simpl. simpl. unfold app_ext.
      remember (λ e, exists le re, _) as f'.
      epose proof set_eq (PropSet f') ⊤. apply H2.
      intros.
      transitivity (f' x0). apply elem_of_PropSet.
      transitivity True. 2: { epose proof elem_of_top x0. apply iff_sym in H3. exact H3. }
      split. auto. intros [].
      rewrite Heqf'.
      do 2 eexists; repeat split.
    }
    Unshelve.
    all: typeclasses eauto.
  Defined.

  (* Counter-proofs for Γ ⊢ (θ -> (l = ti)) <-> (l /\ θ = ti) *) 

  Context (σ : list (evar * Pattern)).
  Hypothesis (Hwfσ : wf (map snd σ)).

  Goal forall (sy : symbols) (x : evar) l, exists M ti σ, forall (ρ' : @Valuation _ M), exists ρ,
    @eval _ M ρ ((predicate_list σ ---> (l =ml ti)) <---> ((l and predicate_list σ) =ml ti)) ≠ ⊤.
  Proof.
    intros.
    pose {| Domain := bool; sym_interp _ := {[true]}; app_interp _ _ := ⊤ |} as M.
    exists M.
    exists (patt_sym sy).
    exists [(x, patt_sym sy)].
    intros.
    pose (false : M).
    pose (update_evar_val x d ρ') as ρ.
    exists ρ.
    
    assert (satisfies_theory M theory). {
      unfold satisfies_theory, satisfies_model.
      intros. inversion H. subst. simpl. unfold axiom.
      case_match. rewrite ! eval_simpl.
      simpl. unfold app_ext. remember (λ e, exists le re, _) as f.
      epose proof set_eq (PropSet f) ⊤ as [_ ?]. apply H1.
      intros. rewrite elem_of_top. repeat split.
      intros []. apply elem_of_PropSet. subst.
      exists true, (evar_valuation ρ0 ev_x). repeat split.
    }

    unfold predicate_list. simpl.
    assert (eval ρ (patt_free_evar x =ml patt_sym sy) = ∅). {
      pose proof not_equal_iff_not_interpr_same_1 M H (patt_free_evar x) (patt_sym sy) ρ as [_ ?]. apply H0.
      rewrite ! eval_simpl. simpl. rewrite decide_eq_same. subst d.
      intro. epose proof set_eq {[false]} {[true]} as [? _].
      specialize (H2 H1 false) as [? _]. ospecialize* H2.
      now apply elem_of_singleton_2.
      set_solver.
    }

    rewrite eval_iff_simpl.
    rewrite eval_imp_simpl.
    rewrite ! eval_and_simpl.
    rewrite H0.
    rewrite ! intersection_empty_l_L difference_empty_L.
    (* set_solver went on vacation *)
    (* TODO: extract these to stdpp_ext? *)
    assert (forall X : propset M, ⊤ ∪ X = ⊤) by (set_unfold; solve [repeat constructor]).
    rewrite ! H1.
    rewrite difference_diag_L union_empty_l_L.
    assert (forall X : propset M, X ∪ ⊤ = ⊤) by (set_unfold; solve [repeat constructor]).
    rewrite ! H2.
    assert (forall X : propset M, X ∩ ⊤ = X). {
      set_unfold. repeat constructor. now intros []. auto.
    }
    rewrite ! H3.
    epose proof not_equal_iff_not_interpr_same_1 M H _ _ ρ as [_ ?].
    erewrite H4. set_unfold. auto.
    rewrite ! eval_and_simpl eval_sym_simpl.
    rewrite H0 intersection_empty_l_L intersection_empty_r_L.
    simpl. symmetry. epose proof non_empty_singleton_L true. exact H5.
    Unshelve. all: try typeclasses eauto.
    (* TODO: possible to make this part of typeclasses eauto's search? *)
    all: exact (@propset_leibniz_equiv _ M).
  Defined.

  Goal forall l ti,
    forall M ρ,
    satisfies_theory M theory ->
    @eval _ M ρ (predicate_list σ) = ∅ ->
    @eval _ M ρ ti ≠ ∅ ->
    @eval _ M ρ ((predicate_list σ ---> (l =ml ti)) <---> ((l and predicate_list σ) =ml ti)) ≠ ⊤.
  Proof.
    intros * HM Hρ Hρ2.
    rewrite eval_iff_simpl.
    rewrite eval_imp_simpl.
    rewrite Hρ.
    rewrite ! difference_empty_L.
    assert (forall X : propset M, ⊤ ∪ X = ⊤) as Htop_l by set_solver.
    assert (forall X : propset M, X ∪ ⊤ = ⊤) as Htop_r by set_solver.
    rewrite ! Htop_l.
    rewrite difference_diag_L.
    rewrite Htop_r.
    assert (forall X : propset M, X ∩ ⊤ = X) as Htop_int by set_solver.
    rewrite Htop_int.
    rewrite union_empty_l_L.
    epose proof not_equal_iff_not_interpr_same_1 M HM (l and predicate_list σ) ti ρ as [_ ->].
    2: {
      rewrite eval_and_simpl.
      rewrite Hρ.
      rewrite intersection_empty_r_L.
      auto.
    }
    set_solver.
  Defined.

  Goal forall (sy : symbols) (a : evar), exists ti s M, forall ρ,
    satisfies_theory M theory /\
    @eval _ M ρ (predicate_list s) = ∅ /\
    @eval _ M ρ ti ≠ ∅.
  Proof.
    intros.
    exists (patt_sym sy).
    exists [(a, ⊥)].
    pose {| Domain := unit; app_interp _ _ := ⊤; sym_interp _ := ⊤ |} as M. exists M.
    intros.
    
    assert (forall X Y, (exists x, x ∈ X) -> (exists y, y ∈ Y) -> @app_ext _ M X Y = ⊤). {
      intros * HX HY. unfold app_ext.
      remember (fun e : Domain M => exists le re : M, _) as f.
      apply set_eq.
      intros e.
      transitivity (f e).
      apply elem_of_PropSet.
      transitivity True.
      2: symmetry; apply elem_of_top.
      split. auto.
      intros []. subst.
      destruct HX as [x HX], HY as [y HY].
      exists x, y. do ! split. all: auto.
    }

    do ! split.

    -
      unfold satisfies_theory, satisfies_model. intros.
      inversion H0. subst. simpl.
      unfold axiom. case_match. rewrite ! eval_simpl. rewrite H.
      3: reflexivity. all: set_solver.
    -
      simpl.
      rewrite ! eval_simpl.
      rewrite ! union_empty_r_L.
      rewrite ! Compl_Compl_propset.
      rewrite H. 3: now rewrite union_empty_r_L difference_diag_L.
      all: set_solver.
    -
      rewrite eval_simpl. simpl.
      apply Contains_Elements_Not_Empty. set_solver.
  Defined.

  (* Proof for Γ ⊢ (⌈∃. l /\ ti⌉) <-> (ti ∈ ∃. l) *) 

  (* This is just a consequence of the commutativity of /\ and *)
  (* the definition of ∈. A proof can be counstructed for *)
  (* multiple exists in the same way *)
  Goal forall l ti,
    well_formed (ex, l) ->
    well_formed ti ->
    Γ ⊢ ⌈(ex, l) and ti⌉ <---> (ti ∈ml ex, l).
  Proof.
    intros * wfl wfti.
    toMLGoal. wf_auto2.
    pose proof patt_and_comm Γ (ex, l) ti wfl wfti.
    use AnyReasoning in H. mlRewrite H at 1.
    fold (ti ∈ml (ex, l)). mlReflexivity.
  Defined.
End MatchingEquivs.

