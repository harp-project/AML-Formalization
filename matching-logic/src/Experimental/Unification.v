From MatchingLogic.Theories Require Export FOEquality_ProofSystem.
Import MatchingLogic.Logic.Notations.
Import MatchingLogic.Theories.Definedness_Syntax.Notations.

From MatchingLogic Require Export Unification.Definitions.

Set Default Proof Mode "Classic".

Close Scope equations_scope. (* Because of [!] *)

Section unification.
  Context {Σ : Signature} {syntax : Syntax}.

  (** The naming of the following lemmas matches this article:
        Unification in Matching Logic - Extended Version
        Andrei Arusoaie, Dorel Lucanu
        https://arxiv.org/abs/1811.02835v3
   *)

  Lemma Prop₃_left: forall Γ φ φ',
    theory ⊆ Γ ->
    well_formed φ -> well_formed φ' ->
    Γ ⊢ (φ and (φ' =ml φ)) ---> (φ and φ').
  Proof.
    intros Γ φ φ' SubTheory Wf1 Wf2.
    toMLGoal. wf_auto2.
    mlIntro "H0". mlDestructAnd "H0" as "H1" "H2".
    mlRewriteBy "H2" at 1.
    mlSplitAnd; mlExact "H1".
  Defined.

  Lemma Prop₃_right : forall Γ φ φ',
      theory ⊆ Γ ->
      well_formed φ -> well_formed φ' -> mu_free φ' ->
      Γ ⊢ (ex , (φ =ml b0))  ->
      Γ ⊢ (ex , (φ' =ml b0))  ->
      Γ ⊢ (φ and φ') ---> (φ and (φ =ml φ')) .
  Proof.
    intros Γ φ φ' HΓ Wf1 Wf2 MF Func1 Func2.
    toMLGoal. wf_auto2.
    mlIntro "H0".
    mlAssert ("H1" : ⌈ φ and φ' ⌉).
    { wf_auto2. }
    {
      pose proof (phi_impl_defined_phi Γ (φ and φ') (fresh_evar (φ and φ')) HΓ
                    ltac:(solve_fresh) ltac:(wf_auto2)) as H.
      use AnyReasoning in H.
      mlApplyMeta H.
      mlExact "H0".
    }
    replace (⌈ φ and φ' ⌉) with (φ ∈ml φ') by auto.
    mlDestructAnd "H0" as "H2" "H3". mlSplitAnd.
    * mlExact "H2".
    * mlApplyMeta membership_imp_equal_meta; auto.
      mlExact "H1".
  Defined.

  Lemma Lemma₁ : forall Γ φ t x, theory ⊆ Γ ->
    well_formed φ ->
    mu_free φ ->
    well_formed t ->
    Γ ⊢ (patt_free_evar x) =ml t ---> φ^[[evar:x↦t]] =ml φ.
  Proof.
    intros * HΓ wfφ mfφ wft.
    mlFreshEvar as y.
    pose proof (equality_elimination_basic Γ (patt_free_evar x) t {| pcEvar := y; pcPattern := φ^[[evar: x ↦ patt_free_evar y]] =ml φ |}).
    ospecialize* H; auto. wf_auto2.
    simpl. now erewrite mu_free_free_evar_subst, mfφ.
    cbn -["=ml"] in H. mlSimpl in H.
    erewrite ! free_evar_subst_chain, free_evar_subst_id, ! (free_evar_subst_no_occurrence y) in H by ltac2:(fm_solve()).
    mlIntro "H".
    mlApplyMeta H in "H".
    mlDestructAnd "H" as "H1" "H2".
    mlApply "H1". mlReflexivity.
  Defined.

  Lemma Lemma₂ : forall Γ φ σ,
    theory ⊆ Γ -> mu_free φ -> well_formed φ ->
    forallb mu_free (map snd σ) -> wf (map snd σ) ->
    Γ ⊢i substitute_list σ φ and predicate_list σ <--->
      φ and predicate_list σ using AnyReasoning.
  Proof.
    intros * HΓ mfφ wfφ mfσ wfσ.
    pose proof (wf_predicate_list σ wfσ) as WF1.
    pose proof (wf_substitute_list σ φ wfσ wfφ) as WF2.
    epose proof (extract_common_from_equivalence_r _ _ _ _ _ _ _).
    eapply (pf_iff_proj2 _ _ _ _ _ _) in H.
    mlApplyMeta H.
    clear H.
    fromMLGoal.
    generalize dependent φ.
    induction σ; simpl; intros. mlIntro. mlReflexivity. destruct a.
    mlIntro "H". mlDestructAnd "H" as "H1" "H2".
    unshelve ospecialize* IHσ. exact φ^[[evar:e↦p]]. 1-6, 8: shelve.
    mlApplyMeta IHσ in "H2". clear IHσ.
    mlApplyMeta (pf_iff_equiv_trans_obj) in "H2".
    mlApply "H2". mlClear "H2".
    epose proof (Lemma₁ _ φ _ _ _ _ _ _).
    mlApplyMeta H in "H1". clear H.
    epose proof (get_fresh_evar (φ^[[evar:e↦p]] <---> φ)) as [y Hy].
    epose proof (total_phi_impl_phi _ _ _ _ Hy _).
    mlApplyMeta H in "H1". clear H.
    mlExact "H1".
    Unshelve. all: try solve [auto | wf_auto2].
    1,3: exact AnyReasoning.
    simpl in mfσ. apply andb_true_iff in mfσ as [].
    apply mu_free_free_evar_subst; auto.
  Defined.

  Lemma Lemma₅ : forall (σ : list (evar * Pattern)) t₁ t₂ Γ,
    theory ⊆ Γ ->
    well_formed t₁ -> well_formed t₂ ->
    mu_free t₁ -> mu_free t₂ ->
    wf (map snd σ) -> forallb mu_free (map snd σ) ->
    Γ ⊢ is_unifier_of σ t₁ t₂ ---> predicate_list σ ---> (t₁ =ml t₂).
  Proof.
    intros * HΓ wft₁ wft₂ mft₁ mft₂ wfσ mfσ.
    unfold is_unifier_of.
    epose proof (wf_predicate_list σ wfσ) as wfpl.
    epose proof (wf_substitute_list σ t₁ wfσ wft₁) as wfsl1.
    epose proof (wf_substitute_list σ t₂ wfσ wft₂) as wfsl2.
    mlIntro "H".
    opose proof* (predicate_list_predicate Γ σ); auto.
    opose proof* (extract_common_from_equality_r_2 Γ t₁ t₂ (predicate_list σ)); auto.
    apply (MP H) in H0.
    apply pf_iff_proj2 in H0. 2,3: wf_auto2.
    mlApplyMeta H0.
    epose proof (Lemma₂ Γ t₁ σ _ _ _ _ _).
    mlRewrite <- H1 at 1.
    epose proof (Lemma₂ Γ t₂ σ _ _ _ _ _).
    mlRewrite <- H2 at 1.
    mlRewriteBy "H" at 1.
    mlReflexivity.
    Unshelve. all: auto.
  Defined.

  Lemma R₅' : forall x Γ, theory ⊆ Γ -> Γ ⊢ (ex , patt_free_evar x =ml b0).
  Proof.
    intros.
    toMLGoal.
    wf_auto2.
    mlExists x.
    mlSimpl.
    rewrite evar_open_not_occur.
    wf_auto2.
    unfold evar_open. simpl.
    mlReflexivity.
  Defined.

  (**
    TODO: this axiom should be placed into Γ later, and we have to use `hypothesis`
          to obtain it. For this, we have to create a spec. for unification/term
          algebras.
  *)
  Axiom injectivity : forall Γ f t g u, Γ ⊢ (f ⋅ t) =ml (g ⋅ u) ---> (f =ml g) and (t =ml u).

  Lemma Lemma₃ {T : Set} {UPT : UP T} Γ P P' : theory ⊆ Γ -> P ===> P' -> P' <> bottomUP -> Γ ⊢wf toPredicateUP P wf---> toPredicateUP P'.
  Proof with inside mlClear "_" outside try apply wfWFPattern.
    intros HΓ [] NB; pose proof (toPredicateInsertUP Γ).
    * specialize (H P0 t t).
      unfold WFDerives in H |- *.
      rewrite unwrap_wfwrapper in H.
      apply pf_iff_proj1 in H...
      toMLGoal...
      rewrite ! unwrap_wfwrapper in H |- *.
      mlIntro "H". mlApplyMeta H in "H".
      mlDestructAnd "H" as "_" "H0"...
      mlAssumption.
    * unfold WFDerives in H |- *.
      pose proof (H P0 (f wf⋅ t) (g wf⋅ u)) as H0.
      rewrite unwrap_wfwrapper in H0.
      pose proof (H (insertUP P0 (f, g)) t u) as H1.
      rewrite unwrap_wfwrapper in H1.
      specialize (H P0 f g).
      rewrite unwrap_wfwrapper in H.
      apply pf_iff_proj1 in H0...
      apply pf_iff_proj2 in H1, H...
      toMLGoal...
      rewrite ! unwrap_wfwrapper in H0, H1, H |- *.
      mlIntro "H".
      mlApplyMeta H0 in "H".
      mlDestructAnd "H" as "H0" "H3".
      mlApplyMeta injectivity in "H0".
      mlDestructAnd "H0" as "H1" "H2".
      mlApplyMeta H1.
      mlSplitAnd. mlAssumption.
      mlApplyMeta H. mlSplitAnd; mlAssumption.
    * now destruct NB.
    * now destruct NB.
    * unfold WFDerives in H |- *.
      pose proof (H P0 x (patt_free_evar y ↾ well_formed_free_evar y)) as H0.
      rewrite unwrap_wfwrapper in H0.
      apply pf_iff_proj1 in H0...
      specialize (H P0 (patt_free_evar y ↾ well_formed_free_evar y) x).
      rewrite unwrap_wfwrapper in H.
      apply pf_iff_proj2 in H...
      toMLGoal...
      rewrite ! unwrap_wfwrapper in H0, H |- *.
      mlIntro "H".
      mlApplyMeta H0 in "H". mlDestructAnd "H" as "H0" "H1".
      mlApplyMeta H. mlSplitAnd. mlSymmetry. 1-2: mlAssumption.
    * now destruct NB.
    * unfold WFDerives in H |- *.
      pose proof (H P0 (patt_free_evar x ↾ well_formed_free_evar x) t).
      rewrite unwrap_wfwrapper in H0.
      apply pf_iff_proj1 in H0...
      specialize (H (substituteAllUP x t P0) (patt_free_evar x ↾ well_formed_free_evar x) t).
      rewrite unwrap_wfwrapper in H.
      apply pf_iff_proj2 in H...
      toMLGoal...
      rewrite ! unwrap_wfwrapper in H0, H |- *.
      mlIntro "H".
      mlApplyMeta H0 in "H".
      mlApplyMeta H. simpl.
      pose proof (toPredicateSubstituteAllUP Γ P0 x t).
      unfold WFDerives in H1.
      rewrite ! unwrap_wfwrapper in H1. simpl in H1.
      pose proof (projT2 t). simpl in H2.
      mlRewrite H1 at 1. clear H2.
      opose proof* (Lemma₂ Γ (proj1_sig (toPredicateUP P0)) [(x, projT1 t)]); cbn; rewrite ? andb_true_r; auto...
      admit.
      simpl in H2. apply pf_iff_proj2 in H2.
      2-3: refine_wf...

      match goal with [H2 : derives_using _ (?x ---> _) _ |- _] => mlAssert ("H0" : x) end. refine_wf...

      mlDestructAnd "H" as "H1" "H2".
      repeat mlSplitAnd; try mlAssumption.
      pose proof (top_holds Γ). use AnyReasoning in H3. mlExactMeta H3.
      mlApplyMeta H2 in "H0".
      mlDestructAnd "H0" as "H1" "H2". mlDestructAnd "H2" as "H3" "_"...
      mlSplitAnd; mlAssumption.
  Admitted.

  (**
    The formalized unification algorithm gives us an MGU.
  *)
  Axiom convenient : forall {T : Set} {UPT : UP T} σ t1 t2, is_most_general_unifier_of σ (`t1) (`t2) -> {P : T & (USrtc (singletonUP t1 t2) P * (P ≠ bottomUP) * forall Γ, Γ ⊢ projT1 (toPredicateUP P) <---> predicate_list σ)%type}.

  Lemma Lemma₄_helper : forall {T : Set} {UPT : UP T} Γ P P',
    theory ⊆ Γ ->
    USrtc P P' ->
    P' ≠ bottomUP ->
    Γ ⊢wf toPredicateUP P wf---> toPredicateUP P'.
  Proof with apply wfWFPattern.
    intros * HΓ R NB.
    unfold WFDerives.
    rewrite unwrap_wfwrapper.
    induction R.
    aapply A_impl_A...
    toMLGoal. apply well_formed_imp...
    mlIntro "H".
    mlApplyMeta IHR; auto.
    opose proof* (Lemma₃ Γ); eauto.
    {
      inversion R; subst.
      auto.
      pose proof insertNotBottomUP.
      inversion H; subst; apply H1; auto.
    }
    unfold WFDerives in H. rewrite unwrap_wfwrapper in H.
    mlApplyMeta H. mlAssumption.
  Defined.

  From stdpp Require Import gmap.
  Definition wf := Pattern.wf.

  Lemma Lemma₄ : forall Γ (σ : list (evar * Pattern)) (t1 t2 : WFPattern),
    theory ⊆ Γ -> wf (map snd σ) ->
    is_most_general_unifier_of σ (`t1) (`t2) -> Γ ⊢ `t1 =ml `t2 ---> predicate_list σ.
  Proof with try apply wfWFPattern.
    intros * HΓ WFσ HMGU.
    opose proof* (@optionSetUP _ _ (gset (WFPattern * WFPattern))).
    1-2: typeclasses eauto.
    pose proof (convenient σ t1 t2 HMGU) as [P [[R NB] EQ] ].
    toMLGoal. simpl. refine_wf...
    now apply wf_predicate_list.
    pose proof (proj2_sig t1). pose proof (proj2_sig t2).
    mlRewrite <- (EQ Γ) at 1.
    clear H H0.
    pose proof (toPredicateSingletonUP Γ t1 t2).
    unfold WFDerives in H. rewrite ! unwrap_wfwrapper in H.
    pose proof (proj2_sig (toPredicateUP P)).
    mlRewrite <- H at 1.
    clear H0.
    opose proof* (Lemma₄_helper Γ); eauto.
    unfold WFDerives in H0. rewrite ! unwrap_wfwrapper in H0.
    mlExactMeta H0.
  Defined.

  Lemma Lemma₆ : forall Γ (σ : list (evar * Pattern)) (t1 t2 : WFPattern),
    theory ⊆ Γ ->
    wf (map snd σ) ->
    mu_free (`t1) -> mu_free (`t2) ->
    forallb mu_free (map snd σ) ->
    is_most_general_unifier_of σ (`t1) (`t2) ->
    Γ ⊢ (`t1 =ml `t2) <---> predicate_list σ.
  Proof with try by refine_wf.
    intros ? ? [t1 wft1] [t2 wft2] HΓ WFσ MFt1 MFt2 MFσ HMGU.
    opose proof* (wf_predicate_list σ) as WFpl...
    toMLGoal... mlSplitAnd; mlIntro "H".
    unshelve opose proof* (Lemma₄ Γ σ (t1 ↾ _) (t2 ↾ _))...
    all: simpl in *. mlApplyMeta H. mlAssumption.
    opose proof* (Lemma₅ σ t1 t2 Γ)...
    destruct HMGU as [IUO _]. specialize (IUO Γ).
    pose proof (MP IUO H). mlApplyMeta H0. mlAssumption.
  Defined.

  Lemma Prop3_full : forall Γ t1 t2,
    theory ⊆ Γ -> well_formed t1 -> well_formed t2 -> mu_free t2 ->
    Γ ⊢ is_functional t1 -> Γ ⊢ is_functional t2 ->
    Γ ⊢ t1 and t2 <---> t1 and t1 =ml t2.
  Proof with try solve [auto | wf_auto2].
    intros * HΓ WFt1 WFt2 MFt2 IFt1 IFt2.
    toMLGoal... mlSplitAnd; mlIntro "H".
    opose proof* (Prop₃_right Γ t1 t2)...
    mlApplyMeta H. mlAssumption.
    opose proof* (Prop₃_left Γ t1 t2)...
    mlApplyMeta H. mlDestructAnd "H" as "H1" "H2".
    mlSplitAnd; only 2: mlSymmetry; mlAssumption.
  Defined.

  Lemma Theorem₁ : forall Γ σ t1 t2,
    theory ⊆ Γ ->
    well_formed t1 -> well_formed t2 ->
    wf (map snd σ) ->
    mu_free t1 -> mu_free t2 ->
    forallb mu_free (map snd σ) ->
    Γ ⊢ is_functional t1 -> Γ ⊢ is_functional t2 ->
    is_most_general_unifier_of σ t1 t2 ->
    (Γ ⊢ (t1 and t2) =ml (t1 and predicate_list σ)) * (Γ ⊢ (t1 and t2) =ml (t2 and predicate_list σ)).
  Proof with try solve [auto | wf_auto2 | refine_wf; auto].
    intros * HΓ WFt1 WFt2 WFσ MFt1 MFt2 MFσ IFt1 IFt2 HMGU.
    opose proof* (Prop3_full Γ t1 t2)...
    assert (Γ ⊢ t1 and t2 <---> t2 and t1 =ml t2). {
      opose proof* (Prop3_full Γ t2 t1)...
      opose proof* (patt_and_comm Γ t1 t2)...
      use AnyReasoning in H1.
      mlRewrite H1 at 1.
      opose proof* (patt_equal_comm t1 t2 Γ).
      1: assumption.
      1-2: wf_auto2.
      use AnyReasoning in H2.
      mlRewrite H2 at 1.
      mlExactMeta H0.
    }
    opose proof* (Lemma₆ Γ σ (t1 ↾ WFt1) (t2 ↾ WFt2))...
    opose proof* (wf_predicate_list σ)...
    split. toMLGoal... 2: toMLGoal...
    all: simpl in H1.
    mlRewrite H at 1. 2: mlRewrite H0 at 1.
    all: mlRewrite H1 at 1; mlReflexivity.
  Defined.

  Goal forall Γ (f' g' one' : symbols) (x' y' z' : evar) (*one : WFPattern*),
    x' ≠ z' -> y' ≠ z' ->
    theory ⊆ Γ ->
    let f := (patt_sym f' ↾ well_formed_sym f') in
    let g := (patt_sym g' ↾ well_formed_sym g') in
    let one := (patt_sym one' ↾ well_formed_sym one') in
    let x := (patt_free_evar x' ↾ well_formed_free_evar x') in
    let y := (patt_free_evar y' ↾ well_formed_free_evar y') in
    let z := (patt_free_evar z' ↾ well_formed_free_evar z') in
    let t1 := f wf⋅ x wf⋅ (g wf⋅ one) wf⋅ (g wf⋅ z) in
    let t2 := f wf⋅ (g wf⋅ y) wf⋅ (g wf⋅ y) wf⋅ (g wf⋅ (g wf⋅ x)) in
    (** f is a functional symbol *)
    (all, all, all, ex, (patt_sym f') ⋅ b3 ⋅ b2 ⋅ b1 =ml b0) ∈ Γ ->
    (** g is a functional symbol *)
    (all, ex, (patt_sym g') ⋅ b1 =ml b0) ∈ Γ ->
    (** one is a functional symbol *)
    (ex, patt_sym one' =ml b0) ∈ Γ ->
    (*
      TODO: after defining term algebra spec. these functional axioms should be
      in the theory of the spec.
    *)
    {σ & Γ ⊢ `t1 and `t2 <---> `t1 and predicate_list σ}.
  Proof with try solve [auto | refine_wf; auto; apply wfWFPattern].
    intros * NE1 NE2 HΓ **.
    rename H into Hfunctional_f.
    rename H0 into Hfunctional_g.
    rename H1 into Hfunctional_one.
    evar (σ : list (evar * Pattern)).
    assert (wf (map snd σ)) as WFσ by shelve.
    pose proof (wf_predicate_list σ WFσ) as WFplσ.
    exists σ.
    toMLGoal... mlSplitAnd; mlIntro.
    opose proof* (Prop₃_right Γ (`t1) (`t2))...
    (* functional patterns: *)
    1: {
      subst t1 t2. cbn.
      toMLGoal. { wf_auto2. }
      solve_functional.
    }
    1: {
      subst t1 t2. cbn.
      toMLGoal. { wf_auto2. }
      solve_functional.
    }
    {
      mlApplyMeta H in "0".
      pose proof (@gset_fin_set _ WFPattern_eq_dec ltac:(typeclasses eauto)).
      pose (@optionSetUP _ _ _ _ _ _ _ _ _ _ H0 ltac:(typeclasses eauto)).
      opose proof* (Lemma₄_helper Γ (Some (singleton (t1, t2)))). auto.
      eright. pose proof (decompositionUS (Some empty)). simpl in H1. rewrite <- union_empty_r_L. apply H1... rewrite union_empty_r_L.
      eright. epose proof (decompositionUS (Some _)). simpl in H1. apply H1...
      rewrite union_comm_L. rewrite <- union_assoc_L.
      eright. epose proof (deleteUS (Some _)). simpl in H1. apply H1...
      eright. epose proof (decompositionUS (Some _)). simpl in H1. apply H1...
      eright. epose proof (decompositionUS (Some _)). simpl in H1. apply H1...
      rewrite union_comm_L. rewrite <- union_assoc_L.
      eright. epose proof (deleteUS (Some _)). simpl in H1. apply H1...
      rewrite <- union_assoc_L.
      eright. epose proof (decompositionUS (Some _)). simpl in H1. apply H1...
      rewrite union_comm_L. rewrite <- union_assoc_L.
      eright. epose proof (deleteUS (Some _)). simpl in H1. apply H1...
      rewrite (union_comm_L {[(z, g wf⋅ x)]}). rewrite <- union_assoc_L.
      eright. epose proof (orientUS (Some _)). simpl in H1. apply H1... fold y.
      rewrite union_assoc_L. rewrite (union_comm_L {[(y, one)]}).
      left. discriminate. cbn -[f g one x y z] in H1.
      rewrite set_fold_singleton in H1. cbn -[f g one x y z] in H1.
      unfold WFDerives in H1. do 3 rewrite unwrap_wfwrapper in H1. cbn [proj1_sig] in H1.
      mlDestructAnd "0". mlSplitAnd. mlAssumption.
      pose proof (top_holds Γ). use AnyReasoning in H2.
      mlAdd H2.
      Time mlConjFast "2" "0" as "3"... (*wfby (refine_wf; apply wfWFPattern).*)
      (* Record: 0.19s *)
      (* Time mlConj "2" "0" as "3". *)
      (* Record: 38.576s *)
      mlApplyMeta H1 in "3".
      mlClear "0". mlClear "1". mlClear "2". clear H H1 H2.
      opose proof* (set_fold_disj_union_strong_equiv Γ (WFPatt_and ∘ uncurry WFPatt_equal) (Top ↾ well_formed_top)).
      3: unfold WFDerives in H; rewrite unwrap_wfwrapper in H; apply pf_iff_proj1 in H; [mlApplyMeta H in "3" | |]...
      intros. simpl. unfold WFDerives. rewrite ! unwrap_wfwrapper.
      toMLGoal. refine_wf; apply wfWFPattern. mlSplitAnd; mlDecomposeAll; do 2? mlSplitAnd; mlAssumption.
      apply disjoint_singleton_r. set_solver.
      rewrite set_fold_singleton. simpl. case_match. simpl.
      instantiate (σ := [(_, _); (_, _); (_, _)]). simpl.
      mlDestructAnd "3". mlSplitAnd. mlExact "0". mlClear "0". clear H.
      apply (f_equal proj1_sig) in H1. simpl in H1. subst x0.
      opose proof* (set_fold_disj_union_strong_equiv Γ (WFPatt_and ∘ uncurry WFPatt_equal) (Top ↾ well_formed_top)).
      3: unfold WFDerives in H; rewrite unwrap_wfwrapper in H; apply pf_iff_proj1 in H; [mlApplyMeta H in "1" | |]...
      intros. simpl. unfold WFDerives. rewrite ! unwrap_wfwrapper.
      toMLGoal. refine_wf; apply wfWFPattern. mlSplitAnd; mlDecomposeAll; do 2? mlSplitAnd; mlAssumption.
      apply disjoint_singleton_r. set_solver.
      rewrite 2! set_fold_singleton. simpl.
      mlExact "1".
    }
    {
      opose proof* (Lemma₂ Γ (`t1) σ)...
      opose proof* (wf_substitute_list σ (`t1))...
      apply pf_iff_proj2 in H... mlSplitAnd. mlDestructAnd "0"; mlAssumption.
      mlApplyMeta H in "0". unfold t1. simpl.
      case_match. 2: now destruct n.
      case_match. now destruct NE1.
      mlSimpl. simpl.
      case_match. 2: now destruct n0.
      case_match. now destruct NE2.
      simpl. case_match. 2: now destruct n1.
      mlDecomposeAll.
      do ! mlRewriteBy "2" at 1.
      mlExact "1".
    }
      Unshelve.
      wf_auto2.
      all: typeclasses eauto.
  Defined.

End unification.

Close Scope ml_scope.
Close Scope string_scope.
Close Scope list_scope.

