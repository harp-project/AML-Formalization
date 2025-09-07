From MatchingLogic.Theories Require Export FOEquality_ProofSystem.
Import MatchingLogic.Logic.Notations.
Import MatchingLogic.Theories.Definedness_Syntax.Notations.

From MatchingLogic Require Export Unification.Definitions.

Set Default Proof Mode "Classic".

Close Scope equations_scope. (* Because of [!] *)

Section unification.
  Context {Σ : Signature} {syntax : Syntax} {Γ : Theory}.
  Hypothesis (HΓ : theory ⊆ Γ).

  Definition injectivity_definition : Pattern := all, all, all, all, (b3 ⋅ b2) =ml (b1 ⋅ b0) ---> (b3 =ml b1) and (b2 =ml b0).

  Hypothesis (HΓinj : injectivity_definition ∈ Γ).

  (* Lemma injectivity_correct : forall f t g u, *)
  (*   well_formed f -> mu_free f -> Γ ⊢ is_functional f -> *)
  (*   well_formed t -> mu_free t -> Γ ⊢ is_functional t -> *)
  (*   well_formed g -> mu_free g -> Γ ⊢ is_functional g -> *)
  (*   well_formed u -> mu_free u -> Γ ⊢ is_functional u -> *)
  Lemma injectivity_correct : forall (f t g u : TermPattern),
    Γ ⊢ (f ⋅ t) =ml (g ⋅ u) ---> (f =ml g) and (t =ml u).
  Proof.
    intros
      [[f Hwff Hmff] Hfpf]
      [[t Hwft Hmft] Hfpt]
      [[g Hwfg Hmfg] Hfpg]
      [[u Hwfu Hmfu] Hfpu].
    simpl in *.
    unshelve epose proof hypothesis _ _ _ HΓinj.
    wf_auto2. use AnyReasoning in H.
    unfold injectivity_definition in H.
    apply forall_functional_subst_meta with (φ' := f) in H; auto.
    mlSimpl in H. simpl in H.
    apply forall_functional_subst_meta with (φ' := t) in H; auto.
    mlSimpl in H. simpl in H.
    rewrite ! bevar_subst_not_occur in H. 1,3-5: wf_auto2.
    apply forall_functional_subst_meta with (φ' := g) in H; auto.
    mlSimpl in H. simpl in H.
    rewrite ! bevar_subst_not_occur in H. 1-2,4-6: wf_auto2.
    apply forall_functional_subst_meta with (φ' := u) in H; auto.
    mlSimpl in H. simpl in H.
    rewrite ! bevar_subst_not_occur in H. 1-3,5-7: wf_auto2.
    exact H.
  Defined.

  (** The naming of the following lemmas matches this article:
        Unification in Matching Logic - Extended Version
        Andrei Arusoaie, Dorel Lucanu
        https://arxiv.org/abs/1811.02835v3
   *)

  (* Lemma Prop₃_left: forall φ φ', *)
  (*   well_formed φ -> well_formed φ' -> *)
  Lemma Prop₃_left: forall (φ φ' : WFMFPattern),
    Γ ⊢ (φ and (φ' =ml φ)) ---> (φ and φ').
  Proof.
    intros [φ Wf1 ?] [φ' Wf2 ?]. simpl.
    toMLGoal. wf_auto2.
    mlIntro "H0". mlDestructAnd "H0" as "H1" "H2".
    mlRewriteBy "H2" at 1.
    mlSplitAnd; mlExact "H1".
  Defined.

  (* Lemma Prop₃_right : forall φ φ', *)
  (*     well_formed φ -> well_formed φ' -> mu_free φ' -> *)
  (*     Γ ⊢ (ex , (φ =ml b0))  -> *)
  (*     Γ ⊢ (ex , (φ' =ml b0))  -> *)
  Lemma Prop₃_right : forall (φ φ' : TermPattern),
      Γ ⊢ (φ and φ') ---> (φ and (φ =ml φ')) .
  Proof.
    intros [[φ Wf1 ?] Func1] [[φ' Wf2 MF] Func2].
    simpl in *.
    toMLGoal. wf_auto2.
    mlIntro "H0".
    mlAssert ("H1" : ⌈ φ and φ' ⌉).
    wf_auto2. 
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

  (* Lemma Lemma₁ : forall φ t x, *)
  (*   well_formed φ -> *)
  (*   mu_free φ -> *)
  Lemma Lemma₁ : forall (φ : WFMFPattern) t x,
    well_formed t ->
    Γ ⊢ (patt_free_evar x) =ml t ---> φ^[[evar:x↦t]] =ml φ.
  Proof.
    intros [φ wfφ mfφ] * wft. simpl.
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

  (* Lemma Lemma₂ : forall φ σ, *)
  (*   mu_free φ -> well_formed φ -> *)
  Lemma Lemma₂ : forall (φ : WFMFPattern) σ,
    forallb mu_free (map snd σ) -> wf (map snd σ) ->
    Γ ⊢ substitute_list σ φ and predicate_list σ <--->
        φ and predicate_list σ.
  Proof.
    intros [φ wfφ mfφ] * mfσ wfσ. simpl.
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
    epose proof (Lemma₁ (mkWFMF φ wfφ mfφ) _ _ _). simpl in H.
    mlApplyMeta H in "H1". clear H.
    mlFreshEvar as y.
    assert (y ∉ free_evars (φ^[[evar:e↦p]] <---> φ)) as Hy by ltac2:(fm_solve()).
    epose proof (total_phi_impl_phi _ _ _ _ Hy _).
    mlApplyMeta H in "H1". clear H.
    mlExact "H1".
    Unshelve. all: try solve [auto | wf_auto2].
    1,3: exact AnyReasoning.
    simpl in mfσ. apply andb_true_iff in mfσ as [].
    apply mu_free_free_evar_subst; auto.
  Defined.

  (* Lemma Lemma₅ : forall (σ : list (evar * Pattern)) t₁ t₂, *)
  (*   well_formed t₁ -> well_formed t₂ -> *)
  (*   mu_free t₁ -> mu_free t₂ -> *)
  Lemma Lemma₅ : forall (σ : list (evar * Pattern)) (t₁ t₂ : WFMFPattern),
    wf (map snd σ) -> forallb mu_free (map snd σ) ->
    Γ ⊢ is_unifier_of σ t₁ t₂ ---> predicate_list σ ---> (t₁ =ml t₂).
  Proof.
    intros ? [t₁ wft₁ mft₁] [t₂ wft₂ mft₂] wfσ mfσ.
    simpl.
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
    epose proof (Lemma₂ (mkWFMF t₁ wft₁ mft₁) σ _ _). simpl in H1.
    mlRewrite <- H1 at 1.
    epose proof (Lemma₂ (mkWFMF t₂ wft₂ mft₂) σ _ _). simpl in H2.
    mlRewrite <- H2 at 1.
    mlRewriteBy "H" at 1.
    mlReflexivity.
    Unshelve. all: auto.
  Defined.

  Lemma R₅' : forall x, Γ ⊢ (ex , patt_free_evar x =ml b0).
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

  Definition wfmfFevar (x : evar) := mkWFMF (patt_free_evar x) (well_formed_free_evar x) eq_refl.

  Lemma Lemma₃ {T : Set} {UPT : UP T} P P' : P ===> P' -> P' <> bottomUP -> Γ ⊢ toPredicateUP P wf---> toPredicateUP P'.
  Proof with inside mlClear "_" outside try apply wfmfWF.
    intros [] NB; pose proof (toPredicateInsertUP Γ).
    * specialize (H P0 t t).
      rewrite unwrap_wfmfbWrapper in H. simpl in H.
      apply pf_iff_proj1 in H...
      toMLGoal...
      rewrite ! unwrap_wfmfbWrapper in H |- *. simpl in H |- *.
      mlIntro "H". mlApplyMeta H in "H".
      mlDestructAnd "H" as "_" "H0"...
      mlAssumption.
    * pose proof (H P0 (f wf⋅ t) (g wf⋅ u)) as H0.
      rewrite unwrap_wfmfbWrapper in H0. simpl in H0.
      pose proof (H (insertUP P0 (f, g)) t u) as H1.
      rewrite unwrap_wfmfbWrapper in H1. simpl in H1.
      specialize (H P0 f g).
      rewrite unwrap_wfmfbWrapper in H. simpl in H.
      apply pf_iff_proj1 in H0...
      apply pf_iff_proj2 in H1, H...
      toMLGoal...
      rewrite ! unwrap_wfmfbWrapper in H0, H1, H |- *.
      simpl in H0, H1, H |- *.
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
    * pose proof (H P0 x (wfmfFevar y)) as H0.
      rewrite ! unwrap_wfmfbWrapper in H0. simpl in H0.
      apply pf_iff_proj1 in H0...
      specialize (H P0 (wfmfFevar y) x).
      rewrite ! unwrap_wfmfbWrapper in H. simpl in H.
      apply pf_iff_proj2 in H...
      toMLGoal...
      rewrite ! unwrap_wfmfbWrapper in H0, H |- *.
      simpl in H0, H |- *.
      mlIntro "H".
      mlApplyMeta H0 in "H". mlDestructAnd "H" as "H0" "H1".
      mlApplyMeta H. mlSplitAnd. mlSymmetry. 1-2: mlAssumption.
      all: wf_auto2.
    * now destruct NB.
    * pose proof (H P0 (wfmfFevar x) t).
      rewrite ! unwrap_wfmfbWrapper in H0. simpl in H0.
      apply pf_iff_proj1 in H0...
      specialize (H (substituteAllUP x t P0) (wfmfFevar x) t).
      rewrite ! unwrap_wfmfbWrapper in H. simpl in H.
      apply pf_iff_proj2 in H...
      toMLGoal...
      rewrite ! unwrap_wfmfbWrapper. simpl.
      mlIntro "H".
      mlApplyMeta H0 in "H".
      mlApplyMeta H.
      pose proof (toPredicateSubstituteAllUP Γ P0 x t).
      rewrite ! unwrap_wfmfbWrapper in H1. simpl in H1.
      mlRewrite H1 at 1.
      opose proof* (Lemma₂ ((toPredicateUP P0)) [(x, wfmfPattern t)]); cbn; rewrite ? andb_true_r; auto...
      apply wfmfMF.
      simpl in H2. apply pf_iff_proj2 in H2.
      2-5: refine_wf...

      match goal with [H2 : derives_using _ (?x ---> _) _ |- _] => mlAssert ("H0" : x) end. refine_wf...

      mlDestructAnd "H" as "H1" "H2".
      repeat mlSplitAnd; try mlAssumption.
      pose proof (top_holds Γ). use AnyReasoning in H3. mlExactMeta H3.
      mlApplyMeta H2 in "H0".
      mlDestructAnd "H0" as "H1" "H2". mlDestructAnd "H2" as "H3" "_"...
      mlSplitAnd; mlAssumption.
    Defined.

  (**********************************************)

  (**
    The formalized unification algorithm gives us an MGU.
  *)
  Axiom convenient : forall {T : Set} {UPT : UP T} σ t1 t2, is_most_general_unifier_of σ (`t1) (`t2) -> {P : T & (USrtc (singletonUP t1 t2) P * (P ≠ bottomUP) * (Γ ⊢ projT1 (toPredicateUP P) <---> predicate_list σ))%type}.

  Lemma Lemma₄_helper : forall {T : Set} {UPT : UP T} P P',
    USrtc P P' ->
    P' ≠ bottomUP ->
    Γ ⊢wf toPredicateUP P wf---> toPredicateUP P'.
  Proof with apply wfWFPattern.
    intros * R NB.
    unfold WFDerives.
    rewrite unwrap_wfwrapper.
    induction R.
    aapply A_impl_A...
    toMLGoal. apply well_formed_imp...
    mlIntro "H".
    mlApplyMeta IHR; auto.
    opose proof* (Lemma₃); eauto.
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

  Lemma Lemma₄ : forall (σ : list (evar * Pattern)) (t1 t2 : WFPattern),
    wf (map snd σ) ->
    is_most_general_unifier_of σ (`t1) (`t2) ->
    Γ ⊢ `t1 =ml `t2 ---> predicate_list σ.
  Proof with try apply wfWFPattern.
    intros * WFσ HMGU.
    opose proof* (@optionSetUP _ _ (gset (WFPattern * WFPattern))).
    1-2: typeclasses eauto.
    pose proof (convenient σ t1 t2 HMGU) as [P [[R NB] EQ] ].
    toMLGoal. simpl. refine_wf...
    now apply wf_predicate_list.
    pose proof (proj2_sig t1). pose proof (proj2_sig t2).
    mlRewrite <- EQ at 1.
    clear H H0.
    pose proof (toPredicateSingletonUP Γ t1 t2).
    unfold WFDerives in H. rewrite ! unwrap_wfwrapper in H.
    pose proof (proj2_sig (toPredicateUP P)).
    mlRewrite <- H at 1.
    clear H0.
    opose proof* Lemma₄_helper; eauto.
    unfold WFDerives in H0. rewrite ! unwrap_wfwrapper in H0.
    mlExactMeta H0.
  Defined.

  Lemma Lemma₆ : forall (σ : list (evar * Pattern)) (t1 t2 : WFPattern),
    wf (map snd σ) ->
    mu_free (`t1) -> mu_free (`t2) ->
    forallb mu_free (map snd σ) ->
    is_most_general_unifier_of σ (`t1) (`t2) ->
    Γ ⊢ (`t1 =ml `t2) <---> predicate_list σ.
  Proof with try by refine_wf.
    intros ? [t1 wft1] [t2 wft2] WFσ MFt1 MFt2 MFσ HMGU.
    opose proof* (wf_predicate_list σ) as WFpl...
    toMLGoal... mlSplitAnd; mlIntro "H".
    unshelve opose proof* (Lemma₄ σ (t1 ↾ _) (t2 ↾ _))...
    all: simpl in *. mlApplyMeta H. mlAssumption.
    opose proof* (Lemma₅ σ t1 t2)...
    destruct HMGU as [IUO _]. specialize (IUO Γ).
    pose proof (MP IUO H). mlApplyMeta H0. mlAssumption.
  Defined.

  Lemma Prop3_full : forall t1 t2,
    well_formed t1 -> well_formed t2 -> mu_free t2 ->
    Γ ⊢ is_functional t1 -> Γ ⊢ is_functional t2 ->
    Γ ⊢ t1 and t2 <---> t1 and t1 =ml t2.
  Proof with try solve [auto | wf_auto2].
    intros * WFt1 WFt2 MFt2 IFt1 IFt2.
    toMLGoal... mlSplitAnd; mlIntro "H".
    opose proof* (Prop₃_right t1 t2)...
    mlApplyMeta H. mlAssumption.
    opose proof* (Prop₃_left t1 t2)...
    mlApplyMeta H. mlDestructAnd "H" as "H1" "H2".
    mlSplitAnd; only 2: mlSymmetry; mlAssumption.
  Defined.

  Lemma Theorem₁ : forall σ t1 t2,
    well_formed t1 -> well_formed t2 ->
    wf (map snd σ) ->
    mu_free t1 -> mu_free t2 ->
    forallb mu_free (map snd σ) ->
    Γ ⊢ is_functional t1 -> Γ ⊢ is_functional t2 ->
    is_most_general_unifier_of σ t1 t2 ->
    (Γ ⊢ (t1 and t2) =ml (t1 and predicate_list σ)) * (Γ ⊢ (t1 and t2) =ml (t2 and predicate_list σ)).
  Proof with try solve [auto | wf_auto2 | refine_wf; auto].
    intros * WFt1 WFt2 WFσ MFt1 MFt2 MFσ IFt1 IFt2 HMGU.
    opose proof* (Prop3_full t1 t2)...
    assert (Γ ⊢ t1 and t2 <---> t2 and t1 =ml t2). {
      opose proof* (Prop3_full t2 t1)...
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
    opose proof* (Lemma₆ σ (t1 ↾ WFt1) (t2 ↾ WFt2))...
    opose proof* (wf_predicate_list σ)...
    split. toMLGoal... 2: toMLGoal...
    all: simpl in H1.
    mlRewrite H at 1. 2: mlRewrite H0 at 1.
    all: mlRewrite H1 at 1; mlReflexivity.
  Defined.

  Goal forall (f' g' one' : symbols) (x' y' z' : evar) (*one : WFPattern*),
    x' ≠ z' -> y' ≠ z' ->
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
    intros * NE1 NE2 **.
    rename H into Hfunctional_f.
    rename H0 into Hfunctional_g.
    rename H1 into Hfunctional_one.
    evar (σ : list (evar * Pattern)).
    assert (wf (map snd σ)) as WFσ by shelve.
    pose proof (wf_predicate_list σ WFσ) as WFplσ.
    exists σ.
    toMLGoal... mlSplitAnd; mlIntro.
    opose proof* (Prop₃_right (`t1) (`t2))...
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
      opose proof* (Lemma₄_helper (Some (singleton (t1, t2)))). auto.
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
      opose proof* (Lemma₂ (`t1) σ)...
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

