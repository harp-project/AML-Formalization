From Coq Require Import ssreflect ssrfun ssrbool.

From Ltac2 Require Import Ltac2.

From Coq Require Import Ensembles Bool String.

From Coq.Logic Require Import FunctionalExtensionality Eqdep_dec.
From Equations Require Import Equations.

Require Import Coq.Program.Tactics.

From MatchingLogic Require Import Syntax DerivedOperators_Syntax ProofSystem IndexManipulation wftactics.

From stdpp Require Import list tactics fin_sets coGset gmap sets.

From MatchingLogic.Utils Require Import stdpp_ext.
Import extralibrary.
From MatchingLogic Require Import Logic
  ProofInfo
  ProofMode_base 
  ProofMode_propositional
  ProofMode_firstorder
  ProofMode_fixpoint
  ProofMode_reshaper
  BasicProofSystemLemmas
.

Import MatchingLogic.Logic.Notations.

Set Default Proof Mode "Classic".

Open Scope ml_scope.
Open Scope string_scope.
Open Scope list_scope.


Ltac2 _callCompletedTransformedAndCast
  (t : constr) (transform : constr) (tac : constr -> unit) :=
  let tac' := (fun (t' : constr) =>
    let tac'' := (fun (t'' : constr) =>
      let tcast := open_constr:(@useGenericReasoning'' _ _ _ _ _ $t'') in
      fillWithUnderscoresAndCall tac tcast []
    ) in
    fillWithUnderscoresAndCall (fun t''' => tac'' t''') transform [t']
  ) in
  fillWithUnderscoresAndCall tac' t []
.

Ltac2 mlApplyMetaGeneralized (t : constr) :=
  _callCompletedTransformedAndCast t constr:(@reshape_lhs_imp_to_and_forward) _mlApplyMetaRaw ;
  try_solve_pile_basic ();
  try_wfa ()
.

Ltac _mlApplyMetaGeneralized t :=
  _ensureProofMode;
  let ff := ltac2:(t' |- mlApplyMetaGeneralized (Option.get (Ltac1.to_constr(t')))) in
  ff t;
  rewrite [foldr patt_and _ _]/=
.

Tactic Notation "mlApplyMeta" constr(t) :=
  (mlApplyMeta t) || (_mlApplyMetaGeneralized t)
.

#[local]
Example ex_mlApplyMetaGeneralized  {Σ : Signature} Γ a b c d e f:
  well_formed a ->
  well_formed b ->
  well_formed c ->
  well_formed d ->
  well_formed e ->
  well_formed f ->
  Γ ⊢ a ---> b ---> c ---> d ---> e ---> f ->
  Γ ⊢ (a and b and c and d and e) ---> f.
Proof.
  intros wfa wfb wfc wfd wfe wff H.
  toMLGoal.
  { wf_auto2. }
  mlIntro "H1".
  mlApplyMeta H.
  mlExact "H1".
Defined.

Lemma foldr_andb_init_true i l:
  foldr andb i l = true -> i = true.
Proof.
  move: i.
  induction l; cbn; intros i H.
  { assumption. }
  {
    rewrite andb_true_iff in H.
    destruct H as [H1 H2].
    apply IHl.
    exact H2.
  }
Qed.

Lemma foldr_andb_true_iff i l:
  foldr andb i l = i && foldr andb true l.
Proof.
  move: i.
  induction l; cbn; intros i.
  {
    rewrite andb_true_r. reflexivity.
  }
  {
    rewrite IHl.
    rewrite !andb_assoc.
    rewrite [a && i]andb_comm.
    reflexivity.
  }
Qed.


Lemma MLGoal_weakenConclusionGen' {Σ : Signature} Γ l₁ l₂ name g' i
    (x : Pattern) (xs : list Pattern)
  :
  forall (r : ImpReshapeS g' (x::xs)),
  mkMLGoal Σ Γ (l₁ ++ (mkNH _ name ((untagPattern (irs_flattened _ _ r)))) :: l₂) ((foldr (patt_and) x xs)) i ->
  mkMLGoal Σ Γ (l₁ ++ (mkNH _ name ((untagPattern (irs_flattened _ _ r)))) :: l₂) g' i.
Proof.
  intros r H.
  intros Hwf1 Hwf2. cbn in *.

  assert (wfr : well_formed r).
  {
    clear H.
    destruct r as [f pf].
    rewrite pf.
    rewrite pf in Hwf2.
    rewrite 2!map_app in Hwf2.
    rewrite foldr_app in Hwf2.
    cbn in Hwf2.
    apply foldr_andb_init_true in Hwf2.
    wf_auto2.
  }

 
  assert (wffa: foldr andb true (map well_formed (map nh_patt (l₁ ++ (mkNH _ name r) :: l₂)))).
  {
    cbn.
    destruct r as [f pf].
    rewrite pf in Hwf2.
    rewrite 2!map_app in Hwf2.
    rewrite foldr_app in Hwf2.
    rewrite 2!map_app.
    rewrite foldr_app.
    cbn in Hwf2. cbn.
    rewrite foldr_andb_true_iff in Hwf2.
    rewrite foldr_andb_true_iff.
    wf_auto2.
  }


  assert (well_formed x).
  {
    rewrite irs_pf in Hwf2.
    rewrite 2!map_app in Hwf2.
    rewrite foldr_app in Hwf2.
    rewrite foldr_andb_true_iff in Hwf2.
    wf_auto2.
  }

  assert (Pattern.wf xs).
  {
    rewrite irs_pf in Hwf2.
    rewrite 2!map_app in Hwf2.
    rewrite foldr_app in Hwf2.
    rewrite foldr_andb_true_iff in Hwf2.
    wf_auto2.
  }

  feed specialize H.
  {
    cbn. wf_auto2.
  }
  { cbn. assumption. }
  cbn in H.


  assert (Hwfl₁ : wf (map nh_patt l₁) = true).
  {
    cbn.
    destruct r as [f pf].
    rewrite pf in Hwf2.
    rewrite 2!map_app in Hwf2.
    rewrite foldr_app in Hwf2.
    rewrite foldr_andb_true_iff in Hwf2.
    cbn in *.
    rewrite map_app in H.
    rewrite map_app in wffa.
    wf_auto2.
  }

  assert (Hwfl₂ : wf (map nh_patt l₂) = true).
  {
    cbn.
    destruct r as [f pf].
    rewrite pf in Hwf2.
    rewrite 2!map_app in Hwf2.
    rewrite foldr_app in Hwf2.
    rewrite foldr_andb_true_iff in Hwf2.
    cbn in *.
    rewrite map_app in H.
    rewrite map_app in wffa.
    wf_auto2.
  }

  rewrite map_app.
  cbn. rewrite map_app in H. cbn in H.
  rewrite irs_pf.

  eapply prf_strenghten_premise_iter_meta_meta.
  6: {
    useBasicReasoning.
    apply lhs_imp_to_and.
    1-3: wf_auto2.
  }
  1-5: wf_auto2.

  apply prf_weaken_conclusion_iter_under_implication_iter_meta.
  1-4: wf_auto2.

  eapply prf_strenghten_premise_iter_meta_meta.
  6: {
    useBasicReasoning.
    apply lhs_and_to_imp.
    1-3: wf_auto2.
  }
  1-5: wf_auto2.

  rewrite irs_pf in H.
  exact H.
Defined.

Lemma MLGoal_weakenConclusionGen {Σ : Signature} Γ l₁ l₂ name g' i
    (x : Pattern) (xs : list Pattern)
  :
  forall (r : ImpReshapeS g' (x::xs)),
  mkMLGoal Σ Γ (l₁ ++ (mkNH _ name ((untagPattern (irs_flattened _ _ r)))) :: l₂)
    (
      match (rev xs) with
      | [] => x
      | yk::ys => (foldr (patt_and) yk (x::(rev ys)))
      end
    )
    i ->
  mkMLGoal Σ Γ (l₁ ++ (mkNH _ name ((untagPattern (irs_flattened _ _ r)))) :: l₂) g' i.
Proof.
  intros r H.
  apply MLGoal_weakenConclusionGen'.
  intros wf1 wf2. cbn.

  feed specialize H.
  {
    cbn. clear H.
    destruct (rev xs) eqn:Heqxs.
    {
      wf_auto2.
    }
    {
      apply (f_equal (@rev Pattern)) in Heqxs.
      rewrite rev_involutive in Heqxs.
      simpl in Heqxs.
      subst xs.
      wf_auto2.
    }
  }
  {
    cbn. clear H. cbn in *.
    wf_auto2.
  }
  cbn in *.
  destruct (rev xs) eqn:Heqxs.
  {
    apply (f_equal (@rev Pattern)) in Heqxs.
    rewrite rev_involutive in Heqxs.
    simpl in Heqxs.
    subst xs.
    cbn in *.
    exact H.
  }
  {
    apply (f_equal (@rev Pattern)) in Heqxs.
    rewrite rev_involutive in Heqxs.
    simpl in Heqxs.
    subst xs.

    eapply prf_weaken_conclusion_iter_meta_meta.
    5: apply H.
    4: {
      rewrite foldr_app. cbn.
      toMLGoal.
      {
        wf_auto2.
      }
      mlIntro "H1".
      mlDestructAnd "H1" as "Hx" "Hf".
      useBasicReasoning.
      mlAdd (foldr_and_weaken_last Γ p (p and x) (rev l) ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2)) as "Hw".
      mlAssert ("Hw'": (foldr patt_and p (rev l) ---> foldr patt_and (p and x) (rev l))).
      { wf_auto2. }
      {
        mlApply "Hw".
        mlIntro "Hp".
        mlSplitAnd;[mlExact "Hp" | mlExact "Hx"].
      }
      mlClear "Hw".
      mlApply "Hw'".
      mlExact "Hf".
    }
    1,2,3: wf_auto2.
  }
Defined.

Tactic Notation "_mlApplyBasic" constr(name') :=
  _ensureProofMode;
  _mlReshapeHypsByName name';
  apply MLGoal_weakenConclusion;
  _mlReshapeHypsBack;
  cbn.


Tactic Notation "_mlApplyGen" constr(name') :=
  _ensureProofMode;
  _mlReshapeHypsByName name';
  apply MLGoal_weakenConclusionGen;
  _mlReshapeHypsBack;
  cbn.

#[local]
Example ex_mlApplyGeneralized  {Σ : Signature} Γ a b c d e f g:
  well_formed a ->
  well_formed b ->
  well_formed c ->
  well_formed d ->
  well_formed e ->
  well_formed f ->
  well_formed g ->
  Γ ⊢ ((a and b and c and d and e) --->
       (a ---> b ---> c ---> d ---> e ---> f) --->
       (f ---> g) --->
       g).
Proof.
  intros wfa wfb wfc wfd wfe wff wfg.
  toMLGoal.
  { wf_auto2. }
  mlIntro "H1".
  mlIntro "H2".
  mlIntro "H3".

  _mlApplyGen "H3".
  _mlApplyGen "H2".
  mlExact "H1".
Defined.

Tactic Notation "mlApply" constr(name') :=
  (_mlApplyBasic name') || (_mlApplyGen name')
.

Section FOL_helpers.

  Context {Σ : Signature}.

  Lemma Framing_left (Γ : Theory) (ϕ₁ ϕ₂ ψ : Pattern) (i : ProofInfo)
    (wfψ : well_formed ψ)
    {pile : ProofInfoLe ((ExGen := ∅, SVSubst := ∅, KT := false)) i}
    :
    Γ ⊢i ϕ₁ ---> ϕ₂ using i ->
    Γ ⊢i ϕ₁ $ ψ ---> ϕ₂ $ ψ using i.
  Proof.
    intros [pf Hpf].
    unshelve (eexists).
    {
      apply ProofSystem.Framing_left.
      { exact wfψ. }
      exact pf.
    }
    {
      destruct Hpf as [Hpf1 Hpf2 Hpf3].
      constructor; simpl.
      {
        assumption.
      }
      {
        assumption.
      }
      {
        assumption.
      }
    }
  Defined.

  Lemma Framing_right (Γ : Theory) (ϕ₁ ϕ₂ ψ : Pattern) (i : ProofInfo)
    (wfψ : well_formed ψ)
    {pile : ProofInfoLe ((ExGen := ∅, SVSubst := ∅, KT := false)) i}
    :
    Γ ⊢i ϕ₁ ---> ϕ₂ using i ->
    Γ ⊢i ψ $ ϕ₁ ---> ψ $ ϕ₂ using i.
  Proof.
    intros [pf Hpf].
    unshelve (eexists).
    {
      apply ProofSystem.Framing_right.
      { exact wfψ. }
      exact pf.
    }
    {
      destruct Hpf as [Hpf1 Hpf2 Hpf3].
      constructor; simpl.
      {
        assumption.
      }
      {
        assumption.
      }
      {
        assumption.
      }
    }
  Defined.

  Lemma Prop_bott_left (Γ : Theory) (ϕ : Pattern) :
    well_formed ϕ ->
    Γ ⊢i ⊥ $ ϕ ---> ⊥ using BasicReasoning.
  Proof.
    intros wfϕ.
    unshelve (eexists).
    {
      apply ProofSystem.Prop_bott_left. exact wfϕ.
    }
    {
      abstract(solve_pim_simple).
    }
  Defined.

  Lemma Prop_bott_right (Γ : Theory) (ϕ : Pattern) :
    well_formed ϕ ->
    Γ ⊢i ϕ $ ⊥ ---> ⊥ using BasicReasoning.
  Proof.
    intros wfϕ.
    unshelve (eexists).
    {
      apply ProofSystem.Prop_bott_right. exact wfϕ.
    }
    {
      abstract(solve_pim_simple).
    }
  Defined.

  Arguments Prop_bott_left _ (_%ml) _ : clear implicits.
  Arguments Prop_bott_right _ (_%ml) _ : clear implicits.

  Lemma Prop_bot_ctx (Γ : Theory) (C : Application_context) :
    Γ ⊢i ((subst_ctx C patt_bott) ---> patt_bott)
    using (ExGen := ∅, SVSubst := ∅, KT := false).
  Proof.
    induction C; simpl in *.
    - apply useBasicReasoning.
      apply bot_elim.
      wf_auto2.
    - eapply syllogism_meta.
      5: { apply useBasicReasoning. apply (Prop_bott_left Γ p ltac:(wf_auto2)). }
      4: { simpl. eapply useGenericReasoning.
           2: eapply (Framing_left _ _ _ _ _ Prf).
           1: apply pile_refl.
           eapply useGenericReasoning.
           2: apply IHC. try_solve_pile.
      }
      all: try solve [wf_auto2].
       - eapply syllogism_meta.
           5: { apply useBasicReasoning. apply (Prop_bott_right Γ p ltac:(wf_auto2)). }
           4: { simpl. eapply useGenericReasoning.
                2: eapply (Framing_right _ _ _ _ _ Prf).
                1: apply pile_refl.
                eapply useGenericReasoning.
                2: apply IHC.
                try_solve_pile.
           }
  Unshelve.
    1-3: wf_auto2.
    1-2: try_solve_pile.
  Defined.

  Lemma Framing (Γ : Theory) (C : Application_context) (A B : Pattern) (i : ProofInfo)
    {pile : ProofInfoLe
     ((ExGen := ∅, SVSubst := ∅, KT := false))
     i
    }
    :
    Γ ⊢i (A ---> B) using i ->
    Γ ⊢i ((subst_ctx C A) ---> (subst_ctx C B)) using i.
  Proof.
    intros H.
    pose proof H as [pf _].
    pose proof (HWF := proved_impl_wf _ _ pf).
    assert (wfA: well_formed A) by wf_auto2.
    assert (wfB: well_formed B) by wf_auto2.
    clear pf HWF.

    move: wfA wfB H.
    induction C; intros WFA WFB H; simpl in *.
    - exact H.
    - destruct i.
      unshelve (eapply (Framing_left _ _ _ _ _ Prf)).
      { 
        try_solve_pile.
      }
      apply IHC.
      1-3: assumption.
    - destruct i.
      unshelve (eapply (Framing_right _ _ _ _ _ Prf)).
      {
        try_solve_pile.
      }
      apply IHC.
      1-3: assumption.
  Defined.

  Lemma A_implies_not_not_A_ctx (Γ : Theory) (A : Pattern) (C : Application_context)
    (i : ProofInfo) {pile : ProofInfoLe ((ExGen := ∅, SVSubst := ∅, KT := false)) i}
    :
    well_formed A ->
    Γ ⊢i A using i ->
    Γ ⊢i (! (subst_ctx C ( !A ))) using i.
  Proof.
    intros WFA H.

    epose proof (ANNA := A_implies_not_not_A_alt Γ _ i _ H).
    replace (! (! A)) with ((! A) ---> Bot) in ANNA by reflexivity.
    epose proof (EF := Framing _ C (! A) Bot _ ANNA).
    epose proof (PB := Prop_bot_ctx Γ C).
    apply liftProofInfoLe with (i₂ := i) in PB. 2: try_solve_pile.
    epose (TRANS := syllogism_meta _ _ _ EF PB).
    apply TRANS.

    Unshelve.
    all: wf_auto2.
    all: set_solver.
  Defined.

  Lemma ctx_bot_prop (Γ : Theory) (C : Application_context) (A : Pattern) 
    (i : ProofInfo)
    {pile : ProofInfoLe ((ExGen := ∅, SVSubst := ∅, KT := false)) i}
  :
    well_formed A ->
    Γ ⊢i (A ---> Bot) using i ->
    Γ ⊢i (subst_ctx C A ---> Bot) using i.
  Proof.
    intros WFA H.
    epose proof (FR := Framing Γ C A Bot _ H).
    epose proof (BPR := Prop_bot_ctx Γ C).
    apply liftProofInfoLe with (i₂ := i) in BPR. 2: try_solve_pile.
    epose proof (TRANS := syllogism_meta _ _ _ FR BPR).
    exact TRANS.
    Unshelve.
    all: wf_auto2.
    all: set_solver.
  Defined.

End FOL_helpers.

Lemma prf_prop_bott_iff {Σ : Signature} Γ AC:
  Γ ⊢i ((subst_ctx AC patt_bott) <---> patt_bott)
  using (
  (ExGen := ∅, SVSubst := ∅, KT := false)).
Proof.
  apply pf_iff_split.
  1,2: wf_auto2.
  1: apply ctx_bot_prop.
  1: apply pile_refl.
  1: wf_auto2.
  {
    useBasicReasoning.
    apply A_impl_A.
    reflexivity.
  }
  {
    useBasicReasoning.
    apply bot_elim.
    wf_auto2.
  }
Defined.

Lemma Prop_disj_left {Σ : Signature} (Γ : Theory) (ϕ₁ ϕ₂ ψ : Pattern) :
  well_formed ϕ₁ ->
  well_formed ϕ₂ ->
  well_formed ψ ->
  Γ ⊢i (ϕ₁ or ϕ₂) $ ψ ---> (ϕ₁ $ ψ) or (ϕ₂ $ ψ) using BasicReasoning.
Proof.
  intros wfϕ₁ wfϕ₂ wfψ.
  unshelve (eexists).
  {
    apply Prop_disj_left; assumption.
  }
  {
    abstract (solve_pim_simple).
  }
Defined.

Lemma Prop_disj_right {Σ : Signature} (Γ : Theory) (ϕ₁ ϕ₂ ψ : Pattern) :
  well_formed ϕ₁ ->
  well_formed ϕ₂ ->
  well_formed ψ ->
  Γ ⊢i ψ $ (ϕ₁ or ϕ₂)  ---> (ψ $ ϕ₁) or (ψ $ ϕ₂) using BasicReasoning.
Proof.
  intros wfϕ₁ wfϕ₂ wfψ.
  unshelve (eexists).
  {
    apply Prop_disj_right; assumption.
  }
  {
    abstract (solve_pim_simple).
  }
Defined.

Lemma prf_prop_or_iff {Σ : Signature} Γ AC p q:
  well_formed p ->
  well_formed q ->
  Γ ⊢i ((subst_ctx AC (p or q)) <---> ((subst_ctx AC p) or (subst_ctx AC q)))
  using (
  (ExGen := ∅, SVSubst := ∅, KT := false)).
Proof.
  intros wfp wfq.
  induction AC; simpl.
  - useBasicReasoning. apply pf_iff_equiv_refl; wf_auto2.
  - apply pf_iff_iff in IHAC; try_wfauto2.
    destruct IHAC as [IH1 IH2].
    remember_constraint as i.
    apply pf_iff_split; try_wfauto2.
    + pose proof (H := IH1).
      apply useGenericReasoning with (i := i) in H.
      2: { try_solve_pile. }
      rewrite Heqi in H.
      apply Framing_left with (ψ := p0)in H; auto.
      2: { apply pile_refl. }
      eapply syllogism_meta. 4: subst i; apply H.
      all: try_wfauto2.
      remember (subst_ctx AC p) as p'.
      remember (subst_ctx AC q) as q'.
      subst i.
      eapply useGenericReasoning.
      2: eapply Prop_disj_left. all: subst; try_wfauto2.
      { try_solve_pile. }
    + eapply prf_disj_elim_meta_meta; try_wfauto2.
      * subst i. 
        apply Framing_left with (ψ := p0); auto.
        { try_solve_pile. }
        eapply prf_weaken_conclusion_meta_meta.
        4: { gapply IH2. try_solve_pile. }
        1-3: wf_auto2.
        useBasicReasoning.
        apply disj_left_intro; wf_auto2.
      * subst i.
        apply Framing_left with (ψ := p0); auto.
        { try_solve_pile. }
        eapply prf_weaken_conclusion_meta_meta. 4: gapply IH2; try_solve_pile. all: try_wfauto2.
        useBasicReasoning.
        apply disj_right_intro; wf_auto2.
  - apply pf_iff_iff in IHAC; try_wfauto2.
    destruct IHAC as [IH1 IH2].
    remember_constraint as i.
    apply pf_iff_split; try_wfauto2.
    + pose proof (H := IH1).
      apply useGenericReasoning with (i := i) in H.
      2: { subst i. try_solve_pile. }
      eapply Framing_right with (ψ := p0)in H; auto.
      eapply syllogism_meta. 4: apply H.
      all: try_wfauto2.
      2: { subst i. try_solve_pile. }
      remember (subst_ctx AC p) as p'.
      remember (subst_ctx AC q) as q'.
      subst i; apply useBasicReasoning.
      apply Prop_disj_right. all: subst; try_wfauto2.
    + eapply prf_disj_elim_meta_meta; try_wfauto2.
      * subst i.
        apply Framing_right with (ψ := p0); auto.
        { try_solve_pile. }
        eapply prf_weaken_conclusion_meta_meta.
        4: gapply IH2; try_solve_pile. all: try_wfauto2.
        useBasicReasoning.
        apply disj_left_intro; wf_auto2.
      * subst i.
        apply Framing_right with (ψ := p0); auto.
        { try_solve_pile. }
        eapply prf_weaken_conclusion_meta_meta.
        4: gapply IH2; try_solve_pile.
        all: try_wfauto2.
        useBasicReasoning.
        apply disj_right_intro; wf_auto2.
Defined.




Lemma Singleton_ctx {Σ : Signature} (Γ : Theory) (C1 C2 : Application_context) (ϕ : Pattern) (x : evar) :
  well_formed ϕ ->
  Γ ⊢i (! ((subst_ctx C1 (patt_free_evar x and ϕ)) and
             (subst_ctx C2 (patt_free_evar x and (! ϕ)))))
  using BasicReasoning.
Proof.
  intros Hwf.
  unshelve (eexists).
  {
    apply ProofSystem.Singleton_ctx. apply Hwf.
  }
  {
    abstract (solve_pim_simple).
  }
Defined.

Lemma Existence {Σ : Signature} (Γ : Theory) :
  Γ ⊢i (ex , patt_bound_evar 0) using BasicReasoning.
Proof.
  unshelve (eexists).
  {
    apply ProofSystem.Existence.
  }
  {
    abstract (solve_pim_simple).
  }
Defined.

Lemma Prop_ex_left {Σ : Signature} (Γ : Theory) (ϕ ψ : Pattern) :
  well_formed (ex, ϕ) ->
  well_formed ψ ->
  Γ ⊢i (ex , ϕ) $ ψ ---> ex , ϕ $ ψ
  using BasicReasoning.
Proof.
  intros wfϕ wfψ.
  unshelve (eexists).
  {
    apply ProofSystem.Prop_ex_left.
    { exact wfϕ. }
    { exact wfψ. }
  }
  { abstract(solve_pim_simple). }
Defined.

Lemma Prop_ex_right {Σ : Signature} (Γ : Theory) (ϕ ψ : Pattern) :
  well_formed (ex, ϕ) ->
  well_formed ψ ->
  Γ ⊢i ψ $ (ex , ϕ) ---> ex , ψ $ ϕ
  using BasicReasoning.
Proof.
  intros wfϕ wfψ.
  unshelve (eexists).
  {
    apply ProofSystem.Prop_ex_right.
    { exact wfϕ. }
    { exact wfψ. }
  }
  { abstract(solve_pim_simple). }
Defined.


Tactic Notation "change" "constraint" "in" ident(H) :=
  let i := fresh "i" in
  remember_constraint as i;
  eapply useGenericReasoning with (i := i) in H;
  subst i;
  [|(try_solve_pile)].
 

Lemma prf_prop_ex_iff {Σ : Signature} Γ AC p x:
  evar_is_fresh_in x (subst_ctx AC p) ->
  well_formed (patt_exists p) = true ->
  Γ ⊢i ((subst_ctx AC (patt_exists p)) <---> (exists_quantify x (subst_ctx AC (p^{evar: 0 ↦ x}))))
  using (
  {| pi_generalized_evars := {[x]};
     pi_substituted_svars := ∅;
     pi_uses_kt := false ;
  |}).
Proof.
  intros Hx Hwf.

  induction AC; simpl.
  - simpl in Hx.
    unfold exists_quantify.
    erewrite evar_quantify_evar_open; auto. 2: now do 2 apply andb_true_iff in Hwf as [_ Hwf].
    useBasicReasoning.
    apply pf_iff_equiv_refl. exact Hwf.
  -
    assert (Hwfex: well_formed (ex , subst_ctx AC p)).
    { unfold well_formed. simpl.
      pose proof (Hwf' := Hwf).
      unfold well_formed in Hwf. simpl in Hwf.
      apply andb_prop in Hwf. destruct Hwf as [Hwfp Hwfc].
      apply (wp_sctx AC p) in Hwfp. rewrite Hwfp. simpl. clear Hwfp.
      unfold well_formed_closed. unfold well_formed_closed in Hwfc. simpl in Hwfc. simpl.
      split_and!.
      + apply wcmu_sctx. destruct_and!. assumption.
      + apply wcex_sctx. destruct_and!. assumption.
    }

    assert(Hxfr1: evar_is_fresh_in x (subst_ctx AC p)).
    { simpl in Hx.
      eapply evar_is_fresh_in_richer.
      2: { apply Hx. }
      solve_free_evars_inclusion 5.
    }

    simpl in Hx.
    pose proof (Hxfr1' := Hxfr1).
    rewrite -> evar_is_fresh_in_subst_ctx in Hxfr1'.
    destruct Hxfr1' as [Hxfrp HxAC].

    assert(Hwf': well_formed (exists_quantify x (subst_ctx AC (p^{evar: 0 ↦ x})))).
    {
      unfold exists_quantify.
      clear -HxAC Hwf.
      apply wf_ex_eq_sctx_eo.
      apply Hwf.
    }

    assert (Hwfeo: well_formed (p^{evar: 0 ↦ x})).
    { wf_auto2. }


    (* TODO automate this. The problem is that [well_formed_app] and others do not have [= true];
       that is why [auto] does not work. But [auto] is not suitable for this anyway.
       A better way would be to create some `simpl_well_formed` tuple, that might use the type class
       mechanism for extension...
     *)
    assert(Hwf'p0: well_formed (exists_quantify x (subst_ctx AC (p^{evar: 0 ↦ x}) $ p0))).
    { wf_auto2. }

    apply pf_iff_iff in IHAC; auto.

    destruct IHAC as [IH1 IH2].
    apply pf_iff_split; auto.
    + pose proof (H := IH1).
      change constraint in IH1.
      apply Framing_left with (ψ := p0) in IH1; auto.
      2: { try_solve_pile. }

      eapply syllogism_meta. 4: apply IH1.
      1-3: wf_auto2.

      remember (subst_ctx AC (p^{evar: 0 ↦ x})) as p'.
      unfold exists_quantify.
      simpl. rewrite [p0^{{evar: x ↦ 0}}]evar_quantify_fresh.
      { eapply evar_is_fresh_in_app_r. apply Hx. }
      useBasicReasoning.
      apply Prop_ex_left. wf_auto2. wf_auto2.
    + clear IH1.

      change constraint in IH2.
      apply Framing_left with (ψ := p0) in IH2; auto.
      2: { try_solve_pile. }
      eapply syllogism_meta. 5: eapply IH2.
      1-3: wf_auto2.

      apply Ex_gen; auto.
      { try_solve_pile. }
      1: {
        unfold exists_quantify.
        simpl.
        rewrite free_evars_evar_quantify.
        unfold evar_is_fresh_in in Hx. simpl in Hx. clear -Hx.
        set_solver.
      }

      (* TODO have some nice implicit parameters *)
      gapply (Framing_left _ _ _ _ _ Prf).
      apply pile_refl.
      Unshelve. 2: { try_solve_pile. }
      unfold evar_open.
      rewrite subst_ctx_bevar_subst.
      unfold exists_quantify. simpl.
      fold ((subst_ctx AC p)^{evar: 0 ↦ x}).
      rewrite -> evar_quantify_evar_open; auto.
      2: now do 2 apply andb_true_iff in Hwfex as [_ Hwfex].
      useBasicReasoning.
      apply Ex_quan; auto.
  -
    assert (Hwfex: well_formed (ex , subst_ctx AC p)).
    { clear Hx. wf_auto2. }

    assert(Hxfr1: evar_is_fresh_in x (subst_ctx AC p)).
    { simpl in Hx.
      eapply evar_is_fresh_in_richer.
      2: { apply Hx. }
      solve_free_evars_inclusion 5.
    }

    simpl in Hx.
    pose proof (Hxfr1' := Hxfr1).
    rewrite -> evar_is_fresh_in_subst_ctx in Hxfr1'.
    destruct Hxfr1' as [Hxfrp HxAC].

    assert(Hwf': well_formed (exists_quantify x (subst_ctx AC (p^{evar: 0 ↦ x})))).
    {
      unfold exists_quantify.
      clear -HxAC Hwf.
      apply wf_ex_eq_sctx_eo.
      apply Hwf.
    }

    assert (Hwfeo: well_formed (p^{evar: 0 ↦ x})).
    {
      wf_auto2.
    }

    (* TODO automate this. The problem is that [well_formed_app] and others do not have [= true];
       that is why [auto] does not work. But [auto] is not suitable for this anyway.
       A better way would be to create some `simpl_well_formed` tuple, that might use the type class
       mechanism for extension...
     *)
    assert(Hwf'p0: well_formed (exists_quantify x (p0 $ subst_ctx AC (p^{evar: 0 ↦ x})))).
    {
      wf_auto2.
    }

    apply pf_iff_iff in IHAC; auto.

    destruct IHAC as [IH1 IH2].
    apply pf_iff_split; auto.
    + pose proof (H := IH1).
      change constraint in IH1.
      apply Framing_right with (ψ := p0) in IH1; auto.
      2: try_solve_pile.
      eapply syllogism_meta. 4: apply IH1.
      1-3: wf_auto2.
      remember (subst_ctx AC (p^{evar: 0 ↦ x})) as p'.
      unfold exists_quantify.
      simpl. rewrite [p0^{{evar: x ↦ 0}}]evar_quantify_fresh.
      { eapply evar_is_fresh_in_app_l. apply Hx. }
      useBasicReasoning.
      apply Prop_ex_right. wf_auto2. wf_auto2.
    + clear IH1.

      change constraint in IH2.
      eapply (Framing_right _ _ _ _ _ Prf) in IH2.
      eapply syllogism_meta. 5: eapply IH2.
      1-3: wf_auto2.
      Unshelve.
      2: { try_solve_pile. }

      apply Ex_gen; auto.
      { try_solve_pile. }
      1: {
        unfold exists_quantify.
        simpl.
        rewrite free_evars_evar_quantify.
        unfold evar_is_fresh_in in Hx. simpl in Hx. clear -Hx.
        set_solver.
      }

      eapply (Framing_right _ _ _ _ _ Prf). Unshelve.
      2: { try_solve_pile. }
      {
      unfold evar_open.
      rewrite subst_ctx_bevar_subst.
      unfold exists_quantify. simpl.
      fold ((subst_ctx AC p)^{evar: 0 ↦ x}).
      erewrite evar_quantify_evar_open; auto.
      2: now do 2 apply andb_true_iff in Hwfex as [_ Hwfex].
      useBasicReasoning.
      apply Ex_quan; auto.
      }
Defined.


Add Search Blacklist "_elim".
Add Search Blacklist "_graph_rect".
Add Search Blacklist "_graph_mut".
Add Search Blacklist "FunctionalElimination_".


Section FOL_helpers.

  Context {Σ : Signature}.

  (**
  NOTE: DO NOT REPLACE! The element variable in this function is 
  needed to substitute in such pattern context, which contain
  arbitrary patterns, but the path to the element variable
  is concrete. For example, in `⌈ E ⌉ $ φ` the path to `E` does
  not contain any ∃-s, thus no new variables need to be generated
  for `mlRewrite`.
  *)
  Fixpoint maximal_exists_depth_to (depth : nat) (E : evar) (ψ : Pattern) : nat :=
    match ψ with
    | patt_bott => 0
    | patt_sym _ => 0
    | patt_bound_evar _ => 0
    | patt_bound_svar _ => 0
    | patt_free_svar _ => 0
    | patt_free_evar E' =>
      match (decide (E' = E)) with
      | left _ => depth
      | right _ => 0
      end
    | patt_imp ψ₁ ψ₂
      => Nat.max
        (maximal_exists_depth_to depth E ψ₁)
        (maximal_exists_depth_to depth E ψ₂)
    | patt_app ψ₁ ψ₂
      => Nat.max
        (maximal_exists_depth_to depth E ψ₁)
        (maximal_exists_depth_to depth E ψ₂)
    | patt_exists ψ' => maximal_exists_depth_to (S depth) E ψ'
    | patt_mu ψ' => maximal_exists_depth_to depth E ψ'
    end.
  
  Lemma maximal_exists_depth_to_0 E ψ depth:
    E ∉ free_evars ψ ->
    maximal_exists_depth_to depth E ψ = 0.
  Proof.
    intros Hnotin.
    move: E depth Hnotin.
    induction ψ; intros E depth Hnotin; simpl in *; try reflexivity.
    { case_match. set_solver. reflexivity. }
    { rewrite IHψ1. set_solver. rewrite IHψ2. set_solver. reflexivity. }
    { rewrite IHψ1. set_solver. rewrite IHψ2. set_solver. reflexivity. }
    { rewrite IHψ. exact Hnotin. reflexivity. }
    { rewrite IHψ. exact Hnotin. reflexivity. }
  Qed.

  Lemma maximal_exists_depth_to_S E ψ depth:
    E ∈ free_evars ψ ->
    maximal_exists_depth_to (S depth) E ψ
    = S (maximal_exists_depth_to depth E ψ).
  Proof.
    intros Hin.
    move: E depth Hin.
    induction ψ; intros E depth Hin; simpl in *; try set_solver.
    { case_match. reflexivity. set_solver. }
    {
      destruct (decide (E ∈ free_evars ψ1)),(decide (E ∈ free_evars ψ2)).
      {
        rewrite IHψ1. assumption. rewrite IHψ2. assumption. simpl. reflexivity.
      }
      {
        rewrite IHψ1. assumption.
        apply maximal_exists_depth_to_0 with (depth := S depth) in n
          as n'.
        apply maximal_exists_depth_to_0 with (depth := depth) in n.
        rewrite n. lia. 
      }
      {
        rewrite IHψ2. assumption.
        apply maximal_exists_depth_to_0 with (depth := S depth) in n
          as n'.
        apply maximal_exists_depth_to_0 with (depth := depth) in n.
        rewrite n. lia. 
      }
      {
        exfalso. set_solver.
      }
    }
    {
      destruct (decide (E ∈ free_evars ψ1)),(decide (E ∈ free_evars ψ2)).
      {
        rewrite IHψ1. assumption. rewrite IHψ2. assumption. simpl. reflexivity.
      }
      {
        rewrite IHψ1. assumption.
        apply maximal_exists_depth_to_0 with (depth := S depth) in n
          as n'.
        apply maximal_exists_depth_to_0 with (depth := depth) in n.
        rewrite n. lia. 
      }
      {
        rewrite IHψ2. assumption.
        apply maximal_exists_depth_to_0 with (depth := S depth) in n
          as n'.
        apply maximal_exists_depth_to_0 with (depth := depth) in n.
        rewrite n. lia. 
      }
      {
        exfalso. set_solver.
      }
    }
  Qed.

  Lemma evar_open_exists_depth φ depth x e : forall dbi,
    x <> e ->
    maximal_exists_depth_to depth x φ^{evar: dbi ↦ e} = maximal_exists_depth_to depth x φ.
  Proof.
    move: depth.
    induction φ; intros depth HeNq; cbn; trivial; intro.
    case_match; auto. cbn. case_match. congruence. lia.
    1-2: rewrite IHφ1; auto; rewrite IHφ2; auto.
    rewrite IHφ; auto.
    rewrite IHφ; auto.
  Qed.

  Lemma svar_open_exists_depth φ depth x X : forall dbi,
    maximal_exists_depth_to depth x φ^{svar: dbi ↦ X} = maximal_exists_depth_to depth x φ.
  Proof.
    move: depth.
    induction φ; intro depth; cbn; trivial; intro.
    case_match; auto.
    1-2: now rewrite IHφ1; rewrite IHφ2.
    now rewrite IHφ.
    now rewrite IHφ.
  Qed.

  Fixpoint maximal_mu_depth_to (depth : nat) (E : evar) (ψ : Pattern) : nat :=
    match ψ with
    | patt_bott => 0
    | patt_sym _ => 0
    | patt_bound_evar _ => 0
    | patt_bound_svar _ => 0
    | patt_free_svar _ => 0
    | patt_free_evar E' =>
      match (decide (E' = E)) with
      | left _ => depth
      | right _ => 0
      end
    | patt_imp ψ₁ ψ₂
      => Nat.max
        (maximal_mu_depth_to depth E ψ₁)
        (maximal_mu_depth_to depth E ψ₂)
    | patt_app ψ₁ ψ₂
      => Nat.max
        (maximal_mu_depth_to depth E ψ₁)
        (maximal_mu_depth_to depth E ψ₂)
    | patt_exists ψ' =>
      maximal_mu_depth_to depth E ψ'
    | patt_mu ψ' =>
      maximal_mu_depth_to (S depth) E ψ'
    end.

  Lemma maximal_mu_depth_to_svar_open depth E n X ψ:
  maximal_mu_depth_to depth E (ψ^{svar: n ↦ X})
    = maximal_mu_depth_to depth E ψ.
  Proof.
    unfold svar_open.
    move: depth n.
    induction ψ; intros depth n'; simpl; try reflexivity; auto.
    {
      case_match; simpl; try reflexivity.
    }
  Qed.

  Lemma evar_open_mu_depth depth E n x ψ:
    E <> x ->
    maximal_mu_depth_to depth E (ψ^{evar: n ↦ x})
    = maximal_mu_depth_to depth E ψ.
  Proof.
    intros Hne.
    unfold evar_open.
    move: depth n.
    induction ψ; intros depth n'; simpl; try reflexivity; auto.
    {
      case_match; simpl; try reflexivity.
      case_match; simpl; try reflexivity.
      subst. contradiction.
    }
  Qed.

  Lemma svar_open_mu_depth depth E n X ψ:
    maximal_mu_depth_to depth E (ψ^{svar: n ↦ X})
    = maximal_mu_depth_to depth E ψ.
  Proof.
    unfold svar_open.
    move: depth n.
    induction ψ; intros depth n'; simpl; try reflexivity; auto.
    {
      case_match; simpl; try reflexivity.
    }
  Qed.

  Lemma maximal_mu_depth_to_0 E ψ depth:
    E ∉ free_evars ψ ->
    maximal_mu_depth_to depth E ψ = 0.
  Proof.
    intros Hnotin.
    move: E depth Hnotin.
    induction ψ; intros E depth Hnotin; simpl in *; try reflexivity.
    { case_match. set_solver. reflexivity. }
    { rewrite IHψ1. set_solver. rewrite IHψ2. set_solver. reflexivity. }
    { rewrite IHψ1. set_solver. rewrite IHψ2. set_solver. reflexivity. }
    { rewrite IHψ. exact Hnotin. reflexivity. }
    { rewrite IHψ. exact Hnotin. reflexivity. }
  Qed.

  Lemma maximal_mu_depth_to_S E ψ depth:
    E ∈ free_evars ψ ->
    maximal_mu_depth_to (S depth) E ψ
    = S (maximal_mu_depth_to depth E ψ).
  Proof.
    intros Hin.
    move: E depth Hin.
    induction ψ; intros E depth Hin; simpl in *; try set_solver.
    { case_match. reflexivity. set_solver. }
    {
      destruct (decide (E ∈ free_evars ψ1)),(decide (E ∈ free_evars ψ2)).
      {
        rewrite IHψ1. assumption. rewrite IHψ2. assumption. simpl. reflexivity.
      }
      {
        rewrite IHψ1. assumption.
        apply maximal_mu_depth_to_0 with (depth := S depth) in n
          as n'.
        apply maximal_mu_depth_to_0 with (depth := depth) in n.
        rewrite n. lia. 
      }
      {
        rewrite IHψ2. assumption.
        apply maximal_mu_depth_to_0 with (depth := S depth) in n
          as n'.
        apply maximal_mu_depth_to_0 with (depth := depth) in n.
        rewrite n. lia. 
      }
      {
        exfalso. set_solver.
      }
    }
    {
      destruct (decide (E ∈ free_evars ψ1)),(decide (E ∈ free_evars ψ2)).
      {
        rewrite IHψ1. assumption. rewrite IHψ2. assumption. simpl. reflexivity.
      }
      {
        rewrite IHψ1. assumption.
        apply maximal_mu_depth_to_0 with (depth := S depth) in n
          as n'.
        apply maximal_mu_depth_to_0 with (depth := depth) in n.
        rewrite n. lia. 
      }
      {
        rewrite IHψ2. assumption.
        apply maximal_mu_depth_to_0 with (depth := S depth) in n
          as n'.
        apply maximal_mu_depth_to_0 with (depth := depth) in n.
        rewrite n. lia. 
      }
      {
        exfalso. set_solver.
      }
    }
  Qed.

  Lemma svar_fresh_seq_max (SvS : SVarSet) (n1 n2 : nat) :
    (@list_to_set svar SVarSet _ _ _ (svar_fresh_seq SvS n1)) ⊆ (list_to_set (svar_fresh_seq SvS (n1 `max` n2))).
  Proof.
    move: SvS n2.
    induction n1; intros SvS n2.
    {
      simpl. set_solver.
    }
    {
      simpl.
      destruct n2.
      {
        simpl. set_solver.
      }
      {
        simpl.
        cut (@list_to_set svar SVarSet _ _ _ (svar_fresh_seq ({[svar_fresh_s SvS]} ∪ SvS) n1)
        ⊆ list_to_set (svar_fresh_seq ({[svar_fresh_s SvS]} ∪ SvS) (n1 `max` n2))).
        {
          set_solver.
        }
        specialize (IHn1 ({[svar_fresh_s SvS]} ∪ SvS) n2).
        apply IHn1.
      }
    }
  Qed.

  (** Note: we cannot reuse NoDup, until the proof system is 
      formalised as `... -> Set`. *)
  Fixpoint no_dups {A : Set} {eqdec : EqDecision A} (l : list A) :=
    match l with
    | [] => True
    | x::xs => x ∉ xs /\ no_dups xs
    end.

  Class fresh_evars (l : list evar) (s : EVarSet) :=
  {
    evar_duplicates : no_dups l;
    all_evars_fresh : forall x, x ∈ l -> x ∉ s;
  }.

  Lemma fresh_evars_bigger {el s} s' :
    fresh_evars el s -> s' ⊆ s -> fresh_evars el s'.
  Proof. intros H H0. constructor; destruct H. auto. intros. set_solver. Qed.

  Lemma less_fresh_evars {x el s} :
    fresh_evars (x::el) s -> fresh_evars el s.
  Proof.
    intros H. constructor; destruct H.
    simpl in *. apply evar_duplicates0.
    intros. apply all_evars_fresh0. now constructor 2.
  Qed.

  Class fresh_svars (l : list svar) (s : SVarSet) :=
  {
    svar_duplicates : no_dups l;
    all_svars_fresh : forall X, X ∈ l -> X ∉ s;
  }.

  Lemma fresh_svars_bigger {sl s} s' :
    fresh_svars sl s -> s' ⊆ s -> fresh_svars sl s'.
  Proof. intros H H0. constructor; destruct H. auto. intros. set_solver. Qed.

  Lemma less_fresh_svars {X sl s} :
    fresh_evars (X::sl) s -> fresh_evars sl s.
  Proof.
    intros H. constructor; destruct H.
    simpl in *. apply evar_duplicates0.
    intros. apply all_evars_fresh0. now constructor 2.
  Qed.

  Lemma congruence_ex Γ E ψ x p q gpi kt evs svs
    (HxneqE : x ≠ E)
    (wfψ : well_formed (ex , ψ))
    (wfp : well_formed p)
    (wfq : well_formed q)
    (Heqx : x ∉ free_evars ψ ∪ free_evars p ∪ free_evars q)
    (Heqx2 : x ∈ evs)
    (pile: ProofInfoLe (ExGen := evs, SVSubst := svs, KT := kt) gpi)
    (IH: Γ ⊢i ψ^{evar: 0 ↦ x}^[[evar: E ↦ p]] <---> ψ^{evar: 0 ↦ x}^[[evar: E ↦ q]]
       using  gpi) :
    (Γ ⊢i (ex , ψ^[[evar: E ↦ p]]) <---> (ex , ψ^[[evar: E ↦ q]]) using  gpi).
  Proof.
    rewrite -evar_open_free_evar_subst_swap in IH; auto.
    rewrite -evar_open_free_evar_subst_swap in IH; auto.
    unshelve (epose proof (IH1 := pf_iff_proj1 Γ _ _ _ _ _ IH)).
    { abstract (wf_auto2). }
    { abstract (wf_auto2). }
    unshelve (epose proof (IH2 := pf_iff_proj2 Γ _ _ _ _ _ IH)).
    { abstract (wf_auto2). }
    { abstract (wf_auto2). }

    (* TODO: remove the well-formedness constraints on this lemma*)
    apply pf_iff_split.
    { abstract (wf_auto2). }
    { abstract (wf_auto2). }
    {
      eapply strip_exists_quantify_l.
      3: {
        apply Ex_gen.
        3: {
          eapply syllogism_meta.
          5: {
            useBasicReasoning.
            apply Ex_quan.
            abstract (wf_auto2).
          }
          4: {
              apply IH1.
            }
          { abstract (wf_auto2). }
          { abstract (simpl; wf_auto2; apply wfc_ex_aux_bevar_subst; wf_auto2). }
          { abstract (wf_auto2). }
        }
        {
          abstract (
            eapply pile_trans;
            [|apply pile];
            split; simpl; [|split; auto; set_solver];
            set_solver
          ).
        }
        {
          abstract (
            pose proof (Htmp2 := free_evars_free_evar_subst ψ q E);
            set_solver
          ).
        }
      }
      {
        abstract (
          pose proof (Htmp2 := free_evars_free_evar_subst ψ p E);
          set_solver
        ).
      }
      {
        wf_auto2.
      }
    }
    (* this block is a symmetric version of the previous block*)
    {
      eapply strip_exists_quantify_l.
      3: {
        apply Ex_gen.
        3: {
          eapply syllogism_meta.
          5: {
            useBasicReasoning.
            apply Ex_quan.
            abstract (wf_auto2).
          }
          4: {
              apply IH2.
            }
          { abstract (wf_auto2). }
          { abstract (simpl; wf_auto2; apply wfc_ex_aux_bevar_subst; wf_auto2). }
          { abstract (wf_auto2). }
        }
        {
          abstract (
            eapply pile_trans;
            [|apply pile];
            split; simpl; [|split; auto; set_solver];
            set_solver
          ).
        }
        {
          abstract (
            pose proof (Htmp2 := free_evars_free_evar_subst ψ p E);
            set_solver
          ).
        }
      }
      {
        abstract (
          pose proof (Htmp2 := free_evars_free_evar_subst ψ q E);
          set_solver
        ).
      }
      {
        abstract (wf_auto2).
      }
    }
  Defined.

End FOL_helpers.

  Ltac pi_exact H := 
    lazymatch type of H with
    | ?H' =>
      lazymatch goal with
      | [|- ?g] =>
        (cut (H' = g);
        [(let H0 := fresh "H0" in intros H0; rewrite -H0; exact H)|
         (repeat f_equal; try reflexivity; try apply proof_irrel)])
      end
    end.

  Ltac pi_assumption :=
    match goal with
    | [H : _ |- _] => pi_exact H
    end.

  Ltac pi_set_solver := set_solver by (try pi_assumption).

Section FOL_helpers.

  Context {Σ : Signature}.

  Lemma congruence_app Γ ψ1 ψ2 p q E i
    (wfψ1: well_formed ψ1)
    (wfψ2: well_formed ψ2)
    (wfp: well_formed p)
    (wfq: well_formed q)
    (pf₁: Γ ⊢i ψ1^[[evar: E ↦ p]] <---> ψ1^[[evar: E ↦ q]] using i)
    (pf₂: Γ ⊢i ψ2^[[evar: E ↦ p]] <---> ψ2^[[evar: E ↦ q]] using i)
    :
    (Γ ⊢i (ψ1^[[evar: E ↦ p]]) $ (ψ2^[[evar: E ↦ p]]) <---> (ψ1^[[evar: E ↦ q]]) $ (ψ2^[[evar: E ↦ q]]) using i).
  Proof.
    remember (well_formed_free_evar_subst_0 E _ _ wfp wfψ1) as Hwf1.
    remember (well_formed_free_evar_subst_0 E _ _ wfq wfψ1) as Hwf2.
    remember (well_formed_free_evar_subst_0 E _ _ wfp wfψ2) as Hwf3.
    remember (well_formed_free_evar_subst_0 E _ _ wfq wfψ2) as Hwf4.

    eapply pf_iff_equiv_trans.
    5: { 
      apply conj_intro_meta.
      4: {
        eapply Framing_right with (ψ := ψ1^[[evar: E ↦ q]]); auto.
        1: { try_solve_pile. }
        {
          eapply pf_conj_elim_r_meta in pf₂.
          apply pf₂.
          { abstract (wf_auto2). }
          { abstract (wf_auto2). }
        }
      }
      3: {
        eapply Framing_right with (ψ := ψ1^[[evar: E ↦ q]]); auto.
        1: { try_solve_pile. }
        {
          eapply pf_conj_elim_l_meta in pf₂.
          apply pf₂.
          { abstract (wf_auto2). }
          { abstract (wf_auto2). }
        }
      }
      {
        abstract (wf_auto2).
      }
      {
        abstract (wf_auto2).
      }
    }
    4: {
      apply conj_intro_meta.
      4: {
        apply Framing_left with (ψ := ψ2^[[evar: E ↦ p]]); auto.
        { try_solve_pile. }
        {
          eapply pf_conj_elim_r_meta in pf₁.
          apply pf₁.
          { abstract (wf_auto2). }
          { abstract (wf_auto2). }
        }
      }
      3: {
        apply Framing_left with (ψ := ψ2^[[evar: E ↦ p]]); auto.
        { try_solve_pile. }
        {
          eapply pf_conj_elim_l_meta in pf₁.
          apply pf₁.
          { abstract (wf_auto2). }
          { abstract (wf_auto2). }
        }
      }
      {
        abstract (wf_auto2).
      }
      {
        abstract (wf_auto2).
      }
    }
    { abstract (wf_auto2). }
    { abstract (wf_auto2). }
    { abstract (wf_auto2). }
  Defined.

  Lemma count_evar_occurrences_evar_replace φ x y :
    x ∉ free_evars φ ->
    count_evar_occurrences x φ^[[evar:y↦patt_free_evar x]] =
    count_evar_occurrences y φ.
  Proof.
    induction φ; intro H; simpl in *; auto.
    * do 2 destruct decide; simpl; case_match; auto; try contradiction; set_solver.
    * rewrite IHφ1. 2: rewrite IHφ2. all: set_solver.
    * rewrite IHφ1. 2: rewrite IHφ2. all: set_solver.
  Qed.


  Definition mu_in_evar_path E ψ sdepth := negb (Nat.eqb 0 (maximal_mu_depth_to sdepth E ψ)).

  Lemma eq_prf_equiv_congruence
    (sz : nat)
    Γ p q evs svs
    (wfp : well_formed p)
    (wfq : well_formed q)
    E ψ edepth sdepth
    (Hsz: size' ψ <= sz)
    (wfψ : well_formed ψ)
    (gpi : ProofInfo)
    (** We need to do a number of Ex_Gen (and Substitution) steps
        in the proof, thus we need at least as many fresh variables
        as ∃-s (and μ-s) are in ψ. These should also be included in gpi.

        Actually, we do not need that many variables always, then
        depth of ∃-s should only be considered in the paths where
        E is present. For simplicity (and the fact that we have 
        infinitely many fresh variables), we chose not to use that
        approach
    *)
    el
    (Hel1 : fresh_evars el (free_evars ψ ∪ free_evars p ∪ free_evars q ∪ {[E]}))
    (Hel2 : length el ≥ maximal_exists_depth_to edepth E ψ)
    (Hel3 : forall x, x ∈ el -> x ∈ evs)
    sl
    (Hsl1 : fresh_svars sl (free_svars ψ ∪ free_svars p ∪ free_svars q))
    (Hsl2 : length sl ≥ maximal_mu_depth_to sdepth E ψ)
    (Hsl3 : forall X, X ∈ sl -> X ∈ svs)
    (pile: ProofInfoLe
           (ExGen := evs,
            SVSubst := svs,
            KT := mu_in_evar_path E ψ sdepth) gpi)
    (pf : Γ ⊢i (p <---> q) using ( gpi)) :
        Γ ⊢i (((ψ^[[evar: E ↦ p]]) <---> (ψ^[[evar: E ↦ q]]))) using ( gpi).
  Proof.
(* TODO: if there were a size function for coEVarSet/coSVarSet, then
         Hel3/Hsl3 would be not necessary *)
    move: edepth sdepth ψ wfψ Hsz evs svs gpi pile pf el Hel1 Hel2 Hel3 sl Hsl1 Hsl2 Hsl3.
    induction sz; intros edepth sdepth ψ wfψ Hsz evs svs gpi pile pf el Hel1 Hel2 Hel3 sl Hsl1 Hsl2 Hsl3.
    abstract (destruct ψ; simpl in Hsz; lia).

    lazymatch type of pile with
    | ProofInfoLe ?st _ => set (i' := st) in *
    end.


  destruct (decide (E ∈ free_evars ψ)) as [HEinψ|HEnotinψ].
    2: { rewrite free_evar_subst_no_occurrence; auto.
      rewrite free_evar_subst_no_occurrence; auto.
      gapply pf_iff_equiv_refl. try_solve_pile.
      { abstract (wf_auto2). } }

    destruct ψ; simpl in Hsz; simpl.
    {
      destruct (decide (E = x)).
      {
        exact pf.
      }
      {
        useBasicReasoning.
        apply pf_iff_equiv_refl.
        abstract (wf_auto2).
      }
    }
    {
      useBasicReasoning.
      apply pf_iff_equiv_refl.
      abstract (wf_auto2).
    }
    {
      useBasicReasoning.
      apply pf_iff_equiv_refl.
      abstract (wf_auto2).
    }
    {
      useBasicReasoning.
      apply pf_iff_equiv_refl.
      abstract (wf_auto2).
    }
    {
      useBasicReasoning.
      apply pf_iff_equiv_refl.
      abstract (wf_auto2).
    }
    {
      assert (wfψ1 : well_formed ψ1 = true).
      { clear -wfψ. abstract (wf_auto2). }
      assert (size' ψ1 <= sz) by abstract(lia).
      assert (wfψ2 : well_formed ψ2 = true).
      { clear -wfψ. abstract (wf_auto2). }
      assert (size' ψ2 <= sz) by abstract(lia).
      
      simpl in *.
      pose proof (Hef1 := fresh_evars_bigger (free_evars ψ1 ∪ free_evars p ∪ free_evars q ∪ {[E]}) Hel1 ltac:(set_solver)).
      
      pose proof (Hsf1 := fresh_svars_bigger (free_svars ψ1 ∪ free_svars p ∪ free_svars q) Hsl1 ltac:(set_solver)).
      
      unshelve (epose proof (pf₁ := IHsz edepth sdepth ψ1 ltac:(assumption) ltac:(assumption) evs svs gpi _ pf el Hef1 _ Hel3 sl Hsf1 _ Hsl3)). 2-3: lia.
      { clear - i' pile. try_solve_pile.
        cbn in *. unfold mu_in_evar_path in *. cbn in *.
        do 2 case_match; cbn in *; auto. lia. }

      epose proof (Hef2 := fresh_evars_bigger (free_evars ψ2 ∪ free_evars p ∪ free_evars q ∪ {[E]}) Hel1 ltac:(set_solver)).

      pose proof (Hsf2 := fresh_svars_bigger (free_svars ψ2 ∪ free_svars p ∪ free_svars q) Hsl1 ltac:(set_solver)).

      unshelve (epose proof (pf₂ := IHsz edepth sdepth ψ2 ltac:(assumption) ltac:(assumption) evs svs gpi _ pf el Hef2 ltac:(lia) Hel3 sl Hsf2 ltac:(lia) Hsl3)).
      { clear - i' pile. try_solve_pile.
        cbn in *. unfold mu_in_evar_path in *. cbn in *.
        do 2 case_match; cbn in *; auto. lia. }

      unshelve (eapply congruence_app); try assumption.
    }
    {
      useBasicReasoning.
      apply pf_iff_equiv_refl.
      abstract (wf_auto2).
    }
    {
      assert (wfψ1 : well_formed ψ1 = true).
      { clear -wfψ. abstract (wf_auto2). }
      assert (size' ψ1 <= sz) by abstract(lia).
      assert (wfψ2 : well_formed ψ2 = true).
      { clear -wfψ. abstract (wf_auto2). }
      assert (size' ψ2 <= sz) by abstract(lia).

      pose proof (Hef1 := fresh_evars_bigger (free_evars ψ1 ∪ free_evars p ∪ free_evars q ∪ {[E]}) Hel1 ltac:(set_solver)).
      
      pose proof (Hsf1 := fresh_svars_bigger (free_svars ψ1 ∪ free_svars p ∪ free_svars q) Hsl1 ltac:(set_solver)).
      
      simpl in *.
      unshelve (epose proof (pf₁ := IHsz edepth sdepth ψ1 ltac:(assumption) ltac:(assumption) evs svs gpi _ pf el Hef1 ltac:(lia) Hel3 sl Hsf1 ltac:(lia) Hsl3)).
      { clear - i' pile. try_solve_pile.
        cbn in *. unfold mu_in_evar_path in *. cbn in *.
        do 2 case_match; cbn in *; auto. lia. }

      epose proof (Hef2 := fresh_evars_bigger (free_evars ψ2 ∪ free_evars p ∪ free_evars q ∪ {[E]}) Hel1 ltac:(set_solver)).

      pose proof (Hsf2 := fresh_svars_bigger (free_svars ψ2 ∪ free_svars p ∪ free_svars q) Hsl1 ltac:(set_solver)).

      unshelve(epose proof (pf₂ := IHsz edepth sdepth ψ2 ltac:(assumption) ltac:(assumption) evs svs gpi _ pf el Hef2 ltac:(lia) Hel3 sl Hsf2 ltac:(lia) Hsl3)).
      { clear - i' pile. try_solve_pile.
        cbn in *. unfold mu_in_evar_path in *. cbn in *.
        do 2 case_match; cbn in *; auto. lia. }

      apply prf_equiv_of_impl_of_equiv.
      { abstract (wf_auto2). }
      { abstract (wf_auto2). }
      { abstract (wf_auto2). }
      { abstract (wf_auto2). }
      { apply pf₁. }
      { apply pf₂. }
    }
    {
      simpl in *.
      
      destruct el as [ | x els].
      { simpl in Hel2.
        rewrite maximal_exists_depth_to_S in Hel2. assumption. lia.
      }
      
      assert (well_formed (ψ^{evar: 0 ↦ x})) by (unfold i' in pile; clear i'; abstract(wf_auto2)).
      assert (size' (ψ^{evar: 0 ↦ x}) <= sz) by abstract(rewrite evar_open_size'; lia).

      assert (fresh_evars els (free_evars ψ^{evar:0↦x} ∪ free_evars p ∪ free_evars q ∪ {[E]})) as HVars. { constructor.
        * destruct Hel1. apply evar_duplicates0.
        * destruct Hel1. intros.
          pose proof (free_evars_evar_open ψ x 0).
          specialize (all_evars_fresh0 x0 ltac:(now right)).
          simpl in *. destruct evar_duplicates0. set_solver.
      }
      simpl in Hel2.
      rewrite maximal_exists_depth_to_S in Hel2. assumption.

      assert (E ≠ x) as HXe. {
        destruct Hel1 as [_ ?]. clear -all_evars_fresh0. set_solver.
      }
      unshelve (epose proof (IH := IHsz edepth sdepth (ψ^{evar: 0 ↦ x}) ltac:(assumption) ltac:(assumption) (evs ∪ {[x]}) svs gpi _ pf els HVars _ ltac:(set_solver) sl)).
      {
        cbn in *. unfold mu_in_evar_path in *. cbn in *.
        rewrite evar_open_mu_depth.
        2: try_solve_pile.
        auto.
      }
      { rewrite evar_open_exists_depth. auto. lia. }
      feed specialize IH.
      { now rewrite free_svars_evar_open. }
      { rewrite evar_open_mu_depth. auto. lia. }
      { assumption. }

      eapply congruence_ex with (x := x); try assumption.
      {
        destruct Hel1 as [_ ?].
        specialize (all_evars_fresh0 x ltac:(now left)).
        set_solver.
      }
      {
        destruct Hel1 as [_ ?].
        specialize (all_evars_fresh0 x ltac:(now left)).
        set_solver.
      }
      { apply Hel3. now left. }
      { eapply pile_trans;[|apply pile].
        unfold i'. now apply pile_refl.
      }
    }
    {
      destruct sl as [ | X sls].
      {
        simpl in Hsl2.
        rewrite maximal_mu_depth_to_S in Hsl2. assumption. lia.
      }

      assert (well_formed (ψ^{svar: 0 ↦ X}) = true) by (abstract(clear -wfψ;wf_auto2)).
      assert (size' (ψ^{svar: 0 ↦ X}) <= sz) by abstract(rewrite svar_open_size'; lia).

      simpl in *.

      subst i'.
      cbn in *. unfold mu_in_evar_path in *. cbn in *.
      rewrite maximal_mu_depth_to_S in pile. assumption.

      unshelve (epose proof (IH := IHsz edepth sdepth (ψ^{svar: 0 ↦ X}) ltac:(assumption) ltac:(assumption) evs svs gpi _ pf el)).
      { 
        try_solve_pile.
      }
      feed specialize IH.
      {
        now rewrite free_evars_svar_open.
      }
      {
        rewrite svar_open_exists_depth. lia.
      }
      {
        assumption.
      }
      specialize (IH sls).
      feed specialize IH.
      {
        constructor.
        * destruct Hsl1. apply svar_duplicates0.
        * destruct Hsl1. intros.
          pose proof (free_svars_svar_open ψ X 0).
          specialize (all_svars_fresh0 X0 ltac:(now right)).
          simpl in *. destruct svar_duplicates0.
          clear -H3 H2 H1 all_svars_fresh0. set_solver.
      }
      {
        rewrite svar_open_mu_depth.
        rewrite maximal_mu_depth_to_S in Hsl2. assumption. lia.
      }
      {
        intros. apply Hsl3. now right. 
      }

      unfold svar_open in IH.
      rewrite free_evar_subst_bsvar_subst in IH.
      1: wf_auto2.
      1: { unfold evar_is_fresh_in. set_solver. }
      rewrite free_evar_subst_bsvar_subst in IH.
      1: wf_auto2.
      1: { unfold evar_is_fresh_in. set_solver. }

      unshelve (epose proof (IH1 := pf_iff_proj1 _ _ _ _ _ _ IH)).
      { clear -wfψ wfp. abstract (wf_auto2). }
      { clear -wfψ wfq. abstract (wf_auto2). }
      unshelve (epose proof (IH2 := pf_iff_proj2 _ _ _ _ _ _ IH)).
      { clear -wfψ wfp. abstract (wf_auto2). }
      { clear -wfψ wfq. abstract (wf_auto2). }

      rewrite <- (svar_quantify_svar_open X 0 (ψ^[[evar:E↦p]])).
      rewrite <- (svar_quantify_svar_open X 0 (ψ^[[evar:E↦q]])).
      2: {
        pose proof (free_svars_free_evar_subst ψ E q).
        destruct Hsl1 as [_ ?]. clear -all_svars_fresh0 H1.
        set_solver.
      }
      3: {
        pose proof (free_svars_free_evar_subst ψ E p).
        destruct Hsl1 as [_ ?]. clear -all_svars_fresh0 H1.
        set_solver.
      }
      2-3: wf_auto2.
      
      apply pf_iff_split.
      4: {
        apply mu_monotone.
        4: {
          unfold svar_open.
          apply IH2.
        }
        2-3:
          abstract (
            destruct Hsl1 as [_ Hsl1];
            specialize (Hsl1 X ltac:(now left));
            clear -wfψ wfp wfq Hsl1;
            wf_auto2; intros; wf_auto2;
            cbn in *;
            pose proof (Htmp1 := free_svars_free_evar_subst ψ E p);
            pose proof (Htmp2 := free_svars_free_evar_subst ψ E q);
            unfold svar_is_fresh_in;
            set_solver
          ).
        {
          abstract (try_solve_pile).
        }
      }
      3: {
        apply mu_monotone.
        4: {
          unfold svar_open.
          apply IH1.
        }
        2-3:
          abstract (
            destruct Hsl1 as [_ Hsl1];
            specialize (Hsl1 X ltac:(now left));
            clear -wfψ wfp wfq Hsl1;
            wf_auto2; intros; wf_auto2;
            cbn in *;
            pose proof (Htmp1 := free_svars_free_evar_subst ψ E p);
            pose proof (Htmp2 := free_svars_free_evar_subst ψ E q);
            unfold svar_is_fresh_in;
            set_solver
          ).
          {
            abstract (try_solve_pile).
          }
      }
      {
        cut (X ∉ free_svars ψ^[[evar:E↦p]]).
        {
          clear -wfψ wfp.
          intros.
          (* TODO: this rewrite somewhy does not happen in wf_auto2 *)
          abstract (rewrite svar_quantify_svar_open;wf_auto2).
        }
        abstract (
          pose proof (Htmp := free_svars_free_evar_subst ψ E p);
          destruct Hsl1 as [_ Hsl1];
          specialize (Hsl1 X ltac:(now left));
          clear -H Htmp ψ Hsl1;
          set_solver
        ).
      }
      {
        cut (X ∉ free_svars ψ^[[evar:E↦q]]).
        {
          clear -wfψ wfq.
          intros.
          abstract (rewrite svar_quantify_svar_open; wf_auto2).
        }
        abstract (
          pose proof (Htmp := free_svars_free_evar_subst ψ E q);
          destruct Hsl1 as [_ Hsl1];
          specialize (Hsl1 X ltac:(now left));
          clear -H Htmp ψ Hsl1;
          set_solver
        ).
      }
    }
  Defined.

  (* Correctness of evar_fresh_seq *)
  Lemma evar_fresh_seq_correct n s:
    fresh_evars (evar_fresh_seq s n) s.
  Proof.
    move: s.
    induction n; intro s; cbn.
    * constructor; simpl. trivial. intros. set_solver.
    * destruct (IHn ({[evar_fresh_s s]} ∪ s)) as [Dups Fresh]. constructor.
      - simpl. split; auto.
        pose proof (evar_fresh_seq_disj ({[evar_fresh_s s]} ∪ s) n).
        set_solver.
      - intros. apply elem_of_cons in H as [H | H].
        + subst. unfold evar_fresh_s. apply set_evar_fresh_is_fresh'.
        + apply Fresh in H. set_solver.
  Qed.

  (* Correctness of svar_fresh_seq *)
  Lemma svar_fresh_seq_correct n s:
    fresh_svars (svar_fresh_seq s n) s.
  Proof.
    move: s.
    induction n; intro s; cbn.
    * constructor; simpl. trivial. intros. set_solver.
    * destruct (IHn ({[svar_fresh_s s]} ∪ s)) as [Dups Fresh]. constructor.
      - simpl. split; auto.
        pose proof (svar_fresh_seq_disj ({[svar_fresh_s s]} ∪ s) n).
        set_solver.
      - intros. apply elem_of_cons in H as [H | H].
        + subst. unfold svar_fresh_s. apply set_svar_fresh_is_fresh'.
        + apply Fresh in H. set_solver.
  Qed.

  Lemma evar_fresh_seq_length l n:
    length (evar_fresh_seq l n) = n.
  Proof.
    move: l.
    induction n; intro l; simpl; auto.
  Qed.

  Lemma svar_fresh_seq_length l n:
    length (svar_fresh_seq l n) = n.
  Proof.
    move: l.
    induction n; intro l; simpl; auto.
  Qed.

  Lemma prf_equiv_congruence Γ p q C
    (gpi : ProofInfo)
    (wfp : well_formed p = true)
    (wfq : well_formed q = true)
    (wfC: PC_wf C)
    (pile : ProofInfoLe
       (ExGen := list_to_set (evar_fresh_seq (free_evars (pcPattern C) ∪ free_evars p ∪ free_evars q ∪ {[pcEvar C]}) (maximal_exists_depth_to 0 (pcEvar C) (pcPattern C))),
       SVSubst := list_to_set (svar_fresh_seq (free_svars (pcPattern C) ∪ free_svars p ∪ free_svars q) (maximal_mu_depth_to 0 (pcEvar C) (pcPattern C))),
       KT := mu_in_evar_path (pcEvar C) (pcPattern C) 0
       )
      gpi
    ) :
      Γ ⊢i (p <---> q) using ( gpi) ->
      Γ ⊢i (((emplace C p) <---> (emplace C q))) using ( gpi).
  Proof.
    intros Hiff.
    assert (well_formed (p <---> q)).
    { abstract (
        pose proof (proved_impl_wf _ _ (proj1_sig Hiff));
        assumption
      ).
    }
    assert (well_formed p) by (abstract (wf_auto2)).
    assert (well_formed q) by (abstract (wf_auto2)).
    destruct C as [E ψ]. simpl in *.
    unfold emplace. simpl.
    eapply eq_prf_equiv_congruence with 
      (el := evar_fresh_seq (free_evars ψ ∪ free_evars p ∪ free_evars q ∪ {[E]})
      (maximal_exists_depth_to 0 E ψ))
      (sl := svar_fresh_seq (free_svars ψ ∪ free_svars p ∪ free_svars q)
      (maximal_mu_depth_to 0 E ψ))
      (evs := list_to_set (evar_fresh_seq (free_evars ψ ∪ free_evars p ∪ free_evars q ∪ {[E]})
      (maximal_exists_depth_to 0 E ψ)))
      (svs := list_to_set (svar_fresh_seq (free_svars ψ ∪ free_svars p ∪ free_svars q)
      (maximal_mu_depth_to 0 E ψ))); try assumption.
    { apply reflexivity. }
    { abstract (apply evar_fresh_seq_correct). }
    { instantiate (1 := 0); abstract (pose proof (evar_fresh_seq_length (free_evars ψ ∪ free_evars p ∪ free_evars q ∪ {[E]}) (maximal_exists_depth_to 0 E ψ)); lia). }
    { intros. set_solver. }
    { abstract (apply svar_fresh_seq_correct). }
    { instantiate (1 := 0); abstract (pose proof (svar_fresh_seq_length (free_svars ψ ∪ free_svars p ∪ free_svars q) (maximal_mu_depth_to 0 E ψ)); lia). }
    { intros. set_solver. }
    { try_solve_pile. }
  Defined.

End FOL_helpers.

Lemma collapse_free_evar_subst {Σ : Signature} φ ψ x y:
  y ∉ free_evars φ ->
  φ^[[evar: x ↦ patt_free_evar y]]^[[evar: y ↦ ψ]] =
  φ^[[evar: x ↦ ψ]].
Proof.
  induction φ; simpl; auto; intro Hin.
  * repeat (case_match; simpl); auto. congruence. set_solver.
  * rewrite IHφ1. set_solver. rewrite IHφ2. set_solver. reflexivity.
  * rewrite IHφ1. set_solver. rewrite IHφ2. set_solver. reflexivity.
  * rewrite IHφ. set_solver. reflexivity.
  * rewrite IHφ. set_solver. reflexivity.
Qed.

Definition free_evars_of_list {Σ : Signature} l := foldr (λ x0 acc, free_evars x0 ∪ acc) ∅ l.

Lemma fresh_foldr_is_context {Σ : Signature} l C p:
  pcEvar C ∉ free_evars_of_list l ->
  foldr patt_imp (emplace C p) l =
  emplace
    {|pcEvar := pcEvar C;
      pcPattern := foldr patt_imp (pcPattern C) l |} p.
Proof.
  revert C p. induction l; intros C p Hin; cbn.
  {
    auto.
  }
  {
    simpl in Hin.
    rewrite free_evar_subst_no_occurrence.
    * simpl in Hin. set_solver.
    * f_equal. apply IHl. set_solver.
  }
Qed.

(** NOTE: the following lemmas are very specific for prf_equiv_congruence_iter  *)

Lemma maximal_exists_depth_foldr_notin {Σ : Signature} l ψ x edepth:
  x ∉ free_evars_of_list l ->
  maximal_exists_depth_to edepth x (foldr patt_imp ψ l) =
  maximal_exists_depth_to edepth x ψ.
Proof.
  induction l; simpl; intros Hin.
  * reflexivity.
  * assert (x ∉ free_evars a) as Ha by set_solver.
    assert (x ∉ free_evars_of_list l) as HIND by set_solver.
    apply IHl in HIND. rewrite HIND.
    rewrite maximal_exists_depth_to_0; auto.
Qed.

Lemma maximal_mu_depth_foldr_notin {Σ : Signature} l ψ x edepth:
  x ∉ free_evars_of_list l ->
  maximal_mu_depth_to edepth x (foldr patt_imp ψ l) =
  maximal_mu_depth_to edepth x ψ.
Proof.
  induction l; simpl; intros Hin.
  * reflexivity.
  * assert (x ∉ free_evars a) as Ha by set_solver.
    assert (x ∉ foldr (λ (x : Pattern) (acc : EVarSet), free_evars x ∪ acc) ∅ l) as HIND by set_solver.
    apply IHl in HIND. rewrite HIND.
    rewrite maximal_mu_depth_to_0; auto.
Qed.

(* NOTE: This version of the iterated congruence lemma is proved by induction.
         There is a way, to prove this lemma without induction (see
         `TEST_proofmode_proof_size.v`), but the generated proof term becomes
         much more larger (2-3 times larger than the induction-based).
         This is because the proof of the congruence lemma is more complex
         for bigger contexts. *)
Lemma prf_equiv_congruence_iter {Σ : Signature} (Γ : Theory) (p q : Pattern) (C : PatternCtx) l
  (wfp : well_formed p)
  (wfq : well_formed q)
  (wfC : PC_wf C)
  (gpi : ProofInfo)
  (pile : ProofInfoLe
    (ExGen := list_to_set (evar_fresh_seq (free_evars (pcPattern C) ∪ free_evars p ∪ free_evars q ∪ {[pcEvar C]}) (maximal_exists_depth_to 0 (pcEvar C) (pcPattern C))),
      SVSubst := list_to_set (svar_fresh_seq (free_svars (pcPattern C) ∪ free_svars p ∪ free_svars q) (maximal_mu_depth_to 0 (pcEvar C) (pcPattern C))),
      KT := mu_in_evar_path (pcEvar C) (pcPattern C) 0
    )
    ( gpi)
  ):
  Pattern.wf l ->
  Γ ⊢i p <---> q using ( gpi) ->
  Γ ⊢i (foldr patt_imp (emplace C p) l) <---> (foldr patt_imp (emplace C q) l) using ( gpi).
Proof.
  intros wfl Himp.
  induction l; simpl in *.
  - unshelve(eapply prf_equiv_congruence); assumption.
  - pose proof (wfal := wfl).
    unfold Pattern.wf in wfl. simpl in wfl. apply andb_prop in wfl as [wfa wfl].
    specialize (IHl wfl).
    pose proof (Hwf1 := proved_impl_wf _ _ (proj1_sig IHl)).
    pose proof (Hwf2 := proved_impl_wf _ _ (proj1_sig Himp)).
    assert (well_formed (emplace C p)).
    {
      unfold emplace.
      wf_auto2.
    }
    assert (well_formed (emplace C q)).
    {
      unfold emplace.
      wf_auto2.
    }
    toMLGoal.
    { unfold emplace. wf_auto2. }
    unfold patt_iff.
    mlSplitAnd.
    + mlIntro. mlIntro.
      mlAssert ((foldr patt_imp (emplace C p) l)).
      { wf_auto2. }
      { mlApply "0". mlExactn 1. }
      apply pf_iff_proj1 in IHl.
      2,3: wf_auto2.
      mlApplyMetaRaw IHl.
      mlExactn 2.
    + mlIntro. mlIntro.
      mlAssert ((foldr patt_imp (emplace C q) l)).
      { wf_auto2. }
      { mlApply "0". mlExactn 1. }
      apply pf_iff_proj2 in IHl.
      2,3: wf_auto2.
      mlApplyMetaRaw IHl.
      mlExactn 2.
Defined.

Lemma extract_wfp {Σ : Signature} (Γ : Theory) (p q : Pattern) (i : ProofInfo):
  Γ ⊢i p <---> q using i ->
  well_formed p.
Proof.
  intros H.
  pose proof (H' := proj1_sig H).
  apply proved_impl_wf in H'.
  wf_auto2.
Qed.

Lemma extract_wfq {Σ : Signature} (Γ : Theory) (p q : Pattern) (i : ProofInfo):
  Γ ⊢i p <---> q using i ->
  well_formed q.
Proof.
  intros H.
  pose proof (H' := proj1_sig H).
  apply proved_impl_wf in H'.
  wf_auto2.
Qed.

Lemma MLGoal_rewriteIff
  {Σ : Signature} (Γ : Theory) (p q : Pattern) (C : PatternCtx) l (gpi : ProofInfo)
  (wfC : PC_wf C)
  (pf : Γ ⊢i p <---> q using ( gpi)) :
  mkMLGoal Σ Γ l (emplace C q) ( gpi) ->
  (ProofInfoLe
    (ExGen := list_to_set (evar_fresh_seq (free_evars (pcPattern C) ∪ free_evars p ∪ free_evars q ∪ {[pcEvar C]}) (maximal_exists_depth_to 0 (pcEvar C) (pcPattern C))),
     SVSubst := list_to_set (svar_fresh_seq (free_svars (pcPattern C) ∪
                free_svars p ∪ free_svars q) (maximal_mu_depth_to 0 (pcEvar C) (pcPattern C))),
     KT := mu_in_evar_path (pcEvar C) (pcPattern C) 0
  )
      gpi) ->
  mkMLGoal Σ Γ l (emplace C p) ( gpi).
Proof.
  rename pf into Hpiffq.
  intros H pile.
  unfold of_MLGoal in *. simpl in *.
  intros wfcp wfl.
  feed specialize H.
  { abstract (
      pose proof (Hwfiff := proved_impl_wf _ _ (proj1_sig Hpiffq));
      unfold emplace;
      apply well_formed_free_evar_subst_0;[wf_auto2|];
      fold (PC_wf C);
      eapply wf_emplaced_impl_wf_context;
      apply wfcp
    ).
  }
  { exact wfl. }

  eapply MP.
  2: apply pf_iff_proj2.
  2: abstract (wf_auto2).
  3: eapply prf_equiv_congruence_iter.
  8: apply Hpiffq.
  all: try assumption.
  all: wf_auto2.
Defined.



Ltac2 mutable ml_debug_rewrite := false.

(* Calls [cont] for every subpattern [a] of pattern [phi], giving the match context as an argument *)
Ltac2 for_each_match := fun (a : constr) (phi : constr) (cont : Pattern.context -> unit) =>
  try (
      if ml_debug_rewrite then
           Message.print (
               Message.concat
                 (Message.of_string "Trying to match ")
                 (Message.of_constr a)
             )
        else ();
      match! phi with
      | context ctx [ ?x ]
        => if ml_debug_rewrite then
             Message.print (
                 Message.concat
                   (Message.of_string " against ")
                   (Message.of_constr x)
               )
           else ();
           (if Constr.equal x a then
              if ml_debug_rewrite then
                Message.print (Message.of_string "Success.")
              else () ;
              cont ctx
            else ());
           fail (* backtrack *)
      end
    ); ().

(* Calls [cont] for [n]th subpatern [a] of pattern [phi]. *)
Ltac2 for_nth_match :=
  fun (n : int) (a : constr) (phi : constr) (cont : Pattern.context -> unit) =>
    if ml_debug_rewrite then
      Message.print (Message.of_string "for_nth_match")
    else () ;
    let curr : int ref := {contents := 0} in
    let found : bool ref := {contents := false} in
    for_each_match a phi
    (fun ctx =>
      if (found.(contents))
      then ()
      else
        curr.(contents) := Int.add 1 (curr.(contents)) ;
        if (Int.equal (curr.(contents)) n) then
          cont ctx
        else ()
    )
.

Local Ltac reduce_free_evar_subst_step_2 star :=
      lazymatch goal with
      | [ |- context ctx [?p^[[evar: star ↦ ?q]] ] ]
        =>
          progress rewrite -> (@free_evar_subst_no_occurrence _ star p q) by (
            subst star;
            eapply evar_is_fresh_in_richer';
            [|apply set_evar_fresh_is_fresh'];
            simpl; clear; set_solver
          )
      end.

Local Ltac reduce_free_evar_subst_2 star :=
  (* unfold free_evar_subst; *)
  repeat (reduce_free_evar_subst_step_2 star).

Local Tactic Notation "solve_fresh_contradictions_2'" constr(star) constr(x) constr(h) :=
  let hcontra := fresh "Hcontra" in
  assert (hcontra: x <> star) by (subst star; unfold fresh_evar,evar_fresh_s; try clear h; simpl; solve_fresh_neq);
  rewrite -> h in hcontra;
  contradiction.

Local Ltac solve_fresh_contradictions_2 star :=
  unfold fresh_evar; simpl;
  match goal with
  | h: ?x = star |- _ =>
    let hprime := fresh "hprime" in
    pose proof (hprime := eq_sym h);
    solve_fresh_contradictions_2' star x hprime
  | h: star = ?x |- _
    => solve_fresh_contradictions_2' star x h
  end.

Local Ltac clear_obvious_equalities_2 :=
  repeat (
      match goal with
      | [ h: ?x = ?x |- _ ] => clear h
      end
    ).


Ltac simplify_emplace_2 star :=
  unfold emplace;
  (* unfold free_evar_subst; *)
  cbn;
  repeat break_match_goal;
  clear_obvious_equalities_2; try contradiction;
  try (solve_fresh_contradictions_2 star);
  (* repeat (rewrite nest_ex_aux_0); *)
  reduce_free_evar_subst_2 star.

(* Returns [n]th matching logic context [C] (of type [PatternCtx]) such that
   [emplace C a = phi].
 *)

 
 (* Ltac simplify_pile_side_condition_helper star :=
  subst star;
  unfold fresh_evar,evar_fresh_s;
  eapply evar_is_fresh_in_richer';
  [|apply set_evar_fresh_is_fresh'];
  clear; simpl; set_solver. *)

Ltac solve_fresh :=
  (eapply not_elem_of_larger_impl_not_elem_of;
  [|apply x_eq_fresh_impl_x_notin_free_evars; reflexivity];
  simpl; clear; set_solver) +
  by (unfold evar_is_fresh_in;
  eapply evar_is_fresh_in_richer'; [|apply set_evar_fresh_is_fresh'];
  clear; set_solver).

Ltac rewrite_0_depths star :=
  unfold mu_in_evar_path; cbn;
  repeat rewrite (maximal_exists_depth_to_0 star);
  repeat rewrite (maximal_mu_depth_to_0 star);
  repeat match goal with
  | [ |- context ctx [decide (star = star)] ] =>
    destruct (decide (star = star)); try congruence
  | [ |- context ctx [decide (?x = star)] ] =>
    destruct (decide (x = star)); try congruence
  | [ |- context ctx [decide (star = ?x)] ] =>
    destruct (decide (star = x)); try congruence
  | _ => idtac
  end;
  cbn.

Ltac try_solve_conplex_pile star :=
  try apply pile_any;
  simplify_emplace_2 star;
  (rewrite_0_depths star);
  match goal with
  | |- star ∉ free_evars _ => subst star; solve_fresh
  | |- ProofInfoLe _ _ => try_solve_pile
  end.

Ltac2 Type HeatResult := {
  star_ident : ident ;
  star_eq : ident ;
  pc : constr ;
  ctx : Pattern.context ;
  ctx_pat : constr ;
  equality : ident ;
}.

(** NOTE: with the new MLGoal_rewriteIff, we also need the variables
          used in the list of hypotheses (l) for the fresh name
          generation.
*)
Ltac2 heat :=
  fun (n : int) (a : constr) (phi : constr) : HeatResult =>
    let found : (Pattern.context option) ref := { contents := None } in
     for_nth_match n a phi
     (fun ctx =>
        found.(contents) := Some ctx; ()
     );
     match found.(contents) with
    | None => Control.backtrack_tactic_failure "Cannot heat"
    | Some ctx
      => (
         let fr := constr:(fresh_evar $phi) in
         let star_ident := Fresh.in_goal ident:(star) in
         let star_eq := Fresh.in_goal ident:(star_eq) in
         (*set ($star_ident := $fr);*)
         remember $fr as $star_ident eqn:star_eq;
         let star_hyp := Control.hyp star_ident in
         let ctxpat := Pattern.instantiate ctx constr:(patt_free_evar $star_hyp) in
         let pc := constr:((@Build_PatternCtx _ $star_hyp $ctxpat)) in
         let heq1 := Fresh.in_goal ident:(heq1) in
         assert(heq1 : ($phi = (@emplace _ $pc $a))) 
         > [ abstract(
             (ltac1:(star |- simplify_emplace_2 star) (Ltac1.of_ident star_ident);
             reflexivity
             ))
           | ()
           ];
          { star_ident := star_ident; star_eq := star_eq; pc := pc; ctx := ctx; ctx_pat := ctxpat; equality := heq1 }
         )
    end
.

Ltac2 mlRewrite (hiff : constr) (atn : int) :=
  let thiff := Constr.type hiff in
  (* we have to unfold [derives] otherwise this might not match *)
  lazy_match! (eval unfold ProofSystem.derives in $thiff) with
  | _ ⊢i (?a <---> ?a') using _
    =>
    unfold AnyReasoning;
    lazy_match! goal with
    | [ |- of_MLGoal (@mkMLGoal ?sgm ?g ?l ?p ( ?gpi))]
      =>
        let hr : HeatResult := heat atn a p in
        if ml_debug_rewrite then
           Message.print (Message.of_constr (hr.(ctx_pat)))
         else () ;
         let heq := Control.hyp (hr.(equality)) in
         let pc := (hr.(pc)) in
         eapply (@cast_proof_ml_goal _ $g) >
           [ rewrite $heq; reflexivity | ()];
         Std.clear [hr.(equality)];
         let wfC := Fresh.in_goal ident:(wfC) in
         assert (wfC : PC_wf $pc = true) > [ ltac1:(unfold PC_wf; simpl; wf_auto2); Control.shelve () | ()] ;
         let wfCpf := Control.hyp wfC in
         apply (@MLGoal_rewriteIff $sgm $g _ _ $pc $l $gpi $wfCpf $hiff)  >
         [
         (lazy_match! goal with
         | [ |- of_MLGoal (@mkMLGoal ?sgm ?g ?l ?p _)]
           =>
             let heq2 := Fresh.in_goal ident:(heq2) in
             let plugged := Pattern.instantiate (hr.(ctx)) a' in
             assert(heq2: ($p = $plugged))
             > [
                 abstract (ltac1:(star |- simplify_emplace_2 star) (Ltac1.of_ident (hr.(star_ident)));
                 reflexivity
                 )
               | ()
               ];
             let heq2_pf := Control.hyp heq2 in
             eapply (@cast_proof_ml_goal _ $g) >
               [ rewrite $heq2_pf; reflexivity | ()];
             Std.clear [wfC; heq2 ; (hr.(star_ident)); (hr.(star_eq))]
         end)
         | (ltac1:(star |- try_solve_conplex_pile star) (Ltac1.of_ident (hr.(star_ident))))
         ]
    end
  end.

Ltac2 rec constr_to_int (x : constr) : int :=
  match! x with
  | 0 => 0
  | (S ?x') => Int.add 1 (constr_to_int x')
  end.


Tactic Notation "mlRewrite" constr(Hiff) "at" constr(atn) :=
  _ensureProofMode;
  (let ff := ltac2:(hiff atn |-
                      mlRewrite
                        (Option.get (Ltac1.to_constr(hiff)))
                        (constr_to_int (Option.get (Ltac1.to_constr(atn))))
                   ) in
   ff Hiff atn);
   fold AnyReasoning.

Lemma pf_iff_equiv_sym_nowf {Σ : Signature} Γ A B i :
  Γ ⊢i (A <---> B) using i ->
  Γ ⊢i (B <---> A) using i.
Proof.
  intros H.
  pose proof (wfp := proved_impl_wf _ _ (proj1_sig H)).
  assert (well_formed A) by wf_auto2.
  assert (well_formed B) by wf_auto2.
  apply pf_iff_equiv_sym; assumption.
Defined.

Tactic Notation "mlRewrite" "->" constr(Hiff) "at" constr(atn) :=
  mlRewrite Hiff at atn.

Tactic Notation "mlRewrite" "<-" constr(Hiff) "at" constr(atn) :=
  mlRewrite (@pf_iff_equiv_sym_nowf _ _ _ _ _ Hiff) at atn.


Local Example ex_prf_rewrite_equiv_2 {Σ : Signature} Γ a a' b x:
  well_formed a ->
  well_formed a' ->
  well_formed b ->
  Γ ⊢ a <---> a' ->
  Γ ⊢i (a $ a $ b $ a ---> (patt_free_evar x)) <---> (a $ a' $ b $ a' ---> (patt_free_evar x))
  using AnyReasoning.
Proof.
  intros wfa wfa' wfb Hiff.
  toMLGoal.
  { abstract(wf_auto2). }
  mlRewrite Hiff at 2.
  mlRewrite <- Hiff at 3.
  fromMLGoal.
  useBasicReasoning.
  apply pf_iff_equiv_refl. abstract(wf_auto2).
Defined.



(* TODO: de-duplicate the code *)
#[local]
Ltac convertToNNF_rewrite_pat Ctx p i :=
  lazymatch p with
    | (! ! ?x) =>
        let H' := fresh "H" in
        pose proof (@not_not_eq _ Ctx x ltac:(wf_auto2)) as H';
        apply (@useBasicReasoning _ _ _ i) in H';
        repeat (mlRewrite H' at 1);
        try clear H';
        convertToNNF_rewrite_pat Ctx x i
    | patt_not (patt_and ?x ?y) =>
        let H' := fresh "H" in
        pose proof (@deMorgan_nand _ Ctx x y ltac:(wf_auto2) ltac:(wf_auto2)) as H';
        apply (@useBasicReasoning _ _ _ i) in H';
        repeat (mlRewrite H' at 1);
        try clear H';
        convertToNNF_rewrite_pat Ctx (!x or !y) i
    | patt_not (patt_or ?x ?y) =>
        let H' := fresh "H" in
        pose proof (@deMorgan_nor _ Ctx x y ltac:(wf_auto2) ltac:(wf_auto2)) as H';
        apply (@useBasicReasoning _ _ _ i) in H';
        repeat (mlRewrite H' at 1);
        try clear H';
        convertToNNF_rewrite_pat Ctx (!x and !y) i
    | patt_not (?x ---> ?y) =>
        let H' := fresh "H" in
        pose proof (@nimpl_eq_and _ Ctx x y ltac:(wf_auto2) ltac:(wf_auto2)) as H';
        apply (@useBasicReasoning _ _ _ i) in H';
        repeat (mlRewrite H' at 1);
        try clear H';
        convertToNNF_rewrite_pat Ctx (x and !y) i
    | (?x ---> ?y) =>
        let H' := fresh "H" in
        pose proof (@impl_eq_or _ Ctx x y ltac:(wf_auto2) ltac:(wf_auto2)) as H';
        apply (@useBasicReasoning _ _ _ i) in H';
        repeat (mlRewrite H' at 1);
        try clear H';
        convertToNNF_rewrite_pat Ctx (!x or y) i
    | patt_and ?x ?y => convertToNNF_rewrite_pat Ctx x i; convertToNNF_rewrite_pat Ctx y i
    | patt_or ?x ?y => convertToNNF_rewrite_pat Ctx x i; convertToNNF_rewrite_pat Ctx y i
    | _ => idtac
  end.

#[local]
Ltac toNNF := 
  repeat mlRevertLast;
  match goal with
    | [ |- @of_MLGoal ?Sgm (@mkMLGoal ?Sgm ?Ctx ?ll ?g ?i) ] 
      =>
        mlApplyMetaRaw (@useBasicReasoning _ _ _ i (@not_not_elim Sgm Ctx g ltac:(wf_auto2)));
        convertToNNF_rewrite_pat Ctx (!g) i
  end.

#[local] Example test_toNNF {Σ : Signature} Γ a b :
  well_formed a ->
  well_formed b ->
  Γ ⊢i ( (b and (a or b) and !b and ( a or a) and a) ---> ⊥)
  using BasicReasoning.
Proof.
  intros wfa wfb.
  toMLGoal.
  { wf_auto2. }
  toNNF.
Abort.

#[local]
Ltac rfindContradictionTo a ll k :=
  match ll with
    | ((mkNH _ ?name (! a)) :: ?m) =>
        mlApply name; mlExactn k
    | ((mkNH _ _ _) :: ?m) => 
        rfindContradictionTo a m k
    | _ => fail
  end.

#[local]
Ltac findContradiction l k:=
    match l with
       | ((mkNH _ _ ?a) :: ?m) => 
             match goal with
                | [ |- @of_MLGoal ?Sgm (@mkMLGoal ?Sgm ?Ctx ?ll ?g ?i) ] 
                  =>
                     try rfindContradictionTo a ll k;
                     let kk := eval compute in ( k + 1 ) in
                     (findContradiction m kk)
             end
       | _ => fail
    end.

#[local]
Ltac findContradiction_start :=
  match goal with
    | [ |- @of_MLGoal ?Sgm (@mkMLGoal ?Sgm ?Ctx ?l ?g ?i) ] 
      =>
        match goal with
          | [ |- @of_MLGoal ?Sgm (@mkMLGoal ?Sgm ?Ctx ?l ?g ?i) ] 
            =>
              findContradiction l 0
        end
  end.

#[local]
Ltac breakHyps l :=
  match l with
  | ((mkNH _ ?name (?x and ?y)) :: ?m) => 
      mlDestructAnd name
  | ((mkNH _ ?name (?x or ?y)) :: ?m) => 
      mlDestructOr name
  | ((mkNH _ ?name ?x) :: ?m)  =>
      breakHyps m
  end.

#[local]
Ltac mlTautoBreak := repeat match goal with
| [ |- @of_MLGoal ?Sgm (@mkMLGoal ?Sgm ?Ctx ?l ?g ?i) ] 
  =>
    lazymatch g with
      | (⊥) =>
              breakHyps l
      | _ => mlApplyMetaRaw (@useBasicReasoning _ _ _ i (@bot_elim _ _ g _))
    end
end.

Ltac try_solve_pile2 fallthrough :=
  lazymatch goal with
  | [ |- ProofInfoLe _ _] => try apply pile_refl; try_solve_pile; fallthrough
  | _ => idtac
  end.

#[global]
Ltac mlTauto :=
  _ensureProofMode;
  unshelve(
    try (
      toNNF; (try_solve_pile2 shelve);
      repeat mlIntro;
      mlTautoBreak;
      findContradiction_start
    )
  )
.

#[local]
Example conj_right {Σ : Signature} Γ a b:
  well_formed a ->
  well_formed b ->
  Γ ⊢i ( (b and (a or b) and !b and ( a or a) and a) ---> ⊥)
  using AnyReasoning.
Proof.
  intros wfa wfb.
  toMLGoal.
  { wf_auto2. }
  (* TODO: fail loudly if there is something else than AnyReasoning *)
  mlTauto.
Defined.

#[local]
Example condtradict_taut_2 {Σ : Signature} Γ a b:
  well_formed a ->
  well_formed b ->
  Γ ⊢i (a ---> ((! a) ---> b))
  using AnyReasoning.
Proof.
  intros wfa wfb.
  toMLGoal.
  { wf_auto2. }
  mlTauto.
Defined.

#[local]
Example taut {Σ : Signature} Γ a b c:
  well_formed a ->
  well_formed b ->
  well_formed c ->
  Γ ⊢i ((a ---> b) ---> ((b ---> c) ---> ((a or b)---> c)))
  using AnyReasoning.
Proof.
  intros wfa wfb wfc.
  toMLGoal.
  { wf_auto2. }
  mlTauto. (* Slow *)
Defined.

#[local]
Example condtradict_taut_1 {Σ : Signature} Γ a:
  well_formed a ->
  Γ ⊢i !(a and !a)
  using AnyReasoning.
Proof.
  intros wfa.
  toMLGoal.
  { wf_auto2. }
  mlTauto.
Defined.

#[local]
Example notnot_taut_1 {Σ : Signature} Γ a:
  well_formed a ->
  Γ ⊢i (! ! a ---> a)
  using AnyReasoning.
Proof.
  intros wfa.
  toMLGoal.
  { wf_auto2. }
  mlTauto.
Defined.

#[local]
Lemma Peirce_taut {Σ : Signature} Γ a b:
  well_formed a ->
  well_formed b ->
  Γ ⊢i ((((a ---> b) ---> a) ---> a))
  using AnyReasoning.
Proof.
  intros wfa wfb.
  toMLGoal.
  { wf_auto2. }
  mlTauto.
Defined.



Close Scope ml_scope.
Close Scope list_scope.
Close Scope string_scope.