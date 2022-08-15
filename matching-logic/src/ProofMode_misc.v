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
  ProofMode_base 
  ProofMode_propositional
  ProofMode_firstorder
  ProofMode_fixpoint
  ProofMode_reshaper
.
Import MatchingLogic.Logic.Notations.

Set Default Proof Mode "Classic".

Open Scope ml_scope.
Open Scope string_scope.
Open Scope list_scope.

Section FOL_helpers.

  Context {Σ : Signature}.



  Lemma liftPi (Γ : Theory) (ϕ : Pattern) (i₁ i₂ : ProofInfo)
    {pile : ProofInfoLe i₁ i₂}
    :
    Γ ⊢i ϕ using i₁ ->
    Γ ⊢i ϕ using i₂.
  Proof.
      intros [pf Hpf].
      apply pile in Hpf.
      exists pf.
      exact Hpf.
  Qed.





  Lemma Framing_left (Γ : Theory) (ϕ₁ ϕ₂ ψ : Pattern) (i : ProofInfo)
    (wfψ : well_formed ψ)
    {pile : ProofInfoLe ((ExGen := ∅, SVSubst := ∅, KT := false, FP := {[(exist _ ψ wfψ)]})) i}
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
      destruct Hpf as [Hpf1 Hpf2 Hpf3 Hpf4].
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
      { 
        destruct i.
        simpl in *.
        apply pile_evs_svs_kt_back in pile.
        destruct_and!.
        (*
        destruct pi_framing_patterns0.
        { exfalso. set_solver. } *)
        clear H H1 H0.
        rewrite elem_of_subseteq.
        intros p0 Hp0.
        rewrite elem_of_gset_to_coGset in Hp0.
        rewrite elem_of_union in Hp0.
        destruct Hp0 as [Hp0|Hp0].
        {
          subst.
          remember ((@sval) Pattern (λ p : Pattern, well_formed p = true)) as F.
          rewrite elem_of_subseteq in H3.
          specialize (H3 (exist _ ψ wfψ)).
          feed specialize H3.
          {
            clear. set_solver.
          }
          subst F.
          clear -Hp0 H3.
          set_solver.
        }
        {
          set_solver.
        }
      }
    }
  Defined.

  Lemma Framing_right (Γ : Theory) (ϕ₁ ϕ₂ ψ : Pattern) (i : ProofInfo)
    (wfψ : well_formed ψ)
    {pile : ProofInfoLe ((ExGen := ∅, SVSubst := ∅, KT := false, FP := {[(exist _ ψ wfψ)]})) i}
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
      destruct Hpf as [Hpf1 Hpf2 Hpf3 Hpf4].
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
      {
        destruct i.
        simpl in *.
        apply pile_evs_svs_kt_back in pile.
        destruct_and!.
        clear H H1 H0.
        rewrite elem_of_subseteq.
        intros p0 Hp0.
        rewrite elem_of_gset_to_coGset in Hp0.
        rewrite elem_of_union in Hp0.
        destruct Hp0 as [Hp0|Hp0].
        {
          subst.
          remember ((@sval) Pattern (λ p : Pattern, well_formed p = true)) as F.
          rewrite elem_of_subseteq in H3.
          specialize (H3 (exist _ ψ wfψ)).
          feed specialize H3.
          {
            clear. set_solver.
          }
          subst F.
          clear -Hp0 H3. set_solver.
        }
        {
          set_solver.
        }
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
      constructor; simpl.
      {
        set_solver.
      }
      {
        set_solver.
      }
      {
        reflexivity.
      }
      {
        apply reflexivity.
      }
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
      constructor; simpl.
      {
        set_solver.
      }
      {
        set_solver.
      }
      {
        reflexivity.
      }
      {
        apply reflexivity.
      }
    }
  Defined.

  Arguments Prop_bott_left _ (_%ml) _ : clear implicits.
  Arguments Prop_bott_right _ (_%ml) _ : clear implicits.


  Lemma useAnyReasoning Γ ϕ i:
    Γ ⊢i ϕ using i ->
    Γ ⊢i ϕ using AnyReasoning.
  Proof.
    intros H.
    {
      destruct i.
      eapply useGenericReasoning.
      { apply pile_any. }
      apply H.
    }
  Qed.



  Fixpoint frames_of_AC (C : Application_context)
    : coWfpSet :=
  match C with
  | box => ∅
  | (@ctx_app_l _ C' p wfp) => {[(exist _ p wfp)]} ∪ (frames_of_AC C')
  | (@ctx_app_r _ p C' wfp) => {[(exist _ p wfp)]} ∪ (frames_of_AC C')
  end.


  (* TODO rename into Prop_bot_ctx *)
  Lemma Prop_bot (Γ : Theory) (C : Application_context) :
    Γ ⊢i ((subst_ctx C patt_bott) ---> patt_bott)
    using (ExGen := ∅, SVSubst := ∅, KT := false, FP := frames_of_AC C).
  Proof.
    remember (frames_of_AC C) as foC.
    move: foC HeqfoC.
    induction C; intros foC HeqfoC; simpl in *.
    - apply useBasicReasoning.
      apply false_implies_everything.
      wf_auto2.
    - eapply syllogism_meta.
      5: { apply useBasicReasoning. apply (Prop_bott_left Γ p ltac:(wf_auto2)). }
      4: { simpl. subst foC.  eapply useGenericReasoning.
           2: eapply Framing_left with (wfψ := Prf).
           1: apply pile_refl.
           1: {
            eapply pile_evs_svs_kt.
            { apply reflexivity. }
            { apply reflexivity. }
            { reflexivity. }      
            { clear. set_solver. }      
           }
           eapply useGenericReasoning.
           2: apply IHC.
           2: reflexivity.
           apply pile_evs_svs_kt.
           { apply reflexivity. }
           { apply reflexivity. }
           { reflexivity. }
           { clear. set_solver. }
      }
      all: wf_auto2.
       - eapply syllogism_meta.
           5: { apply useBasicReasoning. apply (Prop_bott_right Γ p ltac:(wf_auto2)). }
           4: { simpl. subst foC.  eapply useGenericReasoning.
                2: eapply Framing_right with (wfψ := Prf).
                1: apply pile_refl.
                1: {
                 eapply pile_evs_svs_kt.
                 { apply reflexivity. }
                 { apply reflexivity. }
                 { reflexivity. }      
                 { clear. set_solver. }      
                }
                eapply useGenericReasoning.
                2: apply IHC.
                2: reflexivity.
                apply pile_evs_svs_kt.
                { apply reflexivity. }
                { apply reflexivity. }
                { reflexivity. }      
                { clear. set_solver. }
           }
           all: wf_auto2.
  Defined.

  Lemma Framing (Γ : Theory) (C : Application_context) (A B : Pattern) (i : ProofInfo)
    {pile : ProofInfoLe
     ((ExGen := ∅, SVSubst := ∅, KT := false, FP := frames_of_AC C))
     i
    }
    :
    Γ ⊢i (A ---> B) using i ->
    Γ ⊢i ((subst_ctx C A) ---> (subst_ctx C B)) using i.
  Proof.
    intros H.
    pose proof H as [pf _].
    pose proof (HWF := @proved_impl_wf _ _ _ pf).
    assert (wfA: well_formed A) by wf_auto2.
    assert (wfB: well_formed B) by wf_auto2.
    clear pf HWF.

    move: wfA wfB H.
    induction C; intros WFA WFB H; simpl in *.
    - exact H.
    - destruct i.
      apply pile_evs_svs_kt_back in pile.
      destruct_and!. simpl in *.
      apply Framing_left with (wfψ := Prf).
      {
        apply pile_evs_svs_kt; try assumption.
        set_solver.
      }
      apply IHC.
      2,3: assumption.
      2: exact H.
      apply pile_evs_svs_kt; try assumption.
      set_solver.
    - destruct i.
      apply pile_evs_svs_kt_back in pile.
      destruct_and!. simpl in *.
      apply Framing_right with (wfψ := Prf).
      {
        apply pile_evs_svs_kt; try assumption.
        set_solver.
      }
      apply IHC.
      2,3: assumption.
      2: exact H.
      apply pile_evs_svs_kt; try assumption.
      set_solver.
  Defined.

  Lemma A_implies_not_not_A_ctx (Γ : Theory) (A : Pattern) (C : Application_context)
    (i : ProofInfo) {pile : ProofInfoLe ((ExGen := ∅, SVSubst := ∅, KT := false, FP := frames_of_AC C)) i}
    :
    well_formed A ->
    Γ ⊢i A using i ->
    Γ ⊢i (! (subst_ctx C ( !A ))) using i.
  Proof.
    intros WFA H.

    epose proof (ANNA := @A_implies_not_not_A_alt Σ  Γ _ i _ H).
    replace (! (! A)) with ((! A) ---> Bot) in ANNA by reflexivity.
    epose proof (EF := @Framing _ C (! A) Bot _ _ ANNA).
    epose proof (PB := Prop_bot Γ C).
    apply liftPi with (i₂ := i) in PB. 2: apply _.
    epose (TRANS := @syllogism_meta _ _ _ _ _ _ _ _ _ EF PB).
    apply TRANS.

    Unshelve.
    all: wf_auto2.
  Defined.



  Lemma ctx_bot_prop (Γ : Theory) (C : Application_context) (A : Pattern) 
    (i : ProofInfo)
    {pile : ProofInfoLe ((ExGen := ∅, SVSubst := ∅, KT := false, FP := frames_of_AC C)) i}
  :
    well_formed A ->
    Γ ⊢i (A ---> Bot) using i ->
    Γ ⊢i (subst_ctx C A ---> Bot) using i.
  Proof.
    intros WFA H.
    epose proof (FR := @Framing Γ C A Bot _ _ H).
    epose proof (BPR := @Prop_bot Γ C).
    apply liftPi with (i₂ := i) in BPR. 2: apply _.
    epose proof (TRANS := @syllogism_meta _ _ _ _ _ _ _ _ _ FR BPR).
    exact TRANS.
    Unshelve.
    all: wf_auto2.
  Defined.



End FOL_helpers.

Lemma prf_prop_bott_iff {Σ : Signature} Γ AC:
  Γ ⊢i ((subst_ctx AC patt_bott) <---> patt_bott)
  using (
  (ExGen := ∅, SVSubst := ∅, KT := false, FP := frames_of_AC AC)).
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
    abstract (
      constructor; simpl;
      [(set_solver)|(set_solver)|(reflexivity)|(set_solver)]
    ).
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
    abstract (
      constructor; simpl;
      [(set_solver)|(set_solver)|(reflexivity)|(set_solver)]
    ).
  }
Defined.

Lemma prf_prop_or_iff {Σ : Signature} Γ AC p q:
  well_formed p ->
  well_formed q ->
  Γ ⊢i ((subst_ctx AC (p or q)) <---> ((subst_ctx AC p) or (subst_ctx AC q)))
  using (
  (ExGen := ∅, SVSubst := ∅, KT := false, FP := frames_of_AC AC)).
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
      2: { subst i. 
        apply pile_evs_svs_kt; auto. set_solver.
      }
      rewrite Heqi in H.
      apply Framing_left with (ψ := p0) (wfψ := Prf) in H.
      2: { apply pile_evs_svs_kt; auto. set_solver. }
      eapply syllogism_meta. 4: subst i; apply H.
      all: try_wfauto2.
      remember (subst_ctx AC p) as p'.
      remember (subst_ctx AC q) as q'.
      subst i.
      eapply useGenericReasoning.
      2: eapply Prop_disj_left. all: subst; try_wfauto2.
      { apply pile_evs_svs_kt; auto. set_solver. }
    + eapply prf_disj_elim_meta_meta; try_wfauto2.
      * subst i. 
        apply Framing_left with (wfψ := Prf).
        { apply pile_evs_svs_kt; auto. set_solver. }
        eapply prf_weaken_conclusion_meta_meta.
        4: { gapply IH2. try_solve_pile. }
        1-3: wf_auto2.
        useBasicReasoning.
        apply disj_left_intro; wf_auto2.
      * subst i.
        apply Framing_left with (wfψ := Prf).
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
      eapply Framing_right with (ψ := p0)(wfψ := Prf) in H.
      eapply syllogism_meta. 4: apply H.
      all: try_wfauto2.
      2: { subst i. try_solve_pile. }
      remember (subst_ctx AC p) as p'.
      remember (subst_ctx AC q) as q'.
      subst i; apply useBasicReasoning.
      apply Prop_disj_right. all: subst; try_wfauto2.
    + eapply prf_disj_elim_meta_meta; try_wfauto2.
      * subst i.
        apply Framing_right with (wfψ := Prf).
        { try_solve_pile. }
        eapply prf_weaken_conclusion_meta_meta.
        4: gapply IH2; try_solve_pile. all: try_wfauto2.
        useBasicReasoning.
        apply disj_left_intro; wf_auto2.
      * subst i.
        apply Framing_right with (wfψ := Prf).
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
    abstract (
      constructor; simpl;
      [( set_solver )
      |( set_solver )
      |( reflexivity )
      |( set_solver )
      ]
    ).
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
    abstract (
      constructor; simpl;
      [( set_solver )
      |( set_solver )
      |( reflexivity )
      |( set_solver )
      ]
    ).
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
  {
    constructor; simpl.
    { set_solver. }
    { set_solver. }
    { reflexivity. }
    { set_solver. }
  }
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
  {
    constructor; simpl.
    { set_solver. }
    { set_solver. }
    { reflexivity. }
    { set_solver. }
  }
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
     pi_framing_patterns := frames_of_AC AC
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
      apply (@wp_sctx _ AC p) in Hwfp. rewrite Hwfp. simpl. clear Hwfp.
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

    (* TODO automate this *)
    assert (Hwfeo: well_formed (p^{evar: 0 ↦ x})).
    {
      unfold well_formed.
      unfold well_formed,well_formed_closed in Hwf. apply andb_prop in Hwf. simpl in Hwf.
      rewrite wfp_evar_open.
      { apply Hwf. }
      unfold well_formed_closed.
      destruct_and!.
      split_and!; auto.
    }
    
    
    (* TODO automate this. The problem is that [well_formed_app] and others do not have [= true];
       that is why [auto] does not work. But [auto] is not suitable for this anyway.
       A better way would be to create some `simpl_well_formed` tuple, that might use the type class
       mechanism for extension...
     *)
    assert(Hwf'p0: well_formed (exists_quantify x (subst_ctx AC (p^{evar: 0 ↦ x}) $ p0))).
    {
      unfold exists_quantify.
      apply wf_ex_evar_quantify.
      apply well_formed_app.
      2: { apply Prf. }
      auto.
    }

    apply pf_iff_iff in IHAC; auto.

    destruct IHAC as [IH1 IH2].
    apply pf_iff_split; auto.
    + pose proof (H := IH1).
      change constraint in IH1.
      apply Framing_left with (ψ := p0) (wfψ := Prf) in IH1.
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
      apply Framing_left with (ψ := p0) (wfψ := Prf) in IH2.
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
      gapply (@Framing_left _ _ _ _ _ _ Prf).
      2: apply pile_refl.
      1: try_solve_pile.
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
    { unfold well_formed. simpl.
      pose proof (Hwf' := Hwf).
      unfold well_formed in Hwf. simpl in Hwf.
      apply andb_prop in Hwf. destruct Hwf as [Hwfp Hwfc].
      apply (@wp_sctx _ AC p) in Hwfp. rewrite Hwfp. simpl. clear Hwfp.
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

    (* TODO automate this *)
    assert (Hwfeo: well_formed (p^{evar: 0 ↦ x})).
    {
      unfold well_formed.
      unfold well_formed,well_formed_closed in Hwf. apply andb_prop in Hwf. simpl in Hwf.
      rewrite wfp_evar_open.
      { apply Hwf. }
      unfold well_formed_closed.
      destruct_and!.
      split_and!; auto.
    }

    (* TODO automate this. The problem is that [well_formed_app] and others do not have [= true];
       that is why [auto] does not work. But [auto] is not suitable for this anyway.
       A better way would be to create some `simpl_well_formed` tuple, that might use the type class
       mechanism for extension...
     *)
    assert(Hwf'p0: well_formed (exists_quantify x (p0 $ subst_ctx AC (p^{evar: 0 ↦ x})))).
    {
      unfold exists_quantify.
      apply wf_ex_evar_quantify.
      apply well_formed_app; auto.
    }

    apply pf_iff_iff in IHAC; auto.

    destruct IHAC as [IH1 IH2].
    apply pf_iff_split; auto.
    + pose proof (H := IH1).
      change constraint in IH1.
      apply (@Framing_right _ _ _ _ _ _ Prf) in IH1.
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
      eapply (@Framing_right _ _ _ _ _ _ Prf) in IH2.
      eapply syllogism_meta. 5: eapply IH2.
      1-3: wf_auto2.
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

      eapply (@Framing_right _ _ _ _ _ _ Prf).
      { try_solve_pile. }
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


Lemma pf_evar_open_free_evar_subst_equiv_sides {Σ : Signature} Γ x n ϕ p q E i:
  x <> E ->
  well_formed p = true ->
  well_formed q = true ->
  Γ ⊢i ϕ^{evar: n ↦ x}^[[evar: E ↦ p]] <---> ϕ^{evar: n ↦ x}^[[evar: E ↦ q]] using i ->
  Γ ⊢i ϕ^[[evar: E ↦ p]]^{evar: n ↦ x} <---> ϕ^[[evar: E ↦ q]]^{evar: n ↦ x} using i.
Proof.
  intros Hx wfp wfq H.
  unshelve (eapply (@cast_proof' Σ Γ _ _ _ _ H)).
  rewrite -> evar_open_free_evar_subst_swap by assumption.
  rewrite -> evar_open_free_evar_subst_swap by assumption.
  reflexivity.
Defined.

Lemma pf_iff_free_evar_subst_svar_open_to_bsvar_subst_free_evar_subst {Σ : Signature} Γ ϕ p q E X i:
  well_formed_closed_mu_aux p 0 = true ->
  well_formed_closed_mu_aux q 0 = true ->
  Γ ⊢i ϕ^{svar: 0 ↦ X}^[[evar: E ↦ p]] <---> ϕ^{svar: 0 ↦ X}^[[evar: E ↦ q]] using i ->
  Γ ⊢i ϕ^[[evar: E ↦ p]]^[svar: 0 ↦ patt_free_svar X] <--->
      ϕ^[[evar: E ↦ q]]^[svar: 0 ↦ patt_free_svar X] using i.
Proof.
  intros wfp wfq H.
  unshelve (eapply (@cast_proof' _ _ _ _ _ _ H)).

  abstract (
    unfold svar_open in H;
    rewrite <- free_evar_subst_bsvar_subst;
    [idtac|wf_auto| unfold evar_is_fresh_in; simpl; clear; set_solver];
    rewrite <- free_evar_subst_bsvar_subst;
    [idtac|wf_auto|unfold evar_is_fresh_in; simpl; clear; set_solver];
    reflexivity
 ).
Defined.

Lemma pf_iff_mu_remove_svar_quantify_svar_open {Σ : Signature} Γ ϕ p q E X i :
  well_formed_closed_mu_aux (ϕ^[[evar: E ↦ p]]) 1 ->
  well_formed_closed_mu_aux (ϕ^[[evar: E ↦ q]]) 1 ->
  X ∉ free_svars (ϕ^[[evar: E ↦ p]]) ->
  X ∉ free_svars (ϕ^[[evar: E ↦ q]]) ->
  Γ ⊢i (mu , ϕ^[[evar: E ↦ p]]^{svar: 0 ↦ X}^{{svar: X ↦ 0}}) <--->
      (mu , ϕ^[[evar: E ↦ q]]^{svar: 0 ↦ X}^{{svar: X ↦ 0}}) using i ->
  Γ ⊢i (mu , ϕ^[[evar: E ↦ p]]) <---> (mu , ϕ^[[evar: E ↦ q]]) using i.
Proof.
  intros wfp' wfq' Xfrp Xfrq H.
  unshelve (eapply (@cast_proof' _ _ _ _ _ _ H)).
  abstract (
    rewrite -{1}[ϕ^[[evar: E ↦ p]]](@svar_quantify_svar_open _ X 0); [assumption| auto | auto];
    rewrite -{1}[ϕ^[[evar: E ↦ q]]](@svar_quantify_svar_open _ X 0); [assumption| auto | auto];
    reflexivity
  ).
Defined.


Add Search Blacklist "_elim".
Add Search Blacklist "_graph_rect".
Add Search Blacklist "_graph_mut".
Add Search Blacklist "FunctionalElimination_".


Section FOL_helpers.

  Context {Σ : Signature}.

  Fixpoint maximal_exists_depth_of_evar_in_pattern' (depth : nat) (E : evar) (ψ : Pattern) : nat :=
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
        (maximal_exists_depth_of_evar_in_pattern' depth E ψ₁)
        (maximal_exists_depth_of_evar_in_pattern' depth E ψ₂)
    | patt_app ψ₁ ψ₂
      => Nat.max
        (maximal_exists_depth_of_evar_in_pattern' depth E ψ₁)
        (maximal_exists_depth_of_evar_in_pattern' depth E ψ₂)
    | patt_exists ψ' =>
      maximal_exists_depth_of_evar_in_pattern' (S depth) E ψ'
    | patt_mu ψ' =>
      maximal_exists_depth_of_evar_in_pattern' depth E ψ'
    end.

  Definition maximal_exists_depth_of_evar_in_pattern (E : evar) (ψ : Pattern) : nat :=
    maximal_exists_depth_of_evar_in_pattern' 0 E ψ.

  Definition pf_ite {P : Prop} (i : ProofInfo) (dec: {P} + {~P}) (Γ : Theory) (ϕ : Pattern)
    (pf1: P -> Γ ⊢i ϕ using i)
    (pf2: (~P) -> Γ ⊢i ϕ using i) :
    Γ ⊢i ϕ using i :=
    match dec with
    | left pf => pf1 pf
    | right pf => pf2 pf
    end.

  Lemma evar_fresh_seq_max (EvS : EVarSet) (n1 n2 : nat) :
    (@list_to_set evar EVarSet _ _ _ (evar_fresh_seq EvS n1)) ⊆ (list_to_set (evar_fresh_seq EvS (n1 `max` n2))).
  Proof.
    move: EvS n2.
    induction n1; intros EvS n2.
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
        cut (@list_to_set evar EVarSet _ _ _ (evar_fresh_seq ({[evar_fresh_s EvS]} ∪ EvS) n1)
        ⊆ list_to_set (evar_fresh_seq ({[evar_fresh_s EvS]} ∪ EvS) (n1 `max` n2))).
        {
          set_solver.
        }
        specialize (IHn1 ({[evar_fresh_s EvS]} ∪ EvS) n2).
        apply IHn1.
      }
    }
  Qed.

  Lemma medoeip_evar_open depth E n x ψ:
    E <> x ->
    maximal_exists_depth_of_evar_in_pattern' depth E (ψ^{evar: n ↦ x})
    = maximal_exists_depth_of_evar_in_pattern' depth E ψ.
  Proof.
    intros HEnex.
    unfold evar_open.
    move: depth n.
    induction ψ; intros depth n'; simpl; try reflexivity.
    {
      case_match; simpl; try reflexivity.
      case_match; try reflexivity. subst. contradiction.
    }
    {
      rewrite IHψ1. rewrite IHψ2. reflexivity.
    }
    {
      rewrite IHψ1. rewrite IHψ2. reflexivity.
    }
    {
      rewrite IHψ. reflexivity.
    }
    {
      rewrite IHψ. reflexivity.
    }
  Qed.

  Lemma medoeip_svar_open depth E n X ψ:
    maximal_exists_depth_of_evar_in_pattern' depth E (ψ^{svar: n ↦ X})
    = maximal_exists_depth_of_evar_in_pattern' depth E ψ.
  Proof.
    unfold svar_open.
    move: depth n.
    induction ψ; intros depth n'; simpl; try reflexivity.
    {
      case_match; simpl; try reflexivity.
    }
    {
      rewrite IHψ1. rewrite IHψ2. reflexivity.
    }
    {
      rewrite IHψ1. rewrite IHψ2. reflexivity.
    }
    {
      rewrite IHψ. reflexivity.
    }
    {
      rewrite IHψ. reflexivity.
    }
  Qed.

  Lemma medoeip_notin E ψ depth:
    E ∉ free_evars ψ ->
    maximal_exists_depth_of_evar_in_pattern' depth E ψ = 0.
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

  Lemma medoeip_S_in E ψ depth:
    E ∈ free_evars ψ ->
    maximal_exists_depth_of_evar_in_pattern' (S depth) E ψ
    = S (maximal_exists_depth_of_evar_in_pattern' depth E ψ).
  Proof.
    intros Hin.
    move: E depth Hin.
    induction ψ; intros E depth Hin; simpl in *.
    { case_match. reflexivity. set_solver. }
    { set_solver. }
    { set_solver. }
    { set_solver. }
    { set_solver. }
    {
      destruct (decide (E ∈ free_evars ψ1)),(decide (E ∈ free_evars ψ2)).
      {
        rewrite IHψ1. assumption. rewrite IHψ2. assumption. simpl. reflexivity.
      }
      {
        rewrite IHψ1. assumption.
        rewrite [maximal_exists_depth_of_evar_in_pattern' _ _ ψ2]medoeip_notin.
        { assumption. }
        rewrite [maximal_exists_depth_of_evar_in_pattern' _ _ ψ2]medoeip_notin.
        { assumption. }
        simpl.
        rewrite Nat.max_comm.
        simpl.
        reflexivity.
      }
      {
        rewrite IHψ2. assumption.
        rewrite [maximal_exists_depth_of_evar_in_pattern' _ _ ψ1]medoeip_notin.
        { assumption. }
        rewrite [maximal_exists_depth_of_evar_in_pattern' _ _ ψ1]medoeip_notin.
        { assumption. }
        simpl.
        reflexivity.
      }
      {
        exfalso. set_solver.
      }
    }
    { set_solver. }
    {
      destruct (decide (E ∈ free_evars ψ1)),(decide (E ∈ free_evars ψ2)).
      {
        rewrite IHψ1. assumption. rewrite IHψ2. assumption. simpl. reflexivity.
      }
      {
        rewrite IHψ1. assumption.
        rewrite [maximal_exists_depth_of_evar_in_pattern' _ _ ψ2]medoeip_notin.
        { assumption. }
        rewrite [maximal_exists_depth_of_evar_in_pattern' _ _ ψ2]medoeip_notin.
        { assumption. }
        simpl.
        rewrite Nat.max_comm.
        simpl.
        reflexivity.
      }
      {
        rewrite IHψ2. assumption.
        rewrite [maximal_exists_depth_of_evar_in_pattern' _ _ ψ1]medoeip_notin.
        { assumption. }
        rewrite [maximal_exists_depth_of_evar_in_pattern' _ _ ψ1]medoeip_notin.
        { assumption. }
        simpl.
        reflexivity.
      }
      {
        exfalso. set_solver.
      }     
    }
    {
      rewrite IHψ. assumption. reflexivity.
    }
    {
      rewrite IHψ. assumption. reflexivity.
    }
  Qed.


  Fixpoint maximal_mu_depth_of_evar_in_pattern' (depth : nat) (E : evar) (ψ : Pattern) : nat :=
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
        (maximal_mu_depth_of_evar_in_pattern' depth E ψ₁)
        (maximal_mu_depth_of_evar_in_pattern' depth E ψ₂)
    | patt_app ψ₁ ψ₂
      => Nat.max
        (maximal_mu_depth_of_evar_in_pattern' depth E ψ₁)
        (maximal_mu_depth_of_evar_in_pattern' depth E ψ₂)
    | patt_exists ψ' =>
      maximal_mu_depth_of_evar_in_pattern' depth E ψ'
    | patt_mu ψ' =>
      maximal_mu_depth_of_evar_in_pattern' (S depth) E ψ'
    end.

  Definition maximal_mu_depth_of_evar_in_pattern (E : evar) (ψ : Pattern) : nat :=
    maximal_mu_depth_of_evar_in_pattern' 0 E ψ.



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

  Lemma mmdoeip_svar_open depth E n X ψ:
    maximal_mu_depth_of_evar_in_pattern' depth E (ψ^{svar: n ↦ X})
    = maximal_mu_depth_of_evar_in_pattern' depth E ψ.
  Proof.
    unfold svar_open.
    move: depth n.
    induction ψ; intros depth n'; simpl; try reflexivity.
    {
      case_match; simpl; try reflexivity.
    }
    {
      rewrite IHψ1. rewrite IHψ2. reflexivity.
    }
    {
      rewrite IHψ1. rewrite IHψ2. reflexivity.
    }
    {
      rewrite IHψ. reflexivity.
    }
    {
      rewrite IHψ. reflexivity.
    }
  Qed.

  Lemma mmdoeip_evar_open depth E n x ψ:
    E <> x ->
    maximal_mu_depth_of_evar_in_pattern' depth E (ψ^{evar: n ↦ x})
    = maximal_mu_depth_of_evar_in_pattern' depth E ψ.
  Proof.
    intros Hne.
    unfold evar_open.
    move: depth n.
    induction ψ; intros depth n'; simpl; try reflexivity.
    {
      case_match; simpl; try reflexivity.
      case_match; simpl; try reflexivity.
      subst. contradiction.
    }
    {
      rewrite IHψ1. rewrite IHψ2. reflexivity.
    }
    {
      rewrite IHψ1. rewrite IHψ2. reflexivity.
    }
    {
      rewrite IHψ. reflexivity.
    }
    {
      rewrite IHψ. reflexivity.
    }
  Qed.


  Lemma mmdoeip_notin E ψ depth:
    E ∉ free_evars ψ ->
    maximal_mu_depth_of_evar_in_pattern' depth E ψ = 0.
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

  Lemma mmdoeip_S_in E ψ depth:
    E ∈ free_evars ψ ->
    maximal_mu_depth_of_evar_in_pattern' (S depth) E ψ
    = S (maximal_mu_depth_of_evar_in_pattern' depth E ψ).
  Proof.
    intros Hin.
    move: E depth Hin.
    induction ψ; intros E depth Hin; simpl in *.
    { case_match. reflexivity. set_solver. }
    { set_solver. }
    { set_solver. }
    { set_solver. }
    { set_solver. }
    {
      destruct (decide (E ∈ free_evars ψ1)),(decide (E ∈ free_evars ψ2)).
      {
        rewrite IHψ1. assumption. rewrite IHψ2. assumption. simpl. reflexivity.
      }
      {
      rewrite IHψ1. assumption.
      rewrite [maximal_mu_depth_of_evar_in_pattern' _ _ ψ2]mmdoeip_notin.
      { assumption. }
      rewrite [maximal_mu_depth_of_evar_in_pattern' _ _ ψ2]mmdoeip_notin.
      { assumption. }
      simpl.
      rewrite Nat.max_comm.
      simpl.
      reflexivity.
    }
    {
      rewrite IHψ2. assumption.
      rewrite [maximal_mu_depth_of_evar_in_pattern' _ _ ψ1]mmdoeip_notin.
      { assumption. }
      rewrite [maximal_mu_depth_of_evar_in_pattern' _ _ ψ1]mmdoeip_notin.
      { assumption. }
      simpl.
      reflexivity.
    }
    {
      exfalso. set_solver.
    }
  }
  { set_solver. }
  {
    destruct (decide (E ∈ free_evars ψ1)),(decide (E ∈ free_evars ψ2)).
    {
      rewrite IHψ1. assumption. rewrite IHψ2. assumption. simpl. reflexivity.
    }
    {
    rewrite IHψ1. assumption.
    rewrite [maximal_mu_depth_of_evar_in_pattern' _ _ ψ2]mmdoeip_notin.
    { assumption. }
    rewrite [maximal_mu_depth_of_evar_in_pattern' _ _ ψ2]mmdoeip_notin.
    { assumption. }
    simpl.
    rewrite Nat.max_comm.
    simpl.
    reflexivity.
  }
  {
    rewrite IHψ2. assumption.
    rewrite [maximal_mu_depth_of_evar_in_pattern' _ _ ψ1]mmdoeip_notin.
    { assumption. }
    rewrite [maximal_mu_depth_of_evar_in_pattern' _ _ ψ1]mmdoeip_notin.
    { assumption. }
    simpl.
    reflexivity.
  }
  {
    exfalso. set_solver.
  }
}
{
  rewrite IHψ. assumption. reflexivity.
}
{
  rewrite IHψ. assumption. reflexivity.
}
Qed.


  Lemma congruence_ex_helper Γ E ψ x p q gpi exdepth mudepth EvS SvS
    (HxneqE : x ≠ E)
    (wfψ : well_formed (ex , ψ))
    (wfp : well_formed p)
    (wfq : well_formed q)
    (Heqx : x = evar_fresh (elements EvS))
    (HEinψ: E ∈ free_evars ψ)
    (i': ProofInfo)
    (p_sub_EvS: free_evars p ⊆ EvS)
    (q_sub_EvS: free_evars q ⊆ EvS)
    (ψ_sub_EvS : free_evars ψ ⊆ EvS)
    (Heqi': i' =
            (ExGen := list_to_set
                        (evar_fresh_seq EvS
                           (maximal_exists_depth_of_evar_in_pattern' exdepth E
                              (ex , ψ))),
             SVSubst := list_to_set
                          (svar_fresh_seq SvS
                             (maximal_mu_depth_of_evar_in_pattern' mudepth E
                                (ex , ψ))),
             KT := (if
                     decide
                       (0 =
                        maximal_mu_depth_of_evar_in_pattern' mudepth E (ex , ψ))
                    is left _ then false
                    else true),
             FP := ∅
            ))
    (pile: ProofInfoLe i' ( gpi))
    (IH: Γ ⊢i ψ^{evar: 0 ↦ x}^[[evar: E ↦ p]] <---> ψ^{evar: 0 ↦ x}^[[evar: E ↦ q]]
       using  gpi) :
    (Γ ⊢i (ex , ψ^[[evar: E ↦ p]]) <---> (ex , ψ^[[evar: E ↦ q]]) using  gpi).
  Proof.
    apply pf_evar_open_free_evar_subst_equiv_sides in IH.
    2: { exact HxneqE. }
    2: { exact wfp. }
    2: { exact wfq. }
    unshelve (epose proof (IH1 := @pf_iff_proj1 Σ Γ _ _ _ _ _ IH)).
    { abstract (wf_auto2). }
    { abstract (wf_auto2). }
    unshelve (epose proof (IH2 := @pf_iff_proj2 Σ Γ _ _ _ _ _ IH)).
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
            subst i';
            eapply pile_trans;
            [|apply pile];
            apply pile_evs_svs_kt;
            [(
            simpl;
            rewrite medoeip_S_in;
            [assumption|];
            simpl;
            unfold evar_fresh_s;
            rewrite -Heqx;
            clear;
            set_solver
            )|(clear; set_solver)
            |reflexivity|(clear; set_solver)]
          ).
        }
        {
          abstract (
            simpl;
            pose proof (Htmp1 := @set_evar_fresh_is_fresh' _ EvS);
            pose proof (Htmp2 := @free_evars_free_evar_subst Σ ψ q E);   
            set_solver
          ).
        }
      }
      {
        abstract (
          simpl;
          pose proof (Htmp1 := @set_evar_fresh_is_fresh' _ EvS);
          pose proof (Htmp := @free_evars_free_evar_subst Σ ψ p E);
          set_solver
        ).
      }
      {
        abstract (wf_auto2).
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
            subst i';
            eapply pile_trans;
            [|apply pile];
            apply pile_evs_svs_kt;
            [(
              simpl;
              rewrite medoeip_S_in;
              [assumption|];
              simpl;
              unfold evar_fresh_s;
              rewrite -Heqx;
              clear;
              set_solver
            )
           |(clear; set_solver)
           |(reflexivity)|(clear; set_solver)
            ]).
        }
        {
          abstract (
            simpl;
            pose proof (Htmp1 := @set_evar_fresh_is_fresh' _ EvS);
            pose proof (Htmp := @free_evars_free_evar_subst Σ ψ p E);
            set_solver
          ).
        }
      }
      {
        abstract (
          simpl;
          pose proof (Htmp1 := @set_evar_fresh_is_fresh' _ EvS);
          pose proof (Htmp := @free_evars_free_evar_subst Σ ψ q E);
          set_solver
        ).
      }
      {
        abstract (wf_auto2).
      }
    }
  Defined.

  Equations? frames_on_the_way_to_hole'
  (EvS : EVarSet)
  (SvS : SVarSet)
  (E : evar)
  (ψ p q : Pattern)
  (wfψ : well_formed ψ = true)
  (wfp : well_formed p = true)
  (wfq : well_formed q = true)
  : gset wfPattern
  by wf (size' ψ) lt :=
  @frames_on_the_way_to_hole' EvS SvS E (patt_free_evar _) _ _ _ _ _ := ∅ ;

  @frames_on_the_way_to_hole' EvS SvS E (patt_free_svar _) _ _ _ _ _ := ∅ ;

  @frames_on_the_way_to_hole' EvS SvS E (patt_bound_evar _) _ _ _ _ _ := ∅ ;

  @frames_on_the_way_to_hole' EvS SvS E (patt_bound_svar _) _ _ _ _ _ := ∅ ;

  @frames_on_the_way_to_hole' EvS SvS E (patt_sym _) _ _ _ _ _ := ∅ ;

  @frames_on_the_way_to_hole' EvS SvS E (patt_bott) _ _ _ _ _ := ∅ ;

  @frames_on_the_way_to_hole' EvS SvS E (patt_app ψ1 ψ2) p q _ _ _
    :=
      (@singleton _ _ gset_singleton (exist _ (ψ1^[[evar: E ↦ p]]) _))
      ∪ {[(exist _ (ψ2^[[evar: E ↦ p]]) _)]}
      ∪ {[(exist _ (ψ1^[[evar: E ↦ q]]) _)]}
      ∪ {[(exist _ (ψ2^[[evar: E ↦ q]]) _)]}
      ∪ (@frames_on_the_way_to_hole' EvS SvS E ψ1 p q _ _ _)
      ∪ (@frames_on_the_way_to_hole' EvS SvS E ψ2 p q _ _ _) ;

  @frames_on_the_way_to_hole' EvS SvS E (patt_imp ψ1 ψ2) p q _ _ _
  := @union _ gset_union (@frames_on_the_way_to_hole' EvS SvS E ψ1 p q _ _ _)
     (@frames_on_the_way_to_hole' EvS SvS E ψ2 p q _ _ _) ;

  @frames_on_the_way_to_hole' EvS SvS E (patt_exists ψ') p q _ _ _
   := (@frames_on_the_way_to_hole' ({[(evar_fresh (elements EvS))]} ∪ EvS) SvS E (ψ'^{evar: 0 ↦ evar_fresh (elements EvS)}) p q _ _ _) ;

  @frames_on_the_way_to_hole' EvS SvS E (patt_mu ψ') _ _ _ _ _
   := (@frames_on_the_way_to_hole' EvS ({[(svar_fresh (elements SvS))]} ∪ SvS) E (ψ'^{svar: 0 ↦ svar_fresh (elements SvS)}) p q _ _ _)
  .
  Proof.
    all: try (abstract (solve [try_wfauto2])).
    all: simpl in *.
    all: try abstract(lia).
    { rewrite evar_open_size'. abstract(lia). }
    { rewrite svar_open_size'. abstract(lia). }
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

  Lemma frames_on_the_way_to_hole'_app_1 EvS SvS E ψ1 ψ2 p q wfψ1 wfψ wfp wfq :
  (@frames_on_the_way_to_hole' Σ EvS SvS E ψ1 p q wfψ1 wfp wfq)
  ⊆
  (@frames_on_the_way_to_hole' Σ EvS SvS E (ψ1 $ ψ2) p q wfψ wfp wfq).
  Proof.
    simp frames_on_the_way_to_hole'.
    pi_set_solver.
  Qed.

  Lemma frames_on_the_way_to_hole'_app_2 EvS SvS E ψ1 ψ2 p q wfψ2 wfψ wfp wfq:
  (@frames_on_the_way_to_hole' Σ EvS SvS E ψ2 p q wfψ2 wfp wfq)
  ⊆
  (@frames_on_the_way_to_hole' Σ EvS SvS E (ψ1 $ ψ2) p q wfψ wfp wfq).
  Proof.
    simp frames_on_the_way_to_hole'.
    pi_set_solver.
  Qed.

  Lemma frames_on_the_way_to_hole'_imp_1 EvS SvS E ψ1 ψ2 p q wfψ1 wfψ wfp wfq :
  (@frames_on_the_way_to_hole' Σ EvS SvS E ψ1 p q wfψ1 wfp wfq)
  ⊆
  (@frames_on_the_way_to_hole' Σ EvS SvS E (ψ1 ---> ψ2) p q wfψ wfp wfq).
  Proof.
    simp frames_on_the_way_to_hole'.
    (*unfold frames_on_the_way_to_hole'_unfold_clause_7.*)
    pi_set_solver.
  Qed.

  Lemma frames_on_the_way_to_hole'_imp_2 EvS SvS E ψ1 ψ2 p q wfψ2 wfψ wfp wfq:
  (@frames_on_the_way_to_hole' Σ EvS SvS E ψ2 p q wfψ2 wfp wfq)
  ⊆
  (@frames_on_the_way_to_hole' Σ EvS SvS E (ψ1 ---> ψ2) p q wfψ wfp wfq).
  Proof.
    simp frames_on_the_way_to_hole'.
    pi_set_solver.
  Qed.

  Lemma helper_app_lemma Γ ψ1 ψ2 p q E i
    (wfψ1: well_formed ψ1)
    (wfψ2: well_formed ψ2)
    (wfp: well_formed p)
    (wfq: well_formed q)
    (pile: ProofInfoLe ( (
      ExGen := ∅, 
      SVSubst := ∅, 
      KT := false, 
      FP := {[(exist _ (ψ1^[[evar: E ↦ p]]) (well_formed_free_evar_subst_0 E wfp wfψ1))
            ;(exist _ (ψ1^[[evar: E ↦ q]]) (well_formed_free_evar_subst_0 E wfq wfψ1))
            ;(exist _ (ψ2^[[evar: E ↦ p]]) (well_formed_free_evar_subst_0 E wfp wfψ2))
            ;(exist _ (ψ2^[[evar: E ↦ q]]) (well_formed_free_evar_subst_0 E wfq wfψ2))
            ]} )) i )
    (pf₁: Γ ⊢i ψ1^[[evar: E ↦ p]] <---> ψ1^[[evar: E ↦ q]] using i)
    (pf₂: Γ ⊢i ψ2^[[evar: E ↦ p]] <---> ψ2^[[evar: E ↦ q]] using i)
    :
    (Γ ⊢i (ψ1^[[evar: E ↦ p]]) $ (ψ2^[[evar: E ↦ p]]) <---> (ψ1^[[evar: E ↦ q]]) $ (ψ2^[[evar: E ↦ q]]) using i).
  Proof.
    remember (well_formed_free_evar_subst_0 E wfp wfψ1) as Hwf1.
    remember (well_formed_free_evar_subst_0 E wfq wfψ1) as Hwf2.
    remember (well_formed_free_evar_subst_0 E wfp wfψ2) as Hwf3.
    remember (well_formed_free_evar_subst_0 E wfq wfψ2) as Hwf4.

    eapply pf_iff_equiv_trans.
    5: { 
      apply conj_intro_meta.
      4: {
        eapply Framing_right with (ψ := ψ1^[[evar: E ↦ q]]) (wfψ := Hwf2).
        1: { eapply pile_trans. 2: apply pile. try_solve_pile. }
        {
          eapply pf_conj_elim_r_meta in pf₂.
          apply pf₂.
          { abstract (wf_auto2). }
          { abstract (wf_auto2). }
        }
      }
      3: {
        eapply Framing_right with (ψ := ψ1^[[evar: E ↦ q]]) (wfψ := Hwf2).
        1: { eapply pile_trans. 2: apply pile. try_solve_pile. }
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
        apply Framing_left with (ψ := ψ2^[[evar: E ↦ p]]) (wfψ := Hwf3).
        { eapply pile_trans. 2: apply pile. try_solve_pile. }
        {
          eapply pf_conj_elim_r_meta in pf₁.
          apply pf₁.
          { abstract (wf_auto2). }
          { abstract (wf_auto2). }
        }
      }
      3: {
        apply Framing_left with (ψ := ψ2^[[evar: E ↦ p]]) (wfψ := Hwf3).
        { eapply pile_trans. 2: apply pile. try_solve_pile. }
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

  Lemma eq_prf_equiv_congruence
    (sz : nat)
    Γ p q
    (wfp : well_formed p)
    (wfq : well_formed q)
    (EvS : EVarSet)
    (SvS : SVarSet)
    E ψ
    (Hsz: size' ψ <= sz)
    (wfψ : well_formed ψ)
    (p_sub_EvS : (free_evars p) ⊆ EvS)
    (q_sub_EvS : (free_evars q) ⊆ EvS)
    (ψ_sub_EvS : (free_evars ψ) ⊆ EvS)
    (E_in_EvS : E ∈ EvS)
    (p_sub_SvS : (free_svars p) ⊆ SvS)
    (q_sub_SvS : (free_svars q) ⊆ SvS)
    (ψ_sub_SvS : (free_svars ψ) ⊆ SvS)
    (exdepth : nat)
    (mudepth : nat)
    (gpi : ProofInfo)
    (pile : ProofInfoLe
     (
       (ExGen := list_to_set (evar_fresh_seq EvS (maximal_exists_depth_of_evar_in_pattern' exdepth E ψ)),
       SVSubst := list_to_set (svar_fresh_seq SvS (maximal_mu_depth_of_evar_in_pattern' mudepth E ψ)),
       KT := if decide (0 = (maximal_mu_depth_of_evar_in_pattern' mudepth E ψ)) is left _ then false else true,
       FP :=  gset_to_coGset (@frames_on_the_way_to_hole' Σ EvS SvS E ψ p q wfψ wfp wfq)
      )
     )
     ( gpi)
    )
    (pf : Γ ⊢i (p <---> q) using ( gpi)) :
        Γ ⊢i (((ψ^[[evar: E ↦ p]]) <---> (ψ^[[evar: E ↦ q]]))) using ( gpi).
  Proof.

    move: ψ wfψ Hsz EvS SvS pile
      p_sub_EvS q_sub_EvS E_in_EvS ψ_sub_EvS
      p_sub_SvS q_sub_SvS ψ_sub_SvS
    .
    induction sz; intros ψ wfψ Hsz EvS SvS pile
      p_sub_EvS q_sub_EvS E_in_EvS ψ_sub_EvS p_sub_SvS q_sub_SvS ψ_sub_SvS.
    abstract (destruct ψ; simpl in Hsz; lia).  

    lazymatch type of pile with
    | ProofInfoLe ?st _ => set (i' := st) in *
    end.
  
    destruct (decide (E ∈ free_evars ψ)) as [HEinψ|HEnotinψ].
    2: {
      eapply cast_proof'.
      {
        rewrite free_evar_subst_no_occurrence.
        {
          apply count_evar_occurrences_0.
          assumption.
        }
        rewrite free_evar_subst_no_occurrence.
        {
          apply count_evar_occurrences_0.
          assumption.
        }
        reflexivity.
      }
      useBasicReasoning.
      apply pf_iff_equiv_refl.
      { abstract (wf_auto2). }
    }

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
      
      pose proof (pf₁ := (IHsz ψ1) ltac:(assumption) ltac:(assumption)).
      specialize (pf₁ EvS SvS).
      feed specialize pf₁.
      {
        abstract (
          eapply pile_trans;[|apply pile];
          subst i';
        apply pile_evs_svs_kt;
        [
        (
          simpl; clear; pose proof (Htmp := evar_fresh_seq_max); set_solver
        )|
        (
          simpl; clear; pose proof (Htmp := svar_fresh_seq_max); set_solver
        )|
        (
          simpl; clear pf₁;
          repeat case_match; simpl; try reflexivity; lia
        )|(simpl; apply frames_on_the_way_to_hole'_app_1)
        ]).
      }
      { exact p_sub_EvS. }
      { exact q_sub_EvS. }
      { exact E_in_EvS. }
      { abstract(
          simpl in ψ_sub_EvS;
          clear -ψ_sub_EvS;
          set_solver
        ).
      }
      { exact p_sub_SvS. }
      { exact q_sub_SvS. }
      { abstract(
          simpl in ψ_sub_SvS;
          clear -ψ_sub_SvS;
          set_solver
        ).
      }
      pose proof (pf₂ := (IHsz ψ2) ltac:(assumption) ltac:(assumption)).
      specialize (pf₂ EvS SvS).
      feed specialize pf₂.
      {
        abstract (subst i';
          eapply pile_trans;[|(apply pile)];
          simpl;
          apply pile_evs_svs_kt;
          [(simpl; rewrite Nat.max_comm; pose proof (Htmp := evar_fresh_seq_max); set_solver)
          |(rewrite Nat.max_comm; pose proof (Htmp := svar_fresh_seq_max); set_solver)
          |(clear pf₂; repeat case_match; simpl; try reflexivity; try lia)
          |(apply frames_on_the_way_to_hole'_app_2)
          ]
        ).
      }
      { exact p_sub_EvS. }
      { exact q_sub_EvS. }
      { exact E_in_EvS. }
      {
        abstract (
          simpl in ψ_sub_EvS;
          clear -ψ_sub_EvS;
          set_solver
        ).
      }
      { exact p_sub_SvS. }
      { exact q_sub_SvS. }
      { 
        abstract (
          simpl in ψ_sub_SvS;
          clear -ψ_sub_SvS;
          set_solver
        ).
      }

      unshelve (eapply helper_app_lemma); try assumption.
      eapply pile_trans;[|apply pile].
      unfold i'.
      apply pile_evs_svs_kt.
      { clear; set_solver. }
      { clear; set_solver. }
      { reflexivity. }
      {
        simp frames_on_the_way_to_hole'.
        (* This should be automatable! *)
        remember (well_formed_free_evar_subst_0 E wfp wfψ1) as wf1.
        remember (well_formed_free_evar_subst_0 E wfp wfψ2) as wf2.
        remember (well_formed_free_evar_subst_0 E wfq wfψ1) as wf3.
        remember (well_formed_free_evar_subst_0 E wfq wfψ2) as wf4.
        remember (frames_on_the_way_to_hole' EvS SvS E
        (frames_on_the_way_to_hole'_obligation_5 wfψ)
        (frames_on_the_way_to_hole'_obligation_6 wfp)
        (frames_on_the_way_to_hole'_obligation_7 wfq) ∪
      frames_on_the_way_to_hole' EvS SvS E
        (frames_on_the_way_to_hole'_obligation_9 wfψ)
        (frames_on_the_way_to_hole'_obligation_10 wfp)
        (frames_on_the_way_to_hole'_obligation_11 wfq))
        as rest.
        remember (frames_on_the_way_to_hole'_obligation_1 E wfψ wfp) as wf1'.
        remember (frames_on_the_way_to_hole'_obligation_2 E wfψ wfp) as wf2'.
        remember (frames_on_the_way_to_hole'_obligation_3 E wfψ wfq) as wf3'.
        remember (frames_on_the_way_to_hole'_obligation_4 E wfψ wfq) as wf4'.
        clear.
        remember (ψ1^[[evar: E ↦ p]]) as A.
        remember (ψ1^[[evar: E ↦ q]]) as B.
        remember (ψ2^[[evar: E ↦ p]]) as C.
        remember (ψ2^[[evar: E ↦ q]]) as D.
        clear.
        set_unfold.
        intros.
        destruct_or!.
        { left. left. left. left. left. pi_assumption. }
        { left. left. left. right. pi_assumption. }
        { left. left. left. left. right. pi_assumption. }
        { left. left. right. pi_assumption. }
      }
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

      pose proof (pf₁ := (IHsz ψ1) ltac:(assumption) ltac:(assumption)).
      specialize (pf₁ EvS SvS).
      feed specialize pf₁.
      {
        abstract (
          subst i';
          eapply pile_trans;
          [|apply pile];
          apply pile_evs_svs_kt;
          [(simpl; pose proof evar_fresh_seq_max; set_solver)
          |(simpl; pose proof svar_fresh_seq_max; set_solver)
          |(clear pf₁;repeat case_match; simpl; try reflexivity; simpl in *; lia)
          |(apply frames_on_the_way_to_hole'_imp_1)
          ]
        ).
        
      }
      { exact p_sub_EvS. }
      { exact q_sub_EvS. }
      { exact E_in_EvS. }
      {
        abstract (
          simpl in ψ_sub_EvS;
          clear -ψ_sub_EvS;
          set_solver
        ).
      }
      { exact p_sub_SvS. }
      { exact q_sub_SvS. }
      { abstract (
          simpl in ψ_sub_SvS;
          clear -ψ_sub_SvS;
          set_solver
        ).
      }

      pose proof (pf₂ := (IHsz ψ2) ltac:(assumption) ltac:(assumption)).

      specialize (pf₂ EvS SvS).
      feed specialize pf₂.
      {
        abstract (
          subst i';
          eapply pile_trans;
          [|apply pile];
          apply pile_evs_svs_kt;
          [(simpl; rewrite Nat.max_comm; clear; pose proof evar_fresh_seq_max; set_solver)
          |(simpl; rewrite Nat.max_comm; clear; pose proof svar_fresh_seq_max; set_solver)
          |(clear pf₂; repeat case_match; simpl in *; try reflexivity; lia)
          |(apply frames_on_the_way_to_hole'_imp_2)
          ]
        ).
      }
      { exact p_sub_EvS. }
      { exact q_sub_EvS. }
      { exact E_in_EvS. }
      {
        abstract (
          simpl in ψ_sub_EvS;
          clear -ψ_sub_EvS;
          set_solver
        ).
      }
      { exact p_sub_SvS. }
      { exact q_sub_SvS. }
      { 
        abstract (
          simpl in ψ_sub_SvS;
          clear -ψ_sub_SvS;
          set_solver
        ).
      }

      apply prf_equiv_of_impl_of_equiv.
      { abstract (wf_auto2). }
      { abstract (wf_auto2). }
      { abstract (wf_auto2). }
      { abstract (wf_auto2). }
      { apply pf₁. }
      { apply pf₂. }
    }
    {
      pose proof (frx := @set_evar_fresh_is_fresh' Σ EvS).
      remember (evar_fresh (elements EvS)) as x.

      (* there used to be a destruct on whether E is in psi *)

      assert (well_formed (ψ^{evar: 0 ↦ x})) by abstract(wf_auto2).
      assert (size' (ψ^{evar: 0 ↦ x}) <= sz) by abstract(rewrite evar_open_size'; lia).

      pose proof (IH := IHsz (ψ^{evar: 0 ↦ x}) ltac:(assumption) ltac:(assumption)).
      specialize (IH ({[x]} ∪ EvS) SvS).
      feed specialize IH.
      {
        abstract(
          subst i';
          simpl;
          eapply pile_trans;
          [|apply pile];
          assert (HxneE: x <> E);
          [(clear -frx E_in_EvS; set_solver)|];
          apply pile_evs_svs_kt;
          [(
            simpl;
            rewrite medoeip_evar_open;
            [(apply not_eq_sym; exact HxneE)
            |(simpl;
              rewrite medoeip_S_in;
              [(assumption)
              |(remember (maximal_exists_depth_of_evar_in_pattern' exdepth E ψ) as n;
                simpl;
                unfold evar_fresh_s;
                rewrite -Heqx;
                clear;
                set_solver)
              ]
            )]
          )
         |(
            simpl;
            rewrite mmdoeip_evar_open;
            [(apply not_eq_sym; exact HxneE)
            |(apply reflexivity)
            ]
          )
        |(
            clear IH;
            repeat case_match; simpl in *; try reflexivity;
            pose proof (Htmp := n);
            rewrite mmdoeip_evar_open in Htmp;
            [(apply not_eq_sym; exact HxneE)|(lia)]
          )
          |(simp frames_on_the_way_to_hole'; subst x; clear; pi_set_solver)
        ]).
      }
      { clear -p_sub_EvS. abstract (set_solver). }
      { clear -q_sub_EvS. abstract (set_solver). }
      { clear -E_in_EvS. abstract (set_solver). }
      { clear -ψ_sub_EvS.
        abstract (
          rewrite elem_of_subseteq;
          intros x0;
          rewrite free_evars_evar_open'';
          intros [[H1 H2]| H2];
          [
            (subst; clear; set_solver)
            |(simpl in ψ_sub_EvS; set_solver)
          ]
        ).
      }
      { exact p_sub_SvS. }
      { exact q_sub_SvS. }
      { abstract (
          simpl in ψ_sub_SvS;
          clear -ψ_sub_SvS;
          rewrite free_svars_evar_open;
          exact ψ_sub_SvS
        ).
      }
      eapply congruence_ex_helper with (x := x)(EvS := EvS)(SvS := SvS)(exdepth := exdepth)(mudepth := mudepth); try assumption.
      { set_solver. }
      { reflexivity. }
      { eapply pile_trans;[|apply pile].
        unfold i'.
        apply pile_evs_svs_kt.
        { apply reflexivity. }
        { apply reflexivity. }
        { case_match; reflexivity. }
        { clear. set_solver. }
      }
    }
    {
      pose proof (frX := @set_svar_fresh_is_fresh' Σ SvS).
      remember (svar_fresh (elements SvS)) as X.

      simpl in HEinψ.

      assert (well_formed (ψ^{svar: 0 ↦ X}) = true) by (abstract(clear -wfψ;wf_auto2)).
      assert (size' (ψ^{svar: 0 ↦ X}) <= sz) by abstract(rewrite svar_open_size'; lia).
      pose proof (IH := IHsz (ψ^{svar: 0 ↦ X}) ltac:(assumption) ltac:(assumption)).
      specialize (IH EvS ({[X]} ∪ SvS)).
      feed specialize IH.
      {
        abstract (
          subst i';
          eapply pile_trans;
          [|apply pile];
          apply pile_evs_svs_kt;
          [
            (
            simpl;
            rewrite medoeip_svar_open;
            apply reflexivity
            )
          |(
            simpl;
            rewrite mmdoeip_svar_open;
            rewrite mmdoeip_S_in;[exact HEinψ|];
            simpl;
            unfold svar_fresh_s;
            rewrite -HeqX;
            clear;
            set_solver
          )
          |(
            clear IH;
            repeat case_match; simpl in *; try reflexivity;
            pose proof (Htmp := n);
            rewrite mmdoeip_svar_open in Htmp;
            pose proof (Htmp2 := e);
            rewrite mmdoeip_S_in in Htmp2;
            [exact HEinψ|];
            inversion Htmp2
          )
          |(simp frames_on_the_way_to_hole'; subst X; clear; pi_set_solver)]).
      }
      {
        exact p_sub_EvS.
      }
      {
        exact q_sub_EvS.
      }
      {
        exact E_in_EvS.
      }
      {
        abstract (
          rewrite free_evars_svar_open;
          simpl in ψ_sub_EvS;
          apply ψ_sub_EvS
        ).
      }
      {
        clear -p_sub_SvS.
        abstract (set_solver).
      }
      {
        clear -q_sub_SvS.
        abstract (set_solver).
      }
      {
        rewrite elem_of_subseteq.
        intros X'.
        rewrite free_svars_svar_open''.
        intros [[H1 H2]|H1].
        {
          abstract (subst X'; clear; set_solver).
        }
        {
          abstract (
            simpl in ψ_sub_SvS;
            clear -H1 ψ_sub_SvS;
            set_solver
          ).
        }
      }

      apply pf_iff_free_evar_subst_svar_open_to_bsvar_subst_free_evar_subst in IH.
      3: { clear -wfq. abstract (wf_auto2). }
      2: { clear -wfp. abstract (wf_auto2). }

      unshelve (epose proof (IH1 := @pf_iff_proj1 _ _ _ _ _ _ _ IH)).
      { clear -wfψ wfp. abstract (wf_auto2). }
      { clear -wfψ wfq. abstract (wf_auto2). }
      unshelve (epose proof (IH2 := @pf_iff_proj2 _ _ _ _ _ _ _ IH)).
      { clear -wfψ wfp. abstract (wf_auto2). }
      { clear -wfψ wfq. abstract (wf_auto2). }

      eapply pf_iff_mu_remove_svar_quantify_svar_open.
      5: {
        apply pf_iff_split.
        4: {
          apply mu_monotone.
          4: {
            unfold svar_open.
            apply IH2.
          }
          3: {
            abstract (
              clear -ψ_sub_SvS p_sub_SvS frX wfψ wfp;
              wf_auto2;
              simpl in *;
              pose proof (Htmp := @free_svars_free_evar_subst Σ ψ E p);
              clear -Htmp ψ_sub_SvS p_sub_SvS frX;
              set_solver
            ).
          }
          2: {
            abstract (
              clear -ψ_sub_SvS q_sub_SvS frX wfψ wfq;
              wf_auto2;
              simpl in *;
              pose proof (Htmp := @free_svars_free_evar_subst Σ ψ E q);
              clear -Htmp ψ_sub_SvS q_sub_SvS frX;
              set_solver
            ).
          }
          {
            abstract (
              subst i';
              eapply pile_trans;[|apply pile];
              apply pile_evs_svs_kt;
              [(clear; set_solver)
              |(simpl;
                rewrite mmdoeip_S_in;
                [(exact HEinψ)|];
                simpl;
                unfold svar_fresh_s;
                rewrite -HeqX;
                clear;
                set_solver
            )|(repeat case_match; simpl in *; try reflexivity;
            pose proof (Htmp := e);
            rewrite mmdoeip_S_in in Htmp;
            [exact HEinψ|];
            inversion Htmp)|(clear; set_solver)]
            ).
          }
        }
        3: {
          apply mu_monotone.
          4: {
            unfold svar_open.
            apply IH1.
          }
          3: {
            abstract (
              clear -ψ_sub_SvS q_sub_SvS frX wfψ wfq;
              wf_auto2; simpl in *;
              pose proof (Htmp := @free_svars_free_evar_subst Σ ψ E q);
              clear -Htmp ψ_sub_SvS q_sub_SvS frX;
              set_solver
            ).
          }
          2: {
            abstract (
              clear -ψ_sub_SvS p_sub_SvS frX wfψ wfp;
              wf_auto2; simpl in *;
              pose proof (Htmp := @free_svars_free_evar_subst Σ ψ E p);
              clear -Htmp ψ_sub_SvS p_sub_SvS frX;
              set_solver
            ).
          }
          {
            abstract (
              subst i';
              eapply pile_trans;[|apply pile];
              apply pile_evs_svs_kt;
              [(clear; set_solver)
              |(simpl;
                rewrite mmdoeip_S_in;
                [(exact HEinψ)|];
                simpl;
                unfold svar_fresh_s;
                rewrite -HeqX;
                clear;
                set_solver
              )|(repeat case_match; simpl in *; try reflexivity;
              pose proof (Htmp := e);
              rewrite mmdoeip_S_in in Htmp;
              [exact HEinψ|];
              inversion Htmp)|(clear; set_solver)]
            ).
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
            pose proof (Htmp := @free_svars_free_evar_subst Σ ψ E p);
            clear -H Htmp frX ψ_sub_SvS p_sub_SvS;
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
            pose proof (Htmp := @free_svars_free_evar_subst Σ ψ E q);
            clear -H Htmp frX ψ_sub_SvS q_sub_SvS;
            set_solver
          ).
        }
      }
      {
        clear -wfψ wfp.
        abstract (wf_auto2).
      }
      {
        clear -wfψ wfq.
        abstract (wf_auto2).
      }
      {
        abstract (
          pose proof (Htmp := @free_svars_free_evar_subst Σ ψ E p);
          clear -H Htmp frX ψ_sub_SvS p_sub_SvS;
          set_solver
        ).
      }
      {
        abstract (
          pose proof (Htmp := @free_svars_free_evar_subst Σ ψ E q);
          clear -H Htmp frX ψ_sub_SvS q_sub_SvS;
          set_solver
        ).
      }
    }
  Defined.

  Lemma prf_equiv_congruence Γ p q C
    (gpi : ProofInfo)
    (wfp : well_formed p = true)
    (wfq : well_formed q = true)
    (wfC: PC_wf C)
    (pile : ProofInfoLe
     (
       (ExGen := list_to_set (evar_fresh_seq (free_evars (pcPattern C) ∪ free_evars p ∪ free_evars q ∪ {[pcEvar C]}) (maximal_exists_depth_of_evar_in_pattern (pcEvar C) (pcPattern C))),
       SVSubst := list_to_set (svar_fresh_seq (free_svars (pcPattern C) ∪ free_svars p ∪ free_svars q) (maximal_mu_depth_of_evar_in_pattern (pcEvar C) (pcPattern C))),
       KT := if decide (0 = (maximal_mu_depth_of_evar_in_pattern (pcEvar C) (pcPattern C))) is left _ then false else true,
       FP := gset_to_coGset (@frames_on_the_way_to_hole' Σ (free_evars (pcPattern C) ∪ free_evars p ∪ free_evars q ∪ {[pcEvar C]}) (free_svars (pcPattern C) ∪ free_svars p ∪ free_svars q) (pcEvar C) (pcPattern C) p q wfC wfp wfq))
      )
     ( gpi)
    ):
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
    eapply @eq_prf_equiv_congruence
    with (EvS := (free_evars ψ ∪ free_evars p ∪ free_evars q ∪ {[E]}))
         (SvS := (free_svars ψ ∪ free_svars p ∪ free_svars q))
         (exdepth := 0)
         (mudepth := 0)
         (sz := size' ψ)
    .
    { apply reflexivity. }
    { abstract (clear; set_solver). }
    { abstract (clear; set_solver). }
    { abstract (clear; set_solver). }
    { abstract (clear; set_solver). }
    { abstract (clear; set_solver). }
    { abstract (clear; set_solver). }
    { abstract (clear; set_solver). }
    { eapply pile_trans;[|apply pile]. apply pile_refl. }
    { exact Hiff. }
  Defined.

End FOL_helpers.


Lemma prf_equiv_congruence_iter {Σ : Signature} (Γ : Theory) (p q : Pattern) (C : PatternCtx) l
  (wfp : well_formed p)
  (wfq : well_formed q)
  (wfC : PC_wf C)
  (gpi : ProofInfo)
  (pile : ProofInfoLe
  (
    (ExGen := list_to_set (evar_fresh_seq (free_evars (pcPattern C) ∪ free_evars p ∪ free_evars q ∪ {[pcEvar C]}) (maximal_exists_depth_of_evar_in_pattern (pcEvar C) (pcPattern C))),
      SVSubst := list_to_set (svar_fresh_seq (free_svars (pcPattern C) ∪ free_svars p ∪ free_svars q) (maximal_mu_depth_of_evar_in_pattern (pcEvar C) (pcPattern C))),
      KT := if decide (0 = (maximal_mu_depth_of_evar_in_pattern (pcEvar C) (pcPattern C))) is left _ then false else true,
      FP := gset_to_coGset (@frames_on_the_way_to_hole' Σ (free_evars (pcPattern C) ∪ free_evars p ∪ free_evars q ∪ {[pcEvar C]}) (free_svars (pcPattern C) ∪ free_svars p ∪ free_svars q) (pcEvar C) (pcPattern C) p q wfC wfp wfq))  
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
  @mkMLGoal Σ Γ l (emplace C q) ( gpi) ->
  (ProofInfoLe
  (
     (ExGen := list_to_set
                 (evar_fresh_seq
                    (free_evars (pcPattern C) ∪ free_evars p ∪ free_evars q
                     ∪ {[pcEvar C]})
                    (maximal_exists_depth_of_evar_in_pattern 
                       (pcEvar C) (pcPattern C))),
      SVSubst := list_to_set
                   (svar_fresh_seq
                      (free_svars (pcPattern C) ∪ free_svars p
                       ∪ free_svars q)
                      (maximal_mu_depth_of_evar_in_pattern 
                         (pcEvar C) (pcPattern C))),
      KT := (if
              decide
                (0 =
                 maximal_mu_depth_of_evar_in_pattern (pcEvar C) (pcPattern C))
             is left _
             then false
             else true
             ),
      FP := gset_to_coGset (@frames_on_the_way_to_hole' Σ (free_evars (pcPattern C) ∪ free_evars p ∪ free_evars q ∪ {[pcEvar C]}) (free_svars (pcPattern C) ∪ free_svars p ∪ free_svars q) (pcEvar C) (pcPattern C) p q wfC (@extract_wfp Σ Γ p q ( gpi) pf) (@extract_wfq Σ Γ p q ( gpi) pf))
      ))
      ( gpi)) ->
  @mkMLGoal Σ Γ l (emplace C p) ( gpi).
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
  5: apply Hpiffq.
  4: assumption.
  1: apply H.
  1: {
    pose proof (@proved_impl_wf _ _ _ (proj1_sig H)).
    wf_auto2.  
  }
  exact pile.
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
            apply count_evar_occurrences_0;
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
  simpl;
  (* unfold free_evar_subst; *)
  simpl;
  repeat break_match_goal;
  clear_obvious_equalities_2; try contradiction;
  try (solve_fresh_contradictions_2 star);
  (* repeat (rewrite nest_ex_aux_0); *)
  reduce_free_evar_subst_2 star.

(* Returns [n]th matching logic context [C] (of type [PatternCtx]) such that
   [emplace C a = phi].
 *)

 
 Ltac simplify_pile_side_condition_helper star :=
  subst star;
  unfold fresh_evar,evar_fresh_s;
  eapply evar_is_fresh_in_richer';
  [|apply set_evar_fresh_is_fresh'];
  clear; simpl; set_solver.

 Ltac simplify_pile_side_condition star :=
  try apply pile_any;
  cbn;
  simplify_emplace_2 star;
  repeat (rewrite (mmdoeip_notin, medoeip_notin);
  [(simplify_pile_side_condition_helper star)|]);
  simpl;
  repeat (
    lazymatch goal with
    | [H: context [maximal_mu_depth_of_evar_in_pattern' _ _ _] |- _ ]
      => rewrite mmdoeip_notin in H;
         [(simplify_pile_side_condition_helper star)|]
    | [H: context [maximal_exists_depth_of_evar_in_pattern' _ _ _] |- _ ]
      => rewrite medoeip_notin in H;
         [(simplify_pile_side_condition_helper star)|]
    end
  );
  simpl in *;
  try lia;
  try apply pile_any.

Ltac2 Type HeatResult := {
  star_ident : ident ;
  star_eq : ident ;
  pc : constr ;
  ctx : Pattern.context ;
  ctx_pat : constr ;
  equality : ident ;
}.

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
      => let hr : HeatResult := heat atn a p in
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
         | (ltac1:(star |- simplify_pile_side_condition star) (Ltac1.of_ident (hr.(star_ident))))
         ]
    end
  end.

Ltac2 rec constr_to_int (x : constr) : int :=
  match! x with
  | 0 => 0
  | (S ?x') => Int.add 1 (constr_to_int x')
  end.


Tactic Notation "mlRewrite" constr(Hiff) "at" constr(atn) :=
  (let ff := ltac2:(hiff atn |-
                      mlRewrite
                        (Option.get (Ltac1.to_constr(hiff)))
                        (constr_to_int (Option.get (Ltac1.to_constr(atn))))
                   ) in
   ff Hiff atn).

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
    | ((mkNH ?name (! a)) :: ?m) =>
        mlApply name; mlExactn k
    | ((mkNH _ _) :: ?m) => 
        rfindContradictionTo a m k
    | _ => fail
  end.

#[local]
Ltac findContradiction l k:=
    match l with
       | ((mkNH _ ?a) :: ?m) => 
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
  | ((mkNH ?name (?x and ?y)) :: ?m) => 
      mlDestructAnd name
  | ((mkNH ?name (?x or ?y)) :: ?m) => 
      mlDestructOr name
  | ((mkNH ?name ?x) :: ?m)  =>
      breakHyps m
  end.

#[local]
Ltac mlTautoBreak := repeat match goal with
| [ |- @of_MLGoal ?Sgm (@mkMLGoal ?Sgm ?Ctx ?l ?g ?i) ] 
  =>
    lazymatch g with
      | (⊥) =>
              breakHyps l
      | _ => mlApplyMetaRaw (@useBasicReasoning _ _ _ i (@false_implies_everything _ _ g _))
    end
end.

Ltac try_solve_pile2 fallthrough :=
  lazymatch goal with
  | [ |- ProofInfoLe _ _] => try apply pile_refl; try_solve_pile; fallthrough
  | _ => idtac
  end.

#[global]
Ltac mlTauto :=
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