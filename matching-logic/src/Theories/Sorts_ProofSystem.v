From Coq Require Import ssreflect ssrfun ssrbool.

From Ltac2 Require Import Ltac2.

From Coq Require Import String Setoid.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.Classical_Prop.
From Coq.Logic Require Import FunctionalExtensionality Eqdep_dec.
From Coq.Classes Require Import Morphisms_Prop.
From Coq.Unicode Require Import Utf8.
From Coq.micromega Require Import Lia.

From MatchingLogic Require Export Logic ProofMode.MLPM.
From MatchingLogic.Theories Require Export Definedness_Syntax Definedness_ProofSystem Sorts_Syntax FOEquality_ProofSystem.
From MatchingLogic.Utils Require Export stdpp_ext.

Require Export MatchingLogic.wftactics.

From stdpp Require Import base fin_sets sets propset proof_irrel option list.
Import FreshnessManager.
Import extralibrary.

Import MatchingLogic.Logic.Notations.
Import MatchingLogic.Theories.Definedness_Syntax.Notations.

Set Default Proof Mode "Classic".

Require Import MatchingLogic.Theories.DeductionTheorem.

Require MatchingLogic.Theories.Sorts_Syntax.
Export MatchingLogic.Theories.Sorts_Syntax.Notations.

Open Scope ml_scope.
Open Scope string_scope.
Open Scope list_scope.

Set Printing All.


  (* TODO: derive congruence_app with this *)
  Lemma congruence_app1 {Σ : Signature} Γ ψ1 ψ2 p q E i
    (wfψ1: well_formed ψ1)
    (wfψ2: well_formed ψ2)
    (wfp: well_formed p)
    (wfq: well_formed q)
    (pf₁: Γ ⊢i ψ1^[[evar: E ↦ p]] ---> ψ1^[[evar: E ↦ q]] using i)
    (pf₂: Γ ⊢i ψ2^[[evar: E ↦ p]] ---> ψ2^[[evar: E ↦ q]] using i)
    :
    (Γ ⊢i (ψ1^[[evar: E ↦ p]]) $ (ψ2^[[evar: E ↦ p]]) ---> (ψ1^[[evar: E ↦ q]]) $ (ψ2^[[evar: E ↦ q]]) using i).
  Proof.
    remember (well_formed_free_evar_subst_0 E _ _ wfp wfψ1) as Hwf1.
    remember (well_formed_free_evar_subst_0 E _ _ wfq wfψ1) as Hwf2.
    remember (well_formed_free_evar_subst_0 E _ _ wfp wfψ2) as Hwf3.
    remember (well_formed_free_evar_subst_0 E _ _ wfq wfψ2) as Hwf4.
    eapply syllogism_meta.
    4: {
      eapply Framing_right; auto. try_solve_pile.
      apply pf₂.
    }
    1-3: wf_auto2.
    eapply Framing_left; auto. try_solve_pile.
  Defined.

  (* TODO: overwrite with this *)
  Lemma framing_left_under_tot_impl {Σ : Signature} {syntax : Definedness_Syntax.Syntax} Γ ψ phi1 phi2 psi x i:
    well_formed ψ = true ->
    well_formed phi1 = true ->
    well_formed phi2 = true ->
    well_formed psi = true ->
    theory ⊆ Γ ->
    x ∉ free_evars ψ ∪ free_evars psi ->
    ProofInfoLe (ExGen := {[ev_x; x]}, SVSubst := ∅, KT := false, AKT := false) i ->
    Γ ⊢i ⌊ ψ ⌋ ---> phi1 ---> phi2 using i->
    Γ ⊢i ⌊ ψ ⌋ ---> (phi1 $ psi) ---> (phi2 $ psi) using i
  .
  Proof.
    intros Hwfψ Hwfphi1 Hwfphi2 Hwfpsi HΓ HIn HPile H.
    assert (S2: Γ ⊢i phi1 ---> (phi2 or ⌈ ! ψ ⌉) using i).
    { toMLGoal.
      { wf_auto2. }
      mlAdd H as "H". mlIntro "Hphi1".
      mlClassic (⌈ ! ψ ⌉) as "Hcl1" "Hcl2".
      { wf_auto2. }
      - mlRight. mlExact "Hcl1".
      - mlLeft.
        mlApply "H".
        mlSplitAnd.
        { mlExact "Hcl2". }
        { mlExact "Hphi1". }
    }

    assert (S3: Γ ⊢i (⌈ ! ψ ⌉ $ psi) ---> ⌈ ! ψ ⌉ using i).
    {
      replace (⌈ ! ψ ⌉ $ psi)
        with (subst_ctx (ctx_app_l AC_patt_defined psi ltac:(assumption)) (! ψ))
        by reflexivity.
      gapply (in_context_impl_defined _ _ _ x).
      4: { wf_auto2. }
      2: { exact HΓ. }
      1: { assumption. }
      set_solver.
    }

    assert (S4: Γ ⊢i (phi1 $ psi) ---> ((phi2 or ⌈ ! ψ ⌉) $ psi) using i).
    {
      unshelve (eapply Framing_left).
      { wf_auto2. }
      { try_solve_pile. }
      { exact S2. }
    }

    assert (S5: Γ ⊢i (phi1 $ psi) ---> ((phi2 $ psi) or (⌈ ! ψ ⌉ $ psi)) using i).
    {
      pose proof (Htmp := prf_prop_or_iff Γ (ctx_app_l box psi ltac:(assumption)) phi2 (⌈! ψ ⌉)).
      ospecialize* Htmp.
      { wf_auto2. }
      { wf_auto2. }
      simpl in Htmp.
      apply pf_iff_proj1 in Htmp.
      3: { wf_auto2. }
      2: { wf_auto2. }
      eapply syllogism_meta.
      5: {
        gapply Htmp.
        try_solve_pile.
      }
      4: { exact S4. }
      all: wf_auto2.
    }

    assert (S6: Γ ⊢i ((phi2 $ psi) or (⌈ ! ψ ⌉ $ psi)) ---> ((phi2 $ psi) or (⌈ ! ψ ⌉)) using i).
    {
      toMLGoal.
      { wf_auto2. }
      mlIntro "H". mlAdd S3 as "S3".
      mlClassic (phi2 $ psi) as "Hc1" "Hc2".
      { wf_auto2. }
      - mlLeft. mlExact "Hc1".
      - mlRight. mlApply "S3". mlApply "H". mlExact "Hc2".
    }

    assert (S7: Γ ⊢i (phi1 $ psi) ---> ((phi2 $ psi)  or ⌈ ! ψ ⌉) using i).
    {
      toMLGoal.
      { wf_auto2. }
      mlAdd S5 as "S5".
      mlAdd S6 as "S6".
      mlIntro "H".
      mlAssert ("Ha" : ((phi2 $ psi) or (⌈ ! ψ ⌉ $ psi))).
      { wf_auto2. }
      { mlApply "S5". mlExact "H". }
      mlDestructOr "Ha" as "Ha1" "Ha2".
      - mlLeft. mlExact "Ha1".
      - mlApply "S6". mlRight. mlExact "Ha2".
    }

    toMLGoal.
    { wf_auto2. }
    mlIntro "H1".
    mlIntro "H2".
    mlAdd S7 as "S7".
    mlAssert ("Ha" : (phi2 $ psi or ⌈ ! ψ ⌉)).
    { wf_auto2. }
    { mlApply "S7". mlExact "H2". }
    mlDestructOr "Ha" as "Ha1" "Ha2".
    { mlExact "Ha1". }
    { mlAssert ("Ha'" : (phi2 $ psi or ⌈ ! ψ ⌉)).
      { wf_auto2. }
      { mlApply "S7". mlExact "H2". }
      mlClassic (phi2 $ psi) as "Hc1" "Hc2".
      { wf_auto2. }
      { mlExact "Hc1". }
      {
        mlExFalso.
        mlApply "H1".
        mlExact "Ha2".
      }
    }
  Defined.

  (* TODO: overwrite with this *)
  Lemma framing_right_under_tot_impl {Σ : Signature} {syntax : Definedness_Syntax.Syntax} Γ ψ phi1 phi2 psi x i:
    well_formed ψ = true ->
    well_formed phi1 = true ->
    well_formed phi2 = true ->
    well_formed psi = true ->
    theory ⊆ Γ ->
    x ∉ free_evars ψ ∪ free_evars psi ->
    ProofInfoLe (ExGen := {[ev_x; x]}, SVSubst := ∅, KT := false, AKT := false) i ->
    Γ ⊢i ⌊ ψ ⌋ ---> phi1 ---> phi2 using i->
    Γ ⊢i ⌊ ψ ⌋ ---> (psi $ phi1) ---> (psi $ phi2) using i
  .
  Proof.
    intros Hwfψ Hwfphi1 Hwfphi2 Hwfpsi HΓ HIn HPile H.
    assert (S2: Γ ⊢i phi1 ---> (phi2 or ⌈ ! ψ ⌉) using i).
    { toMLGoal.
      { wf_auto2. }
      mlAdd H as "H". mlIntro "Hphi1".
      mlClassic (⌈ ! ψ ⌉) as "Hc1" "Hc2".
      { wf_auto2. }
      - mlRight. mlExact "Hc1".
      - mlLeft.
        mlApply "H".
        mlSplitAnd.
        { mlExact "Hc2". }
        { mlExact "Hphi1". }
    }

    assert (S3: Γ ⊢i (psi $ ⌈ ! ψ ⌉) ---> ⌈ ! ψ ⌉ using i).
    {
      replace (psi $ ⌈ ! ψ ⌉)
      with (subst_ctx (ctx_app_r psi AC_patt_defined ltac:(assumption)) (! ψ))
        by reflexivity.
      gapply (in_context_impl_defined _ _ _ x).
      4: { wf_auto2. }
      2: { exact HΓ. }
      1: { assumption. }
      set_solver.
    }

    assert (S4: Γ ⊢i (psi $ phi1) ---> (psi $ (phi2 or ⌈ ! ψ ⌉)) using i).
    { 
      unshelve (eapply Framing_right).
      { wf_auto2. }
      2: exact S2.
      try_solve_pile.
    }

    assert (S5: Γ ⊢i (psi $ phi1) ---> ((psi $ phi2) or (psi $ ⌈ ! ψ ⌉)) using i).
    {
      pose proof (Htmp := prf_prop_or_iff Γ (ctx_app_r psi box ltac:(assumption)) phi2 (⌈! ψ ⌉)).
      ospecialize* Htmp.
      { wf_auto2. }
      { wf_auto2. }
      simpl in Htmp.
      apply pf_iff_proj1 in Htmp.
      2,3: wf_auto2.
      eapply syllogism_meta.
      5: gapply Htmp; try_solve_pile.
      1-3: wf_auto2.
      exact S4.
    }

    assert (S6: Γ ⊢i ((psi $ phi2) or (psi $ ⌈ ! ψ ⌉)) ---> ((psi $ phi2) or (⌈ ! ψ ⌉)) using i).
    {
      toMLGoal.
      { wf_auto2. }
      mlIntro "H1". mlAdd S3 as "S3".
      mlClassic (psi $ phi2) as "Hc1" "Hc2".
      { wf_auto2. }
      - mlLeft. mlExact "Hc1".
      - mlRight. mlApply "S3". mlApply "H1". mlExact "Hc2".
    }

    assert (S7: Γ ⊢i (psi $ phi1) ---> ((psi $ phi2)  or ⌈ ! ψ ⌉) using i).
    {
      toMLGoal.
      { wf_auto2. }
      mlAdd S5 as "S5". mlAdd S6 as "S6". mlIntro "H".
      (* TODO: a tactic mlFeedImpl *)
      mlAssert ("Ha" : ((psi $ phi2) or (psi $ ⌈ ! ψ ⌉))).
      { wf_auto2. }
      { mlApply "S5". mlExact "H". }
      mlDestructOr "Ha" as "Ha1" "Ha2".
      - mlLeft. mlExact "Ha1".
      - mlApply "S6". mlRight. mlExact "Ha2".
    }

    toMLGoal.
    { wf_auto2. }
    mlIntro "H1".
    mlIntro "H2".
    mlAdd S7 as "S7".
    mlAssert ("Ha" : (psi $ phi2 or ⌈ ! ψ ⌉)).
    { wf_auto2. }
    { mlApply "S7". mlExact "H2". }
    mlDestructOr "Ha" as "Ha1" "Ha2".
    { mlExact "Ha1". }
    + mlAssert ("Ha'" : (psi $ phi2 or ⌈ ! ψ ⌉)).
      { wf_auto2. }
      { mlApply "S7". mlExact "H2". }
      mlClassic (psi $ phi2) as "Hc1" "Hc2".
      { wf_auto2. }
      { mlExact "Hc1". }
      {
        mlExFalso.
        mlApply "H1".
        mlExact "Ha2".
      }
  Defined.

  (* TODO: delete this *)
  Lemma patt_equal_sym {Σ : Signature} {syntax : Definedness_Syntax.Syntax} Γ φ1 φ2 i:
    theory ⊆ Γ ->
    well_formed φ1 -> well_formed φ2 ->
    ProofInfoLe BasicReasoning i ->
    Γ ⊢i φ1 =ml φ2 ---> φ2 =ml φ1
    using i.
  Proof.
    intros.
    apply floor_monotonic; auto.
    mlIntro. mlDestructAnd "0". mlSplitAnd; mlAssumption.
  Defined.

  Lemma move_mu_under_implication
    {Σ : Signature}
    Γ φ ψ :
      well_formed φ ->
      well_formed (mu , ψ) ->
      Γ ⊢i φ ---> (mu , ψ) ---> mu , (φ ---> ψ) using
        (ExGen := ∅,
         SVSubst := ∅,
         KT := true,
         AKT := ~~ bound_svar_is_banned_under_mus ψ 0 0).
  Proof.
    intros.
    assert (no_positive_occurrence_db_b 0 φ). {
    (* TODO: wf_auto2 breaks without this assert later! *)
      wf_auto2.
    }
    do 2 mlIntro.
    mlApplyMeta (Knaster_tarski Γ ψ (mu, φ ---> ψ)) in "1".
    2: {
      toMLGoal. {
        wf_auto2.
      }
      mlIntro; mlApplyMeta Pre_fixp. simpl.
      mlIntro. mlAssumption.
    }
    mlAssumption.
  Defined.

  Lemma move_mu_under_conj
    {Σ : Signature}
    Γ φ ψ :
      well_formed φ ->
      well_formed (mu , ψ) ->
      Γ ⊢i φ and (mu , ψ) ---> mu , (φ and ψ) using
        (ExGen := ∅,
         SVSubst := ∅,
         KT := true,
         AKT := ~~ bound_svar_is_banned_under_mus ψ 0 0).
  Proof.
    intros.
    assert (no_positive_occurrence_db_b 0 φ). {
    (* TODO: wf_auto2 breaks without this assert later! *)
      wf_auto2.
    }
    assert (no_negative_occurrence_db_b 0 φ). {
    (* TODO: wf_auto2 breaks without this assert later! *)
      wf_auto2.
    }
    toMLGoal. wf_auto2.
    mlIntro. mlDestructAnd "0".
    
    mlApplyMeta Pre_fixp. unfold instantiate. mlSimpl.
    rewrite bsvar_subst_not_occur. wf_auto2. mlSplitAnd. mlAssumption.
    mlApplyMeta (Knaster_tarski Γ ψ (ψ^[svar:0↦mu , φ and ψ])) in "2".
    mlAssumption.
    simpl.
    mlIntro.
    Check PreFixp.
  Qed.

(*  eq-elim.0 $e #Substitution ph2 ph4 ph0 x $.   => ph2 = ph4[ph0/x]
    eq-elim.1 $e #Substitution ph3 ph4 ph1 x $.   => ph3 = ph4[ph1/x]
    eq-elim $a |- ( \imp ( \eq ph0 ph1 ) ( \imp ph2 ph3 ) ) $.
                                                  => ph0 = ph1 -> ph2 -> ph3
 *)
Lemma equality_elimination_basic 
  {Σ : Signature}
  {sy : Definedness_Syntax.Syntax}
  Γ φ1 φ2 C x (xs : EVarSet) X
  (HΓ : theory ⊆ Γ)
  (WF1 : well_formed φ1)
  (WF2 :  well_formed φ2)
  (WFC : PC_wf C)
  (Hfree : {[ev_x; x]} ∪ free_evars φ1 ∪ free_evars φ2 ∪ free_evars (pcPattern C) ## xs)
  (Hfree2 : x ∉ free_evars φ1 ∪ free_evars φ2 ∪ free_evars (pcPattern C))
  (* (Hfree3 : x ∉ free_svars ) *)
  (Henough : size xs >= maximal_exists_depth_to 0 (pcEvar C) (pcPattern C)):
(*   mu_free (pcPattern C) -> *)
  Γ ⊢i (φ1 =ml φ2) --->
    (emplace C φ1) ---> (emplace C φ2)
  using (ExGen := {[ev_x; x]} ∪ coGset.gset_to_coGset xs,
         SVSubst := {[X]},
         KT := false,
         AKT := false).
Proof.
  Print maximal_exists_depth_to.
  destruct C as [y φ4]. cbn in *.
  assert (well_formed φ4) by wf_auto2. clear WFC.
  remember (size' φ4) as sz.
  assert (size' φ4 <= sz) by lia. clear Heqsz.
  revert φ4 φ1 φ2 xs x X Γ HΓ H0 H WF1 WF2 Hfree Hfree2 Henough. induction sz; intros.
  {
    destruct φ4; simpl in H0; lia.
  }
  destruct φ4; simpl in *.
  * case_match.
    - subst. rewrite decide_eq_same.
      mlIntro "H".
      mlApplyMeta total_phi_impl_phi in "H".
      mlDestructAnd "H".
      mlAssumption.
      3: wf_auto2.
      1: instantiate (1 := x).
      try_solve_pile.
      set_solver.
    - rewrite decide_False. by auto.
      rewrite decide_False. by auto.
      do 2 mlIntro. mlAssumption.
  * do 2 mlIntro. mlAssumption.
  * do 2 mlIntro. mlAssumption.
  * do 2 mlIntro. mlAssumption.
  * do 2 mlIntro. mlAssumption.
  * mlIntro "H".
    epose proof (IH1 := IHsz φ4_1 φ1 φ2 xs x X Γ HΓ ltac:(lia) ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2) _ ltac:(set_solver) ltac:(lia)).
    epose proof (IH2 := IHsz φ4_2 φ1 φ2 xs x X Γ HΓ ltac:(lia) ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2) _ ltac:(set_solver) ltac:(lia)).
    clear IHsz.
    mlAssert ("H2" : (φ1 =ml φ2)). wf_auto2. mlAssumption.
    eapply framing_left_under_tot_impl with (x := x) in IH1.
    eapply framing_right_under_tot_impl with (x := x) in IH2.
    mlApplyMeta IH1 in "H".
    mlApplyMeta IH2 in "H2".
    mlIntro "H0".
    mlApply "H".
    mlApply "H2".
    mlAssumption.
    5, 12: assumption.
    6, 12: try_solve_pile.
    1-4,6-9: wf_auto2.
    1-2: clear -Hfree2; pose proof free_evars_free_evar_subst; set_solver.
    Unshelve.
    - clear -Hfree.
      apply disjoint_union_l in Hfree as [HF1 HF2].
      apply disjoint_union_l in HF1 as [H ?], HF2 as [? ?].
      apply disjoint_union_l in H as [? ?].
      set_solver.
    - clear -Hfree.
      apply disjoint_union_l in Hfree as [HF1 HF2].
      apply disjoint_union_l in HF1 as [H ?], HF2 as [? ?].
      apply disjoint_union_l in H as [? ?].
      set_solver.
  * do 2 mlIntro. mlAssumption.
  * mlIntro "H".
    epose proof (IH1 := IHsz φ4_1 φ2 φ1 xs x X Γ HΓ ltac:(lia) ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2) _ ltac:(set_solver) ltac:(lia)).
    epose proof (IH2 := IHsz φ4_2 φ1 φ2 xs x X Γ HΓ ltac:(lia) ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2) _ ltac:(set_solver) ltac:(lia)).
    clear IHsz.
    mlAssert ("H2" : (φ2 =ml φ1)). wf_auto2.
    {
      mlApplyMeta patt_equal_sym. mlAssumption. assumption.
    }
    mlApplyMeta IH1 in "H2".
    mlApplyMeta IH2 in "H".
    mlIntro "H0". mlIntro "S".
    clear. mlApply "H". mlApply "H0". mlApply "H2". mlAssumption.
    Unshelve.
    - clear -Hfree.
      apply disjoint_union_l in Hfree as [HF1 HF2].
      apply disjoint_union_l in HF1 as [H ?], HF2 as [? ?].
      apply disjoint_union_l in H as [? ?].
      set_solver.
    - clear -Hfree.
      apply disjoint_union_l in Hfree as [HF1 HF2].
      apply disjoint_union_l in HF1 as [H ?], HF2 as [? ?].
      apply disjoint_union_l in H as [? ?].
      set_solver.
  * mlIntro.
    mlIntro.
    destruct (decide (y ∈ free_evars φ4)).
    2: {
      rewrite free_evar_subst_no_occurrence. assumption.
      rewrite free_evar_subst_no_occurrence. assumption.
      mlAssumption.
    }
    rewrite maximal_exists_depth_to_S in Henough. assumption.
    destruct (elements xs) eqn:Hel.
    {
      apply elements_empty_iff in Hel. apply leibniz_equiv in Hel.
      subst. rewrite size_empty in Henough. lia.
    }
    rename e0 into z.
    (* TODO: extract this, very technical *)
    assert (xs = {[z]} ∪ list_to_set l). {
      rewrite <- (list_to_set_cons z l).
      clear-Hel.
      rewrite <- list_to_set_elements_L at 1.
      by rewrite Hel.
    }
    assert (z ∉ l /\ z <> y) as HZ. {
      split.
      pose proof (HND := NoDup_elements xs).
      clear -Hel HND.
      rewrite Hel in HND. inversion HND. set_solver.
      set_solver.
    }
    subst xs.
    assert (z ∉ free_evars φ1 ∪ free_evars φ2 ∪ free_evars φ4). {
      clear-Hfree. apply disjoint_union_r in Hfree. set_solver.
    }
    (* TODO
       manually applied mlDestructEx, because it does not automatically solve the
       side conditions, thus fails *)
    _mlReshapeHypsByName "1".
    apply MLGoal_destructEx with (x := z). try_solve_pile.
    1-4: cbn; clear-H1.
    1-2: set_solver.
    1-2: pose proof free_evars_free_evar_subst; set_solver.
    (* *** *)
    simpl. mlExists z.
    opose proof* (IHsz (evar_open z 0 φ4) φ1 φ2 (list_to_set l) x X Γ HΓ).
    2-4: wf_auto2.
    1: rewrite evar_open_size'; lia.
    - clear -Hfree e HZ.
      pose proof free_evars_evar_open φ4 z 0.
      repeat apply disjoint_union_r in Hfree as [Hfree ?].
      repeat apply disjoint_union_l in Hfree as [Hfree ?].
      repeat apply disjoint_union_l in H0 as [H0 ?].
      repeat (apply disjoint_union_l; split); try assumption.
      clear -H5 H HZ. set_solver.
    - pose proof free_evars_evar_open φ4 z 0.
      clear-Hfree2 Hfree H2.
      repeat apply disjoint_union_r in Hfree as [Hfree _].
      do 3 apply disjoint_union_l in Hfree as [Hfree _].
      apply disjoint_union_l in Hfree as [_ Hfree].
      set_solver.
    - rewrite evar_open_exists_depth.
      set_solver.
      rewrite size_union in Henough. set_solver.
      rewrite size_singleton in Henough. lia.
    - rewrite evar_open_free_evar_subst_swap. apply HZ. wf_auto2.
      rewrite evar_open_free_evar_subst_swap. apply HZ. wf_auto2.
      use (ExGen := coGset.FinGSet ({[ev_x; x]} ∪ ({[z]} ∪ list_to_set l)),
       SVSubst := {[X]}, KT := false, AKT := false) in H2.
      mlApplyMeta H2. mlSplitAnd; mlAssumption.
  * do 2 mlIntro.
    Search patt_or derives_using.
    Print is_predicate_pattern.
    Search is_predicate_pattern.
    (*
      new idea:
      1. prove Γ ⊢ is_predicate (φ = ψ) -> Γ ⊢ φ = ⊤ or φ = ⊥   (maybe with <--->)
                                                                (maybe with meta-or)
      2. do case separation based on 1.
        a) if φ = ⊥, then contradiction
        b) if φ = ⊤, then it can be eliminated from IHsz, also from the goal.
           then use mu_monotone
    *)
  
  
    Search derives_using (_ ---> _ ---> _).
    Check prf_equiv_congruence.
    Search is_predicate_pattern derives_using.
    opose proof* (IHsz (svar_open X 0 φ4) φ1 φ2 xs x X Γ HΓ) as IHsz.
    1-7: admit.
    pose proof (move_mu_under_implication Γ (φ1 =ml φ2) (φ4^[[evar:y↦φ1]])
      ltac:(wf_auto2) ltac:(wf_auto2)).
    (** TODO ***)
    replace (ExGen := ∅ : coEVarSet, SVSubst := ∅ : coSVarSet, KT := true,
            AKT := ~~ bound_svar_is_banned_under_mus φ4^[[evar:y↦φ1]] 0 0) with
      (ExGen := coGset.FinGSet ({[ev_x; x]} ∪ xs), SVSubst := {[X]}, KT := false,
       AKT := false) in H1.
    (****)
    mlAssert ("H" : ((mu , φ1 =ml φ2 ---> φ4^[[evar:y↦φ1]]))). { admit. }
    {
      mlApplyMeta H1. mlSplitAnd; mlAssumption.
    }
    
    mlApplyMeta H1 in "0".
    mlApply "0" in "1".
    mlClear "0".
    fromMLGoal. clear H1.
    replace ((mu , φ1 =ml φ2 ---> φ4^[[evar:y↦φ1]]) ---> (mu , φ4^[[evar:y↦φ2]]))
      with
      ((mu , (φ1 =ml φ2 ---> φ4^[[evar:y↦φ1]])^{svar:0↦X}^{{svar:X↦0}}) ---> (mu , φ4^[[evar:y↦φ2]]^{svar:0↦X}^{{svar:X↦0}})).
    2: {
      admit.
    }
    apply mu_monotone.
    - admit.
    - apply svar_hno_bsvar_subst.
      + intro HH. cbn in HH. congruence.
      + intros. wf_auto2.
        all: try apply wfc_impl_no_neg_occ; try apply wfc_impl_no_pos_occ.
        all: wf_auto2.
      + intros. apply fresh_svar_no_neg. admit.
    - apply svar_hno_bsvar_subst.
      + intro HH. cbn in HH. congruence.
      + intros. wf_auto2.
        all: try apply wfc_impl_no_neg_occ; try apply wfc_impl_no_pos_occ.
        all: wf_auto2.
      + intros. apply fresh_svar_no_neg. admit.
    - mlSimpl.
      rewrite (svar_open_not_occur 0 X φ1). wf_auto2.
      rewrite (svar_open_not_occur 0 X φ2). wf_auto2.
      unfold svar_open.
      rewrite <- free_evar_subst_bsvar_subst.
      rewrite <- free_evar_subst_bsvar_subst.
      2,4:wf_auto2.
      2-3: unfold evar_is_fresh_in; set_solver.
      fold (svar_open X 0 φ4).
      
      apply IHsz.
Defined.


Local Lemma simplTest
  {Σ : Signature}
  {syntax : Sorts_Syntax.Syntax}
  (Γ : Theory)
  (φ ψ τ: Pattern)
  (s : symbols) x:
  well_formed (ex , φ) ->
  well_formed ψ ->
  well_formed τ ->
  Definedness_Syntax.theory ⊆ Γ ->
  Γ ⊢ ((all ψ , φ) ---> ex ψ ,  φ)^[[evar:x↦τ]].
Proof.
  intros. mlSimpl. mlSortedSimpl. mlSortedSimpl. mlSimpl.
  remember (fresh_evar (ψ $ φ $ τ)) as y.
  mlIntro.
  mlSpecialize "0" with x.
  mlExists x.
Abort.

Lemma ex_sort_impl_ex
  {Σ : Signature}
  {syntax : Sorts_Syntax.Syntax}
  (Γ : Theory)
  (ϕ : Pattern)
  (s : symbols)
  :
  well_formed (ex , ϕ) ->
  Definedness_Syntax.theory ⊆ Γ ->
  Γ ⊢ (ex (patt_sym s) , ϕ) ---> (ex , ϕ).
Proof.
  intros wfϕ HΓ.

  unfold "ex _ , _".

  unfold nest_ex; simpl.

  remember (fresh_evar (b0 ∈ml 〚 patt_sym s 〛 and ϕ)) as x.
  rewrite <- evar_quantify_evar_open with (n := 0) (x := x) (phi := b0 ∈ml 〚 patt_sym s 〛 and ϕ).
  2: {
    subst x. eapply evar_is_fresh_in_richer'.
    2: apply set_evar_fresh_is_fresh'.
    clear. set_solver.
  }
  2: {
    wf_auto2.
  }

  gapply BasicProofSystemLemmas.Ex_gen.
  { apply pile_any. }
  { apply pile_any. }
  {
    subst x. eapply evar_is_fresh_in_richer'.
    2: { apply set_evar_fresh_is_fresh'. }
    clear. set_solver.
  }

  mlSimpl. unfold evar_open. simpl.

  toMLGoal.
  { wf_auto2. }
  mlIntro "H".
  mlDestructAnd "H" as "H0" "H1".
  mlClear "H0".

  mlApplyMeta BasicProofSystemLemmas.Ex_quan. simpl.
  mlExact "H1".
Defined.

Theorem top_includes_everything {Σ : Signature} {syntax : Sorts_Syntax.Syntax}:
  ∀ (Γ : Theory) (x : evar),
  Definedness_Syntax.theory ⊆ Γ -> 
  Γ ⊢i patt_free_evar x  ∈ml patt_top using AnyReasoning.
Proof.
  intros.
  pose proof proved_membership_functional Γ (patt_top) (patt_free_evar x) ltac:(set_solver) ltac:(wf_auto2) ltac:(wf_auto2).
  mlApplyMeta H0.
  * unfold  is_functional.
    mlExists x.
    mlSimpl. cbn.
    mlReflexivity.
  * pose proof top_holds Γ.
    use AnyReasoning in H1.
    mlExactMeta H1.
Defined.

Close Scope ml_scope.
Close Scope string_scope.
Close Scope list_scope.