From Coq Require Import ssreflect ssrfun ssrbool.

From Ltac2 Require Import Ltac2.

Require Import Equations.Prop.Equations.

From Coq Require Import String Ensembles Setoid.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.Classical_Prop.
From Coq.Logic Require Import FunctionalExtensionality Eqdep_dec.
From Coq.Classes Require Import Morphisms_Prop.
From Coq.Unicode Require Import Utf8.
From Coq.micromega Require Import Lia.

From stdpp Require Import base fin_sets sets propset proof_irrel option list coGset finite infinite gmap.

From MatchingLogic Require Import Logic ProofMode.MLPM.
From MatchingLogic.Theories Require Import Definedness_Syntax.
From MatchingLogic.Utils Require Import stdpp_ext.
Import extralibrary.

Import MatchingLogic.Logic.Notations.
Import MatchingLogic.DerivedOperators_Syntax.Notations.
Import MatchingLogic.Syntax.BoundVarSugar.

Set Default Proof Mode "Classic".

Close Scope equations_scope. (* Because of [!] *)

Import Notations.

Section ProofSystemTheorems.

Context
  {Σ : Signature}
  {syntax : Syntax}
.


Definition defFP : coWfpSet := {[(exist (λ p, well_formed p = true) (patt_sym (Definedness_Syntax.inj definedness)) erefl)]}. 

Lemma phi_impl_total_phi_meta Γ φ i:
  well_formed φ ->
  ProofInfoLe BasicReasoning i -> 
  Γ ⊢i φ using i ->
  Γ ⊢i ⌊ φ ⌋ using i.
Proof.
  intros wfφ pile Hφ.
  pose proof (ANNA := A_implies_not_not_A_ctx Γ (φ) AC_patt_defined).
  apply ANNA.
  { simpl. try_solve_pile. }
  { apply wfφ. }
  exact Hφ.
Defined.

Lemma patt_iff_implies_equal :
  forall (φ1 φ2 : Pattern) Γ i,
    well_formed φ1 ->
    well_formed φ2 ->
    ProofInfoLe BasicReasoning i ->
    Γ ⊢i (φ1 <---> φ2) using i ->
    Γ ⊢i φ1 =ml φ2 using i .
Proof.
  intros φ1 φ2 Γ i WF1 WF2 pile H.
  pose proof (ANNA := A_implies_not_not_A_ctx Γ (φ1 <---> φ2) AC_patt_defined).
  apply ANNA.
  { eapply pile_trans;[|apply pile]. try_solve_pile. }
  { wf_auto2. }
  { exact H. }
Defined.

Lemma patt_equal_refl :
  forall φ Γ,
  well_formed φ ->
  Γ ⊢i φ =ml φ
  using BasicReasoning.
Proof.
  intros φ Γ WF. pose proof (IFF := pf_iff_equiv_refl Γ φ WF).
  eapply useBasicReasoning in IFF.
  apply patt_iff_implies_equal in IFF.
  { apply IFF. }
  { exact WF. }
  { exact WF. }
  { apply pile_refl. }
Qed.

Lemma use_defined_axiom Γ:
  theory ⊆ Γ ->
  Γ ⊢i patt_defined p_x
  using BasicReasoning.
Proof.
  intros HΓ.
  apply BasicProofSystemLemmas.hypothesis; auto. unfold theory,theory_of_NamedAxioms in HΓ. simpl in HΓ.
  eapply elem_of_weaken.
  2: { apply HΓ. }
  unfold axiom.
  apply elem_of_PropSet.
  exists AxDefinedness.
  reflexivity.
Defined.

Definition BasicReasoningWithDefinedness := (ExGen := {[ev_x]}, SVSubst := ∅, KT := false, AKT := false).

Lemma defined_evar Γ x:
  theory ⊆ Γ ->
  Γ ⊢i ⌈ patt_free_evar x ⌉
  using  (ExGen := {[ev_x]}, SVSubst := ∅, KT := false, AKT := false).
Proof.
  intros HΓ.
  assert(S1: Γ ⊢i patt_defined p_x using BasicReasoningWithDefinedness).
  {
    useBasicReasoning.
    apply use_defined_axiom.
    apply HΓ.
  }

  apply universal_generalization with (x := ev_x) in S1 as S1'.
  3: { wf_auto2. }
  2: { try_solve_pile. }
  eapply MP.
  exact S1'.
  simpl in S1'. case_match. 2: congruence.
  toMLGoal. case_match. 2: congruence. wf_auto2.
  mlIntro "H".
  mlSpecialize "H" with x.
  mlSimpl. simpl. case_match. 2: congruence.
  mlAssumption.
Defined.
  
Lemma in_context_impl_defined Γ AC φ x:
  theory ⊆ Γ ->
  x ∉ (free_evars φ ∪ AC_free_evars AC) ->
  well_formed φ ->
  Γ ⊢i (subst_ctx AC φ) ---> ⌈ φ ⌉
  using  (ExGen := {[ev_x]} ∪ {[x]}, SVSubst := ∅, KT := false, AKT := false).
Proof.
  intros HΓ Hx Hwfφ.
  assert(S1: Γ ⊢i patt_defined p_x using BasicReasoning).
  {
    apply use_defined_axiom.
    apply HΓ.
  }

  pose proof (S1' := S1).
  apply useBasicReasoning with (i := (ExGen := {[ev_x; x]}, SVSubst := ∅, KT := false, AKT := false)) in S1'.
  apply universal_generalization with (x := ev_x) in S1'.
  3: { wf_auto2. }
  2: { try_solve_pile. }

  assert (Hx1': evar_is_fresh_in x φ).
  {
    unfold evar_is_fresh_in. set_solver.
  }

  assert (Hx'2: x ∉ AC_free_evars AC).
  { 
    unfold evar_is_fresh_in. set_solver.
  }

  remember ( (ExGen := {[ev_x; x]}, SVSubst := ∅, KT := false, AKT := false)) as i.
  assert (S1'' : Γ ⊢i ⌈ patt_free_evar x ⌉ using i).
  {
    gapply defined_evar. try_solve_pile. assumption.
  }
  
  assert(S2: Γ ⊢i ⌈ patt_free_evar x ⌉ or ⌈ φ ⌉ using i).
  {
    toMLGoal.
    { wf_auto2. }
    mlLeft.
    fromMLGoal.
    apply S1''.
  }

  assert(S3: Γ ⊢i ⌈ patt_free_evar x or φ ⌉ using i).
  {
    pose proof (Htmp := (prf_prop_or_iff Γ AC_patt_defined) (patt_free_evar x) φ ltac:(auto) ltac:(auto)).
    simpl in Htmp.
    apply pf_conj_elim_r_meta in Htmp.
    2-3: wf_auto2.
    apply useGenericReasoning with (i := i) in Htmp.
    2: {
      subst i. try_solve_pile.
    }
    subst i.
    eapply MP.
    1: apply S2.
    1: {
      apply Htmp.
    }
  }

  assert(S4: Γ ⊢i ⌈ ((patt_free_evar x) and (! φ)) or φ ⌉ using i).
  {
    assert(Htmp1: Γ ⊢i (patt_free_evar x or φ) ---> (patt_free_evar x and ! φ or φ) using i).
    {
      toMLGoal.
      { wf_auto2. }
      mlIntro "H0".
      mlClassic (φ) as "Hφ" "Hnotφ".
      { wf_auto2. }
      - mlRight. mlExact "Hφ".
      - mlLeft. mlIntro "H1".
        mlDestructOr "H0" as "H01" "H02".
        + mlDestructOr "H1" as "H10" "H11".
          * mlApply "H10". mlExact "H01".
          * mlApply "H11". mlExact "Hnotφ".
        + mlApply "Hnotφ".
          mlExact "H02".
    }

    assert(Htmp2: Γ ⊢i (⌈ patt_free_evar x or φ ⌉) ---> (⌈ patt_free_evar x and ! φ or φ ⌉) using i).
    {
      unshelve (eapply Framing_right).
      { wf_auto2. }
      {
        try_solve_pile.
      }
      apply Htmp1.
    }

    eapply MP.
    2: apply Htmp2.
    1: apply S3.
  }

  assert(S5: Γ ⊢i ⌈ (patt_free_evar x and (! φ)) ⌉ or ⌈ φ ⌉ using i).
  {
    pose proof (Htmp := (prf_prop_or_iff Γ AC_patt_defined) (patt_free_evar x and ! φ) φ ltac:(auto) ltac:(auto)).
    simpl in Htmp.
    apply pf_conj_elim_l_meta in Htmp;[|wf_auto2|wf_auto2].
    apply useGenericReasoning with (i := i) in Htmp.
    2: {
      subst i. try_solve_pile.
    }
    subst i.
    eapply MP.
    2: {
      apply Htmp.
    }
    1: apply S4.
  }

  assert(S6: Γ ⊢i subst_ctx AC (patt_free_evar x and φ) ---> ! ⌈ patt_free_evar x and ! φ ⌉ using i).
  {
    pose proof (Htmp := Singleton_ctx Γ AC AC_patt_defined φ x).
    simpl in Htmp.
    unfold patt_and in Htmp at 1.
    apply not_not_elim_meta in Htmp.
    3: { wf_auto2. }
    2: { wf_auto2. }
    replace (patt_sym (Definedness_Syntax.inj definedness) $ (patt_free_evar x and ! φ))%ml
      with (patt_defined (patt_free_evar x and ! φ)) in Htmp by reflexivity.
    
    toMLGoal.
    { wf_auto2. }
    mlIntro.
    remember (ExGen := {[ev_x; x]}, SVSubst := ∅, KT := false, AKT := false) as gpi.
    rewrite Heqi.
    mlAdd (useBasicReasoning gpi Htmp).
    mlApply "1". mlIntro. mlApply "2".
    mlExactn 1.
  }

  pose proof (S7 := S5). unfold patt_or in S7.

  assert(S8: Γ ⊢i subst_ctx AC (patt_free_evar x and φ) ---> ⌈ φ ⌉ using i).
  {
    eapply syllogism_meta.
    5: apply S7.
    4: apply S6.
    1-3: wf_auto2.
  }
  assert (S9: Γ ⊢i all, (subst_ctx AC (patt_bound_evar 0 and φ) ---> ⌈ φ ⌉) using i).
  {
    eapply universal_generalization with (x := x) in S8.
    3: { wf_auto2. }
    2: { try_solve_pile. }
    simpl in S8.

    rewrite evar_quantify_subst_ctx in S8;[assumption|].

    simpl in S8.
    case_match; try contradiction.
    rewrite evar_quantify_fresh in S8; [assumption|].
    apply S8.
  }

  assert(S10: Γ ⊢i (ex, subst_ctx AC (b0 and φ)) ---> ⌈ φ ⌉ using i).
  {
    unfold patt_forall in S9.
    unfold patt_not in S9 at 1.

    assert (Heq: (subst_ctx AC (patt_free_evar x and φ))^{{evar: x ↦ 0}} = subst_ctx AC (b0 and φ)).
    {
      rewrite evar_quantify_subst_ctx;[assumption|].
      f_equal.
      simpl.
      case_match; [|congruence].
      rewrite evar_quantify_fresh; [assumption|].
      reflexivity.
    }
    rewrite <- Heq.
    apply BasicProofSystemLemmas.Ex_gen.
    2: {simpl. unfold evar_is_fresh_in in Hx1'. clear -Hx1'. set_solver. }
    1: { try_solve_pile. }
    assumption.
  }

  assert (S11: Γ ⊢i φ ---> ((ex, patt_bound_evar 0) and φ) using i).
  {
    toMLGoal.
    { wf_auto2. }
    mlIntro.
    mlAdd (useBasicReasoning i (conj_intro Γ (ex, b0) φ ltac:(auto) ltac:(auto))).

    mlAssert ((φ ---> (ex , b0) and φ)).
    { wf_auto2. }
    {  mlApply "1".
        subst i.
       (* TODO mlAdd should do the cast automatically *)
       mlAdd (useBasicReasoning (ExGen := {[ev_x; x]}, SVSubst := ∅, KT := false, AKT := false) (Existence Γ)).
       mlExactn 0.
    }
    mlApply "2". mlExactn 1.
  }

  assert (well_formed (ex , (b0 and φ))).
  {
    unfold well_formed,well_formed_closed in *.
    destruct_and!.
    simpl; split_and!; auto.
    eapply well_formed_closed_ex_aux_ind. 2: eassumption. lia.
  }

  assert (S12: Γ ⊢i φ ---> ex, (b0 and φ) using i).
  {

    assert(well_formed (ex , ((patt_free_evar x)^{{evar: x ↦ 0}} and φ))).
    {
      unfold well_formed,well_formed_closed in *. simpl in *.
      destruct_and!. split_and!; auto.
      all: repeat case_match; auto.
    }

    assert(Htmp: Γ ⊢i ((ex, b0) and φ ---> (ex, (b0 and φ))) using i).
    {
      toMLGoal.
      { wf_auto2. }
      mlIntro.
      mlDestructAnd "0".
      fromMLGoal.
      replace b0 with ((patt_free_evar x)^{{evar: x ↦ 0}}).
      2: { simpl. case_match;[reflexivity|congruence]. }
      apply BasicProofSystemLemmas.Ex_gen.
      2: { simpl. case_match;[|congruence]. simpl.
           unfold evar_is_fresh_in in Hx1'. clear -Hx1'. set_solver.
      }
      1: {
        try_solve_pile.
      }
      toMLGoal.
      { wf_auto2. }
      do 2 mlIntro.
      mlAssert ((patt_free_evar x and φ)) using first 2.
      { wf_auto2. }
      { unfold patt_and. unfold patt_not at 1. mlIntro.
        mlDestructOr "2".
        - mlApply "3". mlExactn 0.
        - mlApply "4". mlExactn 1.
      }
      mlClear "1". mlClear "0".
      fromMLGoal.
      case_match;[|congruence].

      replace (patt_free_evar x and φ)
        with (instantiate (ex, (patt_bound_evar 0 and φ)) (patt_free_evar x)).
      2: {
        simpl. rewrite bevar_subst_not_occur.
        { unfold well_formed, well_formed_closed in *.
          destruct_and!. auto.
        }
        reflexivity.
      }
      subst i.
      useBasicReasoning.
      apply BasicProofSystemLemmas.Ex_quan.
      { wf_auto2. }
    }
    eapply syllogism_meta.
    5: { apply Htmp. }
    4: assumption.
    1-3: wf_auto2.
  }

  assert(S13: Γ ⊢i (subst_ctx AC φ) ---> (subst_ctx AC (ex, (b0 and φ))) using i).
  {
    apply Framing.
    {
      try_solve_pile.
    }
    apply S12.
  }

  assert(S14: Γ ⊢i (subst_ctx AC (ex, (b0 and φ))) ---> (⌈ φ ⌉) using i).
  {
    pose proof (Htmp := prf_prop_ex_iff Γ AC (b0 and φ) x).
    feed specialize Htmp.
    { unfold evar_is_fresh_in in *.
      rewrite free_evars_subst_ctx. clear -Hx1' Hx'2. simpl. set_solver.
    }
    { auto. }
    unfold exists_quantify in Htmp.
    rewrite evar_quantify_subst_ctx in Htmp.
    { assumption. }

    assert (well_formed (ex , subst_ctx AC (b0 and φ))).
    {
      unfold well_formed,well_formed_closed in *. destruct_and!.
      split_and!; simpl; auto.
      3: { apply wcex_sctx.
           simpl. split_and!; auto.
           eapply well_formed_closed_ex_aux_ind. 2: eassumption. lia.
      }
      2: {
        apply wcmu_sctx.
        simpl. split_and!; auto.
      }
      1: {
        apply wp_sctx. simpl. split_and!; auto.
      }
    }

    rewrite -> evar_quantify_evar_open in Htmp.
    2: { simpl. unfold evar_is_fresh_in in Hx1'. clear -Hx1'. set_solver. }
    apply pf_iff_proj1 in Htmp; auto.
    {
      eapply syllogism_meta.
      5: { apply S10. }
      4: { subst i. eapply useGenericReasoning. 2: apply Htmp.
        try_solve_pile.
      }
      1-3: wf_auto2.
    }
    unfold patt_and,patt_or,patt_not.
    simpl. split_and!; auto.
    apply well_formed_closed_ex_aux_ind with (ind_evar1 := 0); auto.
    wf_auto2.
  }

  eapply syllogism_meta.
  5: apply S14.
  4: assumption.
  1-3: wf_auto2.
Defined.

Lemma elements_union_empty φ:
  elements (free_evars φ ∪ ∅) = elements (free_evars φ).
Proof.
  apply f_equal.
  set_solver.
Qed.

Lemma phi_impl_defined_phi Γ φ x:
  theory ⊆ Γ ->
  x ∉ free_evars φ ->
  well_formed φ ->
  Γ ⊢i φ ---> ⌈ φ ⌉
  using 
                     (ExGen := {[ev_x;x]},
                      SVSubst := ∅, KT := false, AKT := false).
Proof.
  intros HΓ Hx wfφ.
  eapply cast_proof'.
  {
    replace φ with (subst_ctx box φ) at 1 by reflexivity.
    reflexivity.
  }
  eapply useGenericReasoning.
  2: {
    apply in_context_impl_defined; try assumption.
    cbn. instantiate (1:=x). set_solver.
  }
  {
    simpl. replace (free_evars φ ∪ ∅) with (free_evars φ) by set_solver.
    try_solve_pile.
  }
Defined.

Lemma total_phi_impl_phi Γ φ x:
  theory ⊆ Γ ->
  x ∉ free_evars φ -> 
  well_formed φ ->
  Γ ⊢i ⌊ φ ⌋ ---> φ
  using 
  (ExGen := {[ev_x; x]},
   SVSubst := ∅, KT := false, AKT := false).
Proof.
  intros HΓ Hx wfφ.
  unfold patt_total.
  pose proof (Htmp := phi_impl_defined_phi Γ (! φ) x HΓ ltac:(set_solver) ltac:(wf_auto2)).
  apply A_impl_not_not_B_meta.
  1,2: wf_auto2.
  apply modus_tollens.
  simpl in Htmp. assumption.
Defined.

Lemma total_phi_impl_phi_meta Γ φ i x:
  theory ⊆ Γ ->
  x ∉ free_evars φ ->
  well_formed φ ->
  ProofInfoLe
  (ExGen := {[ev_x; x]},
   SVSubst := ∅, KT := false, AKT := false) i ->
  Γ ⊢i ⌊ φ ⌋ using i ->
  Γ ⊢i φ using i.
Proof.
  intros HΓ Hx wfφ pile H.
  eapply MP.
  1: exact H.
  eapply useGenericReasoning.
  2: apply total_phi_impl_phi.
  {
    eapply pile_trans. 2: apply pile.
    try_solve_pile.
  }
  all: assumption.
Defined.

  Lemma framing_left_under_tot_impl Γ ψ phi1 phi2 psi:
    well_formed ψ = true ->
    well_formed phi1 = true ->
    well_formed phi2 = true ->
    well_formed psi = true ->
    theory ⊆ Γ ->
    Γ ⊢ ⌊ ψ ⌋ ---> phi1 ---> phi2 ->
    Γ ⊢ ⌊ ψ ⌋ ---> (phi1 $ psi) ---> (phi2 $ psi)
  .
  Proof.
    intros Hwfψ Hwfphi1 Hwfphi2 Hwfpsi HΓ H.
    assert (S2: Γ ⊢ phi1 ---> (phi2 or ⌈ ! ψ ⌉)).
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

    assert (S3: Γ ⊢ (⌈ ! ψ ⌉ $ psi) ---> ⌈ ! ψ ⌉).
    {
      replace (⌈ ! ψ ⌉ $ psi)
        with (subst_ctx (ctx_app_l AC_patt_defined psi ltac:(assumption)) (! ψ))
        by reflexivity.
      remember (evar_fresh (elements (free_evars ψ ∪ free_evars psi))) as x.
      gapply (in_context_impl_defined _ _ _ x).
      4: { wf_auto2. }
      2: { exact HΓ. }
      1: { apply pile_any. }
      subst x.
      cbn.
      eapply not_elem_of_larger_impl_not_elem_of.
      2: { apply set_evar_fresh_is_fresh'. }
      clear.
      set_solver.
    }

    assert (S4: Γ ⊢ (phi1 $ psi) ---> ((phi2 or ⌈ ! ψ ⌉) $ psi)).
    { 
      unshelve (eapply Framing_left).
      { wf_auto2. }
      { apply pile_any. }
      { exact S2. }
    }

    assert (S5: Γ ⊢ (phi1 $ psi) ---> ((phi2 $ psi) or (⌈ ! ψ ⌉ $ psi))).
    {
      pose proof (Htmp := prf_prop_or_iff Γ (ctx_app_l box psi ltac:(assumption)) phi2 (⌈! ψ ⌉)).
      feed specialize Htmp.
      { wf_auto2. }
      { wf_auto2. }
      simpl in Htmp.
      apply pf_iff_proj1 in Htmp.
      3: { wf_auto2. }
      2: { wf_auto2. }
      eapply syllogism_meta.
      5: {
        gapply Htmp.
        apply pile_any.
      }
      4: { exact S4. }
      all: wf_auto2.
    }

    assert (S6: Γ ⊢ ((phi2 $ psi) or (⌈ ! ψ ⌉ $ psi)) ---> ((phi2 $ psi) or (⌈ ! ψ ⌉))).
    {
      toMLGoal.
      { wf_auto2. }
      mlIntro "H". mlAdd S3 as "S3".
      mlClassic (phi2 $ psi) as "Hc1" "Hc2".
      { wf_auto2. }
      - mlLeft. mlExact "Hc1".
      - mlRight. mlApply "S3". mlApply "H". mlExact "Hc2".
    }

    assert (S7: Γ ⊢ (phi1 $ psi) ---> ((phi2 $ psi)  or ⌈ ! ψ ⌉)).
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

  Lemma framing_right_under_tot_impl Γ ψ phi1 phi2 psi:
    well_formed ψ = true ->
    well_formed phi1 = true ->
    well_formed phi2 = true ->
    well_formed psi = true ->
    theory ⊆ Γ ->
    Γ ⊢ ⌊ ψ ⌋ ---> phi1 ---> phi2 ->
    Γ ⊢ ⌊ ψ ⌋ ---> (psi $ phi1) ---> (psi $ phi2)
  .
  Proof.
    intros Hwfψ Hwfphi1 Hwfphi2 Hwfpsi HΓ H.
    assert (S2: Γ ⊢ phi1 ---> (phi2 or ⌈ ! ψ ⌉)).
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

    assert (S3: Γ ⊢ (psi $ ⌈ ! ψ ⌉) ---> ⌈ ! ψ ⌉).
    {
      replace (psi $ ⌈ ! ψ ⌉)
      with (subst_ctx (ctx_app_r psi AC_patt_defined ltac:(assumption)) (! ψ))
        by reflexivity.
      
      remember (evar_fresh (elements (free_evars ψ ∪ free_evars psi))) as x.
      gapply (in_context_impl_defined _ _ _ x).
      4: { wf_auto2. }
      2: { exact HΓ. }
      1: { apply pile_any. }
      subst x.
      cbn.
      eapply not_elem_of_larger_impl_not_elem_of.
      2: { apply set_evar_fresh_is_fresh'. }
      clear.
      set_solver.
    }

    assert (S4: Γ ⊢ (psi $ phi1) ---> (psi $ (phi2 or ⌈ ! ψ ⌉))).
    { 
      (* TODO: have a variant of apply which automatically solves all wf constraints.
         Like: unshelve (eapply H); try_wfauto
      *)
      unshelve (eapply Framing_right).
      { wf_auto2. }
      2: exact S2.
      apply pile_any.
    }

    assert (S5: Γ ⊢ (psi $ phi1) ---> ((psi $ phi2) or (psi $ ⌈ ! ψ ⌉))).
    {
      pose proof (Htmp := prf_prop_or_iff Γ (ctx_app_r psi box ltac:(assumption)) phi2 (⌈! ψ ⌉)).
      feed specialize Htmp.
      { wf_auto2. }
      { wf_auto2. }
      simpl in Htmp.
      apply pf_iff_proj1 in Htmp.
      2,3: wf_auto2.
      eapply syllogism_meta.
      5: gapply Htmp; apply pile_any.
      1-3: wf_auto2.
      exact S4.
    }

    assert (S6: Γ ⊢ ((psi $ phi2) or (psi $ ⌈ ! ψ ⌉)) ---> ((psi $ phi2) or (⌈ ! ψ ⌉))).
    {
      toMLGoal.
      { wf_auto2. }
      mlIntro "H1". mlAdd S3 as "S3".
      mlClassic (psi $ phi2) as "Hc1" "Hc2".
      { wf_auto2. }
      - mlLeft. mlExact "Hc1".
      - mlRight. mlApply "S3". mlApply "H1". mlExact "Hc2".
    }

    assert (S7: Γ ⊢ (psi $ phi1) ---> ((psi $ phi2)  or ⌈ ! ψ ⌉)).
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

  Theorem deduction_theorem_noKT Γ φ ψ
    (gpi : ProofInfo)
    (pf : Γ ∪ {[ ψ ]} ⊢i φ using  gpi) :
    well_formed φ ->
    well_formed ψ ->
    theory ⊆ Γ ->
    (* x ∈ pi_generalized_evars gpi -> *)
    pi_generalized_evars gpi ## (gset_to_coGset (free_evars ψ)) ->
    pi_substituted_svars gpi ## (gset_to_coGset (free_svars ψ)) ->
    pi_uses_kt gpi = false ->
    Γ ⊢i ⌊ ψ ⌋ ---> φ
    using AnyReasoning.
    (* (ExGen :=
      (
        {[ev_x; x]}
        ∪ pi_generalized_evars gpi
        ∪ gset_to_coGset (free_evars ψ)
      ),
     SVSubst := (pi_substituted_svars gpi ∪ (gset_to_coGset (free_svars ψ))),
     KT := false
    ). *)
    (** TODO: for this proof, the free variables in patterns of Framing need to be
              traced!!!!
     **)
  Proof.
    intros wfφ wfψ HΓ Hgen Hsubst Hkt.
    destruct pf as [pf Hpf]. simpl.
    induction pf.
    - (* hypothesis *)
      rename axiom into axiom0.
      (* We could use [apply elem_of_union in e; destruct e], but that would be analyzing Prop
         when building Set, which is prohibited. *)
      destruct (decide (axiom0 = ψ)).
      + subst.
        eapply useGenericReasoning.
        2: {
          apply total_phi_impl_phi; try assumption.
          instantiate (1 := evar_fresh (elements (free_evars ψ))).
          apply set_evar_fresh_is_fresh'.
        }
        { try_solve_pile. }

      + assert (axiom0 ∈ Γ).
        { clear -e n. set_solver. }
        toMLGoal.
        { wf_auto2. }
        mlIntro. mlClear "0". fromMLGoal.
        eapply useGenericReasoning.
        2: apply (BasicProofSystemLemmas.hypothesis Γ axiom0 i H).
        try_solve_pile.
    - (* P1 *)
      toMLGoal.
      { wf_auto2. }
      do 3 mlIntro. mlExactn 1.
    - (* P2 *)
      toMLGoal.
      { wf_auto2. }
      mlIntro. mlClear "0". fromMLGoal.
      useBasicReasoning.
      apply P2; assumption.
    - (* P3 *)
      toMLGoal.
      { wf_auto2. }
      mlIntro. mlClear "0". fromMLGoal.
      useBasicReasoning.
      apply P3; assumption.
    - (* Modus Ponens *)
      assert (well_formed phi2).
      { unfold well_formed, well_formed_closed in *. simpl in *.
        destruct_and!. split_and!; auto.
      }
      assert (well_formed phi1).
      {
        clear -pf1. apply proved_impl_wf in pf1. exact pf1.
      }

      remember_constraint as i'.

      destruct Hpf as [Hpf2 Hpf3 Hpf4 Hpf5].
      simpl in Hpf2, Hpf3, Hpf4.
      feed specialize IHpf1.
      {
        constructor; simpl.
        { set_solver. }
        { set_solver. }
        { unfold implb in *.
          destruct (uses_kt pf1) eqn:Hktpf1;[|reflexivity]. simpl in *.
          exact Hpf4.
        }
        { unfold implb in *.
          destruct (uses_kt_unreasonably pf1) eqn:Hktpf1;[|reflexivity]. simpl in *.
          rewrite Hktpf1 in Hpf5. simpl in Hpf5.
          unfold is_true in Hpf5.
          rewrite andb_true_iff in Hpf5.
          destruct Hpf5 as [HH1 HH2].
          rewrite HH1. simpl.
          apply kt_unreasonably_implies_somehow.
          exact Hktpf1.
        }
      }
      { assumption. }
      feed specialize IHpf2.
      {
        constructor; simpl.
        { set_solver. }
        { set_solver. }
        { unfold implb in *.
          destruct (uses_kt pf2) eqn:Hktpf2;[|reflexivity].
          rewrite orb_comm in Hpf4. simpl in *.
          exact Hpf4.
        }
        { unfold implb in *.
          destruct (uses_kt_unreasonably pf2) eqn:Hktpf2;[|reflexivity]. simpl in *.
          rewrite Hktpf2 in Hpf5. rewrite orb_true_r in Hpf5.
          unfold is_true in Hpf5.
          rewrite andb_true_iff in Hpf5.
          destruct Hpf5 as [HH1 HH2].
          rewrite HH1. simpl.
          apply kt_unreasonably_implies_somehow.
          exact Hktpf2.
        }
      }
      { wf_auto2. }

      toMLGoal.
      { wf_auto2. }
      mlIntro.
      subst i'. mlAdd IHpf2.
      mlAssert ((phi1 ---> phi2)).
      { wf_auto2. }
      { mlApply "1". mlExactn 1. }
      mlApply "2". (* TODO: proof infos are transformed? Why? *)
      mlAdd IHpf1.
      mlApply "3".
      mlExactn 2.
    - (* Existential Quantifier *)
      toMLGoal.
      { wf_auto2. }
      mlIntro. mlClear "0". fromMLGoal.
      useBasicReasoning.
      apply BasicProofSystemLemmas.Ex_quan. wf_auto2.
    - (* Existential Generalization *)
      destruct Hpf as [Hpf2 Hpf3 Hpf4 Hpf5].
      simpl in Hpf2, Hpf3, Hpf4.
      (*
      simpl in HnoExGen.
      case_match;[congruence|]. *)
      feed specialize IHpf.
      {
        constructor; simpl.
        { clear -Hpf2. set_solver. }
        { clear -Hpf3. set_solver. }
        { apply Hpf4. }
        { apply Hpf5. }
      }
      { clear Hpf5. wf_auto2. }


      apply reorder_meta in IHpf.
      2-4: clear Hpf5; wf_auto2.

      apply BasicProofSystemLemmas.Ex_gen with (x := x) in IHpf.
      3: { simpl. set_solver. }
      2: { try_solve_pile. }
      apply reorder_meta in IHpf.
      2-4: clear Hpf5; wf_auto2.
      exact IHpf.
      
    - (* Propagation of ⊥, left *)
      toMLGoal.
      { wf_auto2. }
      mlIntro. mlClear "0". fromMLGoal.
      useBasicReasoning.
      apply Prop_bott_left; assumption.
    - (* Propagation of ⊥, right *)
      toMLGoal.
      { wf_auto2. }
      mlIntro. mlClear "0"; auto. fromMLGoal.
      useBasicReasoning.
      apply Prop_bott_right; assumption.
    - (* Propagation of 'or', left *)
      toMLGoal.
      { wf_auto2. }
      mlIntro. mlClear "0"; auto. fromMLGoal.
      useBasicReasoning.
      apply Prop_disj_left; assumption.
    - (* Propagation of 'or', right *)
      toMLGoal.
      { wf_auto2. }
      mlIntro. mlClear "0"; auto. fromMLGoal.
      useBasicReasoning.
      apply Prop_disj_right; assumption.
    - (* Propagation of 'exists', left *)
      toMLGoal.
      { wf_auto2. }
      mlIntro. mlClear "0"; auto. fromMLGoal.
      useBasicReasoning.
      apply Prop_ex_left; assumption.
    - (* Propagation of 'exists', right *)
      toMLGoal.
      { wf_auto2. }
      mlIntro. mlClear "0"; auto. fromMLGoal.
      useBasicReasoning.
      apply Prop_ex_right; assumption.
    - (* Framing left *)
      assert (well_formed (phi1)).
      { unfold well_formed,well_formed_closed in *. simpl in *.
        destruct_and!. split_and!; auto. }

      assert (well_formed (phi2)).
      { unfold well_formed,well_formed_closed in *. simpl in *.
        destruct_and!. split_and!; auto. }

      assert (well_formed (psi)).
      { unfold well_formed,well_formed_closed in *. simpl in *.
        destruct_and!. split_and!; auto. }
      
      assert (well_formed (phi1 ---> phi2)).
      { unfold well_formed,well_formed_closed in *. simpl in *.
        destruct_and!. split_and!; auto. }
      destruct Hpf as [Hpf2 Hpf3 Hpf4 Hpf5].
      simpl in Hpf2,Hpf3,Hpf4.
      feed specialize IHpf.
      {
        constructor; simpl.
        { set_solver. }
        { set_solver. }
        { apply Hpf4. }
        { apply Hpf5. }
      }
      { clear Hpf5; wf_auto2. }
      
      apply framing_left_under_tot_impl.
      1-4: wf_auto2.
      { exact HΓ. }
      { exact IHpf. }

    - (* Framing right *)
      assert (well_formed (phi1)).
      { unfold well_formed,well_formed_closed in *. simpl in *.
        destruct_and!. split_and!; auto. }

      assert (well_formed (phi2)).
      { unfold well_formed,well_formed_closed in *. simpl in *.
        destruct_and!. split_and!; auto. }

      assert (well_formed (psi)).
      { unfold well_formed,well_formed_closed in *. simpl in *.
        destruct_and!. split_and!; auto. }

      assert (well_formed (phi1 ---> phi2)).
      { unfold well_formed,well_formed_closed in *. simpl in *.
        destruct_and!. split_and!; auto. }

      destruct Hpf as [Hpf2 Hpf3 Hpf4 Hpf5].
      simpl in Hpf2,Hpf3,Hpf4,Hpf5.
      feed specialize IHpf.
      {
        constructor; simpl.
        { set_solver. }
        { set_solver. }
        { apply Hpf4. }
        { apply Hpf5. }
      }
      { wf_auto2. }

      apply framing_right_under_tot_impl.
      1-4: wf_auto2.
      { exact HΓ. }
      { exact IHpf. }
      
    - (* Set variable substitution *)
      destruct Hpf as [Hpf2 Hpf3 Hpf4 Hpf5].
      simpl in Hpf2, Hpf3, Hpf4.
      feed specialize IHpf.
      {
        constructor; simpl.
        { exact Hpf2. }
        { clear -Hpf3. set_solver. }
        { exact Hpf4. }
        { exact Hpf5. }
      }
      {
        wf_auto2.
      }
      
      remember_constraint as i'.

      replace (⌊ ψ ⌋ ---> phi^[[svar: X ↦ psi]])
        with ((⌊ ψ ⌋ ---> phi)^[[svar: X ↦ psi]]).
      2: {  simpl.
           rewrite [ψ^[[svar: X ↦ psi]]]free_svar_subst_fresh.
           {
            unfold svar_is_fresh_in. set_solver.
           }
           reflexivity.
      }
      apply Svar_subst.
      3: {
        apply IHpf.
      }
      {
        subst i'.
        try_solve_pile.
      }
      { wf_auto2. }

    - (* Prefixpoint *)
      toMLGoal.
      { wf_auto2. }
      mlIntro. mlClear "0". fromMLGoal.
      apply useBasicReasoning.
      apply Pre_fixp. wf_auto2.
    - (* Knaster-Tarski *)
      destruct Hpf as [Hpf2 Hpf3 Hpf4].
      simpl in Hpf2, Hpf3, Hpf4.
      clear -Hkt Hpf4.
      exfalso. congruence.
    - (* Existence *)
      toMLGoal.
      { wf_auto2. }
      mlIntro. mlClear "0". fromMLGoal.
      apply useBasicReasoning.
      apply Existence.
    - (* Singleton *)
      toMLGoal.
      { wf_auto2. }
      mlIntro. mlClear "0". fromMLGoal.
      apply useBasicReasoning.
      apply Singleton_ctx. wf_auto2.
  Defined.

  Lemma membership_introduction Γ φ i:
    ProofInfoLe 
    (ExGen := {[ev_x; fresh_evar φ]},
     SVSubst := ∅,
     KT := false,
     AKT := false
    ) i ->
    well_formed φ ->
    theory ⊆ Γ ->
    Γ ⊢i φ using i ->
    Γ ⊢i all, ((patt_bound_evar 0) ∈ml φ)
    using i.
  Proof.
    intros pile wfφ HΓ Hφ.

    remember (fresh_evar φ) as x.

    replace φ with (φ^{{evar: x ↦ 0}}).
    2: {
      rewrite evar_quantify_fresh.
      subst; auto. reflexivity.
    }
    
    assert (S2: Γ ⊢i (φ ---> (patt_free_evar x ---> φ)) using i).
    {
      useBasicReasoning.
      apply P1.
      { wf_auto2. }
      { wf_auto2. }
    }

    assert(S3: Γ ⊢i patt_free_evar x ---> φ using i).
    {
      eapply MP. 2: apply S2. apply Hφ.
    }

    assert(S4: Γ ⊢i patt_free_evar x ---> patt_free_evar x using i).
    {
      useBasicReasoning.
      apply A_impl_A.
      wf_auto2.
    }

    assert(S5: Γ ⊢i patt_free_evar x ---> (patt_free_evar x and φ) using i).
    {
      toMLGoal.
      { wf_auto2. }
      mlIntro. unfold patt_and. mlIntro.
      mlAssert ((! φ)).
      { wf_auto2. }
      { mlApply "1". mlIntro. mlApply "2". mlExactn 0.  }
      mlApply "2".
      mlAdd Hφ. mlExactn 0.
    }

    assert(S6: Γ ⊢i ⌈ patt_free_evar x ⌉ ---> ⌈ (patt_free_evar x and φ) ⌉ using i).
    {
      unshelve (eapply Framing_right). 
      { try_wfauto2. }
      { eapply pile_trans. 2: apply pile. try_solve_pile. }
      apply S5.
    }
    
    assert(S7: Γ ⊢i ⌈ patt_free_evar x ⌉ using i).
    {
      eapply useGenericReasoning.
      2: apply defined_evar; assumption.
      try_solve_pile.
    }

    assert(S9: Γ ⊢i (patt_free_evar x) ∈ml φ using i).
    {
      eapply MP. 2: apply S6.
      apply S7.
    }

    eapply universal_generalization with (x := x) in S9.
    3: { wf_auto2. }
    1: { simpl in S9. case_match;[|congruence]. exact S9. }
    eapply pile_trans. 2: apply pile.
    try_solve_pile.
  Defined.

  Lemma membership_implies_implication Γ ϕ x:
    well_formed ϕ ->
    Γ ⊢i patt_free_evar x ∈ml ϕ ---> patt_free_evar x ---> ϕ using BasicReasoning.
  Proof.
    intro WF.
    toMLGoal.
    { wf_auto2. }
    mlIntro. mlIntro.
    pose proof (S5 := Singleton_ctx Γ AC_patt_defined box ϕ x ltac:(wf_auto2)).
    mlAdd S5.
    simpl.
    mlApplyMeta P3. mlIntro.
    mlApply "2". mlSplitAnd.
    * mlAssumption.
    * mlSplitAnd; mlAssumption.
  Defined.

  Lemma membership_implies_implication_meta Γ ϕ x i:
    well_formed ϕ ->
    Γ ⊢i patt_free_evar x ∈ml ϕ using i ->
    Γ ⊢i patt_free_evar x ---> ϕ using i.
  Proof.
    intros WF H.
    eapply MP. 2: gapply membership_implies_implication.
    assumption.
    try_solve_pile.
    wf_auto2.
  Defined.

  Lemma membership_elimination Γ φ i x:
    x ∉ free_evars φ ->
    ProofInfoLe 
    (ExGen := {[ev_x; x]},
    SVSubst := ∅,
     KT := false,
     AKT := false
    ) i ->

    well_formed φ ->
    theory ⊆ Γ ->
    Γ ⊢i all, ((patt_bound_evar 0) ∈ml φ) using i ->
    Γ ⊢i φ using i.
  Proof.
    intros Hp pile wfφ HΓ H.
    eapply forall_variable_substitution_meta with (x := x) in H.
    2: wf_auto2.
    assert (S1 : Γ ⊢i patt_free_evar x ∈ml φ using i). {
      cbn in H. rewrite bevar_subst_not_occur in H. wf_auto2. assumption.
    }
    clear H.
    apply membership_implies_implication_meta in S1 as S1'. 2: wf_auto2.
    eapply Ex_gen with (x := x) in S1'.
    2: try_solve_pile.
    2: solve_free_evars 1.
    mlApplyMeta S1'.
    unfold exists_quantify. simpl. case_match. 2: congruence.
    mlExactMeta (useBasicReasoning i (Existence Γ)).
  Defined.

  Lemma membership_not_1 Γ φ x:
    well_formed φ ->
    theory ⊆ Γ ->
    Γ ⊢i ((patt_free_evar x) ∈ml (! φ)) ---> ! ((patt_free_evar x) ∈ml φ)
    using BasicReasoning.
  Proof.
    intros Hwf HΓ.

    pose proof (S1 := Singleton_ctx Γ AC_patt_defined AC_patt_defined φ x ltac:(wf_auto2)).
    simpl in S1.

    assert (S2: Γ ⊢i ⌈ patt_free_evar x and ! φ ⌉ ---> ! ⌈ patt_free_evar x and φ ⌉ using BasicReasoning).
    {

      replace (patt_sym (Definedness_Syntax.inj definedness) $ (patt_free_evar x and φ))
        with (⌈ patt_free_evar x and φ ⌉) in S1 by reflexivity.

      replace (patt_sym (Definedness_Syntax.inj definedness) $ (patt_free_evar x and ! φ))
        with (⌈ patt_free_evar x and ! φ ⌉) in S1 by reflexivity.

      toMLGoal.
      { wf_auto2. }
      mlIntro. mlAdd S1.
      unfold patt_and at 1.
      mlAssert ((! ⌈ patt_free_evar x and φ ⌉ or ! ⌈ patt_free_evar x and ! φ ⌉))
               using first 1.
      { wf_auto2. }
      {
        fromMLGoal.
        useBasicReasoning.
        apply not_not_elim.
        wf_auto2.
      }
      mlClear "1".

      (* Symmetry of Or *)
      mlAssert ((! ⌈ patt_free_evar x and ! φ ⌉ or ! ⌈ patt_free_evar x and φ ⌉))
               using first 1.
      { wf_auto2. }
      {
        mlAdd (A_or_notA Γ (! ⌈ patt_free_evar x and φ ⌉) ltac:(wf_auto2)).
        mlDestructOr "0".
        - mlRight. mlExactn 0.
        - mlLeft. mlApply "2". mlExactn 0.
      }
      mlClear "2".

      mlApply "1". mlClear "1". fromMLGoal.
      useBasicReasoning.
      apply not_not_intro. wf_auto2.
    }
    apply S2.
  Qed.

  Lemma membership_not_2 Γ (φ : Pattern) x:
    well_formed φ = true ->
    theory ⊆ Γ ->
    Γ ⊢i ((!(patt_free_evar x ∈ml φ)) ---> (patt_free_evar x ∈ml (! φ)))%ml
    using  (ExGen := {[ev_x; x]}, SVSubst := ∅, KT := false, AKT := false).
  Proof.
    intros wfφ HΓ.
    pose proof (S1 := defined_evar Γ x HΓ).
    remember_constraint as i.
    assert (S2: Γ ⊢i ⌈ (patt_free_evar x and φ) or (patt_free_evar x and (! φ)) ⌉ using i).
    {
      assert(H: Γ ⊢i (patt_free_evar x ---> ((patt_free_evar x and φ) or (patt_free_evar x and (! φ)))) using BasicReasoning).
      {
        toMLGoal.
        { wf_auto2. }
        mlIntro. mlAdd (A_or_notA Γ φ ltac:(auto)).
        mlDestructOr "1".
        - mlLeft. unfold patt_and. mlIntro. unfold patt_or.
          mlAssert ((! φ)).
          { wf_auto2. }
          {
            mlApply "1". mlClear "2". mlClear "1". fromMLGoal.
            apply not_not_intro; auto.
          }
          mlApply "3". mlExactn 0.
        - mlRight. unfold patt_and. mlIntro. unfold patt_or.
          mlApply "3". mlApplyMeta (not_not_elim Γ φ ltac:(auto)).
          mlApply "1". mlIntro. mlApply "2". mlExactn 1.
      }
      apply useBasicReasoning with (i := i) in H.
      subst i.
      eapply Framing_right in H.
      eapply MP. 2: apply H.
      1: gapply S1; try_solve_pile.
      { wf_auto2. }
      { try_solve_pile. }
    }

    pose proof (Htmp := prf_prop_or_iff Γ AC_patt_defined (patt_free_evar x and φ) (patt_free_evar x and ! φ)
                                        ltac:(wf_auto2) ltac:(wf_auto2)).
    simpl in Htmp.
    apply pf_iff_proj1 in Htmp.
    2-3: wf_auto2.
    subst i.
    eapply MP.
    2: gapply Htmp; try_solve_pile.
    assumption.
  Defined.

  Lemma membership_not_iff Γ φ x:
    well_formed φ ->
    theory ⊆ Γ ->
    Γ ⊢i ((patt_free_evar x) ∈ml (! φ)) <---> ! ((patt_free_evar x) ∈ml φ)
    using  (ExGen := {[ev_x; x]}, SVSubst := ∅, KT := false, AKT := false).
  Proof.
    intros Hwf HΓ.
    apply pf_iff_split.
    1,2: wf_auto2.
    - useBasicReasoning; apply membership_not_1; assumption.
    - apply membership_not_2; assumption.
  Defined.
  
  Lemma membership_or_1 Γ x φ₁ φ₂:
    well_formed φ₁ ->
    well_formed φ₂ ->
    theory ⊆ Γ ->
    Γ ⊢i (patt_free_evar x ∈ml (φ₁ or φ₂)) ---> ((patt_free_evar x ∈ml φ₁) or (patt_free_evar x ∈ml φ₂))
    using BasicReasoning.
  Proof.
    intros wfφ₁ wfφ₂ HΓ.
    unfold patt_in.
    eapply syllogism_meta.
    5: gapply Prop_disj_right. 5: try_solve_pile.
    1,2,3,5,6,7: wf_auto2.
    unshelve (eapply Framing_right).
    { wf_auto2. }
    { try_solve_pile. }
    toMLGoal.
    { wf_auto2. }
    mlIntro. mlDestructAnd "0".
    mlDestructOr "2".
    - mlLeft. unfold patt_and. mlIntro.
      mlDestructOr "2".
      + mlApply "3". mlExactn 0.
      + mlApply "4". mlExactn 1.
    - mlRight. unfold patt_and. mlIntro.
      mlDestructOr "0".
      + mlApply "2". mlExactn 0.
      + mlApply "4". mlExactn 1.
  Defined.

  Lemma membership_or_2 Γ x φ₁ φ₂:
    well_formed φ₁ ->
    well_formed φ₂ ->
    theory ⊆ Γ ->
    Γ ⊢i ((patt_free_evar x ∈ml φ₁) or (patt_free_evar x ∈ml φ₂)) ---> (patt_free_evar x ∈ml (φ₁ or φ₂))
    using BasicReasoning.
  Proof.
    intros wfφ₁ wfφ₂ HΓ.
    unfold patt_in.
    pose proof (H1 := prf_prop_or_iff Γ AC_patt_defined (patt_free_evar x and φ₁) (patt_free_evar x and φ₂)
                                      ltac:(auto) ltac:(auto)).
    apply pf_iff_proj2 in H1.
    2,3: wf_auto2.
    eapply syllogism_meta.
    4: gapply H1; try_solve_pile.
    1-3: wf_auto2.
    simpl.
    unshelve (eapply Framing_right).
    { wf_auto2. }
    { unfold BasicReasoning. try_solve_pile. }

    toMLGoal.
    { wf_auto2. }
    mlIntro. mlDestructOr "0".
    - mlDestructAnd "1". unfold patt_and. mlIntro. mlDestructOr "1".
      + mlApply "3". mlExactn 0.
      + mlApply "4". mlLeft. mlExactn 1.
    - mlDestructAnd "2". unfold patt_and. mlIntro. mlDestructOr "2".
      + mlApply "3". mlExactn 0.
      + mlApply "4". mlRight. mlExactn 1.
  Defined.

  Lemma membership_or_iff Γ x φ₁ φ₂:
    well_formed φ₁ ->
    well_formed φ₂ ->
    theory ⊆ Γ ->
    Γ ⊢i (patt_free_evar x ∈ml (φ₁ or φ₂)) <---> ((patt_free_evar x ∈ml φ₁) or (patt_free_evar x ∈ml φ₂))
    using BasicReasoning.
  Proof.
    intros wfφ₁ wfφ₂ HΓ.
    apply pf_iff_split.
    1,2: wf_auto2.
    + apply membership_or_1; assumption.
    + apply membership_or_2; assumption.
  Defined.


  Lemma membership_and_1 Γ x φ₁ φ₂:
    well_formed φ₁ ->
    well_formed φ₂ ->
    theory ⊆ Γ ->
    Γ ⊢i (patt_free_evar x ∈ml (φ₁ and φ₂)) ---> ((patt_free_evar x ∈ml φ₁) and (patt_free_evar x ∈ml φ₂))
    using  (ExGen := {[ev_x; x]}, SVSubst := ∅, KT := false, AKT := false).
  Proof.
    intros wfφ₁ wfφ₂ HΓ.

    epose proof (Htmp1 := (membership_or_2 _ _ _ _ _ _ HΓ)).
    (* TODO: [change constraint in _] should work even in proof mode! *)
    change constraint in Htmp1.
    remember_constraint as gpi.

    unfold patt_and.
    toMLGoal.
    { wf_auto2. }
    mlIntro.
    assert (wfφ : well_formed (! φ₁ or ! φ₂)).
    { wf_auto2. }
    mlApplyMeta membership_not_1 in "0".
    2: {
      exact HΓ.
    }
    mlIntro. mlApply "0". mlClear "0".
    mlApplyMeta Htmp1.
    mlDestructOr "1"; subst gpi.
    - mlLeft.
      mlApplyMeta membership_not_2 in "0".
      2: { exact HΓ. }
      mlExactn 0.
    - mlRight.
      mlApplyMeta membership_not_2 in "2".
      2: { exact HΓ. }
      mlExactn 0.
      Unshelve. all: wf_auto2.
  Defined.

  Lemma membership_and_2 Γ x φ₁ φ₂:
    well_formed φ₁ ->
    well_formed φ₂ ->
    theory ⊆ Γ ->
    Γ ⊢i ((patt_free_evar x ∈ml φ₁) and (patt_free_evar x ∈ml φ₂)) ---> (patt_free_evar x ∈ml (φ₁ and φ₂))
    using  (ExGen := {[ev_x; x]}, SVSubst := ∅, KT := false, AKT := false).
  Proof.
    intros wfφ₁ wfφ₂ HΓ.

    epose proof (Htmp1 := (membership_or_1 _ _ _ _ _ _ HΓ)).
    change constraint in Htmp1.
    epose proof (Htmp2 := (membership_not_1 _ _ _ _ HΓ)).
    change constraint in Htmp2.
    epose proof (Htmp3 := (membership_not_1 _ _ _ _ HΓ)).
    change constraint in Htmp3.
    toMLGoal.
    { wf_auto2. }
    mlIntro.
    mlDestructAnd "0".
    unfold patt_and.

    unshelve (mlApplyMeta membership_not_2).
    2: { exact HΓ. }
    mlIntro.

    mlApplyMeta Htmp1 in "0".
    mlDestructOr "0".
    - mlApplyMeta Htmp2 in "3".
      mlApply "3". mlExactn 0.
    -
      mlApplyMeta Htmp3 in "4".
      mlApply "4". mlExactn 1.
      Unshelve. all: wf_auto2.
  Defined.

  Lemma membership_and_iff Γ x φ₁ φ₂:
    well_formed φ₁ ->
    well_formed φ₂ ->
    theory ⊆ Γ ->
    Γ ⊢i (patt_free_evar x ∈ml (φ₁ and φ₂)) <---> ((patt_free_evar x ∈ml φ₁) and (patt_free_evar x ∈ml φ₂))
    using  (ExGen := {[ev_x; x]}, SVSubst := ∅, KT := false, AKT := false).
  Proof.
    intros wfφ₁ wfφ₂ HΓ.
    apply pf_iff_split.
    1,2: wf_auto2.
    + apply membership_and_1; assumption.
    + apply membership_and_2; assumption.
  Defined.

  Lemma mu_free_in_path φ:
    mu_free φ = true -> forall x, mu_in_evar_path x φ 0 = false.
  Proof.
    intros H x.
    induction φ; unfold mu_in_evar_path in *; cbn in *; try congruence; try reflexivity.
    case: decide => H0; reflexivity.
    1-2: apply andb_true_iff in H as [H1 H2];
    rewrite /=; do 2 case_match; auto.
    eapply IHφ in H. apply H.
  Qed.

  Lemma equality_elimination_basic_mfpath Γ φ1 φ2 C
    (HΓ : theory ⊆ Γ)
    (WF1 : well_formed φ1)
    (WF2 :  well_formed φ2)
    (WFC : PC_wf C) :
    mu_in_evar_path (pcEvar C) (pcPattern C) 0 = false ->
    Γ ⊢i (φ1 =ml φ2) --->
      (emplace C φ1) <---> (emplace C φ2)
    using AnyReasoning.
      (* using (
    (ExGen := {[ev_x]}
              ∪ {[evar_fresh (elements (free_evars φ1 ∪ free_evars φ2))]}
              ∪ (gset_to_coGset (free_evars φ1))
              ∪ (gset_to_coGset (free_evars φ2))
              ∪ (gset_to_coGset (list_to_set
                (evar_fresh_seq
                   (free_evars (pcPattern C) ∪ free_evars φ1 ∪ free_evars φ2
                    ∪ {[pcEvar C]})
                   (maximal_exists_depth_of_evar_in_pattern 
                      (pcEvar C) (pcPattern C)))))
              ∪ (gset_to_coGset (list_to_set (map
                  (fun psi : wfPattern => evar_fresh (elements (free_evars φ1 ∪ free_evars φ2 ∪ free_evars (`psi))))
                  ((elements
                  (frames_on_the_way_to_hole'
                     (free_evars (pcPattern C) ∪ free_evars φ1
                      ∪ free_evars φ2 ∪ {[
                      pcEvar C]})
                     (free_svars (pcPattern C) ∪ free_svars φ1
                      ∪ free_svars φ2) (pcEvar C) 
                     (pcPattern C) φ1 φ2 WFC WF1 WF2)))
                  )))
              ,
     SVSubst := list_to_set
                  (svar_fresh_seq
                     (free_svars (pcPattern C) ∪ free_svars φ1
                      ∪ free_svars φ2)
                     (maximal_mu_depth_of_evar_in_pattern 
                        (pcEvar C) (pcPattern C)))
                ∪ (gset_to_coGset
                (free_svars φ1 ∪ free_svars φ2)),
     KT := (if
             decide
               (0 =
                maximal_mu_depth_of_evar_in_pattern (pcEvar C) (pcPattern C))
            is left _
            then false
            else true),
     FP := ⊤
    )). *)
  Proof.
    intros Hmf.

    eapply useGenericReasoning.
    2: {
      unshelve(eapply deduction_theorem_noKT).
      2: {
        remember (Γ ∪ {[ (φ1 <---> φ2) ]}) as Γ'.
        remember_constraint as i.
        assert (Γ' ⊢i (φ1 <---> φ2) using i). {
          subst i. useBasicReasoning.
          apply BasicProofSystemLemmas.hypothesis.
          - abstract (now apply well_formed_iff).
          - abstract (rewrite HeqΓ'; apply elem_of_union_r; constructor).
        }
        subst i.
        unshelve (eapply prf_equiv_congruence).
        { apply WF1. }
        { apply WF2. }
        { apply WFC. }
        2: apply H.
        apply pile_refl.
      }
    { 
      abstract (
        apply well_formed_and; apply well_formed_imp; unfold emplace;
        apply well_formed_free_evar_subst_0; auto
      ).
    }
    { abstract (wf_auto2). }
    { exact HΓ. }
    {
      simpl.
      unfold PC_wf in WFC.
      destruct C; simpl in *.
      replace (free_evars φ1 ∪ free_evars φ2 ∪ ∅ ∪ ∅
      ∪ (free_evars φ2 ∪ free_evars φ1 ∪ ∅) ∪ ∅)
      with (free_evars φ1 ∪ free_evars φ2)
      by set_solver.

      pose proof (evar_fresh_seq_disj (free_evars pcPattern ∪ free_evars φ1 ∪ free_evars φ2 ∪ {[pcEvar]}) (maximal_exists_depth_to 0 pcEvar pcPattern)).
      set_solver.
    }
    {
      simpl.
      unfold PC_wf in WFC.
      destruct C; simpl in *.

      pose proof (svar_fresh_seq_disj (free_svars pcPattern ∪ free_svars φ1 ∪ free_svars φ2) (maximal_mu_depth_to 0 pcEvar pcPattern)).
      set_solver.
    }
    {
      simpl. exact Hmf.
    }
  }
  {
    try_solve_pile.
    (* simpl.
    unfold dt_exgen_from_fp. simpl.
    repeat rewrite union_empty_r_L.
    replace (free_evars φ1 ∪ free_evars φ2
    ∪ (free_evars φ2 ∪ free_evars φ1))
    with (free_evars φ1 ∪ free_evars φ2) by set_solver.
    apply pile_evs_svs_kt.
    {
      clear. set_solver.
    }
    {
      clear. set_solver.
    }
    {
      reflexivity.
    }
    {
      clear. set_solver.
    } *)
  }
  Defined.

  Lemma equality_elimination_basic Γ φ1 φ2 C
  (HΓ : theory ⊆ Γ)
  (WF1 : well_formed φ1)
  (WF2 :  well_formed φ2)
  (WFC : PC_wf C) :
  mu_free (pcPattern C) ->
  Γ ⊢i (φ1 =ml φ2) --->
    (emplace C φ1) <---> (emplace C φ2)
  using AnyReasoning.
  Proof.
    intros.
    apply equality_elimination_basic_mfpath; try assumption.
    now apply mu_free_in_path.
  Defined.


  Lemma equality_elimination_basic_ar Γ φ1 φ2 C:
    theory ⊆ Γ ->
    well_formed φ1 ->
    well_formed φ2 ->
    PC_wf C ->
    mu_in_evar_path (pcEvar C) (pcPattern C) 0 = false ->
    Γ ⊢i (φ1 =ml φ2) --->
      (emplace C φ1) <---> (emplace C φ2)
    using AnyReasoning.
  Proof.
    intros.
    unshelve (gapply equality_elimination_basic_mfpath); try assumption.
    unfold AnyReasoning.
    try_solve_pile.
  Defined.

  (* NOTE: could this also be solved withouth induction? *)
  Lemma equality_elimination_basic_ar_iter_1 Γ φ₁ φ₂ l C :
    theory ⊆ Γ ->
    well_formed φ₁ ->
    well_formed φ₂ ->
    Pattern.wf l ->
    PC_wf C ->
    mu_in_evar_path (pcEvar C) (pcPattern C) 0 = false ->
    Γ ⊢i foldr patt_imp ((emplace C φ₁) <---> (emplace C φ₂)) ((φ₁ =ml φ₂) :: l)
    using AnyReasoning.
  Proof.
    intros HΓ wfφ₁ wfφ₂ wfl wfC Hmf.
    induction l; simpl.
    - apply equality_elimination_basic_ar; assumption.
    - pose proof (wfal := wfl). apply andb_prop in wfl as [wfa wfl].
      specialize (IHl wfl).
      simpl in IHl.
      pose proof (proved_impl_wf _ _ (proj1_sig IHl)).

      assert (well_formed (emplace C φ₁) = true) by (unfold emplace; wf_auto2).
      assert (well_formed (emplace C φ₂) = true) by (unfold emplace; wf_auto2).
      
      toMLGoal.
      { wf_auto2. }
      mlIntro. mlIntro. mlClear "1".
      fromMLGoal.
      apply IHl.
  Defined.

  (* TODO: this should NOT be done this way probably. There should be a general lemma, which can propagate another "foldr" lemma inside l₁, since there are other theorems that use the same scheme *)
  Lemma equality_elimination_basic_ar_iter Γ φ₁ φ₂ l₁ l₂ C :
    theory ⊆ Γ ->
    well_formed φ₁ ->
    well_formed φ₂ ->
    Pattern.wf l₁ ->
    Pattern.wf l₂ ->
    PC_wf C ->
    mu_in_evar_path (pcEvar C) (pcPattern C) 0 = false ->
    Γ ⊢i foldr patt_imp ((emplace C φ₁) <---> (emplace C φ₂)) (l₁ ++ (φ₁ =ml φ₂)::l₂)
    using AnyReasoning.
  Proof.
    intros HΓ wfφ₁ wfφ₂ wfl₁ wfl₂ wfC Hmf.
    induction l₁; simpl.
    - apply equality_elimination_basic_ar_iter_1; assumption.
    - pose proof (wfal := wfl₁). unfold wf in wfl₁. simpl in wfl₁. apply andb_prop in wfl₁ as [wfa wfl].
      specialize (IHl₁ wfl).
      pose proof (proved_impl_wf _ _ (proj1_sig IHl₁)).
      toMLGoal.
      { wf_auto2. }
      mlIntro. mlClear "0".
      fromMLGoal.
      apply IHl₁.
  Defined.

  Corollary equality_elimination_proj Γ φ1 φ2 ψ:
    theory ⊆ Γ ->
    mu_free ψ ->
    well_formed φ1 -> well_formed φ2 -> well_formed_closed_ex_aux ψ 1 -> well_formed_closed_mu_aux ψ 0 ->
    Γ ⊢i (φ1 =ml φ2) ---> 
      (ψ^[evar: 0 ↦ φ1]) ---> (ψ^[evar: 0 ↦ φ2])
    using AnyReasoning.
  Proof.
    intros HΓ MF WF1 WF2 WF3 WF4. remember (fresh_evar ψ) as x.
    assert (x ∉ free_evars ψ) by now apply x_eq_fresh_impl_x_notin_free_evars.
    rewrite (bound_to_free_variable_subst ψ x 1 0 φ1 ltac:(lia)); auto.
    { unfold well_formed,well_formed_closed in *. destruct_and!. assumption. }
    rewrite (bound_to_free_variable_subst ψ x 1 0 φ2 ltac:(lia)); auto.
    { unfold well_formed,well_formed_closed in *. destruct_and!. assumption. }
    (* needed for wf_auto2: *)
    have Hmf1 : well_formed_positive ψ = true by apply mu_free_wfp. 
    have Hmf2 : mu_free (pcPattern {| pcEvar := x; pcPattern := ψ^{evar:0↦x} |}) by apply mu_free_evar_open.
    have H0 := equality_elimination_basic Γ φ1 φ2 {|pcEvar := x; pcPattern := ψ^{evar:0 ↦ x}|} HΓ WF1 WF2 ltac:(wf_auto2) Hmf2.

    toMLGoal. wf_auto2.
      mlIntro.

      mlApplyMeta (pf_conj_elim_l Γ
         (ψ^{evar:0↦x}^[[evar:x↦φ1]] ---> ψ^{evar:0↦x}^[[evar:x↦φ2]])
         (ψ^{evar:0↦x}^[[evar:x↦φ2]] ---> ψ^{evar:0↦x}^[[evar:x↦φ1]])
                  ).
      mlApplyMeta H0. mlExact "0".
  Defined.

  (* TODO: proof infos *)
  Lemma patt_equal_sym Γ φ1 φ2:
    theory ⊆ Γ ->
    well_formed φ1 -> well_formed φ2 ->
    Γ ⊢i φ1 =ml φ2 ---> φ2 =ml φ1
    using AnyReasoning.
  Proof.
    intros HΓ WF1 WF2.
    unshelve (gapply deduction_theorem_noKT).
    4,5: abstract(wf_auto2).
    4: exact HΓ.
    3: {
      remember_constraint as i'.
      remember (Γ ∪ {[ (φ1 <---> φ2) ]}) as Γ'.
      assert (Γ' ⊢i (φ1 <---> φ2) using i'). {
        subst i'. useBasicReasoning.
        apply BasicProofSystemLemmas.hypothesis. apply well_formed_iff; auto.
        rewrite HeqΓ'. apply elem_of_union_r. constructor.
      }
      apply pf_iff_equiv_sym in H; auto.
      apply patt_iff_implies_equal; auto.
      subst i'. apply pile_refl.
    }
    {
      apply pile_any.
    }
    {
      simpl. set_solver.
    }
    {
      simpl. set_solver.
    }
    {
      simpl. reflexivity.
    }
  Defined.

  Lemma evar_quantify_equal_simpl : forall φ1 φ2 x n,
      evar_quantify x n (φ1 =ml φ2) = (evar_quantify x n φ1) =ml (evar_quantify x n φ2).
  Proof. auto. Qed.

  Definition is_functional φ : Pattern :=
    (ex, φ =ml b0).

  Lemma patt_equal_comm φ φ' Γ:
    theory ⊆ Γ ->
    well_formed φ ->
    well_formed φ' ->
    Γ ⊢ (φ =ml φ') <---> (φ' =ml φ).
  Proof.
    intros HΓ wfφ wfφ'.
    pose proof (SYM1 := @patt_equal_sym Γ φ' φ HΓ wfφ' wfφ).
    pose proof (SYM2 := @patt_equal_sym Γ φ φ' HΓ wfφ wfφ').
    apply pf_iff_split. 3,4: assumption. 1,2: wf_auto2. 
  Defined.

  Lemma exists_functional_subst φ φ' Γ :
    theory ⊆ Γ ->
    mu_free φ -> well_formed φ' -> well_formed_closed_ex_aux φ 1 -> well_formed_closed_mu_aux φ 0 ->
    Γ ⊢i ((instantiate (patt_exists φ) φ') and is_functional φ') ---> (patt_exists φ)
    using AnyReasoning.
  Proof.
    intros HΓ MF WF WFB WFM.
    remember (fresh_evar (φ $ φ')) as Zvar.
    remember (patt_free_evar Zvar) as Z.
    assert (well_formed Z) as WFZ.
    { rewrite HeqZ. auto. }

    assert (well_formed (instantiate (ex , φ) φ')) as WF1. {
      unfold instantiate.
      unfold well_formed, well_formed_closed.
      apply andb_true_iff in WF as [E1 E2].
      unfold well_formed_closed in *. destruct_and!.
      erewrite bevar_subst_closed_mu, bevar_subst_positive, bevar_subst_closed_ex; auto.
      now apply mu_free_wfp.
    }
    assert (well_formed (instantiate (ex , φ) Z)) as WF2. {
      unfold instantiate.
      unfold well_formed, well_formed_closed.
      apply andb_true_iff in WF as [E1 E2]. simpl in E1, E2.
      unfold well_formed_closed in *. destruct_and!.
      erewrite bevar_subst_closed_mu, bevar_subst_positive, bevar_subst_closed_ex; auto.
      all: try rewrite HeqZ; auto.
      now apply mu_free_wfp.
    }
    
    assert (well_formed (ex, φ)) as WFEX.
    { wf_auto2. }
    pose proof (EQ := BasicProofSystemLemmas.Ex_quan Γ φ Zvar WFEX).
    change constraint in EQ.
    epose proof (PC := prf_conclusion Γ (patt_equal φ' Z) (instantiate (ex , φ) (patt_free_evar Zvar) ---> ex , φ) AnyReasoning ltac:(apply well_formed_equal;wf_auto2) _ EQ).

    assert (Γ ⊢ patt_equal φ' Z ---> (ex , φ) ^ [φ'] ---> ex , φ) as HSUB.
    {
      pose proof (EE := equality_elimination_proj Γ φ' Z φ HΓ
                                               ltac:(auto) ltac:(auto) ltac:(auto) WFB WFM).

      epose proof (PSP := prf_strenghten_premise Γ ((patt_equal φ' Z) and (instantiate (ex , φ) Z))
                                                 ((patt_equal φ' Z) and (instantiate (ex , φ) φ'))
                                                 (ex , φ) _ _ _).
      eapply MP.
      2: useBasicReasoning; apply and_impl.
      2,3,4: wf_auto2.
      eapply MP.
      2: eapply MP.
      3: useBasicReasoning; exact PSP.

      * unshelve (epose proof (AI := and_impl' Γ (patt_equal φ' Z) (φ^[evar: 0 ↦ Z]) (ex , φ) _ _ _)).
        1,2,3: wf_auto2.
        unfold instantiate.
        (* TODO: tactic for modus ponens *)
        eapply MP. 2: useBasicReasoning; exact AI.
        rewrite <- HeqZ in PC.
        exact PC.
      * apply and_drop. 1-3: wf_auto2.
        unshelve(epose proof (AI := and_impl' Γ (patt_equal φ' Z) (instantiate (ex , φ) φ') (instantiate (ex , φ) Z) _ _ _)).
        1-3: wf_auto2.
        eapply MP. 2: useBasicReasoning; exact AI.
        { exact EE. }
    }

    eapply (BasicProofSystemLemmas.Ex_gen Γ _ _ Zvar) in HSUB.
    3: {
      rewrite HeqZvar. unfold fresh_evar. simpl.
      apply not_elem_of_union.
      split.
      - eapply stdpp_ext.not_elem_of_larger_impl_not_elem_of.
        2: { apply set_evar_fresh_is_fresh'. }
        rewrite comm.
        apply free_evars_bevar_subst.
      - eapply stdpp_ext.not_elem_of_larger_impl_not_elem_of.
        2: { apply set_evar_fresh_is_fresh'. }
        clear. set_solver.

    }
    2: { apply pile_any. }
    
    unfold exists_quantify in HSUB.
    mlSimpl in HSUB.
    rewrite -> HeqZ, -> HeqZvar in HSUB.
    simpl evar_quantify in HSUB.
    rewrite decide_eq_same in HSUB.

    rewrite evar_quantify_fresh in HSUB.
    { solve_fresh. }

    (* TODO do something like this, but we need more general mlApplyMeta
    toMLGoal.
    { wf_auto2. }
    mlIntro "H".
    mlDestructAnd "H" as "H1" "H2".

    mlApplyMeta (reshape_lhs_imp_to_and_forward _ _ _ _ _ _ _ _ _ HSUB).
    eapply reshape_lhs_imp_to_and_forward in HSUB; try_wfauto2; simpl in HSUB.
    mlApplyMeta HSUB.
    *)
    eapply MP. 2: useBasicReasoning; apply and_impl'; try_wfauto2.
    apply reorder_meta; try_wfauto2.
    exact HSUB.
    Unshelve.
    all: wf_auto2.
  Defined.

  Corollary forall_functional_subst φ φ' Γ :
    theory ⊆ Γ ->
    mu_free φ -> well_formed φ' -> well_formed_closed_ex_aux φ 1 -> well_formed_closed_mu_aux φ 0 ->
    Γ ⊢i ((patt_forall φ) and (patt_exists (patt_equal φ' (patt_bound_evar 0)))) ---> (φ^[evar: 0 ↦ φ'])
    using AnyReasoning.
  Proof.
    intros HΓ MF WF WFB WFM. unfold patt_forall.
    assert (well_formed (φ^[evar: 0 ↦ φ'])) as BWF. {
      unfold well_formed, well_formed_closed in *.
      destruct_and!.
      split_and!.
      - apply well_formed_positive_bevar_subst; auto.
        now apply mu_free_wfp.
      - auto.
      - apply wfc_ex_aux_bevar_subst; auto.
    }
    assert (well_formed (ex , patt_equal φ' b0)) as SWF. {
      unfold well_formed, well_formed_closed.
      apply andb_true_iff in WF as [E1 E2]. unfold well_formed_closed in E2.
      simpl. rewrite E1.
      unfold well_formed,well_formed_closed in *. destruct_and!.
      split_and!; auto.
      - eapply well_formed_closed_ex_aux_ind. 2: eassumption. lia.
      - eapply well_formed_closed_ex_aux_ind. 2: eassumption. lia.
    }
    assert (well_formed (ex , (φ ---> ⊥))) as NWF. {
      unfold well_formed, well_formed_closed in *.
      clear BWF SWF.
      destruct_and!. split_and!; auto.
      apply mu_free_wfp; simpl; now rewrite MF.
      all: simpl; wf_auto2.
    }
    unshelve (epose proof (H := exists_functional_subst (! φ) φ' Γ HΓ _ WF _ _)).
    { simpl. rewrite andbT. exact MF. }
    { wf_auto2. }
    { wf_auto2. }
    simpl in H.
    epose proof (H0 := and_impl _ _ _ _ _ _ _).
    epose proof (H0' := and_impl _ _ _ _ _ _ _).
    eapply useBasicReasoning with (i := AnyReasoning) in H0.
    eapply MP in H0. 2: apply H.
    apply reorder_meta in H0.
    2-4: wf_auto2.

    epose proof (H1 := and_impl' _ _ _ _ _ _ _).
    eapply useBasicReasoning with (i := AnyReasoning) in H1.
    eapply MP in H1. exact H1.

    apply reorder_meta. 1-3: wf_auto2.
    epose proof (H2 := P4 Γ (φ^[evar: 0 ↦ φ']) (! ex , patt_not (φ)) _ _).
    clear H H1.
    epose proof (otherH := prf_weaken_conclusion Γ (ex , patt_equal φ' b0) ((φ^[evar: 0 ↦ φ'] ---> ⊥) ---> ex , (! φ)) ((φ^[evar: 0 ↦ φ'] ---> ⊥) ---> ! ! ex , (! φ)) _ _ _).
    eapply MP in otherH.
    2: {
      epose proof (H1 := prf_weaken_conclusion Γ (φ^[evar: 0 ↦ φ'] ---> ⊥) (ex , (! φ)) (! ! ex , (! φ)) _ _ _).
      eapply MP. 2: apply H1.
      apply not_not_intro.
      wf_auto2.
    }

    eapply useBasicReasoning with (i := AnyReasoning) in otherH.
    eapply MP in otherH.
    {
      eapply useBasicReasoning with (i := AnyReasoning) in H2.
      eapply syllogism_meta in H2.
      3,4: wf_auto2.
      3: apply otherH.
      2: wf_auto2.
      exact H2.
    }
    exact H0.
    Unshelve.
    (* I do not like this. Why do we have unification variables on which nothing depends? *)
    4,5,6: apply well_formed_bott.
    4: exact Γ.
    all: wf_auto2.
  Defined.

End ProofSystemTheorems.


Lemma MLGoal_rewriteBy {Σ : Signature} {syntax : Syntax}
    (Γ : Theory) (l₁ l₂ : hypotheses) name (φ₁ φ₂ : Pattern) (C : PatternCtx) :
  theory ⊆ Γ ->
  mu_in_evar_path (pcEvar C) (pcPattern C) 0 = false ->
  mkMLGoal Σ Γ (l₁ ++ (mkNH _ name (φ₁ =ml φ₂)) :: l₂) (emplace C φ₂) AnyReasoning ->
  mkMLGoal Σ Γ (l₁ ++ (mkNH _ name (φ₁ =ml φ₂)) :: l₂) (emplace C φ₁) AnyReasoning .
Proof.
  intros HΓ HmfC H.
  mlExtractWF wfl wfg.
  unfold patterns_of in wfl. rewrite map_app in wfl.
  pose proof (wfl₁ := wfapp_proj_1 _ _ wfl).
  apply wfapp_proj_2 in wfl.
  unfold wf in wfl. simpl in wfl.
  apply andb_prop in wfl.
  destruct wfl as [wfeq wfl₂].
  pose proof (wfC := wf_emplaced_impl_wf_context _ _ wfg).
  remember C as C'.
  destruct C as [CE Cψ]. unfold PC_wf in wfC. simpl in *.

  lazymatch goal with
    | [ |- of_MLGoal (mkMLGoal _ _ ?l _ _) ]
      => remember (names_of l) as names_of_l 
  end.

  _mlAssert_nocheck ((fresh names_of_l) : (emplace C' φ₁ <---> emplace C' φ₂)). (* !!! *)
  { unfold emplace in *. wf_auto2. }
  { fromMLGoal.
    unfold patterns_of.
    rewrite map_app.
    simpl.
    apply equality_elimination_basic_ar_iter; auto.
    { wf_auto2. }
    { wf_auto2. }
  }
  unfold patt_iff.
  epose proof (Htmp := (pf_conj_elim_r _ _ _ _ _)).
  apply @useBasicReasoning with (i := AnyReasoning) in Htmp.
  eapply (MLGoal_applyMetaIn Γ _ _ (fresh names_of_l) _ _ Htmp).
  clear Htmp.

  replace (l₁ ++ (mkNH _ name (φ₁ =ml φ₂)) :: l₂)
     with ((l₁ ++ (mkNH _ name (φ₁ =ml φ₂)) :: l₂) ++ [])
     in H
    by (rewrite app_nil_r; reflexivity).
  apply mlGoal_clear_hyp with (h := (mkNH _ (fresh names_of_l) ((emplace C' φ₂) ---> (emplace C' φ₁)))) in H.

  lazymatch goal with
    | [ |- of_MLGoal (mkMLGoal _ _ ?l _ _) ]
      => remember (names_of l) as names_of_l' 
  end.

  eapply mlGoal_assert with (name := (fresh names_of_l')).
  2: {
    apply H.
  }
  { wf_auto2. }

  simpl.
  rewrite -app_assoc.
  simpl.
  eapply MLGoal_weakenConclusion.

  replace ((l₁ ++ (mkNH _ name (φ₁ =ml φ₂)) :: l₂)
            ++ [(mkNH _ (fresh names_of_l) ((emplace C' φ₂) ---> (emplace C' φ₁)));
                (mkNH _ (fresh names_of_l') (emplace C' φ₂))])
  with (((l₁ ++ (mkNH _ name (φ₁ =ml φ₂)) :: l₂)
        ++ [mkNH _ (fresh names_of_l) ((emplace C' φ₂) ---> (emplace C' φ₁))])
        ++ [mkNH _ (fresh names_of_l') (emplace C' φ₂)]).
  2: {  rewrite -app_assoc. simpl. reflexivity. }
  useBasicReasoning.
  apply MLGoal_exactn.
  Unshelve.
  all: abstract (wf_auto2).
Defined.

Ltac2 mlRewriteBy (name' : constr) (atn : int) :=
_mlReshapeHypsByName name';
lazy_match! goal with
| [ |- @of_MLGoal ?sgm (@mkMLGoal ?sgm ?g (?l₁ ++ (mkNH _ _ (?a' =ml ?a))::?l₂) ?p AnyReasoning)]
  => 
    let hr : HeatResult := heat atn a' p in
    let heq := Control.hyp (hr.(equality)) in
    let pc := (hr.(pc)) in
    eapply (@cast_proof_ml_goal _ $g) >
      [ rewrite $heq; reflexivity | ()];
    Std.clear [hr.(equality)];
    apply MLGoal_rewriteBy
    > [ ()
      | ()
      | lazy_match! goal with
        | [ |- of_MLGoal (@mkMLGoal ?sgm ?g ?l ?p AnyReasoning)]
          =>
            let heq2 := Fresh.in_goal ident:(heq2) in
            let plugged := Pattern.instantiate (hr.(ctx)) a in
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
            Std.clear [heq2 ; (hr.(star_ident)); (hr.(star_eq))];
            _mlReshapeHypsBack
        end
      ]
end
.

Tactic Notation "mlRewriteBy" constr(name') "at" constr(atn) :=
(let ff := ltac2:(name'' atn |-
                    mlRewriteBy
                      (Option.get (Ltac1.to_constr(name'')))
                      (constr_to_int (Option.get (Ltac1.to_constr(atn))))
                 ) in
 ff name' atn).



Local Example ex_rewriteBy {Σ : Signature} {syntax : Syntax} Γ a a' b:
  theory ⊆ Γ ->
  well_formed a ->
  well_formed a' ->
  well_formed b ->
  mu_free b ->
  Γ ⊢i a $ b ---> (a' =ml a) ---> a' $ b
  using AnyReasoning.
Proof.
  intros HΓ wfa wfa' wfb mfb.
  toMLGoal.
  { wf_auto2. }
  mlIntro "H0". mlIntro "H1".
  mlRewriteBy "H1" at 1.
  { assumption. }
  { apply mu_free_in_path.
    simpl.
  assumption.
  }
  mlExactn 0.
Defined.

Lemma patt_equal_implies_iff
  {Σ : Signature} {syntax : Syntax} (φ1 φ2 : Pattern) (Γ : Theory) (i : ProofInfo) x :
  theory ⊆ Γ ->
  x ∉ (free_evars φ1 ∪ free_evars φ2) ->
  ProofInfoLe
    (ExGen := {[ev_x; x]},
      SVSubst := ∅, KT := false, AKT := false) i ->
  well_formed φ1 ->
  well_formed φ2 ->
  Γ ⊢i φ1 =ml φ2 using i ->
  Γ ⊢i (φ1 <---> φ2) using i.
Proof.
  intros HΓ Hx pile wfφ1 wfφ2 H.
  unfold "=ml" in H.
  apply total_phi_impl_phi_meta with (Γ := Γ) (i := i) (x := x) in H.
  { assumption. }
  { assumption. }
  { simpl. set_solver. }
  { wf_auto2. }
  { simpl.
    replace (free_evars φ1 ∪ free_evars φ2 ∪ ∅ ∪ ∅
    ∪ (free_evars φ2 ∪ free_evars φ1 ∪ ∅) ∪ ∅)
    with (free_evars φ1 ∪ free_evars φ2)
    by set_solver.
    apply pile.
  }
Defined.


Lemma disj_equals_greater_1_meta {Σ : Signature} {syntax : Syntax} Γ φ₁ φ₂ i x:
  theory ⊆ Γ ->
  x ∉ free_evars φ₁ ∪ free_evars φ₂ ->
  ProofInfoLe
       (ExGen := {[ev_x; x]},
        SVSubst := ∅, KT := false, AKT := false) i ->
  well_formed φ₁ ->
  well_formed φ₂ ->
  Γ ⊢i φ₁ ⊆ml φ₂ using i ->
  Γ ⊢i (φ₁ or φ₂) =ml φ₂ using i.
Proof.
  intros HΓ Hx pile wfφ₁ wfφ₂ Hsub.
  apply patt_iff_implies_equal; try_wfauto2.
  { eapply pile_trans;[|apply pile].
    try_solve_pile.
  }
  apply pf_iff_split; try_wfauto2.
  + toMLGoal.
    { wf_auto2. }
    mlIntro "H0". mlDestructOr "H0".
    * apply total_phi_impl_phi_meta with (x := x) in Hsub;[ | auto |assumption|try_wfauto2|idtac].
      { fromMLGoal. apply Hsub. }
      { simpl. apply pile. }
    * fromMLGoal. useBasicReasoning; apply A_impl_A;try_wfauto2.
  + toMLGoal.
    { wf_auto2. }
    mlIntro "H0". mlRight.
    fromMLGoal. 
    useBasicReasoning.
    apply A_impl_A; try_wfauto2.
Defined.

Lemma def_not_phi_impl_not_total_phi {Σ : Signature} {syntax : Syntax} Γ φ:
  theory ⊆ Γ ->
  well_formed φ ->
  Γ ⊢i ⌈ ! φ ⌉ ---> ! ⌊ φ ⌋ using BasicReasoning.
Proof.
  intros HΓ wfφ.
  toMLGoal.
  { wf_auto2. }
  mlIntro "H0".
  unfold patt_total. (* TODO need an [mlUnfold in _] tactic *)
  unfold patt_not.
  mlIntro "H1".
  mlApply "H1".
  mlExact "H0".
Defined.

Lemma def_def_phi_impl_def_phi
  {Σ : Signature} {syntax : Syntax} {Γ : Theory} (φ : Pattern) x :
  theory ⊆ Γ ->
  x ∉ free_evars φ ->
  well_formed φ ->
    Γ ⊢i ⌈ ⌈ φ ⌉ ⌉ ---> ⌈ φ ⌉
  using 
    (ExGen := {[ev_x; x]},
     SVSubst := ∅, KT := false, AKT := false).
Proof.
  intros HΓ Hx wfφ.
  eapply (cast_proof').
  { 
    remember (ctx_app_r (patt_sym (Definedness_Syntax.inj definedness)) box ltac:(wf_auto2)) as AC1.
    remember (ctx_app_r (patt_sym (Definedness_Syntax.inj definedness)) AC1 ltac:(wf_auto2)) as AC2.
    replace (⌈ ⌈ φ ⌉ ⌉) with (subst_ctx AC2 φ) by (subst; reflexivity).
    subst. reflexivity.
  }
  gapply in_context_impl_defined.
  {
    simpl. try_solve_pile.
  }
  { exact HΓ. }
  { set_solver. }
  { exact wfφ. }
Defined.

Lemma bott_not_defined {Σ : Signature} {syntax : Syntax} Γ :
  Γ ⊢i ! ⌈ ⊥ ⌉ using BasicReasoning.
Proof.
  apply Prop_bott_right.
  { wf_auto2. }
Defined.

Lemma not_def_phi_impl_not_phi {Σ : Signature} {syntax : Syntax} Γ φ x :
  theory ⊆ Γ ->
  x ∉ free_evars φ ->
  well_formed φ ->
  Γ ⊢i ! ⌈ φ ⌉ ---> ! φ
  using 
  (ExGen := {[ev_x; x]},
   SVSubst := ∅, KT := false, AKT := false).
Proof.
  intros HΓ Hx wfφ.
  toMLGoal.
  { wf_auto2. }
  mlIntro "H0".
  mlIntro "H1".
  mlApply "H0".
  mlClear "H0".
  mlApplyMeta phi_impl_defined_phi; auto. mlExact "H1".
Defined.

Lemma tot_phi_impl_tot_def_phi {Σ : Signature} {syntax : Syntax} Γ φ x :
  theory ⊆ Γ ->
  x ∉ free_evars φ ->
  well_formed φ ->
  Γ ⊢i ⌊ φ ⌋ ---> ⌊ ⌈ φ ⌉ ⌋
  using 
     (ExGen := {[ev_x; x]},
      SVSubst := ∅, KT := false, AKT := false).
Proof.
  intros HΓ Hx wfφ.
  toMLGoal.
  { wf_auto2. }
  mlIntro "H0".
  mlIntro "H1".
  mlApply "H0".
  mlClear "H0".
  fromMLGoal.
  gapply Framing_right.
  { apply pile_refl. }
  { wf_auto2. }
  {
    try_solve_pile.
  }
  apply not_def_phi_impl_not_phi; assumption.
Defined.

Lemma def_of_pred_impl_pred {Σ : Signature} {syntax : Syntax} Γ ψ :
  theory ⊆ Γ ->
  well_formed ψ ->
  Γ ⊢i (ψ =ml patt_bott) or (ψ =ml patt_top) using AnyReasoning ->
  Γ ⊢i ⌈ ψ ⌉ ---> ψ using AnyReasoning.
Proof.
  intros HΓ wfψ H.
  toMLGoal.
  {wf_auto2. }
  mlAdd H as "H0".
  mlDestructOr "H0" as "H1" "H1".
  - mlRewriteBy "H1" at 2.
    { exact HΓ. }
    { simpl. unfold mu_in_evar_path. cbn. case_match;[reflexivity|].
      case_match;[|contradiction].
      rewrite Nat.max_0_r in H0.
      rewrite maximal_mu_depth_to_0 in H0.
      {
        subst star. clear.
        eapply evar_is_fresh_in_richer'.
        2: {
          apply set_evar_fresh_is_fresh.
        }
        {
          simpl. set_solver.
        }
      }
      inversion H0.
    }
    mlRewriteBy "H1" at 1.
    { exact HΓ. }
    { simpl.
    unfold mu_in_evar_path. cbn. case_match;[reflexivity|].
      case_match;[|contradiction].
      simpl in H0. inversion H0.
    }
    mlClear "H1".
    fromMLGoal.
    aapply bott_not_defined.
  - mlRewriteBy "H1" at 2.
    { exact HΓ. }
    { simpl. unfold mu_in_evar_path. cbn. case_match;[reflexivity|].
      case_match;[|contradiction].
      rewrite Nat.max_0_r in H0.
      rewrite maximal_mu_depth_to_0 in H0.
      {
        subst star. clear.
        eapply evar_is_fresh_in_richer'.
        2: {
          apply set_evar_fresh_is_fresh.
        }
        {
          simpl. set_solver.
        }
      }
      inversion H0.
    }
    mlClear "H1".
    unfold patt_top. mlIntro. mlIntro. mlExactn 1.
Defined.

(* TODO need this non-meta *)
Lemma subseteq_antisym_meta {Σ : Signature} {syntax : Syntax} Γ φ₁ φ₂:
  theory ⊆ Γ ->
  well_formed φ₁ ->
  well_formed φ₂ ->
  Γ ⊢i (φ₁ ⊆ml φ₂) and (φ₂ ⊆ml φ₁) using AnyReasoning ->
  Γ ⊢i φ₁ =ml φ₂ using AnyReasoning.
Proof.
  intros HΓ wfφ₁ wfφ₂ H.
  unfold "=ml".
  apply phi_impl_total_phi_meta.
  { wf_auto2. }
  { apply pile_any. }
  toMLGoal.
  { wf_auto2. }
  mlAdd H as "H0".
  mlDestructAnd "H0" as "H1" "H2".
  remember (fresh_evar (φ₁ $ φ₂)) as x.

  epose proof (Htmp := (total_phi_impl_phi Γ _ x HΓ _)).
  apply useGenericReasoning with (i := AnyReasoning) in Htmp.
  2: { apply pile_any. }
  mlApplyMetaRaw Htmp in "H1".
  clear Htmp.

  epose proof (Htmp := (total_phi_impl_phi Γ _ x HΓ _)).
  apply useGenericReasoning with (i := AnyReasoning) in Htmp.
  2: { apply pile_any. }
  unshelve (mlApplyMetaRaw Htmp in "H2"). 2-3: wf_auto2.
  clear Htmp.
  mlSplitAnd.
  - mlExact "H1".
  - mlExact "H2".
  Unshelve.
  all: wf_auto2.
  exact (set_evar_fresh_is_fresh (φ₁ $ φ₂)).
  pose proof (set_evar_fresh_is_fresh (φ₁ $ φ₂)).
  unfold evar_is_fresh_in in H. set_solver.
Defined.

Lemma propagate_membership_conjunct_1 {Σ : Signature} {syntax : Syntax}
    Γ AC x φ₁ φ₂ :
  theory ⊆ Γ ->
  well_formed φ₁ ->
  well_formed φ₂ ->
  Γ ⊢i (subst_ctx AC (φ₁ and ((patt_free_evar x) ∈ml φ₂))) ---> ((patt_free_evar x) ∈ml φ₂)
  using AnyReasoning.
Proof.
  intros HΓ wfφ₁ wfφ₂.
  unfold patt_in.
  eapply syllogism_meta.
  1,3 : wf_auto2.
  2: apply Framing.
  2: { apply pile_any. }
  2: useBasicReasoning; apply pf_conj_elim_r.
  1-3: wf_auto2.
  eapply syllogism_meta.
  1,3: wf_auto2.
  2: gapply in_context_impl_defined.
  3: exact HΓ.
  4: wf_auto2.
  2: apply pile_any.
  1: wf_auto2.
  instantiate (1 :=  evar_fresh (elements ({[x]} ∪ free_evars φ₂ ∪ AC_free_evars AC))).
  { simpl. eapply not_elem_of_larger_impl_not_elem_of.
    2: apply set_evar_fresh_is_fresh'. set_solver. }
  gapply def_def_phi_impl_def_phi.
  { apply pile_any. }
  { assumption. }
  { instantiate (1 := evar_fresh (elements ({[x]} ∪ free_evars φ₂))). 
    simpl.  eapply not_elem_of_larger_impl_not_elem_of.
    2: apply set_evar_fresh_is_fresh'. set_solver. }
  { wf_auto2. }
Defined.


Lemma ceil_monotonic {Σ : Signature} {syntax : Syntax} Γ φ₁ φ₂ i :
  theory ⊆ Γ ->
  well_formed φ₁ ->
  well_formed φ₂ ->
  Γ ⊢i φ₁ ---> φ₂ using i ->
  Γ ⊢i ⌈ φ₁ ⌉ ---> ⌈ φ₂ ⌉ using i.
Proof.
  intros HΓ wfφ₁ wfφ₂ H.
  unshelve (eapply Framing_right).
  { wf_auto2. }
  { try_solve_pile. }
  exact H.
Defined.

Lemma floor_monotonic {Σ : Signature} {syntax : Syntax} Γ φ₁ φ₂ i :
  theory ⊆ Γ ->
  well_formed φ₁ ->
  well_formed φ₂ ->
  Γ ⊢i φ₁ ---> φ₂ using i ->
  Γ ⊢i ⌊ φ₁ ⌋ ---> ⌊ φ₂ ⌋ using i.
Proof.
  intros HΓ wfφ₁ wfφ₂ H.
  unfold patt_total.
  apply BasicProofSystemLemmas.modus_tollens.
  apply ceil_monotonic.
  { assumption. }
  { wf_auto2. }
  { wf_auto2. }
  apply BasicProofSystemLemmas.modus_tollens.
  exact H.
Defined.

Lemma double_not_ceil_alt {Σ : Signature} {syntax : Syntax} Γ φ i :
  theory ⊆ Γ ->
  well_formed φ ->
  Γ ⊢i ( ⌈ ! ⌈ φ ⌉ ⌉ ---> (! ⌈ φ ⌉)) using i ->
  Γ ⊢i ( ⌈ φ ⌉ ---> ! ( ⌈ ! ⌈ φ ⌉ ⌉)) using i.
Proof.
  intros HΓ wfφ H.
  toMLGoal.
  { wf_auto2. }
  mlRewrite (useBasicReasoning i (not_not_iff Γ (⌈ φ ⌉) ltac:(wf_auto2))) at 1.
  fromMLGoal.
  apply BasicProofSystemLemmas.modus_tollens.
  exact H.
Defined.


Lemma membership_imp {Σ : Signature} {syntax : Syntax} Γ x φ₁ φ₂:
  theory ⊆ Γ ->
  well_formed φ₁ ->
  well_formed φ₂ ->
  Γ ⊢i (patt_free_evar x ∈ml (φ₁ ---> φ₂)) <---> ((patt_free_evar x ∈ml φ₁) ---> (patt_free_evar x ∈ml φ₂))
  using (ExGen := {[ev_x; x]}, SVSubst := ∅, KT := false, AKT := false).
Proof.
  intros HΓ wfφ₁ wfφ₂.

  toMLGoal.
  { wf_auto2. }
  mlRewrite (useBasicReasoning (ExGen := {[ev_x; x]}, SVSubst := ∅, KT := false, AKT := false) (@impl_iff_notp_or_q Σ Γ φ₁ φ₂ ltac:(wf_auto2) ltac:(wf_auto2))) at 1.
  mlRewrite (useBasicReasoning (ExGen := {[ev_x; x]}, SVSubst := ∅, KT := false, AKT := false) (@membership_or_iff Σ syntax Γ x (! φ₁) φ₂ ltac:(wf_auto2) ltac:(wf_auto2) HΓ)) at 1.
  mlRewrite (@membership_not_iff Σ syntax Γ φ₁ x ltac:(wf_auto2) HΓ) at 1.
  mlRewrite <- (useBasicReasoning (ExGen := {[ev_x; x]}, SVSubst := ∅, KT := false, AKT := false) (@impl_iff_notp_or_q Σ Γ (patt_free_evar x ∈ml φ₁) (patt_free_evar x ∈ml φ₂) ltac:(wf_auto2) ltac:(wf_auto2))) at 1.
  fromMLGoal.
  useBasicReasoning.
  apply pf_iff_equiv_refl.
  { wf_auto2. }
Defined.

Lemma membership_imp_1 {Σ : Signature} {syntax : Syntax} Γ x φ₁ φ₂:
  theory ⊆ Γ ->
  well_formed φ₁ ->
  well_formed φ₂ ->
  Γ ⊢i (patt_free_evar x ∈ml (φ₁ ---> φ₂)) ---> ((patt_free_evar x ∈ml φ₁) ---> (patt_free_evar x ∈ml φ₂))
  using (ExGen := {[ev_x; x]}, SVSubst := ∅, KT := false, AKT := false).
Proof.
  intros HΓ ??.
  eapply pf_iff_proj1.
  3: apply membership_imp.
  1,2,4,5: solve[wf_auto2].
  { exact HΓ. }
Defined.

Lemma membership_imp_2 {Σ : Signature} {syntax : Syntax} Γ x φ₁ φ₂:
  theory ⊆ Γ ->
  well_formed φ₁ ->
  well_formed φ₂ ->
  Γ ⊢i ((patt_free_evar x ∈ml φ₁) ---> (patt_free_evar x ∈ml φ₂)) ---> (patt_free_evar x ∈ml (φ₁ ---> φ₂))
  using (ExGen := {[ev_x; x]}, SVSubst := ∅, KT := false, AKT := false).
Proof.
  intros HΓ ??.
  eapply pf_iff_proj2.
  3: apply membership_imp.
  1,2,4,5: solve[wf_auto2].
  { exact HΓ. }
Defined.

Lemma ceil_propagation_exists_1 {Σ : Signature} {syntax : Syntax} Γ φ:
  theory ⊆ Γ ->
  well_formed (ex, φ) ->
  Γ ⊢i (⌈ ex, φ ⌉) ---> (ex, ⌈ φ ⌉)
  using BasicReasoning.
Proof.
  intros HΓ wfφ.
  apply Prop_ex_right.
  { wf_auto2. }
  { wf_auto2. }
Defined.

(* I think that lemmas like this one should not generate fresh variable themselves,
   but should be given them (ala "dependency injection").
   We can always have a wrapper that generates the fresh variables.
   But a concrete solution for this is for another PR.
   What I want to avoid is annotations that contain fresh variable generation.
   Maybe lemmas could be parameterized by a vector of a particular length
   of distinct fresh variables. We could have a type for that.
   Like, there would be a parameter
   [fresh_vars : n_fresh_vars n [φ1; φ2]].
   And maybe the whole Definedness module should be parameterized by a variable
   which is used in the definedness axiom. This way, every lemma will be parameterized
   twice - or, in general, multiple times.

   This lemma is interesting in that the fresh variable that it generates
   may be the same as the fresh variable that is used for the definedness axiom.
   But in general, we may want to have a disjoint set of fresh variables...
 *)
Lemma ceil_propagation_exists_2 {Σ : Signature} {syntax : Syntax} Γ φ:
  theory ⊆ Γ ->
  well_formed (ex, φ) ->
  Γ ⊢i (ex, ⌈ φ ⌉) ---> (⌈ ex, φ ⌉)
  using  (ExGen := {[ev_x; fresh_evar φ]}, SVSubst := ∅, KT := false, AKT := false).
Proof.
  intros HΓ wfφ.

  remember (fresh_evar φ) as x.
  replace (⌈ φ ⌉) with (⌈ φ ⌉^{evar: 0 ↦ x}^{{evar: x ↦ 0}}).
  2: {
    rewrite evar_quantify_evar_open.
       {
         pose proof (set_evar_fresh_is_fresh φ).
         unfold evar_is_fresh_in in H.
         simpl. set_solver.
       }
       { wf_auto2. }
       reflexivity.
  }
  apply BasicProofSystemLemmas.Ex_gen.
  { try_solve_pile. }
  {  simpl.
        pose proof (Hfr := set_evar_fresh_is_fresh φ).
        unfold evar_is_fresh_in in Hfr.
        simpl. set_solver.
  }
  mlSimpl.
  apply ceil_monotonic.
  { assumption. }
  { wf_auto2. }
  { wf_auto2. }
  useBasicReasoning.
  apply BasicProofSystemLemmas.Ex_quan.
  { wf_auto2. }
Defined.

Lemma ceil_propagation_exists_iff {Σ : Signature} {syntax : Syntax} Γ φ:
  theory ⊆ Γ ->
  well_formed (ex, φ) ->
  Γ ⊢i (⌈ ex, φ ⌉) <---> (ex, ⌈ φ ⌉)
  using  (ExGen := {[ev_x; fresh_evar φ]}, SVSubst := ∅, KT := false, AKT := false).
Proof.
  intros HΓ wfφ.
  apply pf_iff_split.
  { wf_auto2. }
  { wf_auto2. }
  - useBasicReasoning. apply ceil_propagation_exists_1; assumption.
  - apply ceil_propagation_exists_2; assumption.
Defined.

Lemma membership_exists {Σ : Signature} {syntax : Syntax} Γ x φ:
  theory ⊆ Γ ->
  well_formed (ex, φ) ->
  Γ ⊢i (patt_free_evar x ∈ml (ex, φ)) <---> (ex, patt_free_evar x ∈ml φ)
  using (ExGen := ⊤, SVSubst := ∅, KT := false, AKT := false).
Proof.
  intros HΓ wfφ.
  unfold "∈ml".
  toMLGoal.
  { wf_auto2. }
  mlRewrite <- (@liftProofInfoLe Σ Γ _ (ExGen := {[ev_x; fresh_evar (patt_free_evar x and φ)]}, SVSubst := ∅, KT := false, AKT := false) (ExGen := ⊤, SVSubst := ∅, KT := false, AKT := false) ltac:(try_solve_pile) (@ceil_propagation_exists_iff Σ syntax Γ (patt_free_evar x and φ) HΓ ltac:(wf_auto2))) at 1.
  fromMLGoal.
  assert (Htmp: Γ ⊢i (patt_free_evar x and ex, φ) <---> (ex, (patt_free_evar x and φ)) using (ExGen := ⊤, SVSubst := ∅, KT := false, AKT := false)).
  { (* prenex-exists-and *)
    toMLGoal.
    { wf_auto2. }
    mlRewrite (useBasicReasoning (ExGen := ⊤, SVSubst := ∅, KT := false, AKT := false) (patt_and_comm Γ (patt_free_evar x) (ex, φ) ltac:(wf_auto2) ltac:(wf_auto2))) at 1.
    mlRewrite <- (@liftProofInfoLe Σ Γ _ (ExGen := {[fresh_evar (φ and patt_free_evar x)]}, SVSubst := ∅, KT := false, AKT := false) (ExGen := ⊤, SVSubst := ∅, KT := false, AKT := false) ltac:(try_solve_pile) (@prenex_exists_and_iff Σ Γ φ (patt_free_evar x) ltac:(wf_auto2) ltac:(wf_auto2))) at 1.
    remember (evar_fresh (elements ({[x]} ∪ (free_evars φ)))) as y.
    mlSplitAnd; fromMLGoal.
    - apply (strip_exists_quantify_l Γ y).
      { subst y. simpl.
        eapply not_elem_of_larger_impl_not_elem_of.
        2: { apply set_evar_fresh_is_fresh'. }
        clear. set_solver.
      }
      { wf_auto2. }
      apply (strip_exists_quantify_r Γ y).
      { subst y. simpl.
        eapply not_elem_of_larger_impl_not_elem_of.
        2: { apply set_evar_fresh_is_fresh'. }
        clear. set_solver.
      }
      { wf_auto2. }
      apply ex_quan_monotone.
      { try_solve_pile. }
      mlSimpl.
      toMLGoal.
      { wf_auto2. }
      mlIntro "H0". mlDestructAnd "H0" as "H1" "H2". mlSplitAnd.
      + mlExact "H2".
      + mlExact "H1".
    - apply (strip_exists_quantify_l Γ y).
      { subst y. simpl.
        eapply not_elem_of_larger_impl_not_elem_of.
        2: { apply set_evar_fresh_is_fresh'. }
        clear. set_solver.
      }
      { wf_auto2. }
      apply (strip_exists_quantify_r Γ y).
      { subst y. simpl.
        eapply not_elem_of_larger_impl_not_elem_of.
        2: { apply set_evar_fresh_is_fresh'. }
        clear. set_solver.
      }
      { wf_auto2. }
      apply ex_quan_monotone.
      { try_solve_pile. }
      mlSimpl.
      toMLGoal.
      { wf_auto2. }
      (* TODO: Isn't this just a commutativity of [patt_and]? *)
      mlIntro "H0".
      mlDestructAnd "H0" as "H1" "H2".
      mlSplitAnd.
      + mlExact "H2".
      + mlExact "H1".
  }
  toMLGoal.
  { wf_auto2. }
  mlRewrite Htmp at 1.
  fromMLGoal.
  aapply pf_iff_equiv_refl.
  { try_solve_pile. }
  { wf_auto2. }
Defined.


Lemma membership_exists_1 {Σ : Signature} {syntax : Syntax} Γ x φ:
  theory ⊆ Γ ->
  well_formed (ex, φ) ->
  Γ ⊢i (patt_free_evar x ∈ml (ex, φ)) ---> (ex, patt_free_evar x ∈ml φ)
  using (ExGen := ⊤, SVSubst := ∅, KT := false, AKT := false).
Proof.
  intros HΓ ?.
  eapply pf_iff_proj1.
  3: apply membership_exists.
  1,2,4: solve[wf_auto2].
  { exact HΓ. }
Defined.

Lemma membership_exists_2 {Σ : Signature} {syntax : Syntax} Γ x φ:
  theory ⊆ Γ ->
  well_formed (ex, φ) ->
  Γ ⊢i (ex, patt_free_evar x ∈ml φ) ---> (patt_free_evar x ∈ml (ex, φ))
  using (ExGen := ⊤, SVSubst := ∅, KT := false, AKT := false).
Proof.
  intros HΓ ?.
  eapply pf_iff_proj2.
  3: apply membership_exists.
  1,2,4: solve[wf_auto2].
  { exact HΓ. }
Defined.

Lemma membership_symbol_ceil_aux_aux_0 {Σ : Signature} {syntax : Syntax} Γ x φ:
  theory ⊆ Γ ->
  well_formed φ ->
  Γ ⊢i ((⌈ patt_free_evar x and φ ⌉) ---> (⌊ ⌈ patt_free_evar x and φ ⌉  ⌋))
  using (ExGen := ⊤, SVSubst := ∅, KT := false, AKT := false).
Proof.
  intros HΓ wfφ.
  unfold patt_total.
  eapply syllogism_meta.
  { wf_auto2. }
  2: { wf_auto2. }
  3: {
    apply BasicProofSystemLemmas.modus_tollens.
    {
      apply ceil_monotonic.
      { exact HΓ. }
      { wf_auto2. }
      2: {
        gapply membership_not_2.
        { try_solve_pile. }
        { wf_auto2. }
        { exact HΓ. }
      }
      { wf_auto2. }
    }
  }
  { wf_auto2. }
  toMLGoal.
  { wf_auto2. }

  mlRewrite (useBasicReasoning (ExGen := ⊤, SVSubst := ∅, KT := false, AKT := false) (not_not_iff Γ (⌈patt_free_evar x and φ ⌉) ltac:(wf_auto2))) at 1.
  fold (! ⌈ patt_free_evar x and φ ⌉ or ! ⌈ patt_free_evar x ∈ml (! φ) ⌉).
  mlRewrite (useBasicReasoning (ExGen := ⊤, SVSubst := ∅, KT := false, AKT := false) (not_not_iff Γ (! ⌈ patt_free_evar x and φ ⌉ or ! ⌈ patt_free_evar x ∈ml (! φ) ⌉) ltac:(wf_auto2))) at 1.
  fold ((⌈ patt_free_evar x and φ ⌉ and ⌈ patt_free_evar x ∈ml (! φ) ⌉)).
  unfold "∈ml".
  fromMLGoal.
  eapply cast_proof'.
  {
    replace (⌈ patt_free_evar x and φ ⌉)
            with (subst_ctx AC_patt_defined (patt_free_evar x and φ))
                 by reflexivity.
    replace (⌈ ⌈ patt_free_evar x and ! φ ⌉ ⌉)
            with (subst_ctx (ctx_app_r ((patt_sym (Definedness_Syntax.inj definedness))) AC_patt_defined ltac:(wf_auto2)) (patt_free_evar x and ! φ))
      by reflexivity.
    reflexivity.
  }
  gapply Singleton_ctx.
  { try_solve_pile. }
  { exact wfφ. }
  all: try_solve_pile.
Defined.

Lemma ceil_compat_in_or {Σ : Signature} {syntax : Syntax} Γ φ₁ φ₂:
  theory ⊆ Γ ->
  well_formed φ₁ ->
  well_formed φ₂ ->
  Γ ⊢i ( (⌈ φ₁ or φ₂ ⌉) <---> (⌈ φ₁ ⌉ or ⌈ φ₂ ⌉))
  using (ExGen := ∅, SVSubst := ∅, KT := false, AKT := false).
Proof.
  intros HΓ wfφ₁ wfφ₂.
  toMLGoal.
  { wf_auto2. }
  mlSplitAnd; mlIntro "H0".
  - mlApplyMeta (useBasicReasoning (ExGen := ∅, SVSubst := ∅, KT := false, AKT := false) (Prop_disj_right Γ φ₁ φ₂ (patt_sym (Definedness_Syntax.inj definedness)) ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2) )).
    mlExact "H0".
  - mlDestructOr "H0" as "H1" "H2"; fromMLGoal.
    + unshelve (eapply Framing_right).
      * wf_auto2.
      * try_solve_pile.
      * toMLGoal. wf_auto2. mlIntro "H0'". mlLeft. mlExact "H0'".
    + unshelve (eapply Framing_right).
      * wf_auto2.
      * try_solve_pile.
      * toMLGoal. wf_auto2. mlIntro "H0'". mlRight. mlExact "H0'".
Defined.


Lemma helper_propositional_lemma_1 (Σ : Signature) Γ φ₁ φ₂:
  well_formed φ₁ = true ->
  well_formed φ₂ = true ->
  Γ ⊢i (! φ₁ or φ₂) ---> (! φ₁ or (φ₂ and φ₁)) using BasicReasoning.
Proof.
  mlIntro "H0".
  mlClassic (φ₁) as "H1'" "H1'".
  { assumption. }
  { mlTauto. }
  { mlTauto. }
Defined.

Lemma membership_symbol_ceil_aux_0 {Σ : Signature} {syntax : Syntax} Γ x y φ:
  theory ⊆ Γ ->
  well_formed φ ->
  Γ ⊢i (⌈ patt_free_evar x and φ ⌉) ---> ⌈ patt_free_evar y and ⌈ patt_free_evar x and φ ⌉ ⌉
  using (ExGen := ⊤, SVSubst := ∅, KT := false, AKT := false).
Proof.
  intros HΓ wfφ.

  toMLGoal.
  { wf_auto2. }
  mlIntro "H0".
  mlApplyMeta (membership_symbol_ceil_aux_aux_0 Γ x φ HΓ wfφ) in "H0".
  fromMLGoal.
  unfold patt_total.
  fold (⌈ ! ⌈ patt_free_evar x and φ ⌉ ⌉ or ⌈ patt_free_evar y and ⌈ patt_free_evar x and φ ⌉ ⌉).
  toMLGoal.
  { wf_auto2. }
  mlRewrite <- (@liftProofInfoLe _ _ _ (ExGen := ∅, SVSubst := ∅, KT := false, AKT := false) (ExGen := ⊤, SVSubst := ∅, KT := false, AKT := false) ltac:(try_solve_pile) (ceil_compat_in_or Γ (! ⌈ patt_free_evar x and φ ⌉) (patt_free_evar y and ⌈ patt_free_evar x and φ ⌉) HΓ ltac:(wf_auto2) ltac:(wf_auto2))) at 1.

  ltac2:(mlApplyMeta ceil_monotonic with (φ₁ := (patt_free_evar y))).
  3: { exact HΓ. }
  2: {
    useBasicReasoning.
    mlIntro "H0".
    mlApplyMeta helper_propositional_lemma_1.
    mlRight.
    mlExact "H0".
  }
  fromMLGoal.
  gapply defined_evar.
  { try_solve_pile. }
  { exact HΓ. }
Defined.


Lemma membership_symbol_ceil_left_aux_0 {Σ : Signature} {syntax : Syntax} Γ φ:
  theory ⊆ Γ ->
  well_formed φ ->
  Γ ⊢i φ ---> (ex, ⌈ b0 and φ ⌉)
  using (ExGen := ⊤, SVSubst := ∅, KT := false, AKT := false).
Proof.
  intros HΓ wfφ.
  apply membership_elimination with (x := fresh_evar (φ ---> (ex , ⌈ b0 and φ ⌉))).
  { solve_fresh. }
  { try_solve_pile. }
  { wf_auto2. }
  { assumption. }
  remember (fresh_evar φ) as x.
  replace (b0 ∈ml (φ ---> ex , ⌈ b0 and φ ⌉))
    with ((b0 ∈ml (φ ---> ex , ⌈ b0 and φ ⌉))^{evar: 0 ↦ x}^{{evar: x ↦ 0}}).
  2: { rewrite evar_quantify_evar_open.
       {
         pose proof (set_evar_fresh_is_fresh φ).
         unfold evar_is_fresh_in in H.
         simpl. set_solver.
       }
       wf_auto2.
       reflexivity.
  }

  apply universal_generalization.
  { try_solve_pile. }
  { wf_auto2. }
  unfold evar_open. mlSimpl. simpl.
  rewrite bevar_subst_not_occur.
  { wf_auto2. }
  rewrite bevar_subst_not_occur.
  { wf_auto2. }
  toMLGoal.
  { wf_auto2. }
  pose proof (Htmp := @liftProofInfoLe Σ Γ _ (ExGen := {[ev_x; x]}, SVSubst := ∅, KT := false, AKT := false) (ExGen := ⊤, SVSubst := ∅, KT := false, AKT := false) ltac:(try_solve_pile) (@membership_imp Σ syntax Γ x φ (ex, ⌈ b0 and φ ⌉) HΓ ltac:(wf_auto2) ltac:(wf_auto2))).
  mlRewrite Htmp at 1. clear Htmp.
  pose proof (Htmp := @liftProofInfoLe Σ Γ _ (ExGen := ⊤, SVSubst := ∅, KT := false, AKT := false) (ExGen := ⊤, SVSubst := ∅, KT := false, AKT := false) ltac:(try_solve_pile) (@membership_exists Σ syntax Γ x (⌈ b0 and φ ⌉) HΓ ltac:(wf_auto2))).
  mlRewrite Htmp at 1.
  mlIntro "H0".
  remember (fresh_evar φ) as y.
  mlApplyMeta (useBasicReasoning (ExGen := ⊤, SVSubst := ∅, KT := false, AKT := false) (Ex_quan Γ (patt_free_evar x ∈ml ⌈ b0 and φ ⌉) y ltac:(wf_auto2))).
  unfold instantiate. mlSimpl. simpl.
  rewrite bevar_subst_not_occur.
  { wf_auto2. }

  unshelve (mlApplyMetaRaw (liftProofInfoLe _ _ _ _ (membership_symbol_ceil_aux_0 Γ y x φ HΓ wfφ))).
  { try_solve_pile. }
  subst y. subst x.
  mlExact "H0".
  all: try_solve_pile.
Defined.

Lemma ceil_and_x_ceil_phi_impl_ceil_phi {Σ : Signature} {syntax : Syntax} Γ (φ : Pattern) x:
  theory ⊆ Γ ->
  well_formed φ ->
  Γ ⊢i ( (⌈ patt_free_evar x and ⌈ φ ⌉ ⌉) ---> (⌈ φ ⌉))
  using (ExGen := ⊤, SVSubst := ∅, KT := false, AKT := false).
Proof.
  intros HΓ wfφ.
  eapply syllogism_meta.
  { wf_auto2. }
  2: { wf_auto2. }
  3: {
    gapply def_def_phi_impl_def_phi.
    { shelve. (* B is not known here *) }
    { assumption. }
    { shelve. (* B is not known here *) }
    { assumption. }
  }
  { wf_auto2. }
  apply ceil_monotonic.
  { exact HΓ. }
  { wf_auto2. }
  { wf_auto2. }
  toMLGoal.
  { wf_auto2. }
  mlIntro "H0".
  mlDestructAnd "H0" as "H1" "H2".
  mlExact "H2".
Unshelve.
  exact (fresh_evar φ).
  try_solve_pile.
  solve_fresh.
Defined.

Lemma membership_monotone {Σ : Signature} {syntax : Syntax} Γ (φ₁ φ₂ : Pattern) x i:
  theory ⊆ Γ ->
  well_formed φ₁ ->
  well_formed φ₂ ->
  Γ ⊢i (φ₁ ---> φ₂) using i ->
  Γ ⊢i (patt_free_evar x ∈ml φ₁) ---> (patt_free_evar x ∈ml φ₂) using i.
Proof.
  intros HΓ wfφ₁ wfφ₂ H.
  unfold patt_in.
  apply ceil_monotonic.
  { exact HΓ. }
  { wf_auto2. }
  { wf_auto2. }
  toMLGoal.
  { wf_auto2. }
  mlIntro "H0".
  mlDestructAnd "H0" as "H1" "H2".
  mlSplitAnd.
  - mlExact "H1".
  - mlApplyMetaRaw H in "H2".
    mlExact "H2".
Defined.

Lemma membership_symbol_ceil_left {Σ : Signature} {syntax : Syntax} Γ φ x:
  theory ⊆ Γ ->
  well_formed φ ->
  Γ ⊢i (patt_free_evar x ∈ml ⌈ φ ⌉) ---> (ex, (patt_bound_evar 0 ∈ml φ))
  using (ExGen := ⊤, SVSubst := ∅, KT := false, AKT := false).
Proof.
  intros HΓ wfφ.
  eapply syllogism_meta.
  { wf_auto2. }
  2: { wf_auto2. }
  2: {
    apply membership_monotone.
    { exact HΓ. }
    { wf_auto2. }
    2: {
      apply ceil_monotonic.
      { exact HΓ. }
      { assumption. }
      2: {
        apply membership_symbol_ceil_left_aux_0.
        { wf_auto2. }
        { wf_auto2. }
      }
      wf_auto2.
    }
    wf_auto2.
  }
  { wf_auto2. }

  eapply syllogism_meta.
  { wf_auto2. }
  2: { wf_auto2. }
  2: {
    apply membership_monotone.
    { exact HΓ. }
    { wf_auto2. }
    2: {
      gapply ceil_propagation_exists_1.
      { try_solve_pile. }
      { exact HΓ. }
      { wf_auto2. }
    }
    { wf_auto2. }
  }
  { wf_auto2. }

  remember (evar_fresh (elements ({[x]} ∪ (free_evars φ)))) as y.
  eapply syllogism_meta.
  { wf_auto2. }
  2: { wf_auto2. }
  2: {
    apply membership_monotone.
    { exact HΓ. }
    { wf_auto2. }
    2: {
      eapply cast_proof'.
      {
        rewrite -[⌈ ⌈ b0 and φ ⌉ ⌉](evar_quantify_evar_open y 0).
        { simpl.
          pose proof (Hfr := set_evar_fresh_is_fresh' ({[x]} ∪ (free_evars φ))).
          subst y. clear -Hfr. set_solver.
        }
        simpl. split_and!; auto.
        unfold well_formed, well_formed_closed in wfφ. destruct_and!.
        eapply well_formed_closed_ex_aux_ind; try eassumption; lia.
        reflexivity.
      }
      apply ex_quan_monotone.
      { try_solve_pile. }
      {
        unfold evar_open. mlSimpl. simpl.
        rewrite bevar_subst_not_occur.
        { wf_auto2. }
        gapply def_def_phi_impl_def_phi.
        { shelve. }
        { exact HΓ. }
        { shelve. }
        { wf_auto2. }
      }
    }
    {
      unfold exists_quantify.
      unfold well_formed. split_and!.
      { wf_auto2; case_match; wf_auto2. }
      unfold well_formed_closed. split_and!.
      { simpl; case_match; wf_auto2. }
      { simpl; case_match; try congruence. simpl.
        wf_auto2.
      }
    }
  }
  {
      unfold exists_quantify.
      unfold well_formed. split_and!.
      { wf_auto2; case_match; wf_auto2. }
      unfold well_formed_closed. split_and!.
      { simpl; case_match; wf_auto2. }
      { simpl; case_match; try congruence. simpl.
        wf_auto2.
      }
  }

  toMLGoal.
  {
    unfold exists_quantify.
    unfold well_formed. split_and!.
    { wf_auto2; case_match; wf_auto2. }
    unfold well_formed_closed. split_and!.
    { simpl; case_match; wf_auto2. }
    { simpl; case_match; try congruence. simpl.
      split_and!; auto; wf_auto2.
    }
  }

  unfold exists_quantify.
  pose proof (Htmp := membership_exists Γ x (evar_quantify y 0 ⌈ patt_free_evar y and φ ⌉) HΓ).
  feed specialize Htmp.
  { 
      unfold exists_quantify.
      unfold well_formed. split_and!.
      { wf_auto2; case_match; wf_auto2. }
      unfold well_formed_closed. split_and!.
      { simpl; case_match; wf_auto2. }
      { simpl; case_match; try congruence. simpl.
        split_and!; auto; wf_auto2.
      }
  }
  mlRewrite -> Htmp at 1. clear Htmp.

  fromMLGoal.
  case_match; try congruence.
  rewrite evar_quantify_fresh.
  { subst y. solve_fresh. }
  fold (patt_not b0).
  fold (patt_not (patt_not b0)).
  fold (patt_not φ).
  fold (! b0 or ! φ).
  fold (!(! b0 or ! φ)).
  fold (b0 and φ).
  fold (patt_defined (b0 and φ)).
  unfold patt_in.

  apply (strip_exists_quantify_l Γ y).
  { simpl.
    pose proof (Hfr := set_evar_fresh_is_fresh' ({[x]} ∪ (free_evars φ))).
    rewrite -Heqy in Hfr.
    clear -Hfr.
    set_solver.
  }
  { simpl. split_and!; auto; wf_auto2. }

  apply (strip_exists_quantify_r Γ y).
  { simpl.
    pose proof (Hfr := @set_evar_fresh_is_fresh' Σ ({[x]} ∪ (free_evars φ))).
    rewrite -Heqy in Hfr.
    clear -Hfr.
    set_solver.
  }
  { simpl. split_and!; auto; wf_auto2. }
  apply ex_quan_monotone.
  { try_solve_pile. }
  unfold evar_open. mlSimpl. simpl.
  rewrite bevar_subst_not_occur.
  { wf_auto2. }

  apply ceil_and_x_ceil_phi_impl_ceil_phi.
  { exact HΓ. }
  { wf_auto2. }
Unshelve.
  exact (fresh_evar (patt_free_evar y and φ)).
  try_solve_pile.
  solve_fresh.
Defined.


Lemma membership_symbol_ceil_right_aux_0 {Σ : Signature} {syntax : Syntax} Γ φ:
  theory ⊆ Γ ->
  well_formed φ ->
  Γ ⊢i (ex, (⌈ b0 and  φ ⌉ and b0)) ---> φ
  using (ExGen := ⊤, SVSubst := ∅, KT := false, AKT := false).
Proof.
  intros HΓ wfφ.
  apply prenex_forall_imp.
  1,2: wf_auto2.
  { try_solve_pile. }
  remember (fresh_evar (⌈ b0 and φ ⌉ and b0 ---> φ)) as x.
  eapply cast_proof'.
  {
    rewrite -[HERE in (all, HERE)](evar_quantify_evar_open x 0).
    { subst x. apply set_evar_fresh_is_fresh. }
    unfold well_formed, well_formed_closed in wfφ. destruct_and!. simpl.
    split_and!; auto.
    1-2: eapply well_formed_closed_ex_aux_ind; try eassumption; lia.
    reflexivity.
  }
  apply universal_generalization.
  { try_solve_pile. }
  { wf_auto2. }
  assert (Htmp: forall (φ₁ φ₂ φ₃ : Pattern),
             well_formed φ₁ ->
             well_formed φ₂ ->
             well_formed φ₃ ->
             Γ ⊢i ((! (φ₁ and (φ₂ and !φ₃))) ---> ((φ₁ and φ₂) ---> φ₃)) using (ExGen := ⊤, SVSubst := ∅, KT := false, AKT := false)).
  {
    intros φ₁ φ₂ φ₃ wfφ₁ wfφ₂ wfφ₃.
    toMLGoal.
    { wf_auto2. }
    mlIntro "H0".
    mlIntro "H1".
    mlDestructAnd "H1" as "H2" "H3".
    mlApplyMetaRaw (useBasicReasoning _ (not_not_elim Γ φ₃ wfφ₃)).
    mlIntro "H4".
    mlApply "H0".
    mlClear "H0".
    mlSplitAnd.
    { mlExact "H2". }
    mlSplitAnd.
    { mlExact "H3". }
    { mlExact "H4". }
  }
  eapply MP.
  2: apply Htmp.
  all: fold bevar_subst.
  2,3,4: wf_auto2.
  mlSimpl. simpl.
  rewrite bevar_subst_not_occur.
  { wf_auto2. }
  replace (⌈ patt_free_evar x and φ ⌉) with (subst_ctx AC_patt_defined (patt_free_evar x and φ)) by reflexivity.
  replace (patt_free_evar x and ! φ) with (subst_ctx box (patt_free_evar x and ! φ)) by reflexivity.
  gapply Singleton_ctx.
  { try_solve_pile. }
  exact wfφ.
Defined.

Lemma membership_symbol_ceil_right {Σ : Signature} {syntax : Syntax} Γ φ x:
  theory ⊆ Γ ->
  well_formed φ ->
  Γ ⊢i ((ex, (BoundVarSugar.b0 ∈ml φ)) ---> (patt_free_evar x ∈ml ⌈ φ ⌉))
  using (ExGen := ⊤, SVSubst := ∅, KT := false, AKT := false).
Proof.
  intros HΓ wfφ.
  remember (evar_fresh (elements ({[x]} ∪ (free_evars φ)))) as y.
  pose proof (Htmp := set_evar_fresh_is_fresh' ({[x]} ∪ free_evars φ)).
  rewrite -Heqy in Htmp.
  assert (x <> y).
  { solve_fresh_neq. }

  eapply syllogism_meta.
  1,3: wf_auto2.
  2: {
    apply (strip_exists_quantify_l Γ y).
    { simpl. clear -Htmp. set_solver. }
    { simpl. split_and!; try reflexivity. wf_auto2. }
    apply ex_quan_monotone.
    { try_solve_pile. }
    {
      unfold evar_open. mlSimpl. simpl.
      rewrite bevar_subst_not_occur.
      { wf_auto2. }
      eapply liftProofInfoLe.
      2: apply membership_symbol_ceil_aux_0 with (y := x); assumption.
      try_solve_pile.
    }
  }
  { unfold exists_quantify. simpl. repeat case_match; try congruence; wf_auto2. }

  eapply syllogism_meta.
  3: wf_auto2.
  1: { unfold exists_quantify. simpl. repeat case_match; try congruence; wf_auto2. }
  2: {
    apply pf_iff_proj2.
    2: { unfold exists_quantify. simpl. repeat case_match; try congruence; wf_auto2. }
    2: { 
      unfold exists_quantify. simpl.
      repeat case_match; try congruence; try contradiction.
      apply membership_exists.
      { exact HΓ. }
      { wf_auto2. }
    }
    { wf_auto2. }
  }
  { wf_auto2. }

  eapply syllogism_meta.
  1,3: wf_auto2.
  2: {
    apply membership_monotone.
    { exact HΓ. }
    { wf_auto2. }
    2: {
      apply (strip_exists_quantify_l Γ y).
      { simpl.
        rewrite evar_quantify_fresh.
        { subst y. solve_fresh. }
        set_solver.
      }
      { simpl. split_and!; try reflexivity. wf_auto2. }
      apply ex_quan_monotone.
      { try_solve_pile. }
      {
        eapply syllogism_meta.
        1: wf_auto2.
        3: {
          unfold evar_open. mlSimpl. simpl.
          rewrite bevar_subst_evar_quantify_free_evar.
          { wf_auto2. }
          apply membership_symbol_ceil_aux_0 with (y := y); assumption.
        }
        { wf_auto2. }
        2: {
          apply ceil_monotonic.
          { exact HΓ. }
          { wf_auto2. }
          2: {
            eapply pf_iff_proj1.
            { wf_auto2. }
            2: {
              (* TODO I think we should have an easier way of applying commutativity of [and] *)
              useBasicReasoning. apply patt_and_comm.
              { wf_auto2. }
              { wf_auto2. }
            }
            { wf_auto2. }
          }
          { wf_auto2. }
        }
        { wf_auto2. }
      }
    }
    { unfold exists_quantify. simpl. repeat case_match; try congruence; wf_auto2. }
  }
  { unfold exists_quantify. simpl. repeat case_match; try congruence; wf_auto2. }

  eapply syllogism_meta.
  { unfold exists_quantify. simpl. repeat case_match; try congruence; wf_auto2. }
  2: { wf_auto2. }
  2: {
    apply membership_monotone.
    { exact HΓ. }
    { unfold exists_quantify. simpl. repeat case_match; try congruence; wf_auto2. } 
    2: {
      unfold exists_quantify.
      simpl.
      repeat case_match; try congruence.
      rewrite evar_quantify_fresh.
      { subst y. solve_fresh. }
      gapply ceil_propagation_exists_2.
      { try_solve_pile. }
      { exact HΓ. }
      { wf_auto2. }
    }
    { wf_auto2. }
  }
  { wf_auto2. }
  apply membership_monotone.
  { exact HΓ. }
  { wf_auto2. }
  { wf_auto2. }
  apply ceil_monotonic.
  { exact HΓ. }
  { wf_auto2. }
  { wf_auto2. }
  unshelve eapply (liftProofInfoLe Γ _ (ExGen := ⊤, SVSubst := ∅, KT := false, AKT := false) (ExGen := ⊤, SVSubst := ∅, KT := false, AKT := false) (membership_symbol_ceil_right_aux_0 Γ _ HΓ wfφ)).
  try_solve_pile.
Defined.

Lemma def_phi_impl_tot_def_phi {Σ : Signature} {syntax : Syntax} Γ φ :
  theory ⊆ Γ ->
  well_formed φ ->
  Γ ⊢i ⌈ φ ⌉ ---> ⌊ ⌈ φ ⌉ ⌋
  using (ExGen := ⊤, SVSubst := ∅, KT := false, AKT := false).
Proof.
  intros HΓ wfφ.
  unfold patt_total.
  apply double_not_ceil_alt.
  { assumption. }
  { assumption. }
  apply membership_elimination with (x := fresh_evar (⌈ ! ⌈ φ ⌉ ⌉ ---> ! ⌈ φ ⌉)).
  { solve_fresh. }
  { try_solve_pile. }
  { wf_auto2. }
  { assumption. }

  remember (fresh_evar φ) as x.
  eapply cast_proof'.
  { 
    rewrite -[b0 ∈ml _](evar_quantify_evar_open x 0).
    { subst x. solve_fresh. }
    unfold well_formed, well_formed_closed in wfφ. destruct_and!.
    simpl; split_and!; auto.
    1-2: eapply well_formed_closed_ex_aux_ind; try eassumption; lia.
    reflexivity.
  }
  apply universal_generalization.
  { try_solve_pile. }
  { wf_auto2. }
  unfold evar_open. mlSimpl. simpl.
  rewrite bevar_subst_not_occur.
  { wf_auto2. }

  toMLGoal.
  { wf_auto2. }
  pose proof (Htmp := @liftProofInfoLe Σ Γ _ (ExGen := {[ev_x; x]}, SVSubst := ∅, KT := false, AKT := false) (ExGen := ⊤, SVSubst := ∅, KT := false, AKT := false) ltac:(try_solve_pile) (membership_imp Γ x (⌈ ! ⌈ φ ⌉ ⌉) (! ⌈ φ ⌉) HΓ ltac:(wf_auto2) ltac:(wf_auto2))).
  mlRewrite Htmp at 1. clear Htmp.
  mlIntro "H0".
  mlApplyMeta (@membership_symbol_ceil_left Σ syntax Γ (! ⌈ φ ⌉) x HΓ ltac:(wf_auto2)) in "H0".
  mlRewrite (@liftProofInfoLe Σ Γ _ (ExGen := {[ev_x; x]}, SVSubst := ∅, KT := false, AKT := false) (ExGen := ⊤, SVSubst := ∅, KT := false, AKT := false) ltac:(try_solve_pile) (membership_not_iff Γ (⌈ φ ⌉) x ltac:(wf_auto2) HΓ)) at 1.

  remember (evar_fresh (elements ({[x]} ∪ (free_evars φ)))) as y.
  pose proof (Hfr := set_evar_fresh_is_fresh' ({[x]} ∪ (free_evars φ))).
  eapply cast_proof_ml_hyps.
  {
    rewrite <- (evar_quantify_evar_open y 0 (b0 ∈ml (! ⌈ φ ⌉))).
    2: { subst x y. solve_fresh. }
    reflexivity.
    unfold well_formed, well_formed_closed in wfφ. destruct_and!.
    simpl; split_and!; auto.
    eapply well_formed_closed_ex_aux_ind; try eassumption; lia.
  }

  assert (Htmp: Γ ⊢i (((b0 ∈ml (! ⌈ φ ⌉))^{evar: 0 ↦ y}) ---> ((! (b0 ∈ml ⌈ φ ⌉))^{evar: 0 ↦ y})) using (ExGen := {[y]}, SVSubst := ∅, KT := false, AKT := false)).
  {
    unfold evar_open. mlSimpl. simpl. gapply membership_not_1.
    { try_solve_pile. }
    { wf_auto2. }
    exact HΓ.
  }

  mlApplyMeta (ex_quan_monotone Γ y _ _ _ ltac:(try_solve_pile) Htmp) in "H0".
  clear Htmp.


  eapply cast_proof_ml_hyps.
  {
    unfold exists_quantify.
    rewrite -> (evar_quantify_evar_open y 0 (! b0 ∈ml (⌈ φ ⌉))).
    2: { simpl. rewrite <- Heqy in Hfr. clear -Hfr. set_solver. }
    reflexivity.
    unfold well_formed, well_formed_closed in wfφ. destruct_and!.
    simpl; split_and!; auto.
    eapply well_formed_closed_ex_aux_ind; try eassumption; lia.
  }
  mlApplyMeta (useBasicReasoning (ExGen := ⊤, SVSubst := ∅, KT := false, AKT := false) (not_not_intro Γ (ex , (! b0 ∈ml ⌈ φ ⌉)) ltac:(wf_auto2))) in "H0".
  eapply cast_proof_ml_hyps.
  {
    replace (! ! ex , (! b0 ∈ml ⌈ φ ⌉)) with (! all , (b0 ∈ml ⌈ φ ⌉)) by reflexivity.
    reflexivity.
  }

  eassert (Htmp: Γ ⊢i (! (ex, b0 ∈ml φ)) ---> (! (patt_free_evar x ∈ml ⌈ φ ⌉)) using _).
  {
    apply BasicProofSystemLemmas.modus_tollens.
    apply membership_symbol_ceil_left; assumption.
  }
  mlApplyMeta Htmp.
  fromMLGoal.
  apply BasicProofSystemLemmas.modus_tollens.

  pose proof (Hfr' := @set_evar_fresh_is_fresh Σ φ).
  eapply cast_proof'.
  {
    rewrite -[THIS in (patt_exists THIS)](evar_quantify_evar_open x 0).
    { subst x. solve_fresh. }
    {
      unfold well_formed, well_formed_closed in wfφ. destruct_and!.
      simpl; split_and!; auto.
      eapply well_formed_closed_ex_aux_ind; try eassumption; lia.
    }
    rewrite -[THIS in (patt_forall THIS)](evar_quantify_evar_open y 0).
    { subst y. solve_fresh. }
    {
      unfold well_formed, well_formed_closed in wfφ. destruct_and!.
      simpl; split_and!; auto.
      eapply well_formed_closed_ex_aux_ind; try eassumption; lia.
    }
    reflexivity.
  }
  apply forall_gen.
  { simpl. case_match;[|congruence].
    subst x y.
    eapply evar_is_fresh_in_richer'.
    2: { eapply set_evar_fresh_is_fresh'. }
    simpl.
    rewrite free_evars_evar_quantify.
    pose proof (Hsub := free_evars_bevar_subst φ (patt_free_evar (fresh_evar φ)) 0).
    rewrite !simpl_free_evars.
    set_solver.
  }
  { try_solve_pile. }

  rewrite evar_quantify_evar_open.
  { subst x. solve_fresh. }
  {
    unfold well_formed, well_formed_closed in wfφ. destruct_and!.
    simpl; split_and!; auto.
    eapply well_formed_closed_ex_aux_ind; try eassumption; lia.
  }
  mlSimpl. unfold evar_open. simpl. rewrite bevar_subst_not_occur.
  { wf_auto2. }
  apply membership_symbol_ceil_right; assumption.
  try_solve_pile.
Defined.

Lemma def_tot_phi_impl_tot_phi {Σ : Signature} {syntax : Syntax} Γ φ :
  theory ⊆ Γ ->
  well_formed φ ->
  Γ ⊢i ⌈ ⌊ φ ⌋ ⌉ ---> ⌊ φ ⌋ using (ExGen := ⊤, SVSubst := ∅, KT := false, AKT := false).
Proof.
  intros HΓ wfφ.
  toMLGoal.
  { wf_auto2. }
  mlIntro "H0".
  mlApplyMeta (useBasicReasoning (ExGen := ⊤, SVSubst := ∅, KT := false, AKT := false) (not_not_intro Γ (⌈ ⌊ φ ⌋ ⌉) ltac:(wf_auto2))) in "H0".
  mlIntro "H1". mlApply "H0". mlClear "H0".
  fromMLGoal.
  apply def_phi_impl_tot_def_phi.
  { exact HΓ. }
  { wf_auto2. }
Defined.

Lemma floor_is_predicate {Σ : Signature} {syntax : Syntax} Γ φ :
  theory ⊆ Γ ->
  well_formed φ ->
  Γ ⊢i is_predicate_pattern (⌊ φ ⌋)
  using (ExGen := ⊤, SVSubst := ∅, KT := false, AKT := false).
Proof.
  intros HΓ wfφ.
  unfold is_predicate_pattern.
  unfold "=ml".
  toMLGoal.
  { wf_auto2. }

  mlRewrite (pf_iff_equiv_sym Γ (⌊ φ ⌋) (⌊ φ ⌋ <---> Top) (ExGen := ⊤, SVSubst := ∅, KT := false, AKT := false) ltac:(wf_auto2) ltac:(wf_auto2) (useBasicReasoning _ (phi_iff_phi_top Γ (⌊ φ ⌋) ltac:(wf_auto2)))) at 1.
  mlRewrite (pf_iff_equiv_sym Γ (! ⌊ φ ⌋) (⌊ φ ⌋ <---> ⊥) (ExGen := ⊤, SVSubst := ∅, KT := false, AKT := false) ltac:(wf_auto2) ltac:(wf_auto2) (useBasicReasoning _ (not_phi_iff_phi_bott Γ (⌊ φ ⌋) ltac:(wf_auto2)))) at 1.

  fromMLGoal.

  unfold patt_total at 1.
  unfold patt_total at 2.
  unfold patt_or.
  apply BasicProofSystemLemmas.modus_tollens.

  assert (Γ ⊢i (! ! ⌊ φ ⌋) <---> ⌊ φ ⌋ using (ExGen := ⊤, SVSubst := ∅, KT := false, AKT := false)).
  { toMLGoal.
    { wf_auto2. }
    mlSplitAnd; mlIntro "H0".
    - fromMLGoal.
      useBasicReasoning.
      apply not_not_elim.
      { wf_auto2. }
    - mlIntro "H1". mlApply "H1". mlClear "H1". mlExact "H0".
  }

  toMLGoal.
  { wf_auto2. }
  mlRewrite H at 1.
  clear H.
  mlIntro "H0".
  mlApplyMeta (def_phi_impl_tot_def_phi Γ (⌊ φ ⌋) HΓ ltac:(wf_auto2)) in "H0".
  fromMLGoal.
  apply floor_monotonic.
  { exact HΓ. }
  { wf_auto2. }
  { wf_auto2. }
  apply def_tot_phi_impl_tot_phi; assumption.
Defined.

Lemma def_propagate_not {Σ : Signature} {syntax : Syntax} Γ φ:
  theory ⊆ Γ ->
  well_formed φ ->
  Γ ⊢i (! ⌈ φ ⌉) <---> (⌊ ! φ ⌋)
  using (ExGen := ∅, SVSubst := ∅, KT := false, AKT := false).
Proof.
  intros HΓ wfφ.
  toMLGoal.
  { wf_auto2. }
  mlRewrite (useBasicReasoning (ExGen := ∅, SVSubst := ∅, KT := false, AKT := false) (not_not_iff Γ φ wfφ)) at 1.
  mlSplitAnd; mlIntro; mlExactn 0.
Defined.

Lemma def_def_phi_impl_tot_def_phi {Σ : Signature} {syntax : Syntax} Γ φ :
  theory ⊆ Γ ->
  well_formed φ ->
  Γ ⊢i ⌈ ⌈ φ ⌉ ⌉ ---> ⌊ ⌈ φ ⌉ ⌋
  using (ExGen := ⊤, SVSubst := ∅, KT := false, AKT := false).
Proof.
  intros HΓ wfφ.
  eapply syllogism_meta.
  1,3: wf_auto2.
  2: { gapply def_def_phi_impl_def_phi. shelve. assumption. shelve. assumption. }
  { wf_auto2. }
  apply def_phi_impl_tot_def_phi; assumption.
Unshelve.
  exact (fresh_evar φ).
  try_solve_pile.
  solve_fresh.
Defined.


Lemma ceil_is_predicate {Σ : Signature} {syntax : Syntax} Γ φ :
  theory ⊆ Γ ->
  well_formed φ ->
  Γ ⊢i is_predicate_pattern (⌈ φ ⌉)
  using AnyReasoning.
Proof.
  intros HΓ wfφ.
  unfold is_predicate_pattern.
  apply or_comm_meta.
  { wf_auto2. }
  { wf_auto2. }
  unfold patt_or.
  apply @syllogism_meta with (B := ⌈ ⌈ φ ⌉ ⌉).
  1,2,3: wf_auto2.
  - toMLGoal.
    { wf_auto2. }

    mlRewrite (useBasicReasoning AnyReasoning (not_not_iff Γ (⌈ ⌈ φ ⌉ ⌉) ltac:(wf_auto2))) at 1.
    mlIntro "H0".
    mlIntro "H1".
    mlApply "H0".
    mlClear "H0".
    mlRevertLast.
    pose proof (Htmp := def_propagate_not Γ (⌈ φ ⌉) HΓ ltac:(wf_auto2)).
    use AnyReasoning in Htmp.
    mlRewrite Htmp at 1.
    clear Htmp.
    mlIntro "H0".
    epose proof (Htmp := @liftProofInfoLe _ _ _ (ExGen := {[ev_x; evar_fresh (elements (free_evars (! ⌈ φ ⌉)))]}, SVSubst := ∅, KT := false, AKT := false) (ExGen := ⊤, SVSubst := ⊤, KT := false, AKT := false) ltac:(try_solve_pile) (total_phi_impl_phi Γ (! ⌈ φ ⌉) _ HΓ _ ltac:(wf_auto2))).
    mlApplyMeta Htmp in "H0".
    clear Htmp.
    mlRevertLast.
    pose proof (Htmp := @liftProofInfoLe _ _ _ (ExGen := ∅, SVSubst := ∅, KT := false, AKT := false) AnyReasoning ltac:(try_solve_pile) (def_propagate_not Γ φ HΓ ltac:(wf_auto2))).
    mlRewrite Htmp at 1.
    clear Htmp.
    fromMLGoal.
    unshelve (gapply deduction_theorem_noKT).
    6: exact HΓ.
    4,5: wf_auto2.
    3: { apply patt_iff_implies_equal.
      1,2: wf_auto2.
      { apply pile_refl. }
      remember_constraint as i'.
      toMLGoal.
      { wf_auto2. }
      mlSplitAnd; mlIntro "H0".
      2: { 
        useBasicReasoning.
        mlExFalso.
        mlExact "H0".
      }
      assert (Htmp: ((Γ ∪ {[! φ]})) ⊢i ! φ using i').
      { gapply BasicProofSystemLemmas.hypothesis. subst i'. try_solve_pile. wf_auto2. clear. set_solver. }
      apply phi_impl_total_phi_meta in Htmp.
      2: { wf_auto2. }
      2: { subst i'. apply pile_refl.  }
      mlAdd Htmp as "H1".  mlApply "H1". mlClear "H1".
      fromMLGoal.
      subst i'. 
      gapply Framing_right.
      { apply pile_refl. }
      { wf_auto2. }
      { try_solve_pile. }
      useBasicReasoning.
      apply not_not_intro.
      assumption.
    }
    { simpl. clear. try_solve_pile. }
    { set_solver. }
    { set_solver. }
    { reflexivity. }
    - eapply @syllogism_meta with (B := ⌊ ⌈ φ ⌉ ⌋).
      1,2,3: wf_auto2.
      { eapply liftProofInfoLe. 2: apply def_def_phi_impl_tot_def_phi; assumption. try_solve_pile. }
      unshelve (gapply deduction_theorem_noKT).
      4,5: wf_auto2.
      4: exact HΓ.
      3: {
        apply phi_impl_total_phi_meta.
        { wf_auto2. }
        { apply pile_refl. }
        apply pf_iff_split.
        1,2: wf_auto2.
        + toMLGoal. wf_auto2.
          (* use [mlIntro _] *)
          mlIntro "H1". mlClear "H1". fromMLGoal.
          useBasicReasoning. apply top_holds.
        + toMLGoal. wf_auto2.
          mlIntro "H0". mlClear "H0". fromMLGoal.
          gapply BasicProofSystemLemmas.hypothesis.
          { try_solve_pile. }
          { wf_auto2. }
          clear. set_solver.
      }
      { try_solve_pile. }
      {
        simpl. clear. set_solver.
      }
      { simpl. clear. set_solver. }
      { reflexivity. }
Unshelve.
  solve_fresh.
Defined.

Lemma predicate_elim
  {Σ : Signature} {syntax : Syntax} Γ (C : PatternCtx) (ψ : Pattern):
  theory ⊆ Γ ->
  well_formed (pcPattern C) ->
  well_formed ψ ->
  mu_in_evar_path (pcEvar C) (pcPattern C) 0 = false ->
  Γ ⊢ is_predicate_pattern ψ ->
  Γ ⊢ emplace C patt_bott ->
  Γ ⊢ emplace C patt_top ->
  Γ ⊢ emplace C ψ
.
Proof.
  intros HΓ HwfC Hwfψ HmfC Hpredψ Hb Ht.
  toMLGoal.
  { wf_auto2. }
  mlAdd Hpredψ as "Hψ".
  mlDestructOr "Hψ" as "H1" "H2".
  {
    mlAssert ("H": (emplace C ψ <---> emplace C Top )).
    { wf_auto2. }
    {
      pose proof (Htmp := equality_elimination_basic_mfpath Γ ψ Top C HΓ ltac:(wf_auto2) ltac:(wf_auto2)).
      feed specialize Htmp.
      {
        unfold PC_wf. exact HwfC.
      }
      { exact HmfC. }
      mlApplyMeta Htmp.
      mlExact "H1".
    }
    mlDestructAnd "H" as "HA" "HB".
    mlApply "HB".
    mlExactMeta Ht.
  }
  {
    mlAssert ("H": (emplace C ψ <---> emplace C Bot )).
    { wf_auto2. }
    {
      pose proof (Htmp := equality_elimination_basic_mfpath Γ ψ Bot C HΓ ltac:(wf_auto2) ltac:(wf_auto2)).
      feed specialize Htmp.
      {
        unfold PC_wf. exact HwfC.
      }
      { exact HmfC. }
      mlApplyMeta Htmp.
      mlExact "H2".
    }
    mlDestructAnd "H" as "HA" "HB".
    mlApply "HB".
    mlExactMeta Hb.
  }
Defined.

Lemma predicate_propagate_right_2 {Σ : Signature} {syntax : Syntax} Γ ϕ ψ P :
  theory ⊆ Γ ->
  well_formed ϕ ->
  well_formed ψ ->
  well_formed P ->
  Γ ⊢ is_predicate_pattern ψ ->
  Γ ⊢ ψ and P $ ϕ <---> P $ (ψ and ϕ).
Proof.
  intros HΓ wfϕ wfψ wfP predψ.
  toMLGoal.
  { wf_auto2. }
  mlAdd predψ as "Htmp".
  mlDestructOr "Htmp" as "Htmp1" "Htmp2".
  {
    mlRewriteBy "Htmp1" at 1.
    { exact HΓ. }
    { cbn. unfold mu_in_evar_path. cbn.
      rewrite !Nat.max_0_r.
      rewrite !maximal_mu_depth_to_0.
      {
        subst star. clear.
        eapply evar_is_fresh_in_richer'.
        2: {
          apply set_evar_fresh_is_fresh.
        }
        {
          cbn. set_solver.
        }
      }
      {
        subst star. clear.
        eapply evar_is_fresh_in_richer'.
        2: {
          apply set_evar_fresh_is_fresh.
        }
        {
          cbn. set_solver.
        }
      }
      {
        subst star. clear.
        eapply evar_is_fresh_in_richer'.
        2: {
          apply set_evar_fresh_is_fresh.
        }
        {
          cbn. set_solver.
        }
      }
      {
        cbn.
        repeat case_match; try reflexivity; lia.
      }
    }
    mlRewriteBy "Htmp1" at 1.
    { exact HΓ. }
    { cbn. unfold mu_in_evar_path. cbn.
      rewrite !Nat.max_0_r.
      rewrite !maximal_mu_depth_to_0.
      {
        subst star. clear.
        eapply evar_is_fresh_in_richer'.
        2: {
          apply set_evar_fresh_is_fresh.
        }
        {
          cbn. set_solver.
        }
      }
      {
        subst star. clear.
        eapply evar_is_fresh_in_richer'.
        2: {
          apply set_evar_fresh_is_fresh.
        }
        {
          cbn. set_solver.
        }
      }
      {
        cbn.
        repeat case_match; try reflexivity; lia.
      }
    }
    mlClear "Htmp1".
    mlRewrite (top_and Γ ϕ ltac:(wf_auto2)) at 1.
    mlRewrite (top_and Γ (P $ ϕ) ltac:(wf_auto2)) at 1.
    fromMLGoal.
    useBasicReasoning.
    apply pf_iff_equiv_refl.
    wf_auto2.
  }
  {
    mlRewriteBy "Htmp2" at 1.
    { exact HΓ. }
    { cbn. unfold mu_in_evar_path. cbn.
      rewrite !Nat.max_0_r.
      rewrite !maximal_mu_depth_to_0.
      {
        subst star. clear.
        eapply evar_is_fresh_in_richer'.
        2: {
          apply set_evar_fresh_is_fresh.
        }
        {
          cbn. set_solver.
        }
      }
      {
        subst star. clear.
        eapply evar_is_fresh_in_richer'.
        2: {
          apply set_evar_fresh_is_fresh.
        }
        {
          cbn. set_solver.
        }
      }
      {
        subst star. clear.
        eapply evar_is_fresh_in_richer'.
        2: {
          apply set_evar_fresh_is_fresh.
        }
        {
          cbn. set_solver.
        }
      }
      {
        cbn.
        repeat case_match; try reflexivity; lia.
      }
    }
    mlRewriteBy "Htmp2" at 1.
    { exact HΓ. }
    { cbn. unfold mu_in_evar_path. cbn.
      rewrite !Nat.max_0_r.
      rewrite !maximal_mu_depth_to_0.
      {
        subst star. clear.
        eapply evar_is_fresh_in_richer'.
        2: {
          apply set_evar_fresh_is_fresh.
        }
        {
          cbn. set_solver.
        }
      }
      {
        subst star. clear.
        eapply evar_is_fresh_in_richer'.
        2: {
          apply set_evar_fresh_is_fresh.
        }
        {
          cbn. set_solver.
        }
      }
      {
        cbn.
        repeat case_match; try reflexivity; lia.
      }
    }
    mlClear "Htmp2".
    mlRewrite (bott_and Γ ϕ ltac:(wf_auto2)) at 1.
    mlRewrite (bott_and Γ (P $ ϕ) ltac:(wf_auto2)) at 1.
    fromMLGoal.
    mlSplitAnd.
    {
      mlIntro "H". mlDestructBot "H".
    }
    {
      fromMLGoal.
      useBasicReasoning.
      apply Prop_bott_right.
      wf_auto2.
    }
  }
Defined.


Lemma predicate_propagate_left_2 {Σ : Signature} {syntax : Syntax} Γ ϕ ψ P :
  theory ⊆ Γ ->
  well_formed ϕ ->
  well_formed ψ ->
  well_formed P ->
  Γ ⊢ is_predicate_pattern ψ ->
  Γ ⊢ ψ and P $ ϕ <---> (ψ and P) $ ϕ.
Proof.
  intros HΓ wfϕ wfψ wfP predψ.
  toMLGoal.
  { wf_auto2. }
  mlAdd predψ as "Htmp".
  mlDestructOr "Htmp" as "Htmp1" "Htmp2".
  {
    mlRewriteBy "Htmp1" at 1.
    { exact HΓ. }
    { cbn. unfold mu_in_evar_path. cbn.
      rewrite !Nat.max_0_r.
      rewrite !maximal_mu_depth_to_0.
      {
        subst star. clear.
        eapply evar_is_fresh_in_richer'.
        2: {
          apply set_evar_fresh_is_fresh.
        }
        {
          cbn. set_solver.
        }
      }
      {
        subst star. clear.
        eapply evar_is_fresh_in_richer'.
        2: {
          apply set_evar_fresh_is_fresh.
        }
        {
          cbn. set_solver.
        }
      }
      {
        subst star. clear.
        eapply evar_is_fresh_in_richer'.
        2: {
          apply set_evar_fresh_is_fresh.
        }
        {
          cbn. set_solver.
        }
      }
      {
        cbn.
        repeat case_match; try reflexivity; lia.
      }
    }
    mlRewriteBy "Htmp1" at 1.
    { exact HΓ. }
    { cbn. unfold mu_in_evar_path. cbn.
      rewrite !Nat.max_0_r.
      rewrite !maximal_mu_depth_to_0.
      {
        subst star. clear.
        eapply evar_is_fresh_in_richer'.
        2: {
          apply set_evar_fresh_is_fresh.
        }
        {
          cbn. set_solver.
        }
      }
      {
        subst star. clear.
        eapply evar_is_fresh_in_richer'.
        2: {
          apply set_evar_fresh_is_fresh.
        }
        {
          cbn. set_solver.
        }
      }
      {
        cbn.
        repeat case_match; try reflexivity; lia.
      }
    }
    mlClear "Htmp1".
    mlRewrite (top_and Γ P ltac:(wf_auto2)) at 1.
    mlRewrite (top_and Γ (P $ ϕ) ltac:(wf_auto2)) at 1.
    fromMLGoal.
    useBasicReasoning.
    apply pf_iff_equiv_refl.
    wf_auto2.
  }
  {
    mlRewriteBy "Htmp2" at 1.
    { exact HΓ. }
    { cbn. unfold mu_in_evar_path. cbn.
      rewrite !Nat.max_0_r.
      rewrite !maximal_mu_depth_to_0.
      {
        subst star. clear.
        eapply evar_is_fresh_in_richer'.
        2: {
          apply set_evar_fresh_is_fresh.
        }
        {
          cbn. set_solver.
        }
      }
      {
        subst star. clear.
        eapply evar_is_fresh_in_richer'.
        2: {
          apply set_evar_fresh_is_fresh.
        }
        {
          cbn. set_solver.
        }
      }
      {
        subst star. clear.
        eapply evar_is_fresh_in_richer'.
        2: {
          apply set_evar_fresh_is_fresh.
        }
        {
          cbn. set_solver.
        }
      }
      {
        cbn.
        repeat case_match; try reflexivity; lia.
      }
    }
    mlRewriteBy "Htmp2" at 1.
    { exact HΓ. }
    { cbn. unfold mu_in_evar_path. cbn.
      rewrite !Nat.max_0_r.
      rewrite !maximal_mu_depth_to_0.
      {
        subst star. clear.
        eapply evar_is_fresh_in_richer'.
        2: {
          apply set_evar_fresh_is_fresh.
        }
        {
          cbn. set_solver.
        }
      }
      {
        subst star. clear.
        eapply evar_is_fresh_in_richer'.
        2: {
          apply set_evar_fresh_is_fresh.
        }
        {
          cbn. set_solver.
        }
      }
      {
        cbn.
        repeat case_match; try reflexivity; lia.
      }
    }
    mlClear "Htmp2".
    mlRewrite (bott_and Γ P ltac:(wf_auto2)) at 1.
    mlRewrite (bott_and Γ (P $ ϕ) ltac:(wf_auto2)) at 1.
    fromMLGoal.
    mlSplitAnd.
    {
      mlIntro "H". mlDestructBot "H".
    }
    {
      fromMLGoal.
      useBasicReasoning.
      apply Prop_bott_left.
      wf_auto2.
    }
  }
Defined.

(* TODO: Put in a different file? *)
Lemma predicate_propagate_right {Σ : Signature} {syntax : Syntax} Γ ϕ ψ P :
  theory ⊆ Γ ->
  well_formed ϕ ->
  well_formed ψ ->
  well_formed P ->
  mu_free ϕ ->
  mu_free ψ ->
  mu_free P ->
  Γ ⊢ is_predicate_pattern ψ ->
  Γ ⊢ ψ and P $ ϕ <---> P $ (ψ and ϕ).
Proof.
  intros HΓ wfϕ wfψ wfP mϕ mψ mP predψ.
  toMLGoal.
  { wf_auto2. }
  mlAdd predψ as "P"; clear predψ.
  unfold is_predicate_pattern.
  mlDestructOr "P" as "T" "B".
  {
    mlRewriteBy "T" at 1.
    { set_solver. }
    {
      apply mu_free_in_path. simpl. split_and!; reflexivity || assumption.
    }
    mlRewriteBy "T" at 1.
    { set_solver. }
    {
      apply mu_free_in_path. simpl. split_and!; reflexivity || assumption.
    }
    mlClear "T".
    pose proof (Ht := top_and Γ (P $ ϕ) ltac:(wf_auto2)).
    mlRewrite Ht at 1; clear Ht.
    pose proof (Ht := top_and Γ ϕ ltac:(wf_auto2)).
    mlRewrite Ht at 1; clear Ht.
    fromMLGoal.
    aapply pf_iff_equiv_refl; wf_auto2.
  }
  {
    mlRewriteBy "B" at 1.
    { set_solver. }
    {
      apply mu_free_in_path. simpl. split_and!; reflexivity || assumption.
    }
    mlRewriteBy "B" at 1.
    { set_solver. }
    {
      apply mu_free_in_path. simpl. split_and!; reflexivity || assumption.
    }
    mlClear "B".
    pose proof (Hb := bott_and Γ (P $ ϕ) ltac:(wf_auto2)).
    mlRewrite Hb at 1; clear Hb.
    pose proof (Hb := bott_and Γ ϕ ltac:(wf_auto2)).
    mlRewrite Hb at 1; clear Hb.
    fromMLGoal.
    apply pf_iff_equiv_sym;[wf_auto2|wf_auto2|].
    pose proof (Hiff := prf_prop_bott_iff).
    specialize Hiff with (AC := ctx_app_r P box ltac:(wf_auto2)).
    simpl in Hiff.
    aapply Hiff.
  }
Defined.


Lemma equal_imp_membership {Σ : Signature} {syntax : Syntax} Γ φ φ' :
  theory ⊆ Γ -> 
  well_formed φ -> well_formed φ' ->
  Γ ⊢ ⌈ φ' ⌉  ->
  Γ ⊢ (φ =ml φ') ---> (φ ∈ml φ').
Proof.
  intros HΓ WF1 WF2 Def.
  toMLGoal. wf_auto2.
  mlIntro "H0".
  mlRewriteBy "H0" at 1; cbn; try_wfauto2; try assumption.
  {
    unfold mu_in_evar_path. simpl.
    rewrite decide_eq_same. simpl.
    case_match;[reflexivity|].
    rewrite 2!Nat.max_0_r in H.
    rewrite maximal_mu_depth_to_0 in H.
    2: { inversion H. }
    subst star. clear.
    eapply evar_is_fresh_in_richer'.
    2: { apply set_evar_fresh_is_fresh. }
    {
      cbn. set_solver.
    }
  }
  mlClear "H0". unfold patt_in.
  assert (Γ ⊢ ( φ' and φ' <---> φ') ) as H1.
  {
    toMLGoal. wf_auto2.
    mlSplitAnd; mlIntro "H1".
    - mlDestructAnd "H1" as "H2" "H3". mlExact "H3".
    - mlSplitAnd; mlExact "H1".
  }
  now mlRewrite H1 at 1.
Defined.

Lemma phi_impl_ex_in_phi {Σ : Signature} {syntax : Syntax} Γ ϕ:
  theory ⊆ Γ ->
  well_formed ϕ ->
  Γ ⊢ ϕ ---> (ex , b0 ∈ml ϕ and b0).
Proof.
  intros HΓ wfϕ.
  aapply (membership_elimination _ _ _ (fresh_evar (ϕ ---> (ex , b0 ∈ml ϕ and b0)))).
  { solve_fresh. }
  { wf_auto2. }
  { assumption. }
  remember (fresh_evar ϕ) as x.
  rewrite <- evar_quantify_evar_open with (x := x) (n := 0) (phi := b0 ∈ml (ϕ ---> (ex , b0 ∈ml ϕ and b0))).
  2: {
    subst x.
    eapply evar_is_fresh_in_richer'.
    2: apply set_evar_fresh_is_fresh'.
    clear. set_solver.
  }
  2: wf_auto2.
  aapply universal_generalization;[wf_auto2|].
  unfold evar_open. mlSimpl. simpl.
  rewrite bevar_subst_not_occur;[wf_auto2|].
  rewrite bevar_subst_not_occur;[wf_auto2|].
  toMLGoal.
  { wf_auto2. }
  pose proof (H := membership_imp Γ x ϕ (ex , b0 ∈ml ϕ and b0)).
  feed specialize H.
  { set_solver. }
  { wf_auto2. }
  { wf_auto2. }
  apply pf_iff_proj2 in H;[|wf_auto2|wf_auto2].
  mlApplyMeta H; clear H.
  mlIntro "H".
  pose proof (H := membership_exists Γ x (b0 ∈ml ϕ and b0)).
  feed specialize H.
  { set_solver. }
  { wf_auto2. }
  use AnyReasoning in H.
  mlRewrite H at 1; clear H.
  pose proof (H := Ex_quan).
  specialize H with (y := x).
  mlApplyMeta H; clear H.
  unfold instantiate. mlSimpl. simpl.
  rewrite bevar_subst_not_occur;[wf_auto2|].
  pose proof (H := membership_and_iff Γ x (patt_free_evar x ∈ml ϕ) (patt_free_evar x)).
  feed specialize H.
  { wf_auto2. }
  { wf_auto2. }
  { set_solver. }
  use AnyReasoning in H.
  mlRewrite H at 1; clear H.
  mlSplitAnd.
  + fromMLGoal.
    aapply ceil_monotonic;[set_solver|wf_auto2|wf_auto2|].
    toMLGoal. wf_auto2.
    mlIntro "H".
    mlSplitAnd.
    * mlDestructAnd "H" as "x" "p". mlExact "x".
    * mlApplyMeta phi_impl_defined_phi;[mlExact "H"| | assumption].
      instantiate (1 := fresh_evar (patt_free_evar x and ϕ)). solve_fresh.
  + mlClear "H".
    mlApplyMeta equal_imp_membership.
    fromMLGoal.
    aapply patt_equal_refl.
    wf_auto2.
    aapply defined_evar.
    { exact HΓ. }
    { exact HΓ. }
Defined.

Lemma membership_symbol_right {Σ : Signature} {syntax : Syntax} Γ ϕ ψ x :
  theory ⊆ Γ ->
  well_formed ϕ ->
  well_formed ψ ->
  mu_free ϕ ->
  mu_free ψ ->
  Γ ⊢ (patt_free_evar x ∈ml ψ $ ϕ) ---> (ex , (b0 ∈ml ϕ and patt_free_evar x ∈ml ψ $ b0)).
Proof.
  intros HΓ wfϕ wfψ mϕ mψ.
  toMLGoal.
  { wf_auto2. }
  mlIntro "H0".
  mlAssert ("H1" : (patt_free_evar x ∈ml ψ $ (ex , b0 ∈ml ϕ and b0))).
  { wf_auto2. }
  {
    fromMLGoal.
    aapply membership_monotone;[set_solver|wf_auto2|wf_auto2|].
    apply Framing_right with (ψ := ψ); auto. apply pile_any.
    aapply phi_impl_ex_in_phi;[set_solver|wf_auto2].
  } mlClear "H0".
  mlAssert ("H2" : (patt_free_evar x ∈ml (ex, ψ $ (b0 ∈ml ϕ and b0)))).
  { wf_auto2. }
  {
    fromMLGoal.
    aapply membership_monotone;[set_solver|wf_auto2|wf_auto2|].
    toMLGoal.
    { wf_auto2. }
    mlIntro "H".
    mlApplyMeta Prop_ex_right.
    mlExact "H".
  } mlClear "H1".
  pose proof (H := membership_exists Γ x (ψ $ (b0 ∈ml ϕ and b0))).
  feed specialize H.
  { set_solver. }
  { wf_auto2. }
  use AnyReasoning in H.
  mlRevertLast.
  mlRewrite H at 1; clear H.
  fromMLGoal.
  remember (fresh_evar ((patt_free_evar x) and ϕ and ψ)) as y.
  rewrite <- evar_quantify_evar_open with (x := y) (n := 0) (phi := patt_free_evar x ∈ml ψ $ (b0 ∈ml ϕ and b0)).
  2: {
    subst y.
    eapply evar_is_fresh_in_richer'.
    2: apply set_evar_fresh_is_fresh'.
    clear. set_solver.
  }
  2: wf_auto2.
  rewrite <- evar_quantify_evar_open with (x := y) (n := 0) (phi := b0 ∈ml ϕ and patt_free_evar x ∈ml ψ $ b0).
  2: {
    subst y.
    eapply evar_is_fresh_in_richer'.
    2: apply set_evar_fresh_is_fresh'.
    clear. set_solver.
  }
  2: wf_auto2.
  aapply ex_quan_monotone.
  mlSimpl. unfold evar_open. simpl.
  repeat (rewrite bevar_subst_not_occur;[wf_auto2|]).

  toMLGoal.
  { wf_auto2. }
  pose proof (H := predicate_propagate_right Γ (patt_free_evar y) (patt_free_evar y ∈ml ϕ) ψ).
  feed specialize H.
  { set_solver. }
  { wf_auto2. }
  { wf_auto2. }
  { wf_auto2. }
  { reflexivity. }
  { simpl. split_and!;reflexivity || assumption. }
  { assumption. }
  { aapply ceil_is_predicate;[set_solver|wf_auto2]. }
  mlRewrite <- H at 1; clear H.

  mlIntro "H".
  mlApplyMeta membership_and_1 in "H";[|set_solver].
  mlDestructAnd "H" as "H0" "H1".
  mlApplyMeta ceil_and_x_ceil_phi_impl_ceil_phi in "H0";[|set_solver].
  mlSplitAnd.
  + mlExact "H0".
  + mlExact "H1".
Defined.

Lemma disj_equals_greater_1 {Σ : Signature} {syntax : Syntax} Γ φ₁ φ₂:
  theory ⊆ Γ ->
  well_formed φ₁ ->
  well_formed φ₂ ->
  Γ ⊢i (φ₁ ⊆ml φ₂) ---> ((φ₁ or φ₂) =ml φ₂)
  using AnyReasoning.
Proof.
  intros HΓ wfφ₁ wfφ₂.
  unshelve (gapply deduction_theorem_noKT).
  2: { apply pile_any. }
  3,4: wf_auto2.
  3: exact HΓ.
  2: {
    apply phi_impl_total_phi_meta.
    { wf_auto2. }
    { apply pile_refl. }
    apply pf_iff_split.
    1,2: wf_auto2.
    - toMLGoal. wf_auto2. mlIntro "H0". mlDestructOr "H0" as "H0'" "H0'".
      + assert (Γ ∪ {[φ₁ ---> φ₂]} ⊢i φ₁ ---> φ₂ using ( (ExGen := ∅, SVSubst := ∅, KT := false, AKT := false))).
        {
          gapply BasicProofSystemLemmas.hypothesis.
          { try_solve_pile. }
          { wf_auto2. }
          clear. set_solver.
        }
        mlApplyMetaRaw H. mlExact "H0'".
      + mlExact "H0'".
    - useBasicReasoning. apply disj_right_intro; assumption.
  }
  { simpl. clear. set_solver. }
  { simpl. clear. set_solver. }
  { reflexivity. }
Defined.


Lemma disj_equals_greater_2_meta {Σ : Signature} {syntax : Syntax} Γ φ₁ φ₂:
  theory ⊆ Γ ->
  well_formed φ₁ ->
  well_formed φ₂ ->
  Γ ⊢i (φ₁ or φ₂) =ml φ₂ using AnyReasoning ->
  Γ ⊢i φ₁ ⊆ml φ₂ using AnyReasoning.
Proof.
  intros HΓ wfφ₁ wfφ₂ Heq.
  toMLGoal.
  { wf_auto2. }
  unshelve (epose proof (Htmp := patt_equal_implies_iff _ _ _ _ (fresh_evar (φ₁ or φ₂)) HΓ _ _ _ _ Heq)).
  { solve_fresh. }
  { apply pile_any. }
  { wf_auto2. }
  { wf_auto2. }
  apply pf_iff_equiv_sym in Htmp.
  3: { wf_auto2. }
  2: { wf_auto2. }
  mlRewrite Htmp at 1.
  fromMLGoal.
  unfold "⊆ml".
  apply phi_impl_total_phi_meta.
  { wf_auto2. }
  { apply pile_any. }
  toMLGoal.
  { wf_auto2. }
  mlIntro "H0". mlLeft. mlExact "H0".
Defined.

Lemma disj_equals_greater_2 {Σ : Signature} {syntax : Syntax} Γ φ₁ φ₂:
  theory ⊆ Γ ->
  well_formed φ₁ ->
  well_formed φ₂ ->
  mu_free φ₁ -> (* TODO get rid of it *)
  Γ ⊢i ((φ₁ or φ₂) =ml φ₂) ---> (φ₁ ⊆ml φ₂)
  using AnyReasoning.
Proof.
  intros HΓ wfφ₁ wfφ₂ mfφ₁.
  toMLGoal.
  { wf_auto2. }
  mlIntro "H0".

  unshelve(mlApplyMeta patt_equal_sym in "H0").
  2: { assumption. }
  mlRewriteBy "H0" at 1.
  { assumption. }
  { apply mu_free_in_path. simpl. rewrite mfφ₁. reflexivity. }
  mlClear "H0".

  fromMLGoal.
  unfold "⊆ml".
  apply phi_impl_total_phi_meta.
  { wf_auto2. }
  { apply pile_any. }
  toMLGoal.
  { wf_auto2. }
  mlIntro "H0". mlLeft. mlExact "H0".
Defined.

Lemma bott_not_total {Σ : Signature} {syntax : Syntax}:
  forall Γ, theory ⊆ Γ ->
  Γ ⊢i ! ⌊ ⊥ ⌋
  using AnyReasoning.
Proof.
  intros Γ SubTheory.
  toMLGoal. wf_auto2.
  mlIntro "H0". mlApply "H0".
  mlApplyMetaRaw (liftProofInfoLe _ _ _ AnyReasoning (phi_impl_defined_phi _ (! ⊥) _ SubTheory _ ltac:(wf_auto2))).
  mlIntro "H1". mlExact "H1".
Unshelve.
  2: exact (fresh_evar ⊥).
  try_solve_pile.
  solve_fresh.
Defined.

Lemma defined_not_iff_not_total {Σ : Signature} {syntax : Syntax}:
  ∀ (Γ : Theory) (φ : Pattern),
  theory ⊆ Γ → well_formed φ → Γ ⊢i ⌈ ! φ ⌉ <---> ! ⌊ φ ⌋
  using AnyReasoning.
Proof.
  intros Γ φ HΓ Wf. toMLGoal. wf_auto2.
  mlSplitAnd.
  * mlIntro "H0".
    mlApplyMetaRaw (liftProofInfoLe _ _ _ AnyReasoning (def_not_phi_impl_not_total_phi Γ φ HΓ Wf)).
    mlExact "H0".
  * unfold patt_total.
    epose proof (liftProofInfoLe _ _ _ AnyReasoning (not_not_iff Γ ⌈ ! φ ⌉ ltac:(wf_auto2))) as H.
    mlRewrite <- H at 1.
    mlIntro "H0".
    mlExact "H0".
  Unshelve.
  all: try_solve_pile.
Defined.

Lemma patt_or_total {Σ : Signature} {syntax : Syntax}:
  forall Γ φ ψ,
  theory ⊆ Γ ->
  well_formed φ -> well_formed ψ ->
  Γ ⊢i  ⌊ φ ⌋ or ⌊ ψ ⌋ ---> ⌊ φ or ψ ⌋
  using AnyReasoning.
Proof.
  intros Γ φ ψ HΓ Wf1 Wf2. toMLGoal. wf_auto2.
  mlIntro "H0".
  mlDestructOr "H0" as "H0'" "H0'".
  * epose proof (liftProofInfoLe _ _ _ AnyReasoning (disj_left_intro Γ φ ψ Wf1 Wf2)) as H.
    apply floor_monotonic in H. 3-4: try wf_auto2.
    2: { exact HΓ. }
    mlApplyMetaRaw H.
    mlExact "H0'".
  * epose proof (liftProofInfoLe _ _ _ AnyReasoning (disj_right_intro Γ φ ψ Wf1 Wf2)) as H.
    apply floor_monotonic in H.
    3,4: wf_auto2.
    2: { exact HΓ. }
    mlApplyMetaRaw H.
    mlExact "H0'".
Unshelve.
  all: try_solve_pile.
Defined.

Lemma patt_defined_and {Σ : Signature} {syntax : Syntax}:
  forall Γ φ ψ,
  theory ⊆ Γ ->
  well_formed φ -> well_formed ψ ->
  Γ ⊢i ⌈ φ and ψ ⌉ ---> ⌈ φ ⌉ and ⌈ ψ ⌉
  using AnyReasoning.
Proof.
  intros Γ φ ψ HΓ Wf1 Wf2. toMLGoal. wf_auto2.
  unfold patt_and.

  epose proof (liftProofInfoLe _ _ _ AnyReasoning (defined_not_iff_not_total Γ (! φ or ! ψ) HΓ ltac:(wf_auto2))) as H.
  mlRewrite H at 1.
  mlIntro "H0".
  mlIntro "H1".
  mlApply "H0".
  mlClear "H0".
  mlApplyMeta (patt_or_total _ (! φ) (! ψ) HΓ).
  mlDestructOr "H1" as "H1'" "H1'".
  * mlLeft. unfold patt_total.
    epose proof (liftProofInfoLe _ _ _ AnyReasoning (not_not_iff Γ φ Wf1)) as H0.
    mlRewrite <- H0 at 1.
    mlExact "H1'".
  * mlRight. unfold patt_total.
    epose proof ((liftProofInfoLe _ _ _ AnyReasoning (not_not_iff Γ ψ Wf2))) as H1.
    mlRewrite <- H1 at 1.
    mlExact "H1'".
Unshelve.
  all: try_solve_pile.
Defined.

Lemma patt_total_and {Σ : Signature} {syntax : Syntax}:
  forall Γ φ ψ,
  theory ⊆ Γ ->
  well_formed φ -> well_formed ψ ->
  Γ ⊢i ⌊ φ and ψ ⌋ <---> ⌊ φ ⌋ and ⌊ ψ ⌋
  using (ExGen := ∅, SVSubst := ∅, KT := false, AKT := false).
Proof.
  intros Γ φ ψ HΓ Wf1 Wf2. toMLGoal. wf_auto2.
  mlSplitAnd.
  * unfold patt_and.
    pose proof (Htmp := def_propagate_not Γ (! φ or ! ψ) HΓ ltac:(wf_auto2)).
    mlRewrite <- Htmp at 1.
    mlIntro "H1".
    mlIntro "H2".
    mlApply "H1".
    mlClear "H1".
    mlRewrite (ceil_compat_in_or Γ (! φ) (! ψ) HΓ ltac:(wf_auto2) ltac:(wf_auto2)) at 1.
    mlDestructOr "H2" as "H2'" "H2'".
    - mlLeft. mlRevertLast. unfold patt_total.
      mlRewrite <- (useBasicReasoning (ExGen := ∅, SVSubst := ∅, KT := false, AKT := false) (not_not_iff Γ ⌈ ! φ ⌉ ltac:(wf_auto2))) at 1.
      mlIntro "H3". mlExact "H3".
    - mlRight. mlRevertLast. unfold patt_total.
      mlRewrite <- (useBasicReasoning (ExGen := ∅, SVSubst := ∅, KT := false, AKT := false) (not_not_iff Γ ⌈ ! ψ ⌉ ltac:(wf_auto2))) at 1.
      mlIntro "H3". mlExact "H3".
  * mlIntro "H0". mlDestructAnd "H0" as "H1" "H2".
    unfold patt_and.
    pose proof (Htmp := def_propagate_not Γ (! φ or ! ψ) HΓ ltac:(wf_auto2)).
    mlRewrite <- Htmp at 1.
    mlRewrite (ceil_compat_in_or Γ (! φ) (! ψ) HΓ ltac:(wf_auto2) ltac:(wf_auto2)) at 1.
    mlIntro "H3". mlDestructOr "H3" as "H3'" "H3'".
    - mlRevertLast. mlExact "H1".
    - mlRevertLast. mlExact "H2".
Defined.

Definition overlaps_with {Σ : Signature} {syntax : Syntax} (p q : Pattern) : Pattern
:= ⌈ p and q ⌉.

Lemma overlapping_variables_equal {Σ : Signature} {syntax : Syntax} :
  forall x y Γ,
  theory ⊆ Γ ->
  Γ ⊢ overlaps_with (patt_free_evar y) (patt_free_evar x) ---> patt_free_evar y =ml patt_free_evar x.
Proof.
  intros x y Γ HΓ.

  remember (patt_free_evar x) as pX. assert (well_formed pX) by (rewrite HeqpX;auto).
  remember (patt_free_evar y) as pY. assert (well_formed pY) by (rewrite HeqpY;auto).
  unfold overlaps_with.
  toMLGoal. wf_auto2.
  unfold patt_equal, patt_iff.
  epose proof (H2 := liftProofInfoLe _ _ _ AnyReasoning (patt_total_and Γ
                            (pY ---> pX)
                            (pX ---> pY) HΓ
                            ltac:(wf_auto2) ltac:(wf_auto2))).
  mlRewrite H2 at 1.
  mlIntro "H0".
  mlIntro "H1".
  mlDestructOr "H1" as "H1'" "H1'".
  * mlApply "H1'".
    mlClear "H1'".
    mlIntro "H2".
    pose proof (MH := nimpl_eq_and Γ pY pX
                  ltac:(wf_auto2) ltac:(wf_auto2)).
    use AnyReasoning in MH.
    mlRevertLast.
    mlRewrite MH at 1. fold AnyReasoning.
    unshelve (epose proof (MH1 := Singleton_ctx Γ 
           (⌈_⌉ $ᵣ □)
           (⌈_⌉ $ᵣ □) pX y ltac:(wf_auto2))). 1-2: wf_auto2.
    rewrite -HeqpY in MH1.
    use AnyReasoning in MH1. simpl in MH1.
    (* TODO: having mlExactMeta would help here *)
    mlRevertLast. unfold patt_defined. unfold patt_not in *.
    mlIntro "H1". mlIntro "H2".
    mlApplyMeta MH1. simpl. mlSplitAnd. mlExact "H1". mlExact "H2".
  * mlApply "H1'".
    mlClear "H1'".
    mlIntro "H2".
    pose proof (MH := nimpl_eq_and Γ pX pY
                  ltac:(wf_auto2) ltac:(wf_auto2)).
    mlRevertLast. use AnyReasoning in MH.
    mlRewrite MH at 1.
    pose proof (MH1 := patt_and_comm Γ pY pX ltac:(wf_auto2) ltac:(wf_auto2)).
    mlRevertLast. use AnyReasoning in MH1. mlRewrite MH1 at 1.
    unshelve (epose proof (Singleton_ctx Γ 
           (⌈_⌉ $ᵣ □)
           (⌈_⌉ $ᵣ □) pY x ltac:(wf_auto2)) as MH2). 1-2: wf_auto2.
    rewrite -HeqpX in MH2.
    use AnyReasoning in MH2.
    mlIntro "H1". mlIntro "H2".
    mlApplyMeta MH2. simpl. mlSplitAnd. mlExact "H1". mlExact "H2".
Unshelve.
  try_solve_pile.
Defined.

Lemma mlSpecializeMeta {Σ : Signature} {syntax : Syntax} :
  forall Γ φ ψ, theory ⊆ Γ-> 
  well_formed (ex , φ) -> well_formed ψ -> mu_free φ ->
  Γ ⊢i (all , φ) using AnyReasoning -> 
  Γ ⊢i ex , ψ =ml b0 using AnyReasoning ->
  Γ ⊢i φ^[evar: 0 ↦ ψ] using AnyReasoning.
Proof.
  intros Γ φ ψ HΓ WF1 WF2 MF P1 P2.
  toMLGoal. wf_auto2.
  mlApplyMeta forall_functional_subst.
  mlSplitAnd; fromMLGoal; auto.
  Unshelve. all: auto. all: wf_auto2.
Defined.

(* TODO: make sure that the final [assumption] does not solve goals we do not want to solve. *)
Tactic Notation "mgSpecMeta" ident(hyp) "with" constr(t) := 
  unshelve (eapply (@mlSpecializeMeta _ _ _ _ t) in hyp); try_wfauto2; try assumption.

Local Lemma test_spec {Σ : Signature} {syntax : Syntax}:
  forall Γ φ ψ, theory ⊆ Γ-> 
  well_formed (ex , φ) -> well_formed ψ -> mu_free φ ->
  Γ ⊢i (all , φ) using AnyReasoning -> 
  Γ ⊢i ex , ψ =ml b0 using AnyReasoning ->
  Γ ⊢i φ^[evar: 0 ↦ ψ] using AnyReasoning.
Proof.
  intros. mgSpecMeta H3 with ψ.
Defined.

Lemma MLGoal_mlSpecialize {Σ : Signature} {syntax : Syntax} Γ l₁ l₂ p t g name:
  theory ⊆ Γ ->
  mu_free p -> well_formed t ->
  mkMLGoal Σ Γ (l₁ ++ (mkNH _ name p^[evar: 0 ↦ t]) ::l₂ ) g AnyReasoning ->
  mkMLGoal Σ Γ (l₁ ++ (mkNH _ name ((all, p) and (ex , t =ml b0)))::l₂) g AnyReasoning.
Proof.
  intros HΓ MF WF MG.
  unfold of_MLGoal in *. simpl in *. intros H H0.
  assert (well_formed (ex , p)). {
    unfold patterns_of in H0. rewrite map_app in H0.
    apply wfl₁hl₂_proj_h in H0; simpl in H0.
    apply andb_true_iff in H0 as [H0'' H0'].
    apply andb_true_iff in H0' as [H0_1 H0_2]; simpl in *; repeat rewrite andb_true_r in H0_1, H0_2; repeat rewrite andb_true_iff in H0_1, H0_2; 
    destruct_and!;
    wf_auto2.
  }
  unshelve (epose proof (MG H _) as MG').
  {
    unfold patterns_of in *; rewrite -> map_app in *; simpl in H0; wf_auto2.
  }
  clear MG.
  unfold patterns_of in *. rewrite -> map_app in *. simpl.
  eapply prf_strenghten_premise_iter_meta_meta.
  7: exact MG'.
  5: assumption.
  1: now apply wfl₁hl₂_proj_l₁ in H0.
  1: now apply wfl₁hl₂_proj_l₂ in H0.
  1,2: wf_auto2.
  simpl.
  apply forall_functional_subst. 1-3: assumption.
  all: wf_auto2.
Defined.

(**
  This tactic can be used on local hypotheses shaped in the following way:
     (all , φ) and ex , t = b0
*)
Tactic Notation "mlSpecn" constr(n) := 
  _mlReshapeHypsByIdx n;
  apply MLGoal_mlSpecialize; [ auto | wf_auto2 | wf_auto2 | _mlReshapeHypsBack ].

Tactic Notation "mlSpec" constr(name') :=
  _mlReshapeHypsByName name';
  apply MLGoal_mlSpecialize; [ auto | wf_auto2 | wf_auto2 | _mlReshapeHypsBack ].


Goal forall (Σ : Signature) (syntax : Syntax) Γ φ t, 
  theory ⊆ Γ -> mu_free φ -> well_formed t -> well_formed (ex , φ) ->
  Γ ⊢i (all , φ) ---> (ex , t =ml b0) ---> φ^[evar: 0 ↦ t] using AnyReasoning.
Proof.
  intros. toMLGoal. wf_auto2.
  mlIntro "mH". mlIntro "mH0".
  mlAssert ("mH1" : ((all , φ) and ex , t =ml b0)). wf_auto2. mlSplitAnd; mlAssumption.
  mlClear "mH". mlClear "mH0".
  mlSpec "mH1". mlExact "mH1".
Defined.

(** 
  TODO: why should x be introduced for proof info (it could be constructed "ony the fly")? Could we avoid this?
 *)
Lemma forall_defined {Σ : Signature} {syntax : Syntax}:
  forall Γ i, theory ⊆ Γ ->
  ProofInfoLe (ExGen := {[ev_x]}, SVSubst := ∅, KT := false, AKT := false) i  ->
  Γ ⊢i all , ⌈b0⌉ using i.
Proof.
  intros Γ i HΓ PI.
  (* remember (fresh_evar ⊥) as x. *)
  toMLGoal. wf_auto2.
  epose proof (BasicProofSystemLemmas.Ex_gen Γ (! ⌈patt_free_evar ev_x⌉) ⊥ ev_x i _ _).
  unfold exists_quantify in H. cbn in H. case_match. 2: congruence.
  mlIntro "H". mlApplyMeta H. fold (patt_defined b0) (patt_not ⌈b0⌉).
  mlExact "H".
    Unshelve.
    * eapply pile_trans. 2: exact PI. try_solve_pile.
    * set_solver.
    * toMLGoal. wf_auto2. mlIntro "H". mlApply "H".
      pose proof (defined_evar _ ev_x HΓ).
      eapply liftProofInfoLe in H. mlExactMeta H.
      eapply pile_trans. 2: exact PI.
      try_solve_pile.
Defined.

Lemma membership_refl {Σ : Signature} {syntax : Syntax}:
  forall Γ t, well_formed t -> 
  theory ⊆ Γ-> Γ ⊢i ((ex , t =ml b0) ---> t ∈ml t) using AnyReasoning.
Proof.
  intros Γ t WF HΓ.
  unfold "∈ml". toMLGoal. wf_auto2.
  mlIntro "mH".
  pose proof (and_singleton Γ t WF). use AnyReasoning in H.
  mlRewrite H at 1.
  remember (fresh_evar t) as x.
  mlAssert ("mH1" : ((all, ⌈patt_bound_evar 0⌉) and ex, t =ml b0)). wf_auto2. {
    mlSplitAnd.
    * mlClear "mH".
      epose proof (forall_defined Γ AnyReasoning HΓ _).
      mlExactMeta H0.
      Unshelve.
      apply pile_any.
    * mlAssumption.
  }
  mlClear "mH".
  mlSpec "mH1".
  mlExact "mH1".
Defined.

Lemma MLGoal_reflexivity {Σ : Signature} {syntax : Syntax} Γ l ϕ i :
  theory ⊆ Γ ->
  mkMLGoal _ Γ l (ϕ =ml ϕ) i.
Proof.
  intros HΓ. unfold of_MLGoal. simpl. intros wfl wfg.
  eapply MP. 2: gapply nested_const.
  2: try_solve_pile. 2-3: wf_auto2.
  gapply patt_equal_refl. try_solve_pile. wf_auto2.
Defined.

Tactic Notation "mlReflexivity" :=
  _ensureProofMode;
  apply MLGoal_reflexivity; try assumption; set_solver.

Local Example mlReflexivity_test {Σ : Signature} {syntax : Syntax} Γ ϕ ψ :
  theory ⊆ Γ -> well_formed ϕ -> well_formed ψ ->
  Γ ⊢i ϕ ---> ψ ---> ψ =ml ψ using BasicReasoning.
Proof.
  intros.
  do 2 mlIntro.
  mlReflexivity.
Defined.

(* TODO: strengthen proof info about this: *)
Lemma MLGoal_symmetry {Σ : Signature} {syntax : Syntax} Γ l ϕ ψ :
  theory ⊆ Γ ->
  mkMLGoal _ Γ l (ϕ =ml ψ) AnyReasoning ->
  mkMLGoal _ Γ l (ψ =ml ϕ) AnyReasoning.
Proof.
  unfold of_MLGoal. simpl.
  intros HΓ H wfl wfg.
  eapply prf_weaken_conclusion_iter_meta_meta. 5: apply H.
  1-3,5,6: wf_auto2.
  apply patt_equal_sym; auto.
  1-2: wf_auto2.
Defined.

(* TODO: strengthen proof info about this: *)
Lemma MLGoal_symmetryIn {Σ : Signature} {syntax : Syntax} name Γ l1 l2 ϕ ψ g  :
  theory ⊆ Γ ->
  mkMLGoal _ Γ (l1 ++ (mkNH _ name (ϕ =ml ψ)) :: l2) g AnyReasoning ->
  mkMLGoal _ Γ (l1 ++ (mkNH _ name (ψ =ml ϕ)) :: l2) g AnyReasoning.
Proof.
  unfold of_MLGoal. simpl.
  intros HΓ H wfl wfg.
  unfold patterns_of in *. rewrite -> map_app in *. simpl in *.
  eapply prf_strenghten_premise_iter_meta_meta.
  6 : apply patt_equal_sym; auto.
  8: apply H.
  all: wf_auto2.
Defined.


Tactic Notation "mlSymmetry" :=
  _ensureProofMode;
  apply MLGoal_symmetry; [try assumption; set_solver|].

Tactic Notation "mlSymmetry" "in" constr(name) :=
  _ensureProofMode;
  _mlReshapeHypsByName name;
  apply (MLGoal_symmetryIn name); [try assumption; set_solver|];
  _mlReshapeHypsBack.

Local Example mlSymmetry_test {Σ : Signature} {syntax : Syntax} Γ ϕ ψ :
  theory ⊆ Γ -> well_formed ϕ -> well_formed ψ ->
  Γ ⊢i ϕ =ml ψ ---> ϕ =ml ψ using AnyReasoning.
Proof.
  intros.
  mlIntro "H".
  mlSymmetry.
  mlSymmetry in "H".
  mlAssumption.
Defined.


(* TODO: eliminate mu_free *)
Lemma patt_equal_trans {Σ : Signature} {syntax : Syntax} Γ φ1 φ2 φ3:
  theory ⊆ Γ ->
  well_formed φ1 -> well_formed φ2 -> well_formed φ3 ->
  mu_free φ1 -> mu_free φ2 -> mu_free φ3 ->
  Γ ⊢i φ1 =ml φ2 ---> φ2 =ml φ3 ---> φ1 =ml φ3
  using AnyReasoning.
Proof.
  intros HΓ WF1 WF2 WF3 MF1 MF2 MF3.
  mlIntro "H". mlIntro "H0".
  mlAssert ("H1" : ⌊ (φ1 <---> φ2) and (φ2 <---> φ3) ⌋). wf_auto2. {
    pose proof (patt_total_and Γ (φ1 <---> φ2) (φ2 <---> φ3) HΓ ltac:(wf_auto2) ltac:(wf_auto2)).
    apply pf_iff_proj2 in H. 2-3: wf_auto2.
    use AnyReasoning in H. mlApplyMeta H. mlSplitAnd; mlAssumption.
  }
  mlClear "H". mlClear "H0". fromMLGoal.
  unshelve (gapply deduction_theorem_noKT). exact BasicReasoning. try_solve_pile.
  2-3: abstract(wf_auto2).
  2: exact HΓ.
  {
    remember (Γ ∪ {[(φ1 <---> φ2) and (φ2 <---> φ3)]}) as Γ'.
    assert (Γ' ⊢i ((φ1 <---> φ2) and (φ2 <---> φ3)) using BasicReasoning). {
      apply BasicProofSystemLemmas.hypothesis. wf_auto2.
      rewrite HeqΓ'. apply elem_of_union_r. constructor. 
    }
    epose proof (pf_conj_elim_l _ _ _ _ _) as H'.
    eapply MP in H'.
    2: { exact H. }
    epose proof (pf_conj_elim_r _ _ _ _ _) as H''.
    eapply MP in H''.
    2: { exact H. }
    clear H.
    apply pf_iff_equiv_sym in H'; auto.
    apply pf_iff_equiv_sym in H''; auto.
    apply patt_iff_implies_equal; auto.
    2 : {
    toMLGoal. wf_auto2. mlSplitAnd.
    * apply pf_iff_proj2 in H'. apply pf_iff_proj2 in H''. 2-5: wf_auto2.
      mlIntro. mlApplyMeta H''. mlApplyMeta H'. mlAssumption.
    * apply pf_iff_proj1 in H'. apply pf_iff_proj1 in H''. 2-5: wf_auto2.
      mlIntro. mlApplyMeta H'. mlApplyMeta H''. mlAssumption.
    }
    try_solve_pile.
  }
  1-2: set_solver.
  auto.
  Unshelve.
  1-4: wf_auto2.
Defined.

Close Scope ml_scope.
Close Scope string_scope.
Close Scope list_scope.
