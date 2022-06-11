From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Ltac2 Require Import Ltac2.

Require Import Equations.Prop.Equations.

From Coq Require Import String Ensembles Setoid.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.Classical_Prop.
From Coq.Logic Require Import FunctionalExtensionality Eqdep_dec.
From Coq.Classes Require Import Morphisms_Prop.
From Coq.Unicode Require Import Utf8.
From Coq.micromega Require Import Lia.

From MatchingLogic Require Import Syntax NamedAxioms DerivedOperators_Syntax ProofSystem ProofMode IndexManipulation.
From MatchingLogic.Theories Require Import Definedness_Syntax.
From MatchingLogic.Utils Require Import stdpp_ext.

Require Import MatchingLogic.wftactics.

From stdpp Require Import base fin_sets sets propset proof_irrel option list.

Import extralibrary.

Import MatchingLogic.Syntax.Notations.
Import MatchingLogic.DerivedOperators_Syntax.Notations.
Import MatchingLogic.Syntax.BoundVarSugar.
Import MatchingLogic.ProofSystem.Notations.

Set Default Proof Mode "Classic".

Close Scope equations_scope. (* Because of [!] *)

Import Notations.
Open Scope ml_scope.

Section ProofSystemTheorems.

Context
  {Σ : Signature}
  {syntax : Syntax}
.

Lemma phi_impl_total_phi_meta Γ ϕ i:
  well_formed ϕ ->
  ProofInfoLe BasicReasoning i ->
  Γ ⊢ ϕ using i ->
  Γ ⊢ ⌊ ϕ ⌋ using i.
Proof.
  intros wfϕ pile Hϕ.
  epose proof (ANNA := @A_implies_not_not_A_ctx Σ Γ (ϕ) (ctx_app_r box _)).
  apply ANNA.
  { exact pile. }
  { apply wfϕ. }
  exact Hϕ.
  Unshelve. wf_auto2.
Defined.

Lemma patt_iff_implies_equal :
  forall (φ1 φ2 : Pattern) Γ i,
    well_formed φ1 ->
    well_formed φ2 ->         
    ProofInfoLe BasicReasoning i ->                 
    Γ ⊢ (φ1 <---> φ2) using i ->
    Γ ⊢ φ1 =ml φ2 using i .
Proof.
  intros φ1 φ2 Γ i WF1 WF2 pile H.
  epose proof (ANNA := @A_implies_not_not_A_ctx Σ Γ (φ1 <---> φ2) (ctx_app_r box _)).
  apply ANNA.
  { exact pile. }
  { wf_auto2. }
  { exact H. }
  Unshelve.
  wf_auto2.
Defined.

Lemma patt_equal_refl :
  forall φ Γ,
  well_formed φ ->
  Γ ⊢ φ =ml φ
  using BasicReasoning.
Proof.
  intros φ Γ WF. pose proof (IFF := @pf_iff_equiv_refl Σ Γ φ WF).
  eapply usePropositionalReasoning in IFF.
  apply patt_iff_implies_equal in IFF.
  { apply IFF. }
  { exact WF. }
  { exact WF. }
  { apply pile_refl. }
Qed.

Lemma use_defined_axiom Γ:
  theory ⊆ Γ ->
  Γ ⊢ patt_defined p_x
  using BasicReasoning.
Proof.
  intros HΓ.
  apply hypothesis; auto. unfold theory,theory_of_NamedAxioms in HΓ. simpl in HΓ.
  eapply elem_of_weaken.
  2: { apply HΓ. }
  unfold axiom.
  apply elem_of_PropSet.
  exists AxDefinedness.
  reflexivity.
Defined.

Definition BasicReasoningWithDefinedness := pi_Generic (ExGen := {[ev_x]}, SVSubst := ∅, KT := false).

Lemma defined_evar Γ x:
  theory ⊆ Γ ->
  Γ ⊢ ⌈ patt_free_evar x ⌉
  using pi_Generic (ExGen := {[ev_x]} ∪ {[x]}, SVSubst := ∅, KT := false).
Proof.
  intros HΓ.
  assert(S1: Γ ⊢ patt_defined p_x using BasicReasoningWithDefinedness).
  {
    useBasicReasoning.
    apply use_defined_axiom.
    apply HΓ.
  }

  pose proof (S1' := S1).
  apply universal_generalization with (x0 := ev_x) in S1'.
  3: { wf_auto2. }
  2: { apply pile_refl. }
  replace (evar_quantify ev_x 0 ( @patt_defined Σ syntax p_x))
    with (evar_quantify x 0 ⌈ patt_free_evar x ⌉) in S1'.
  2: { simpl. repeat case_match; auto; contradiction. }
  eapply MP.
  2: { eapply useGenericReasoning with (evs := {[x]}) (svs := ∅) (kt := false).
    apply pile_evs_svs_kt.
    { clear. unfold ev_x.
      rewrite elem_of_subseteq.
      intros x0 Hx0. rewrite elem_of_singleton in Hx0. subst x0.
      set_solver.
    }
    { apply reflexivity. }
    { reflexivity. }
    apply forall_variable_substitution with (x0 := x).
    wf_auto2.
  }
  eapply useGenericReasoning.
  2: { apply S1'. }
  apply pile_evs_svs_kt.
  { set_solver. }
  { apply reflexivity. }
  { reflexivity. }
Defined.
  
Lemma in_context_impl_defined Γ AC ϕ:
  theory ⊆ Γ ->
  well_formed ϕ ->
  Γ ⊢ (subst_ctx AC ϕ) ---> ⌈ ϕ ⌉
  using pi_Generic (ExGen := {[ev_x]} ∪ {[(evar_fresh (elements (free_evars ϕ ∪ AC_free_evars AC )))]}, SVSubst := ∅, KT := false).
Proof.
  intros HΓ Hwfϕ.
  assert(S1: Γ ⊢ patt_defined p_x using BasicReasoning).
  {
    apply use_defined_axiom.
    apply HΓ.
  }

  remember (evar_fresh (elements (free_evars ϕ ∪ AC_free_evars AC ))) as x'.

  pose proof (S1' := S1).
  apply useBasicReasoning with (gpi := (ExGen := {[ev_x; x']}, SVSubst := ∅, KT := false)) in S1'.
  apply universal_generalization with (x := ev_x) in S1'.
  3: { wf_auto2. }
  2: {
    apply pile_evs_svs_kt.
    { set_solver. }
    { apply reflexivity. }
    { reflexivity. }
  }

  assert (Hx1': evar_is_fresh_in x' ϕ).
  { rewrite Heqx'.
    eapply not_elem_of_larger_impl_not_elem_of.
    2: { apply set_evar_fresh_is_fresh'. }
    clear. set_solver.
  }

  assert (Hx'2: x' ∉ AC_free_evars AC).
  { rewrite Heqx'.
    eapply not_elem_of_larger_impl_not_elem_of.
    2: apply set_evar_fresh_is_fresh'.
    clear.
    set_solver.
  }
  
  remember (pi_Generic (ExGen := {[ev_x; x']}, SVSubst := ∅, KT := false)) as i.
  assert (S1'' : Γ ⊢ ⌈ patt_free_evar x' ⌉ using i).
  {
    (* For some reason, Coq cannot infer the implicit argument 'syntax' automatically *)
    replace (evar_quantify ev_x 0 ( @patt_defined Σ syntax p_x))
      with (evar_quantify x' 0 ⌈ patt_free_evar x' ⌉) in S1'.
    2: { simpl. repeat case_match; auto; contradiction. }
        
    eapply MP.
    { apply S1'. }
    eapply useGenericReasoning.
    2: apply forall_variable_substitution.
    2: wf_auto2.
    subst i.
    apply pile_evs_svs_kt.
    { set_solver. }
    { apply reflexivity. }
    { reflexivity. }
  }
  
  assert(S2: Γ ⊢ ⌈ patt_free_evar x' ⌉ or ⌈ ϕ ⌉ using i).
  {
    toMyGoal.
    { wf_auto2. }
    mgLeft.
    fromMyGoal.
    apply S1''.
  }

  assert(S3: Γ ⊢ ⌈ patt_free_evar x' or ϕ ⌉ using i).
  {
    pose proof (Htmp := (prf_prop_or_iff Γ AC_patt_defined) (patt_free_evar x') ϕ ltac:(auto) ltac:(auto)).
    simpl in Htmp.
    apply pf_conj_elim_r_meta in Htmp.
    2-3: wf_auto2.
    eapply MP.
    2: {
      rewrite Heqi.
      eapply useBasicReasoning.
      apply Htmp.
    }
    apply S2.
  }

  assert(S4: Γ ⊢ ⌈ ((patt_free_evar x') and (! ϕ)) or ϕ ⌉ using i).
  {
    assert(Htmp1: Γ ⊢ (patt_free_evar x' or ϕ) ---> (patt_free_evar x' and ! ϕ or ϕ) using i).
    {
      toMyGoal.
      { wf_auto2. }
      mgIntro.
      mgAdd (@usePropositionalReasoning Σ _ _ i (@A_or_notA Σ Γ ϕ Hwfϕ)).
      mgDestructOr 0.
      - mgRight. mgExactn 0.
      - mgLeft. mgIntro.
        mgDestructOr 1.
        + mgDestructOr 2.
          * mgApply 2. mgExactn 1.
          * mgApply 2. mgExactn 0.
        + mgApply 0.
          mgExactn 1.
    }
    
    assert(Htmp2: Γ ⊢ (⌈ patt_free_evar x' or ϕ ⌉) ---> (⌈ patt_free_evar x' and ! ϕ or ϕ ⌉) using i).
    {
      apply Framing_right.
      {  
        subst i.
        apply pile_evs_svs_kt.
        { set_solver. }
        { apply reflexivity. }
        { reflexivity. }
      }
      wf_auto2. apply Htmp1.
    }
    
    eapply MP.
    2: apply Htmp2.
    1: apply S3.
  }

  assert(S5: Γ ⊢ ⌈ (patt_free_evar x' and (! ϕ)) ⌉ or ⌈ ϕ ⌉ using i).
  {
    pose proof (Htmp := (prf_prop_or_iff Γ AC_patt_defined) (patt_free_evar x' and ! ϕ) ϕ ltac:(auto) ltac:(auto)).
    simpl in Htmp.
    apply pf_conj_elim_l_meta in Htmp;[|wf_auto2|wf_auto2].
    eapply MP.
    2: {
      subst i.
      useBasicReasoning.
      apply Htmp.
    }
    1: apply S4.
  }

  assert(S6: Γ ⊢ subst_ctx AC (patt_free_evar x' and ϕ) ---> ! ⌈ patt_free_evar x' and ! ϕ ⌉ using i).
  {
    pose proof (Htmp := @Singleton_ctx Σ Γ AC AC_patt_defined ϕ x').
    simpl in Htmp.
    unfold patt_and in Htmp at 1.
    apply not_not_elim_meta in Htmp.
    3: { wf_auto2. }
    2: { wf_auto2. }
    replace (patt_sym (Definedness_Syntax.inj definedness) $ (patt_free_evar x' and ! ϕ))%ml
      with (patt_defined (patt_free_evar x' and ! ϕ)) in Htmp by reflexivity.
    
    toMyGoal.
    { wf_auto2. }
    mgIntro.
    remember (ExGen := {[ev_x; x']}, SVSubst := ∅, KT := false) as gpi.
    rewrite Heqi.
    mgAdd (@useBasicReasoning _ _ _ gpi Htmp).
    mgApply 0. mgIntro. mgApply 2.
    mgExactn 1.
  }

  pose proof (S7 := S5). unfold patt_or in S7.

  assert(S8: Γ ⊢ subst_ctx AC (patt_free_evar x' and ϕ) ---> ⌈ ϕ ⌉ using i).
  {
    eapply syllogism_meta.
    5: apply S7.
    4: apply S6.
    1-3: wf_auto2.
  }
  assert (S9: Γ ⊢ all, (subst_ctx AC (patt_bound_evar 0 and ϕ) ---> ⌈ ϕ ⌉) using i).
  {
    eapply universal_generalization with (x := x') in S8.
    3: { wf_auto2. }
    2: { subst i. apply pile_evs_svs_kt.
      { set_solver. }
      { apply reflexivity. }
      { reflexivity. }
    }
    simpl in S8.
    
    rewrite evar_quantify_subst_ctx in S8;[assumption|].

    simpl in S8.
    case_match; try contradiction.
    rewrite evar_quantify_fresh in S8; [assumption|].
    apply S8.
  }

  assert(S10: Γ ⊢ (ex, subst_ctx AC (b0 and ϕ)) ---> ⌈ ϕ ⌉ using i).
  {
    unfold patt_forall in S9.
    unfold patt_not in S9 at 1.

    assert (Heq: evar_quantify x' 0 (subst_ctx AC (patt_free_evar x' and ϕ)) = subst_ctx AC (b0 and ϕ)).
    {
      rewrite evar_quantify_subst_ctx;[assumption|].
      f_equal.
      simpl.
      case_match; [|congruence].
      rewrite evar_quantify_fresh; [assumption|].
      reflexivity.
    }
    rewrite <- Heq.
    apply Ex_gen.
    2: {simpl. unfold evar_is_fresh_in in Hx1'. clear -Hx1'. set_solver. }
    1: {
      subst i.
      apply pile_evs_svs_kt.
      { set_solver. }
      { apply reflexivity. }
      { reflexivity. }
    }
    assumption.
  }

  assert (S11: Γ ⊢ ϕ ---> ((ex, patt_bound_evar 0) and ϕ) using i).
  {
    toMyGoal.
    { wf_auto2. }
    mgIntro.
    mgAdd (@usePropositionalReasoning _ _ _ i (@conj_intro Σ Γ (ex, b0) ϕ ltac:(auto) ltac:(auto))).
    
    mgAssert ((ϕ ---> ex , b0 and ϕ)).
    { wf_auto2. }
    {  mgApply 0.
        subst i.
       mgAdd (@useBasicReasoning _ _ _ (ExGen := {[ev_x; x']}, SVSubst := ∅, KT := false) (Existence Γ)).
       mgExactn 0.
    }
    mgApply 2. mgExactn 1.
  }

  assert (well_formed (ex , (b0 and ϕ))).
  {
    unfold well_formed,well_formed_closed in *.
    destruct_and!.
    simpl; split_and!; auto.
    eapply well_formed_closed_ex_aux_ind. 2: eassumption. lia.
  }
  
  assert (S12: Γ ⊢ ϕ ---> ex, (b0 and ϕ) using i).
  {

    assert(well_formed (ex , (evar_quantify x' 0 (patt_free_evar x') and ϕ))).
    {
      unfold well_formed,well_formed_closed in *. simpl in *.
      destruct_and!. split_and!; auto.
      all: repeat case_match; auto.
    }
    
    assert(Htmp: Γ ⊢ ((ex, b0) and ϕ ---> (ex, (b0 and ϕ))) using i).
    {
      toMyGoal.
      { wf_auto2. }
      mgIntro.
      mgDestructAnd 0.
      fromMyGoal.
      replace b0 with (evar_quantify x' 0 (patt_free_evar x')).
      2: { simpl. case_match;[reflexivity|congruence]. }
      apply Ex_gen.
      2: { simpl. case_match;[|congruence]. simpl.
           unfold evar_is_fresh_in in Hx1'. clear -Hx1'. set_solver.
      }
      1: {
        subst i.
        apply pile_evs_svs_kt.
        { set_solver. }
        { apply reflexivity. }
        { reflexivity. }
      }
      toMyGoal.
      { wf_auto2. }
      do 2 mgIntro.
      mgAssert ((patt_free_evar x' and ϕ)) using first 2.
      { wf_auto2. }
      { unfold patt_and. unfold patt_not at 1. mgIntro.
        mgDestructOr 2.
        - mgApply 2. mgExactn 0.
        - mgApply 2. mgExactn 1.
      }
      mgClear 1. mgClear 0.
      fromMyGoal.
      case_match;[|congruence].

      replace (patt_free_evar x' and ϕ)
        with (instantiate (ex, (patt_bound_evar 0 and ϕ)) (patt_free_evar x')).
      2: {
        simpl. rewrite bevar_subst_not_occur.
        { unfold well_formed, well_formed_closed in *.
          destruct_and!. auto.
        }
        reflexivity.
      }
      subst i.
      useBasicReasoning.
      apply Ex_quan.
      { wf_auto2. }
    }
    eapply syllogism_meta.
    5: { apply Htmp. }
    4: assumption.
    1-3: wf_auto2.
  }

  assert(S13: Γ ⊢ (subst_ctx AC ϕ) ---> (subst_ctx AC (ex, (b0 and ϕ))) using i).
  {
    apply Framing.
    {
      subst i. apply pile_evs_svs_kt.
      { set_solver. }
      { set_solver. }
      { reflexivity. }
    }
    apply S12.
  }

  assert(S14: Γ ⊢ (subst_ctx AC (ex, (b0 and ϕ))) ---> (⌈ ϕ ⌉) using i).
  {
    pose proof (Htmp := @prf_prop_ex_iff Σ Γ AC (b0 and ϕ) x').
    feed specialize Htmp.
    { unfold evar_is_fresh_in in *.
      rewrite free_evars_subst_ctx. clear -Hx1' Hx'2. simpl. set_solver.
    }
    { auto. }
    unfold exists_quantify in Htmp.
    rewrite evar_quantify_subst_ctx in Htmp.
    { assumption. }

    assert (well_formed (ex , subst_ctx AC (b0 and ϕ))).
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
        apply pile_evs_svs_kt.
        {
          set_solver.
        }
        {
          apply reflexivity.
        }
        {
          reflexivity.
        }
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

Lemma elements_union_empty ϕ:
  elements (free_evars ϕ ∪ ∅) = elements (free_evars ϕ).
Proof.
  apply f_equal.
  set_solver.
Qed.

Lemma phi_impl_defined_phi Γ ϕ:
  theory ⊆ Γ ->
  well_formed ϕ ->
  Γ ⊢ ϕ ---> ⌈ ϕ ⌉
  using pi_Generic
                     (ExGen := {[ev_x;
                               evar_fresh
                                 (elements (free_evars ϕ) )]},
                      SVSubst := ∅, KT := false).
Proof.
  intros HΓ wfϕ.
  eapply cast_proof'.
  {
    replace ϕ with (subst_ctx box ϕ) at 1 by reflexivity.
    reflexivity.
  }
  eapply useGenericReasoning.
  2: {
    apply in_context_impl_defined; assumption.  
  }
  {
    simpl.
    apply pile_evs_svs_kt.
    { 
      cut (elements (free_evars ϕ ∪ ∅) = elements (free_evars ϕ)).
      {
        intros H'. rewrite H'. apply reflexivity.
      }
      rewrite elements_union_empty.
      reflexivity.
    }
    {
      apply reflexivity.
    }
    {
      reflexivity.
    }
  }
Defined.

Lemma total_phi_impl_phi Γ ϕ:
  theory ⊆ Γ ->
  well_formed ϕ ->
  Γ ⊢ ⌊ ϕ ⌋ ---> ϕ
  using pi_Generic
  (ExGen := {[ev_x;
            evar_fresh
              (elements (free_evars ϕ) )]},
   SVSubst := ∅, KT := false).
Proof.
  intros HΓ wfϕ.
  unfold patt_total.
  pose proof (Htmp := @phi_impl_defined_phi Γ (! ϕ) HΓ ltac:(wf_auto2)).
  apply A_impl_not_not_B_meta.
  1,2: wf_auto2.
  apply modus_tollens.
  simpl in Htmp.
  cut (free_evars ϕ ∪ ∅ = free_evars ϕ).
  {
    intros H'. rewrite H' in Htmp. apply Htmp.
  }
  set_solver.
Defined.

Lemma total_phi_impl_phi_meta Γ ϕ i:
  theory ⊆ Γ ->
  well_formed ϕ ->
  ProofInfoLe (pi_Generic
  (ExGen := {[ev_x;
            evar_fresh
              (elements (free_evars ϕ) )]},
   SVSubst := ∅, KT := false)) i ->
  Γ ⊢ ⌊ ϕ ⌋ using i ->
  Γ ⊢ ϕ using i.
Proof.
  intros HΓ wfϕ pile H.
  eapply MP.
  1: exact H.
  eapply useGenericReasoning.
  2: apply total_phi_impl_phi.
  {
    eapply pile_trans. 2: apply pile.
    apply pile_evs_svs_kt.
    { apply reflexivity. }
    { apply reflexivity. }
    { reflexivity. }
  }
  1: exact HΓ.
  exact wfϕ.
Defined.
  Fixpoint framing_patterns Γ ϕ (pf : Γ ⊢ ϕ) : list Pattern :=
    match pf with
    | ProofSystem.hypothesis _ _ _ _ => []
    | ProofSystem.P1 _ _ _ _ _ => []
    | ProofSystem.P2 _ _ _ _ _ _ _ => []
    | ProofSystem.P3 _ _ _ => []
    | ProofSystem.Modus_ponens _ _ _ m0 m1
      => (@framing_patterns _ _ m0) ++ (@framing_patterns _ _ m1)
    | ProofSystem.Ex_quan _ _ _ _ => []
    | ProofSystem.Ex_gen _ _ _ x _ _ pf _ => @framing_patterns _ _ pf
    | ProofSystem.Prop_bott_left _ _ _ => []
    | ProofSystem.Prop_bott_right _ _ _ => []
    | ProofSystem.Prop_disj_left _ _ _ _ _ _ _ => []
    | ProofSystem.Prop_disj_right _ _ _ _ _ _ _ => []
    | ProofSystem.Prop_ex_left _ _ _ _ _ => []
    | ProofSystem.Prop_ex_right _ _ _ _ _ => []
    | ProofSystem.Framing_left _ _ _ psi _ m0 => psi :: (@framing_patterns _ _ m0)
    | ProofSystem.Framing_right _ _ _ psi _ m0 => psi :: (@framing_patterns _ _ m0)
    | ProofSystem.Svar_subst _ _ _ _ _ _ m0 => @framing_patterns _ _ m0
    | ProofSystem.Pre_fixp _ _ _ => []
    | ProofSystem.Knaster_tarski _ _ phi psi m0 => @framing_patterns _ _ m0
    | ProofSystem.Existence _ => []
    | ProofSystem.Singleton_ctx _ _ _ _ _ _ => []
    end.
  
  Check map.
    (*fun psi => evar_fresh (elements (free_evars ψ ∪ free_evars psi))*)

  Theorem deduction_theorem_noKT Γ ϕ ψ
    (gpi : GenericProofInfo)
    (pf : Γ ∪ {[ ψ ]} ⊢ ϕ using pi_Generic gpi) :
    well_formed ϕ ->
    well_formed ψ ->
    theory ⊆ Γ ->
    pi_generalized_evars gpi ## free_evars ψ ->
    pi_substituted_svars gpi ## free_svars ψ ->
    pi_uses_kt gpi = false ->
    Γ ⊢ ⌊ ψ ⌋ ---> ϕ
    using pi_Generic
    (ExGen :=
      (
        {[ev_x; evar_fresh (elements (free_evars ψ))]}
        ∪ pi_generalized_evars gpi
        ∪ free_evars ψ
        ∪ (list_to_set (map (fun psi => evar_fresh (elements (free_evars ψ ∪ free_evars psi))) (framing_patterns (proj1_sig pf)) ))
      ),
     SVSubst := (pi_substituted_svars gpi ∪ free_svars ψ),
     KT := false
    ).
  Proof.
    intros wfϕ wfψ HΓ HnoExGen HnoSvarSubst HnoKT.
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
          apply total_phi_impl_phi; assumption.
        }
        {
          apply pile_evs_svs_kt.
          {
            clear. set_solver.
          }
          {
            clear. set_solver.
          }
          { reflexivity. }
        }
        
      + assert (axiom0 ∈ Γ).
        { clear -e n. set_solver. }
        toMyGoal.
        { wf_auto2. }
        mgIntro. mgClear 0. fromMyGoal.
        eapply useGenericReasoning.
        2: apply (@hypothesis Σ Γ axiom0 i H).
        apply pile_evs_svs_kt.
        {
          set_solver.
        }
        {
          set_solver.
        }
        {
          simpl. reflexivity.
        }
    - (* P1 *)
      toMyGoal.
      { wf_auto2. }
      do 3 mgIntro. mgExactn 1.
    - (* P2 *)
      toMyGoal.
      { wf_auto2. }
      mgIntro. mgClear 0. fromMyGoal.
      usePropositionalReasoning.
      apply P2; assumption.
    - (* P3 *)
      toMyGoal.
      { wf_auto2. }
      mgIntro. mgClear 0. fromMyGoal.
      usePropositionalReasoning.
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

      destruct Hpf as [Hpf1 Hpf2 Hpf3 Hpf4].
      simpl in Hpf1, Hpf2, Hpf3, Hpf4.
      feed specialize IHpf1.
      {
        constructor; simpl.
        { exact I. }
        { set_solver. }
        { set_solver. }
        { unfold implb in *. repeat case_match; try reflexivity; simpl in *; try assumption. inversion Heqb. }
      }
      { assumption. }
      feed specialize IHpf2.
      {
        constructor; simpl.
        { exact I. }
        { set_solver. }
        { set_solver. }
        { unfold implb in *. repeat case_match; try reflexivity; simpl in *; try assumption. inversion Heqb. }
      }
      { wf_auto2. }
      
      (* simplify the constraint *)
      simpl.
      rewrite map_app.
      rewrite list_to_set_app_L.
      simpl.
      match goal with
      | [|- _ using ?constraint] => remember constraint as i'
      end.

      (* weaken the induction hypotheses so that their constraint
         matches the constraint of the goal *)
      apply useGenericReasoning with (i := i') in IHpf1.
      2: {
        subst i'.
        apply pile_evs_svs_kt.
        { clear. set_solver. }
        { clear. set_solver. }
        { reflexivity. }
      }

      apply useGenericReasoning with (i := i') in IHpf2.
      2: {
        subst i'.
        apply pile_evs_svs_kt.
        { clear. set_solver. }
        { clear. set_solver. }
        { reflexivity. }
      }

      toMyGoal.
      { wf_auto2. }
      mgIntro.
      mgAdd IHpf2.
      mgAssert ((phi1 ---> phi2)).
      { wf_auto2. }
      { mgApply 0. mgExactn 1. }
      mgApply 2.
      mgAdd IHpf1.
      mgApply 0.
      mgExactn 2.
    - (* Existential Quantifier *)
      toMyGoal.
      { wf_auto2. }
      mgIntro. mgClear 0. fromMyGoal.
      useBasicReasoning.
      apply Ex_quan. wf_auto2.
    - (* Existential Generalization *)
      destruct Hpf as [Hpf1 Hpf2 Hpf3 Hpf4].
      simpl in Hpf1, Hpf2, Hpf3, Hpf4.
      (*
      simpl in HnoExGen.
      case_match;[congruence|]. *)
      feed specialize IHpf.
      {
        constructor; simpl.
        { exact I. }
        { clear -Hpf2. set_solver. }
        { clear -Hpf3. set_solver. }
        { apply Hpf4. }
      }
      { wf_auto2. }

      apply reorder_meta in IHpf.
      2-4: wf_auto2.
      apply Ex_gen with (x0 := x) in IHpf.
      3: { simpl. set_solver. }
      2: { apply pile_evs_svs_kt.
        { set_solver. }
        { set_solver. }
        { reflexivity. }
      }
      apply reorder_meta in IHpf.
      2-4: wf_auto2.
      exact IHpf.
      
    - (* Propagation of ⊥, left *)
      toMyGoal.
      { wf_auto2. }
      mgIntro. mgClear 0; auto. fromMyGoal.
      useBasicReasoning.
      apply Prop_bott_left; assumption.
    - (* Propagation of ⊥, right *)
      toMyGoal.
      { wf_auto2. }
      mgIntro. mgClear 0; auto. fromMyGoal.
      useBasicReasoning.
      apply Prop_bott_right; assumption.
    - (* Propagation of 'or', left *)
      toMyGoal.
      { wf_auto2. }
      mgIntro. mgClear 0; auto. fromMyGoal.
      useBasicReasoning.
      apply Prop_disj_left; assumption.
    - (* Propagation of 'or', right *)
      toMyGoal.
      { wf_auto2. }
      mgIntro. mgClear 0; auto. fromMyGoal.
      useBasicReasoning.
      apply Prop_disj_right; assumption.
    - (* Propagation of 'exists', left *)
      toMyGoal.
      { wf_auto2. }
      mgIntro. mgClear 0; auto. fromMyGoal.
      useBasicReasoning.
      apply Prop_ex_left; assumption.
    - (* Propagation of 'exists', right *)
      toMyGoal.
      { wf_auto2. }
      mgIntro. mgClear 0; auto. fromMyGoal.
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
      destruct Hpf as [Hpf1 Hpf2 Hpf3 Hpf4].
      simpl in Hpf1,Hpf2,Hpf3,Hpf4.
      feed specialize IHpf.
      {
        constructor; simpl.
        { exact I. }
        { set_solver. }
        { set_solver. }
        { apply Hpf4. }
      }
      { wf_auto2. }

      match goal with
      | [|- _ using ?constraint] => remember constraint as i'
      end.

      apply useGenericReasoning with (i0 := i') in IHpf.
      2: {
        subst i'.
        apply pile_evs_svs_kt.
        { clear. set_solver. }
        { apply reflexivity. }
        { reflexivity. }
      }

      assert (S2: Γ ⊢ phi1 ---> (phi2 or ⌈ ! ψ ⌉) using i').
      { toMyGoal.
        { wf_auto2. }
        mgAdd IHpf. mgIntro.
        mgAdd (@usePropositionalReasoning _ _ _ i' (@A_or_notA Σ Γ (⌈ ! ψ ⌉) ltac:(wf_auto2))).
        mgDestructOr 0.
        - mgRight. mgExactn 0.
        - mgLeft.
          mgAssert((phi1 ---> phi2)).
          { wf_auto2. }
          { mgApply 1. mgExactn 0. }
          mgApply 3. mgExactn 2.
      }

      assert (S3: Γ ⊢ (⌈ ! ψ ⌉ $ psi) ---> ⌈ ! ψ ⌉ using i').
      {
        replace (⌈ ! ψ ⌉ $ psi)
          with (subst_ctx (@ctx_app_l _ AC_patt_defined psi ltac:(assumption)) (! ψ))
          by reflexivity.
        subst i'.
        eapply useGenericReasoning.
        2: apply in_context_impl_defined; auto.
        apply pile_evs_svs_kt.
        {
          replace (free_evars (! ψ)) with (free_evars (ψ)).
          2: {
            simpl. set_solver.
          }
          simpl.
          clear.
          replace (free_evars psi ∪ (∅ ∪ ∅)) with (free_evars psi) by set_solver.
          set_solver.
        }
        { clear. set_solver. }
        { reflexivity. }
      }

      assert (S4: Γ ⊢ (phi1 $ psi) ---> ((phi2 or ⌈ ! ψ ⌉) $ psi) using i').
      { apply Framing_left. 2: wf_auto2. 2: exact S2.
        subst i'. apply pile_basic_generic.
      }

      assert (S5: Γ ⊢ (phi1 $ psi) ---> ((phi2 $ psi) or (⌈ ! ψ ⌉ $ psi)) using i').
      {
        pose proof (Htmp := @prf_prop_or_iff Σ Γ (@ctx_app_l _ box psi ltac:(assumption)) phi2 (⌈! ψ ⌉)).
        feed specialize Htmp.
        { wf_auto2. }
        { wf_auto2. }
        simpl in Htmp.
        apply pf_iff_proj1 in Htmp.
        3: wf_auto2.
        2: wf_auto2.
        eapply syllogism_meta.
        5: {
          subst i'. useBasicReasoning.
          apply Htmp.
        }
        4: assumption.
        all: wf_auto2.
      }
      
      assert (S6: Γ ⊢ ((phi2 $ psi) or (⌈ ! ψ ⌉ $ psi)) ---> ((phi2 $ psi) or (⌈ ! ψ ⌉)) using i').
      {
        toMyGoal.
        { wf_auto2. }
        mgIntro. mgAdd S3.
        (* TODO we need a tactic for adding  something with stronger constraint. *)
        mgAdd (@usePropositionalReasoning _ _ _ i' (@A_or_notA Σ Γ (phi2 $ psi) ltac:(auto))).
        mgDestructOr 0.
        - mgLeft. mgExactn 0.
        - mgRight. mgApply 1. mgApply 2. mgExactn 0.
      }

      assert (S7: Γ ⊢ (phi1 $ psi) ---> ((phi2 $ psi)  or ⌈ ! ψ ⌉) using i').
      {
        toMyGoal.
        { wf_auto2. }
        mgAdd S5. mgAdd S6. mgIntro.
        mgAssert (((phi2 $ psi) or (⌈ ! ψ ⌉ $ psi))).
        { wf_auto2. }
        { mgApply 1. mgExactn 2. }
        mgDestructOr 3.
        - mgLeft. mgExactn 3.
        - mgApply 0. mgRight. mgExactn 3.
      }

      toMyGoal.
      { wf_auto2. }
      do 2 mgIntro. mgAdd S7.
      mgAssert ((phi2 $ psi or ⌈ ! ψ ⌉)).
      { wf_auto2. }
      { mgApply 0. mgExactn 2. }
      mgDestructOr 3.
      + mgExactn 3.
      + mgAssert ((phi2 $ psi or ⌈ ! ψ ⌉)).
        { wf_auto2. }
        { mgApply 0. mgExactn 2. }
        mgAdd (@usePropositionalReasoning _ _ _ i' (@A_or_notA Σ Γ (phi2 $ psi) ltac:(auto))).
        mgDestructOr 0.
        * mgExactn 0.
        * mgAdd (@usePropositionalReasoning _ _ _ i' (@bot_elim Σ Γ (phi2 $ psi) ltac:(auto))).
          mgApply 0.
          mgApply 3.
          mgExactn 5.
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
      simpl in HnoExGen. simpl in HnoSvarSubst. simpl in HnoKT.

      destruct Hpf as [Hpf1 Hpf2 Hpf3 Hpf4].
      simpl in Hpf1,Hpf2,Hpf3,Hpf4.
      feed specialize IHpf.
      {
        constructor; simpl.
        { exact I. }
        { set_solver. }
        { set_solver. }
        { apply Hpf4. }
      }
      { wf_auto2. }

      match goal with
      | [|- _ using ?constraint] => remember constraint as i'
      end.

      apply useGenericReasoning with (i0 := i') in IHpf.
      2: {
        subst i'.
        apply pile_evs_svs_kt.
        { clear. set_solver. }
        { apply reflexivity. }
        { reflexivity. }
      }

      assert (S2: Γ ⊢ phi1 ---> (phi2 or ⌈ ! ψ ⌉) using i').
      { toMyGoal.
        { wf_auto2. }
        mgAdd IHpf. mgIntro.
        mgAdd (@usePropositionalReasoning _ _ _ i' (@A_or_notA Σ Γ (⌈ ! ψ ⌉) ltac:(wf_auto2))).
        mgDestructOr 0.
        - mgRight. mgExactn 0.
        - mgLeft.
          mgAssert((phi1 ---> phi2)).
          { wf_auto2. }
          { mgApply 1. mgExactn 0. }
          mgApply 3. mgExactn 2.
      }

      assert (S3: Γ ⊢ (psi $ ⌈ ! ψ ⌉) ---> ⌈ ! ψ ⌉ using i').
      {
        replace (psi $ ⌈ ! ψ ⌉)
          with (subst_ctx (@ctx_app_r _ psi AC_patt_defined ltac:(assumption)) (! ψ))
          by reflexivity.
          subst i'.
          eapply useGenericReasoning.
          2: apply in_context_impl_defined; auto.

          apply pile_evs_svs_kt.
          {
            replace (free_evars (! ψ)) with (free_evars (ψ)).
            2: {
              simpl. set_solver.
            }
            simpl.
            clear.
            replace (free_evars psi ∪ (∅ ∪ ∅)) with (free_evars psi) by set_solver.
            set_solver.
          }
          { clear. set_solver. }
          { reflexivity. }
      }

      assert (S4: Γ ⊢ (psi $ phi1) ---> (psi $ (phi2 or ⌈ ! ψ ⌉)) using i').
      { apply Framing_right. 2: wf_auto2. 2: exact S2.
        subst i'. apply pile_basic_generic.
      }

      assert (S5: Γ ⊢ (psi $ phi1) ---> ((psi $ phi2) or (psi $ ⌈ ! ψ ⌉)) using i').
      {
        pose proof (Htmp := @prf_prop_or_iff Σ Γ (@ctx_app_r _ psi box ltac:(assumption)) phi2 (⌈! ψ ⌉)).
        feed specialize Htmp.
        { wf_auto2. }
        { wf_auto2. }
        simpl in Htmp.
        apply pf_iff_proj1 in Htmp.
        2,3: wf_auto2.
        eapply syllogism_meta.
        5: subst i'; useBasicReasoning; apply Htmp.
        4: assumption.
        all: wf_auto2.
      }
      
      assert (S6: Γ ⊢ ((psi $ phi2) or (psi $ ⌈ ! ψ ⌉)) ---> ((psi $ phi2) or (⌈ ! ψ ⌉)) using i').
      {
        toMyGoal.
        { wf_auto2. }
        mgIntro. mgAdd S3.
        mgAdd (@usePropositionalReasoning _ _ _ i' (@A_or_notA Σ Γ (psi $ phi2) ltac:(auto))).
        mgDestructOr 0.
        - mgLeft. mgExactn 0.
        - mgRight. mgApply 1. mgApply 2. mgExactn 0.
      }

      assert (S7: Γ ⊢ (psi $ phi1) ---> ((psi $ phi2)  or ⌈ ! ψ ⌉) using i').
      {
        toMyGoal.
        { wf_auto2. }
        mgAdd S5. mgAdd S6. mgIntro.
        mgAssert (((psi $ phi2) or (psi $ ⌈ ! ψ ⌉))).
        { wf_auto2. }
        { mgApply 1. mgExactn 2. }
        mgDestructOr 3.
        - mgLeft. mgExactn 3.
        - mgApply 0. mgRight. mgExactn 3.
      }

      toMyGoal.
      { wf_auto2. }
      do 2 mgIntro. mgAdd S7.
      mgAssert ((psi $ phi2 or ⌈ ! ψ ⌉)).
      { wf_auto2. }
      { mgApply 0. mgExactn 2. }
      mgDestructOr 3.
      + mgExactn 3.
      + mgAssert ((psi $ phi2 or ⌈ ! ψ ⌉)).
        { wf_auto2. }
        { mgApply 0. mgExactn 2. }
        mgAdd (@usePropositionalReasoning _ _ _ i' (@A_or_notA Σ Γ (psi $ phi2) ltac:(auto))).
        mgDestructOr 0.
        * mgExactn 0.
        * mgAdd (@usePropositionalReasoning _ _ _ i' (@bot_elim Σ Γ (psi $ phi2) ltac:(auto))).
          mgApply 0.
          mgApply 3.
          mgExactn 5.
    - (* Set variable substitution *)
      simpl in HnoExGen. simpl in HnoSvarSubst. simpl in IHpf.
      case_match.
      { congruence. }
      specialize (IHpf ltac:(assumption) ltac:(assumption) ltac:(assumption)).
      replace (⌊ ψ ⌋ ---> free_svar_subst phi psi X)
        with (free_svar_subst (⌊ ψ ⌋ ---> phi) psi X).
      2: {  simpl.
           rewrite [free_svar_subst ψ psi X]free_svar_subst_fresh.
           { assumption. }
           reflexivity.
      }
      apply Svar_subst.
      3: auto.
      1,2: wf_auto2.
    - (* Prefixpoint *)
      toMyGoal.
      { wf_auto2. }
      mgIntro. mgClear 0; auto. fromMyGoal. intros _ _.
      apply Pre_fixp. wf_auto2.
    - (* Knaster-Tarski *)
      simpl in HnoKT. congruence.
    - (* Existence *)
      toMyGoal.
      { wf_auto2. }
      mgIntro. mgClear 0. fromMyGoal. intros _ _.
      apply Existence.
    - (* Singleton *)
      toMyGoal.
      { wf_auto2. }
      mgIntro. mgClear 0. fromMyGoal. intros _ _.
      apply Singleton_ctx. wf_auto2.
  Defined.

  Lemma membership_introduction Γ ϕ:
    well_formed ϕ ->
    theory ⊆ Γ ->
    Γ ⊢ ϕ ->
    Γ ⊢ all, ((patt_bound_evar 0) ∈ml ϕ).
  Proof.
    intros wfϕ HΓ Hϕ.

    remember (fresh_evar ϕ) as x.

    replace ϕ with (evar_quantify x 0 ϕ).
    2: {
      rewrite evar_quantify_fresh.
      subst; auto. reflexivity.
    }
    
    
    assert (S2: Γ ⊢ (ϕ ---> (patt_free_evar x ---> ϕ))).
    {
      apply P1; auto.
    }

    assert(S3: Γ ⊢ patt_free_evar x ---> ϕ).
    {
      eapply Modus_ponens. 4: apply S2. all: auto.
    }

    assert(S4: Γ ⊢ patt_free_evar x ---> patt_free_evar x).
    {
      apply A_impl_A; auto.
    }

    assert(S5: Γ ⊢ patt_free_evar x ---> (patt_free_evar x and ϕ)).
    {
      toMyGoal.
      { wf_auto2. }
      mgIntro. unfold patt_and. mgIntro.
      mgAssert ((! ϕ)).
      { wf_auto2. }
      { mgApply 1. mgIntro. mgApply 2. mgExactn 0.  }
      mgApply 2.
      mgAdd Hϕ. mgExactn 0.
    }

    assert(S6: Γ ⊢ ⌈ patt_free_evar x ⌉ ---> ⌈ (patt_free_evar x and ϕ) ⌉).
    {
      apply Framing_right. wf_auto2. assumption.
    }
    
    assert(S7: Γ ⊢ ⌈ patt_free_evar x ⌉).
    {
      apply defined_evar; assumption.
    }

    assert(S9: Γ ⊢ (patt_free_evar x) ∈ml ϕ).
    {
      eapply Modus_ponens. 4: apply S6.
      3: assumption.
      1,2: wf_auto2.
    }

    eapply universal_generalization with (x0 := x) in S9.
    2: { wf_auto2. }
    simpl in S9. case_match;[|congruence]. exact S9.
  Defined.

  Lemma membership_elimination Γ ϕ:
    well_formed ϕ ->
    theory ⊆ Γ ->
    Γ ⊢ all, ((patt_bound_evar 0) ∈ml ϕ) ->
    Γ ⊢ ϕ.
  Proof.
    intros wfϕ HΓ H.

    remember (fresh_evar ϕ) as x.
    assert(S1: Γ ⊢ all, ((patt_bound_evar 0) ∈ml (evar_quantify x 0 ϕ))).
    {
      rewrite evar_quantify_fresh.
      { subst x.  apply set_evar_fresh_is_fresh'. }
      assumption.
    }
    
    assert(S2: Γ ⊢ (all, ((patt_bound_evar 0) ∈ml (evar_quantify x 0 ϕ))) ---> (patt_free_evar x ∈ml ϕ)).
    {
      replace (b0 ∈ml evar_quantify x 0 ϕ)
        with (evar_quantify x 0 (patt_free_evar x ∈ml ϕ))
      .
      2: {
        simpl. case_match;[|congruence]. reflexivity.
      }
      apply forall_variable_substitution.
      { wf_auto2. }
    }

    assert(well_formed (all , b0 ∈ml evar_quantify x 0 ϕ)) by wf_auto2.
    
    assert(S3: Γ ⊢ patt_free_evar x ∈ml ϕ).
    {
      eapply Modus_ponens. 4: apply S2.
      3: assumption.
      1,2: wf_auto2.
    }

    pose proof (S5 := Singleton_ctx Γ AC_patt_defined box ϕ x ltac:(wf_auto2)).
    simpl in S5.

    assert (S6: Γ ⊢ ⌈ patt_free_evar x and ϕ ⌉ ---> (patt_free_evar x ---> ϕ) ).
    {
      toMyGoal.
      { wf_auto2. }
      mgIntro. mgIntro.
      mgAdd S5. unfold patt_and at 1. unfold patt_or at 1.
      mgAssert((! ! patt_sym (Definedness_Syntax.inj definedness) $ (patt_free_evar x and ϕ) ---> ! (patt_free_evar x and ! ϕ)))
      using first 1.
      { wf_auto2. }
      {
        remember ((! ! patt_sym (Definedness_Syntax.inj definedness) $ (patt_free_evar x and ϕ) ---> ! (patt_free_evar x and ! ϕ)))
          as A.
        fromMyGoal. intros _ _. apply not_not_elim; subst; auto 10.
      }
      mgClear 0.

      mgAssert((! (patt_free_evar x and ! ϕ))) using first 2.
      { wf_auto2. }
      {
        mgApply 0. mgClear 0.
        fromMyGoal. intros _ _. apply not_not_intro; auto 10.
      }
      mgClear 0. mgClear 0.

      unfold patt_and.
      mgAssert ((! patt_free_evar x or ! ! ϕ)) using first 1.
      { wf_auto2. }
      {
        fromMyGoal. intros _ _. apply not_not_elim; auto 10.
      }
      mgClear 0.

      unfold patt_or.
      mgApplyMeta (@not_not_elim Σ _ _ _).
      mgApply 0.
      mgApplyMeta (@not_not_intro Σ _ _ _).
      mgExactn 1.
    }

    assert (S7: Γ ⊢ patt_free_evar x ---> ϕ).
    {
      eapply Modus_ponens. 4: apply S6.
      3: assumption.
      1,2: wf_auto2.
    }

    pose proof (S8 := S7).
    apply universal_generalization with (x0 := x) in S8; auto.

    assert (S9: Γ ⊢ (ex, patt_bound_evar 0) ---> ϕ).
    {
      unfold patt_forall in S8.
      simpl in S8.
      case_match; [|congruence].
      
      replace b0 with (evar_quantify x 0 (patt_free_evar x)).
      2: { simpl. case_match; [|congruence]. reflexivity. }
      
      apply Ex_gen; auto.
    }

    eapply Modus_ponens.
    4: apply S9.
    3: apply Existence.
    all: auto.
    Unshelve. all: wf_auto2.
  Defined.

  Lemma membership_not_1 Γ ϕ x:
    well_formed ϕ ->
    theory ⊆ Γ ->
    Γ ⊢ ((patt_free_evar x) ∈ml (! ϕ)) ---> ! ((patt_free_evar x) ∈ml ϕ).
  Proof.
    intros Hwf HΓ.
    
    pose proof (S1 := Singleton_ctx Γ AC_patt_defined AC_patt_defined ϕ x ltac:(wf_auto2)).
    simpl in S1.

    assert (S2: Γ ⊢ ⌈ patt_free_evar x and ! ϕ ⌉ ---> ! ⌈ patt_free_evar x and ϕ ⌉).
    {

      replace (patt_sym (Definedness_Syntax.inj definedness) $ (patt_free_evar x and ϕ))
        with (⌈ patt_free_evar x and ϕ ⌉) in S1 by reflexivity.

      replace (patt_sym (Definedness_Syntax.inj definedness) $ (patt_free_evar x and ! ϕ))
        with (⌈ patt_free_evar x and ! ϕ ⌉) in S1 by reflexivity.
      
      toMyGoal.
      { wf_auto2. }
      mgIntro. mgAdd S1.
      unfold patt_and at 1.
      mgAssert ((! ⌈ patt_free_evar x and ϕ ⌉ or ! ⌈ patt_free_evar x and ! ϕ ⌉))
               using first 1.
      { wf_auto2. }        
      {
        fromMyGoal. intros _ _.
        apply not_not_elim; auto 10.
      }
      mgClear 0.

      (* Symmetry of Or *)
      mgAssert ((! ⌈ patt_free_evar x and ! ϕ ⌉ or ! ⌈ patt_free_evar x and ϕ ⌉))
               using first 1.
      { wf_auto2. }
      {
        mgAdd (@A_or_notA Σ Γ (! ⌈ patt_free_evar x and ϕ ⌉) ltac:(wf_auto2)).
        mgDestructOr 0.
        - mgRight. mgExactn 0.
        - mgLeft. mgApply 1. mgExactn 0.
      }
      mgClear 0.

      mgApply 0. mgClear 0. fromMyGoal. intros _ _.
      apply not_not_intro. wf_auto2.
    }
    apply S2.
  Qed.

  Lemma membership_not_2 Γ (ϕ : Pattern) x:
    well_formed ϕ = true ->
    theory ⊆ Γ ->
    Γ ⊢ ((!(patt_free_evar x ∈ml ϕ)) ---> (patt_free_evar x ∈ml (! ϕ)))%ml.
  Proof.
    intros wfϕ HΓ.
    pose proof (S1 := @defined_evar Γ x HΓ).
    assert (S2: Γ ⊢ ⌈ (patt_free_evar x and ϕ) or (patt_free_evar x and (! ϕ)) ⌉).
    {
      assert(H: Γ ⊢ (patt_free_evar x ---> ((patt_free_evar x and ϕ) or (patt_free_evar x and (! ϕ))))).
      {
        toMyGoal.
        { wf_auto2. }
        mgIntro. mgAdd (@A_or_notA Σ Γ ϕ ltac:(auto)).
        mgDestructOr 0.
        - mgLeft. unfold patt_and. mgIntro. unfold patt_or.
          mgAssert ((! ϕ)).
          { wf_auto2. }
          {
            mgApply 2. mgClear 0. mgClear 1. fromMyGoal. intros _ _.
            apply not_not_intro; auto.
          }
          mgApply 3. mgExactn 0.
        - mgRight. unfold patt_and. mgIntro. unfold patt_or.
          mgApply 0. mgApplyMeta (@not_not_elim Σ Γ ϕ ltac:(auto)).
          mgApply 2. mgIntro. mgApply 3. mgExactn 1.
      }
      eapply Framing_right in H.
      eapply Modus_ponens. 4: apply H.
      3: assumption.
      1-3: wf_auto2.
    }

    pose proof (Htmp := @prf_prop_or_iff Σ Γ AC_patt_defined (patt_free_evar x and ϕ) (patt_free_evar x and ! ϕ)
                                        ltac:(wf_auto2) ltac:(wf_auto2)).
    simpl in Htmp.
    apply pf_iff_proj1 in Htmp; auto 10.
    eapply Modus_ponens.
    4: apply Htmp.
    3: assumption.
    1,2: wf_auto2.
  Defined.

  Lemma membership_not_iff Γ ϕ x:
    well_formed ϕ ->
    theory ⊆ Γ ->
    Γ ⊢ ((patt_free_evar x) ∈ml (! ϕ)) <---> ! ((patt_free_evar x) ∈ml ϕ).
  Proof.
    intros Hwf HΓ.
    apply pf_iff_split.
    1,2: wf_auto2.
    - apply membership_not_1; assumption.
    - apply membership_not_2; assumption.
  Defined.
  
  Lemma membership_or_1 Γ x ϕ₁ ϕ₂:
    well_formed ϕ₁ ->
    well_formed ϕ₂ ->
    theory ⊆ Γ ->
    Γ ⊢ (patt_free_evar x ∈ml (ϕ₁ or ϕ₂)) ---> ((patt_free_evar x ∈ml ϕ₁) or (patt_free_evar x ∈ml ϕ₂)).
  Proof.
    intros wfϕ₁ wfϕ₂ HΓ.
    unfold patt_in.
    eapply syllogism_intro.
    5: apply Prop_disj_right.
    1,2,3,5,6,7: wf_auto2.
    apply Framing_right. wf_auto2.
    toMyGoal.
    { wf_auto2. }
    mgIntro. mgDestructAnd 0.
    mgDestructOr 1.
    - mgLeft. unfold patt_and. mgIntro.
      mgDestructOr 2.
      + mgApply 2. mgExactn 0.
      + mgApply 2. mgExactn 1.
    - mgRight. unfold patt_and. mgIntro.
      mgDestructOr 2.
      + mgApply 2. mgExactn 0.
      + mgApply 2. mgExactn 1.
  Defined.

  Lemma membership_or_2 Γ x ϕ₁ ϕ₂:
    well_formed ϕ₁ ->
    well_formed ϕ₂ ->
    theory ⊆ Γ ->
    Γ ⊢ ((patt_free_evar x ∈ml ϕ₁) or (patt_free_evar x ∈ml ϕ₂)) ---> (patt_free_evar x ∈ml (ϕ₁ or ϕ₂)).
  Proof.
    intros wfϕ₁ wfϕ₂ HΓ.
    unfold patt_in.
    pose proof (H1 := @prf_prop_or_iff Σ Γ AC_patt_defined (patt_free_evar x and ϕ₁) (patt_free_evar x and ϕ₂)
                                      ltac:(auto) ltac:(auto)).
    apply pf_iff_proj2 in H1; auto 10.
    eapply syllogism_intro.
    4: apply H1.
    1-3: wf_auto2.
    simpl.
    apply Framing_right. wf_auto2.

    toMyGoal.
    { wf_auto2. }
    mgIntro. mgDestructOr 0; mgDestructAnd 0.
    - unfold patt_and. mgIntro. mgDestructOr 2.
      + mgApply 2. mgExactn 0.
      + mgApply 2. mgLeft. mgExactn 1.
    - unfold patt_and. mgIntro. mgDestructOr 2.
      + mgApply 2. mgExactn 0.
      + mgApply 2. mgRight. mgExactn 1.
  Defined.

  Lemma membership_or_iff Γ x ϕ₁ ϕ₂:
    well_formed ϕ₁ ->
    well_formed ϕ₂ ->
    theory ⊆ Γ ->
    Γ ⊢ (patt_free_evar x ∈ml (ϕ₁ or ϕ₂)) <---> ((patt_free_evar x ∈ml ϕ₁) or (patt_free_evar x ∈ml ϕ₂)).
  Proof.
    intros wfϕ₁ wfϕ₂ HΓ.
    apply pf_iff_split.
    1,2: wf_auto2.
    + apply membership_or_1; assumption.
    + apply membership_or_2; assumption.
  Defined.

  Lemma membership_and_1 Γ x ϕ₁ ϕ₂:
    well_formed ϕ₁ ->
    well_formed ϕ₂ ->
    theory ⊆ Γ ->
    Γ ⊢ (patt_free_evar x ∈ml (ϕ₁ and ϕ₂)) ---> ((patt_free_evar x ∈ml ϕ₁) and (patt_free_evar x ∈ml ϕ₂)).
  Proof.
    intros wfϕ₁ wfϕ₂ HΓ.
    unfold patt_and.
    toMyGoal.
    { wf_auto2. }
    mgIntro.
    unshelve (mgApplyMeta (membership_not_1 _ _ _) in 0); auto.
    mgIntro. mgApply 0. mgClear 0.
    unshelve (mgApplyMeta (membership_or_2 _ _ _ _)); auto.
    mgDestructOr 0.
    - mgLeft.
      unshelve (mgApplyMeta (membership_not_2 _ _ _) in 0); auto 10.
      mgExactn 0.
    - mgRight.
      unshelve (mgApplyMeta (membership_not_2 _ _ _) in 0); auto 10.
      mgExactn 0.
  Defined.
  
  Lemma membership_and_2 Γ x ϕ₁ ϕ₂:
    well_formed ϕ₁ ->
    well_formed ϕ₂ ->
    theory ⊆ Γ ->
    Γ ⊢ ((patt_free_evar x ∈ml ϕ₁) and (patt_free_evar x ∈ml ϕ₂)) ---> (patt_free_evar x ∈ml (ϕ₁ and ϕ₂)).
  Proof.
    intros wfϕ₁ wfϕ₂ HΓ.
    toMyGoal.
    { wf_auto2. }
    mgIntro.
    mgDestructAnd 0.
    unfold patt_and.
    unshelve (mgApplyMeta (@membership_not_2 _ _ _ _ _)); auto 10.
    mgIntro.
    unshelve (mgApplyMeta (membership_or_1 _ _ _ _) in 2); auto 10.
    mgDestructOr 2.
    - unshelve (mgApplyMeta (membership_not_1 _ _ _) in 2); auto 10.
      mgApply 2. mgExactn 0.
    - unshelve (mgApplyMeta (membership_not_1 _ _ _) in 2); auto 10.
      mgApply 2. mgExactn 1.
  Defined.

  Lemma membership_and_iff Γ x ϕ₁ ϕ₂:
    well_formed ϕ₁ ->
    well_formed ϕ₂ ->
    theory ⊆ Γ ->
    Γ ⊢ (patt_free_evar x ∈ml (ϕ₁ and ϕ₂)) <---> ((patt_free_evar x ∈ml ϕ₁) and (patt_free_evar x ∈ml ϕ₂)).
  Proof.
    intros wfϕ₁ wfϕ₂ HΓ.
    apply pf_iff_split.
    1,2: wf_auto2.
    + apply membership_and_1; assumption.
    + apply membership_and_2; assumption.
  Defined.

  Lemma equality_elimination_basic Γ φ1 φ2 C :
    theory ⊆ Γ ->
    well_formed φ1 -> well_formed φ2 ->
    PC_wf C ->
    mu_free (pcPattern C) ->
    Γ ⊢ (φ1 =ml φ2) ---> (* somewhere "and" is here, somewhere meta-implication *)
      (emplace C φ1) <---> (emplace C φ2).
  Proof.
    intros HΓ WF1 WF2 WFC Hmf.

    unshelve(eapply deduction_theorem_noKT).
    remember (Γ ∪ {[ (φ1 <---> φ2) ]}) as Γ'.
    assert (Γ' ⊢ (φ1 <---> φ2)). {
      apply hypothesis.
      - abstract (now apply well_formed_iff).
      - abstract (rewrite HeqΓ'; apply elem_of_union_r; constructor).
    }
    eapply prf_equiv_congruence.
    all: try assumption.
    all: try (abstract auto).
    { 
      abstract (
        apply well_formed_and; apply well_formed_imp; unfold emplace;
        apply well_formed_free_evar_subst_0; auto
      ).
    }
    3: {
      abstract(
        simpl; unfold prf_equiv_congruence; destruct C as [ψ E]; simpl;
        rewrite uses_kt_nomu_eq_prf_equiv_congruence;[apply Hmf|reflexivity|reflexivity]
      ).
    }
    2: {
      abstract (
        simpl;
        unfold prf_equiv_congruence; destruct C as [ψ E];
        simpl;
        match goal with
        | [ |- uses_svar_subst ?S _ = false ]
          => replace S with (free_svars φ1 ∪ free_svars φ2) by (clear; set_solver)
        end;
        rewrite uses_svar_subst_eq_prf_equiv_congruence;
        [(clear;set_solver)|reflexivity|reflexivity]
      ).
    }
    1: {
      abstract (
        simpl;
        unfold prf_equiv_congruence; destruct C as [ψ E];
        match goal with
        | [ |- uses_ex_gen ?e _ = false ]
          => replace e with (free_evars φ1 ∪ free_evars φ2) by (clear; set_solver)
        end;
        simpl;
        rewrite uses_ex_gen_eq_prf_equiv_congruence;
          [(clear; set_solver)|reflexivity|reflexivity]
      ).
    }
  Defined.

  Lemma equality_elimination_basic_iter_1 Γ ϕ₁ ϕ₂ l C :
    theory ⊆ Γ ->
    well_formed ϕ₁ ->
    well_formed ϕ₂ ->
    wf l ->
    PC_wf C ->
    mu_free (pcPattern C) ->
    Γ ⊢ foldr patt_imp ((emplace C ϕ₁) <---> (emplace C ϕ₂)) ((ϕ₁ =ml ϕ₂) :: l).
  Proof.
    intros HΓ wfϕ₁ wfϕ₂ wfl wfC Hmf.
    induction l; simpl.
    - apply equality_elimination_basic; assumption.
    - pose proof (wfal := wfl). apply andb_prop in wfl as [wfa wfl].
      specialize (IHl wfl).
      simpl in IHl.
      pose proof (proved_impl_wf _ _ IHl).
      toMyGoal.
      { wf_auto2. }
      mgIntro. mgIntro. mgClear 1.
      fromMyGoal. intros _ _.
      apply IHl.
  Defined.


  Lemma equality_elimination_basic_iter Γ ϕ₁ ϕ₂ l₁ l₂ C :
    theory ⊆ Γ ->
    well_formed ϕ₁ ->
    well_formed ϕ₂ ->
    wf l₁ ->
    wf l₂ ->
    PC_wf C ->
    mu_free (pcPattern C) ->
    Γ ⊢ foldr patt_imp ((emplace C ϕ₁) <---> (emplace C ϕ₂)) (l₁ ++ (ϕ₁ =ml ϕ₂)::l₂).
  Proof.
    intros HΓ wfϕ₁ wfϕ₂ wfl₁ wfl₂ wfC Hmf.
    induction l₁; simpl.
    - apply equality_elimination_basic_iter_1; assumption.
    - pose proof (wfal := wfl₁). unfold wf in wfl₁. simpl in wfl₁. apply andb_prop in wfl₁ as [wfa wfl].
      specialize (IHl₁ wfl).
      pose proof (proved_impl_wf _ _ IHl₁).
      toMyGoal.
      { wf_auto2. }
      mgIntro. mgClear 0.
      fromMyGoal. intros _ _.
      apply IHl₁.
  Defined.

  Lemma equality_elimination_helper Γ φ1 φ2 ψ x :
    theory ⊆ Γ ->
    mu_free ψ ->
    well_formed φ1 -> well_formed φ2 -> well_formed ψ ->     
    Γ ⊢ (φ1 =ml φ2) ---> 
      (free_evar_subst ψ φ1 x) ---> (free_evar_subst ψ φ2 x).
  Proof.
    intros HΓ MF WF1 WF2 WFψ.
    unshelve (eapply (deduction_theorem_noKT)); try assumption.
    2,3: abstract(auto).

    remember (Γ ∪ {[ (φ1 <---> φ2) ]}) as Γ'.
    assert (Γ' ⊢ (φ1 <---> φ2)). {
      apply hypothesis.
      - abstract (now apply well_formed_iff).
      - abstract (rewrite HeqΓ'; apply elem_of_union_r; constructor).
    }
    apply pf_iff_proj1; auto.

    apply (@eq_prf_equiv_congruence Σ Γ' φ1 φ2 WF1 WF2 (free_evars ψ ∪ free_evars φ1 ∪ free_evars φ2)
        (free_svars ψ ∪ free_svars φ1 ∪ free_svars φ2)); auto.
    3: {
      abstract (
        simpl; rewrite orbF;
        rewrite uses_kt_nomu_eq_prf_equiv_congruence;
        [apply MF|reflexivity|reflexivity]
      ).
    }
    2: {
      abstract (
        simpl; rewrite orbF;
        match goal with
        | [ |- uses_svar_subst ?S _ = false ]
          => replace S with (free_svars φ1 ∪ free_svars φ2) by (clear; set_solver)
        end;
        rewrite uses_svar_subst_eq_prf_equiv_congruence;
        [(clear;set_solver)|reflexivity|reflexivity]
     ).
    }
    1: {
      abstract (
        simpl; rewrite orbF;
        match goal with
        | [ |- uses_ex_gen ?e _ = false ]
          => replace e with (free_evars φ1 ∪ free_evars φ2) by (clear; set_solver)
        end;
        simpl;
        rewrite uses_ex_gen_eq_prf_equiv_congruence;
          [(clear; set_solver)|reflexivity|reflexivity]
      ).
    }
  Defined.


  Corollary equality_elimination2 Γ φ1 φ2 ψ:
    theory ⊆ Γ ->
    mu_free ψ ->
    well_formed φ1 -> well_formed φ2 -> well_formed_closed_ex_aux ψ 1 -> well_formed_closed_mu_aux ψ 0 ->
    Γ ⊢ (φ1 =ml φ2) ---> 
      (bevar_subst ψ φ1 0) ---> (bevar_subst ψ φ2 0).
  Proof.
    intros HΓ MF WF1 WF2 WF3 WF4. remember (fresh_evar ψ) as x.
    assert (x ∉ free_evars ψ) by now apply x_eq_fresh_impl_x_notin_free_evars.
    rewrite (@bound_to_free_variable_subst _ ψ x 1 0 φ1 ltac:(lia)); auto.
    { unfold well_formed,well_formed_closed in *. destruct_and!. assumption. }
    rewrite (@bound_to_free_variable_subst _ ψ x 1 0 φ2 ltac:(lia)); auto.
    { unfold well_formed,well_formed_closed in *. destruct_and!. assumption. }
    apply equality_elimination_helper; auto.
    { now apply mu_free_evar_open. }
    apply wf_evar_open_from_wf_ex.
    unfold well_formed, well_formed_closed; simpl.
    rewrite -> WF3, -> WF4, -> mu_free_wfp; auto.
  Defined.

  Lemma patt_eq_sym Γ φ1 φ2:
    theory ⊆ Γ ->
    well_formed φ1 -> well_formed φ2 ->
    Γ ⊢ φ1 =ml φ2 ---> φ2 =ml φ1.
  Proof.
    intros HΓ WF1 WF2.
    unshelve (eapply deduction_theorem_noKT).
    4: exact HΓ.
    2,3: wf_auto.
    remember (Γ ∪ {[ (φ1 <---> φ2) ]}) as Γ'.
    assert (Γ' ⊢ (φ1 <---> φ2)). {
      apply hypothesis. apply well_formed_iff; auto.
      rewrite HeqΓ'. apply elem_of_union_r. constructor.
    }
    apply pf_iff_equiv_sym in H; auto.
    apply patt_iff_implies_equal; auto.
    all: reflexivity.
  Qed.

  Lemma evar_quantify_equal_simpl : forall φ1 φ2 x n,
      evar_quantify x n (φ1 =ml φ2) = (evar_quantify x n φ1) =ml (evar_quantify x n φ2).
  Proof. auto. Qed.

  Lemma exists_functional_subst φ φ' Γ :
    theory ⊆ Γ ->
    mu_free φ -> well_formed φ' -> well_formed_closed_ex_aux φ 1 -> well_formed_closed_mu_aux φ 0 ->
    Γ ⊢ ((instantiate (patt_exists φ) φ') and (patt_exists (patt_equal φ' (patt_bound_evar 0)))) ---> (patt_exists φ).
  Proof.
    intros HΓ MF WF WFB WFM.
    remember (fresh_evar (φ $ φ')) as Zvar.
    remember (patt_free_evar Zvar) as Z.
    assert (well_formed Z) as WFZ. { rewrite HeqZ. auto. }
                                   assert (Γ ⊢ (patt_equal φ' Z <---> patt_equal Z φ')). {
      pose proof (SYM1 := @patt_eq_sym Γ φ' Z ltac:(auto) ltac:(auto) WFZ).
      pose proof (SYM2 := @patt_eq_sym Γ Z φ' ltac:(assumption) WFZ ltac:(auto)).
      apply pf_iff_split. 3,4: assumption. 1,2: wf_auto2.  
    }
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
    pose proof (@equality_elimination2 Γ φ' Z φ HΓ MF WF WFZ WFB).
    apply pf_iff_iff in H. destruct H.
    assert (well_formed (ex, φ)) as WFEX. { wf_auto. now apply mu_free_wfp. }
    pose proof (EQ := Ex_quan Γ φ Zvar WFEX).
    epose proof (PC := @prf_conclusion Σ Γ (patt_equal φ' Z) (instantiate (ex , φ) (patt_free_evar Zvar) ---> ex , φ) ltac:(apply well_formed_equal;auto) _ EQ).
    2-3: apply well_formed_equal;auto.
    assert (Γ
              ⊢ patt_equal φ' Z ---> instantiate (ex , φ) φ' ---> ex , φ) as HSUB. {
      pose proof (EE := @equality_elimination2 Γ φ' Z φ HΓ
                                               ltac:(auto) ltac:(auto) ltac:(auto) WFB).
      unfold instantiate in EE.
      epose proof (PSP := @prf_strenghten_premise Σ Γ ((patt_equal φ' Z) and (instantiate (ex , φ) Z))
                                                 ((patt_equal φ' Z) and (instantiate (ex , φ) φ'))
                                                 (ex , φ) _ _ _).
      eapply Modus_ponens. 4: apply and_impl.
      1,2,4,5,6: wf_auto2.
      eapply Modus_ponens. 4: eapply Modus_ponens.
      7: exact PSP.
      1,2,4,5: wf_auto2.
      * unshelve (epose proof (AI := @and_impl' Σ Γ (patt_equal φ' Z) (bevar_subst φ Z 0) (ex , φ) _ _ _)).
        1,2,3: wf_auto2.
        unfold instantiate. eapply Modus_ponens. 4: exact AI.
        1, 2: unfold patt_equal, patt_iff, patt_total, patt_defined; wf_auto2.
        rewrite <- HeqZ in PC.
        exact PC.
      * apply and_drop. 1-3: wf_auto2.
        unshelve(epose proof (AI := @and_impl' Σ Γ (patt_equal φ' Z) (instantiate (ex , φ) φ') (instantiate (ex , φ) Z) _ _ _)).
        1-3: wf_auto2.
        eapply Modus_ponens. 4: exact AI. 3: apply EE.
        all: wf_auto2.
    }
    eapply Modus_ponens. 4: apply and_impl'; auto.
    1,2,4: unfold instantiate,patt_equal,patt_total,patt_defined in *; wf_auto2.
    apply reorder_meta; auto.
    { wf_auto2. }
    eapply (Ex_gen Γ _ _ Zvar) in HSUB. unfold exists_quantify in HSUB.
    rewrite evar_quantify_equal_simpl in HSUB.
    rewrite -> HeqZ, -> HeqZvar in HSUB. simpl evar_quantify in HSUB.
    2-3: wf_auto2.
    2: {
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
    destruct (decide ((fresh_evar (φ $ φ')) = (fresh_evar (φ $ φ')))) in HSUB;
      simpl in HSUB. 2: congruence.
    rewrite evar_quantify_noop in HSUB; auto.

    apply count_evar_occurrences_0.
    unfold fresh_evar. simpl.
    epose (NIN := not_elem_of_union (evar_fresh (elements (free_evars φ ∪ free_evars φ'))) (free_evars φ) (free_evars φ')). destruct NIN as [NIN1 NIN2].
    epose (NIN3 := NIN1 _). destruct NIN3. auto.
    Unshelve.
    5: { unfold instantiate. simpl.
         apply set_evar_fresh_is_fresh'.
    }

    1-4: wf_auto2.
  Qed.

  Corollary forall_functional_subst φ φ' Γ :
    theory ⊆ Γ ->
    mu_free φ -> well_formed φ' -> well_formed_closed_ex_aux φ 1 -> well_formed_closed_mu_aux φ 0 ->
    Γ ⊢ ((patt_forall φ) and (patt_exists (patt_equal φ' (patt_bound_evar 0)))) ---> (bevar_subst φ φ' 0).
  Proof.
    intros HΓ MF WF WFB WFM. unfold patt_forall.
    assert (well_formed (bevar_subst φ φ' 0)) as BWF. {
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
      all: simpl; wf_auto.
    }
    unshelve (epose proof (H := @exists_functional_subst (! φ) φ' Γ HΓ _ WF _)).
    { simpl. rewrite andbT. exact MF. }
    { wf_auto. }
    simpl in H.
    epose proof (H0 := @and_impl Σ _ _ _ _ _ _ _).
    eapply Modus_ponens in H0. 4: apply H. 2-3: unfold patt_equal,patt_total,patt_defined;wf_auto2.
    apply reorder_meta in H0. 2-4: auto.
    2: { wf_auto. }
    
    epose proof (H1 := @and_impl' Σ _ _ _ _ _ _ _). eapply Modus_ponens in H1. exact H1.
    1-2: shelve.
    apply reorder_meta. 1-3: shelve.
    epose proof (H2 := @P4 Σ Γ (bevar_subst φ φ' 0) (! ex , patt_not (φ)) _ _).
    clear H H1.
    epose proof (H := @prf_weaken_conclusion Σ Γ (ex , patt_equal φ' b0) ((bevar_subst φ φ' 0 ---> ⊥) ---> ex , (! φ)) ((bevar_subst φ φ' 0 ---> ⊥) ---> ! ! ex , (! φ)) _ _ _).
    eapply Modus_ponens in H. eapply Modus_ponens in H; auto.
    2-4: shelve.
    2: {
      epose proof (H1 := @prf_weaken_conclusion Σ Γ (bevar_subst φ φ' 0 ---> ⊥) (ex , (! φ)) (! ! ex , (! φ)) _ _ _). eapply Modus_ponens. 4: exact H1. 1-2: shelve.
      apply not_not_intro. shelve.
    }
    eapply syllogism_intro in H2. exact H2. all: auto.
    Unshelve.
    all: wf_auto2.
  Qed.

End ProofSystemTheorems.


Lemma MyGoal_rewriteBy {Σ : Signature} {syntax : Syntax}
    (Γ : Theory) (l₁ l₂ : list Pattern) (ϕ₁ ϕ₂ : Pattern) (C : PatternCtx) :
theory ⊆ Γ ->
mu_free (pcPattern C) ->
@mkMyGoal Σ Γ (l₁ ++ (ϕ₁ =ml ϕ₂) :: l₂) (emplace C ϕ₂) ->
@mkMyGoal Σ Γ (l₁ ++ (ϕ₁ =ml ϕ₂) :: l₂) (emplace C ϕ₁).
Proof.
intros HΓ HmfC H.
mgExtractWF wfl wfg.

pose proof (wfl₁ := wfapp_proj_1 wfl).
apply wfapp_proj_2 in wfl.
unfold wf in wfl. simpl in wfl.
apply andb_prop in wfl.
destruct wfl as [wfeq wfl₂].
pose proof (wfC := wf_emplaced_impl_wf_context wfg).
remember C as C'.
destruct C as [CE Cψ]. unfold PC_wf in wfC. simpl in *.
mgAssert ((emplace C' ϕ₁ <---> emplace C' ϕ₂)).
{ unfold emplace in *. wf_auto2. }
{ fromMyGoal. intros _ _. apply equality_elimination_basic_iter; auto.
  { wf_auto2. }
  { wf_auto2. }
}
unfold patt_iff.
unshelve(eapply (@MyGoal_applyMetaIn _ _ _ _ (@pf_conj_elim_r _ _ _ _ _ _))).
{ wf_auto2. }
{ wf_auto2. }

replace (l₁ ++ (ϕ₁ =ml ϕ₂) :: l₂) with ((l₁ ++ (ϕ₁ =ml ϕ₂) :: l₂) ++ []) in H
 by (rewrite app_nil_r; reflexivity).
apply myGoal_clear_hyp with (h := ((emplace C' ϕ₂) ---> (emplace C' ϕ₁))) in H.
unshelve (eapply (@myGoal_assert _ _ _ _ _ _ H)).
{ wf_auto2. }

simpl.
rewrite -app_assoc.
simpl.
eapply MyGoal_weakenConclusion.

replace ((l₁ ++ (ϕ₁ =ml ϕ₂) :: l₂) ++ [(emplace C' ϕ₂) ---> (emplace C' ϕ₁); emplace C' ϕ₂])
with (((l₁ ++ (ϕ₁ =ml ϕ₂) :: l₂) ++ [(emplace C' ϕ₂) ---> (emplace C' ϕ₁)]) ++ [emplace C' ϕ₂]).
2: {  rewrite -app_assoc. simpl. reflexivity. }
apply MyGoal_exactn.
Qed.

Ltac2 mgRewriteBy (n : constr) (atn : int) :=
eapply (@cast_proof_mg_hyps)
> [ (rewrite <- (firstn_skipn $n); ltac1:(rewrite /firstn; rewrite /skipn); reflexivity)
  | ()
  ];
lazy_match! goal with
| [ |- @of_MyGoal ?sgm (@mkMyGoal ?sgm ?g (?l₁ ++ (?a' =ml ?a)::?l₂) ?p)]
  => 
    let hr : HeatResult := heat atn a' p in
    let heq := Control.hyp (hr.(equality)) in
    let pc := (hr.(pc)) in
    eapply (@cast_proof_mg_goal _ $g) >
      [ rewrite $heq; reflexivity | ()];
    Std.clear [hr.(equality)];
    apply MyGoal_rewriteBy
    > [ ()
      | ()
      | lazy_match! goal with
        | [ |- of_MyGoal (@mkMyGoal ?sgm ?g ?l ?p)]
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
            eapply (@cast_proof_mg_goal _ $g) >
              [ rewrite $heq2_pf; reflexivity | ()];
            Std.clear [heq2 ; (hr.(star_ident))];
            eapply (@cast_proof_mg_hyps)
            > [ (ltac1:(rewrite /app); reflexivity)
              | ()
              ]
        end
      ]
end
.

Tactic Notation "mgRewriteBy" constr(n) "at" constr(atn) :=
(let ff := ltac2:(n atn |-
                    mgRewriteBy
                      (Option.get (Ltac1.to_constr(n)))
                      (constr_to_int (Option.get (Ltac1.to_constr(atn))))
                 ) in
 ff n atn).



Local Example ex_rewriteBy {Σ : Signature} {syntax : Syntax} Γ a a' b:
theory ⊆ Γ ->
well_formed a ->
well_formed a' ->
well_formed b ->
mu_free b ->
Γ ⊢ a $ b ---> (a' =ml a) ---> a' $ b.
Proof.
intros HΓ wfa wfa' wfb mfb.
toMyGoal.
{ wf_auto2. }
mgIntro. mgIntro.
mgRewriteBy 1 at 1.
{ assumption. }
{ simpl. assumption. }
mgExactn 0.
Defined.

Lemma patt_equal_implies_iff {Σ : Signature} {syntax : Syntax} (ϕ1 ϕ2 : Pattern) (Γ : Theory) :
  theory ⊆ Γ ->
  well_formed ϕ1 ->
  well_formed ϕ2 ->
  Γ ⊢ ϕ1 =ml ϕ2 ->
  Γ ⊢ (ϕ1 <---> ϕ2).
Proof.
intros HΓ wfϕ1 wfϕ2 H.
unfold "=ml" in H.
apply total_phi_impl_phi_meta in H.
{ assumption. }
{ assumption. }
{ wf_auto2. }
Defined.


Ltac wfauto' := try_wfauto2.

Lemma disj_equals_greater_1_meta {Σ : Signature} {syntax : Syntax} Γ ϕ₁ ϕ₂:
theory ⊆ Γ ->
well_formed ϕ₁ ->
well_formed ϕ₂ ->
Γ ⊢ ϕ₁ ⊆ml ϕ₂ ->
Γ ⊢ (ϕ₁ or ϕ₂) =ml ϕ₂.
Proof.
intros HΓ wfϕ₁ wfϕ₂ Hsub.
apply patt_iff_implies_equal; wfauto'.
apply pf_iff_split; wfauto'.
+ toMyGoal.
  { wf_auto2. }
  mgIntro. mgDestructOr 0.
  * apply total_phi_impl_phi_meta in Hsub;[|assumption|wfauto'].
    fromMyGoal. intros _ _. apply Hsub.
  * fromMyGoal. intros _ _. apply A_impl_A;wfauto'.
+ toMyGoal.
  { wf_auto2. }
  mgIntro. mgRight;wfauto'. fromMyGoal. intros _ _. apply A_impl_A; wfauto'.
Defined.

Lemma def_not_phi_impl_not_total_phi {Σ : Signature} {syntax : Syntax} Γ ϕ:
theory ⊆ Γ ->
well_formed ϕ ->
Γ ⊢ ⌈ ! ϕ ⌉ ---> ! ⌊ ϕ ⌋.
Proof.
intros HΓ wfϕ.
toMyGoal.
{ wf_auto2. }
mgIntro.
unfold patt_total.
unfold patt_not.
mgIntro.
mgApply 1.
mgExactn 0.
Defined.

Lemma def_def_phi_impl_def_phi
{Σ : Signature} {syntax : Syntax} {Γ : Theory} (ϕ : Pattern) :
theory ⊆ Γ ->
well_formed ϕ ->
Γ ⊢ ⌈ ⌈ ϕ ⌉ ⌉ ---> ⌈ ϕ ⌉.
Proof.
intros HΓ wfϕ.
eapply (cast_proof).
{ 
  remember (@ctx_app_r _ (patt_sym (Definedness_Syntax.inj definedness)) box ltac:(wf_auto2)) as AC1.
  remember (@ctx_app_r _ (patt_sym (Definedness_Syntax.inj definedness)) AC1 ltac:(wf_auto2)) as AC2.
  replace (⌈ ⌈ ϕ ⌉ ⌉) with (subst_ctx AC2 ϕ) by (subst; reflexivity).
  subst. reflexivity.
}
apply in_context_impl_defined.
{ exact HΓ. }
{ exact wfϕ. }
Defined.

Lemma bott_not_defined {Σ : Signature} {syntax : Syntax} Γ :
Γ ⊢ ! ⌈ ⊥ ⌉.
Proof.
apply Prop_bott_right.
{ wf_auto2. }
Defined.

Lemma not_def_phi_impl_not_phi {Σ : Signature} {syntax : Syntax} Γ ϕ :
theory ⊆ Γ ->
well_formed ϕ ->
Γ ⊢ ! ⌈ ϕ ⌉ ---> ! ϕ.
Proof.
intros HΓ wfϕ.
toMyGoal.
{ wf_auto2. }
mgIntro.
mgIntro.
mgApply 0.
mgClear 0.
fromMyGoal. intros _ _.
apply phi_impl_defined_phi; assumption.
Defined.

Lemma tot_phi_impl_tot_def_phi {Σ : Signature} {syntax : Syntax} Γ ϕ :
theory ⊆ Γ ->
well_formed ϕ ->
Γ ⊢ ⌊ ϕ ⌋ ---> ⌊ ⌈ ϕ ⌉ ⌋.
Proof.
intros HΓ wfϕ.
toMyGoal.
{ wf_auto2. }
mgIntro.
mgIntro. mgApply 0. mgClear 0.
fromMyGoal. intros _ _.
apply Framing_right.
{ wf_auto2. }
apply not_def_phi_impl_not_phi; assumption.
Defined.



Lemma def_of_pred_impl_pred {Σ : Signature} {syntax : Syntax} Γ ψ :
theory ⊆ Γ ->
well_formed ψ ->
mu_free ψ ->
Γ ⊢ (ψ =ml patt_bott) or (ψ =ml patt_top) ->
Γ ⊢ ⌈ ψ ⌉ ---> ψ.
Proof.
intros HΓ wfψ Hmfψ H.
toMyGoal.
{wf_auto2. }
mgAdd H.
mgDestructOr 0.
- mgRewriteBy 0 at 2.
  { exact HΓ. }
  { simpl. rewrite Hmfψ.  reflexivity. }
  mgRewriteBy 0 at 1.
  { exact HΓ. }
  { simpl. reflexivity. }
  mgClear 0.
  fromMyGoal. intros _ _.
  apply bott_not_defined.
- mgRewriteBy 0 at 2.
  { exact HΓ. }
  { simpl. rewrite Hmfψ.  reflexivity. }
  mgClear 0.
  unfold patt_top. mgIntro. mgIntro. mgExactn 1.
Defined.

(* TODO need this non-meta *)
Lemma subseteq_antisym_meta {Σ : Signature} {syntax : Syntax} Γ ϕ₁ ϕ₂:
theory ⊆ Γ ->
well_formed ϕ₁ ->
well_formed ϕ₂ ->
Γ ⊢ (ϕ₁ ⊆ml ϕ₂) and (ϕ₂ ⊆ml ϕ₁) ->
Γ ⊢ ϕ₁ =ml ϕ₂.
Proof.
intros HΓ wfϕ₁ wfϕ₂ H.
unfold "=ml".
apply phi_impl_total_phi_meta.
{ wf_auto2. }
toMyGoal.
{ wf_auto2. }
mgAdd H.
mgDestructAnd 0.
unshelve (mgApplyMeta (total_phi_impl_phi HΓ _) in 0).
{ wf_auto2. }
unshelve (mgApplyMeta (total_phi_impl_phi HΓ _) in 1).
{ wf_auto2. }
mgSplitAnd.
- mgExactn 0.
- mgExactn 1.
Defined.

Lemma propagate_membership_conjunct_1 {Σ : Signature} {syntax : Syntax}
    Γ AC x ϕ₁ ϕ₂ :
theory ⊆ Γ ->
well_formed ϕ₁ ->
well_formed ϕ₂ ->
Γ ⊢ (subst_ctx AC (ϕ₁ and ((patt_free_evar x) ∈ml ϕ₂))) ---> ((patt_free_evar x) ∈ml ϕ₂).
Proof.
intros HΓ wfϕ₁ wfϕ₂.
unfold patt_in.
eapply syllogism_intro.
1,3 : wf_auto2.
2: apply Framing.
2: wf_auto2.
3: apply pf_conj_elim_r.
1-4: wf_auto2.
eapply syllogism_intro.
1,3: wf_auto2.
2: apply in_context_impl_defined.
2: assumption.
1,2: wf_auto2.
apply def_def_phi_impl_def_phi.
{ assumption. }
{ wf_auto2. }
Defined.


Lemma ceil_monotonic {Σ : Signature} {syntax : Syntax} Γ ϕ₁ ϕ₂ :
theory ⊆ Γ ->
well_formed ϕ₁ ->
well_formed ϕ₂ ->
Γ ⊢ ϕ₁ ---> ϕ₂ ->
Γ ⊢ ⌈ ϕ₁ ⌉ ---> ⌈ ϕ₂ ⌉.
Proof.
intros HΓ wfϕ₁ wfϕ₂ H.
apply Framing_right.
{ wf_auto2. }
exact H.
Defined.


Lemma floor_monotonic {Σ : Signature} {syntax : Syntax} Γ ϕ₁ ϕ₂ :
theory ⊆ Γ ->
well_formed ϕ₁ ->
well_formed ϕ₂ ->
Γ ⊢ ϕ₁ ---> ϕ₂ ->
Γ ⊢ ⌊ ϕ₁ ⌋ ---> ⌊ ϕ₂ ⌋.
Proof.
intros HΓ wfϕ₁ wfϕ₂ H.
unfold patt_total.
apply ProofMode.modus_tollens.
{ wf_auto2. }
{ wf_auto2. }
apply ceil_monotonic.
{ assumption. }
{ wf_auto2. }
{ wf_auto2. }
apply ProofMode.modus_tollens.
{ wf_auto2. }
{ wf_auto2. }
exact H.
Defined.

Lemma double_not_ceil_alt {Σ : Signature} {syntax : Syntax} Γ ϕ :
theory ⊆ Γ ->
well_formed ϕ ->
Γ ⊢ ( ⌈ ! ⌈ ϕ ⌉ ⌉ ---> (! ⌈ ϕ ⌉)) ->
Γ ⊢ ( ⌈ ϕ ⌉ ---> ! ( ⌈ ! ⌈ ϕ ⌉ ⌉)).
Proof.
intros HΓ wfϕ H.
toMyGoal.
{ wf_auto2. }
mgRewrite (@not_not_iff Σ Γ (⌈ ϕ ⌉) ltac:(wf_auto2)) at 1.
fromMyGoal. intros _ _.
apply ProofMode.modus_tollens.
{ wf_auto2. }
{ wf_auto2. }
exact H.
Defined.

Lemma membership_imp {Σ : Signature} {syntax : Syntax} Γ x ϕ₁ ϕ₂:
theory ⊆ Γ ->
well_formed ϕ₁ ->
well_formed ϕ₂ ->
Γ ⊢ (patt_free_evar x ∈ml (ϕ₁ ---> ϕ₂)) <---> ((patt_free_evar x ∈ml ϕ₁) ---> (patt_free_evar x ∈ml ϕ₂)).
Proof.
intros HΓ wfϕ₁ wfϕ₂.

toMyGoal.
{ wf_auto2. }
mgRewrite (@impl_iff_notp_or_q Σ Γ ϕ₁ ϕ₂ ltac:(wf_auto2) ltac:(wf_auto2)) at 1.
mgRewrite (@membership_or_iff Σ syntax Γ x (! ϕ₁) ϕ₂ ltac:(wf_auto2) ltac:(wf_auto2) HΓ) at 1.
mgRewrite (@membership_not_iff Σ syntax Γ ϕ₁ x ltac:(wf_auto2) HΓ) at 1.
mgRewrite <- (@impl_iff_notp_or_q Σ Γ (patt_free_evar x ∈ml ϕ₁) (patt_free_evar x ∈ml ϕ₂) ltac:(wf_auto2) ltac:(wf_auto2)) at 1.
fromMyGoal. intros _ _.
apply pf_iff_equiv_refl.
{ wf_auto2. }

Defined.

Lemma ceil_propagation_exists_1 {Σ : Signature} {syntax : Syntax} Γ ϕ:
theory ⊆ Γ ->
well_formed (ex, ϕ) ->
Γ ⊢ (⌈ ex, ϕ ⌉) ---> (ex, ⌈ ϕ ⌉).
Proof.
intros HΓ wfϕ.
apply Prop_ex_right.
{ wf_auto2. }
{ wf_auto2. }
Defined.

Lemma ceil_propagation_exists_2 {Σ : Signature} {syntax : Syntax} Γ ϕ:
theory ⊆ Γ ->
well_formed (ex, ϕ) ->
Γ ⊢ (ex, ⌈ ϕ ⌉) ---> (⌈ ex, ϕ ⌉).
Proof.
intros HΓ wfϕ.

remember (fresh_evar ϕ) as x.
replace (⌈ ϕ ⌉) with (evar_quantify x 0 (evar_open 0 x (⌈ ϕ ⌉))).
2: {
  rewrite evar_quantify_evar_open.
     {
       pose proof (@set_evar_fresh_is_fresh _ ϕ).
       unfold evar_is_fresh_in in H.
       simpl. set_solver.
     }
     wf_auto.
     reflexivity.
}
apply Ex_gen.
{ wf_auto2. }
{ wf_auto2. }
2: {  simpl.
      pose proof (Hfr := @set_evar_fresh_is_fresh _ ϕ).
      unfold evar_is_fresh_in in Hfr.
      simpl. set_solver.
}
unfold evar_open. simpl_bevar_subst.
fold (evar_open 0 x ϕ).
apply ceil_monotonic.
{ assumption. }
{ wf_auto2. }
{ wf_auto2. }
apply Ex_quan.
{ wf_auto2. }
Defined.

Lemma ceil_propagation_exists_iff {Σ : Signature} {syntax : Syntax} Γ ϕ:
theory ⊆ Γ ->
well_formed (ex, ϕ) ->
Γ ⊢ (⌈ ex, ϕ ⌉) <---> (ex, ⌈ ϕ ⌉).
Proof.
intros HΓ wfϕ.
apply pf_iff_split.
{ wf_auto2. }
{ wf_auto2. }
- apply ceil_propagation_exists_1; assumption.
- apply ceil_propagation_exists_2; assumption.
Defined.

Lemma membership_exists {Σ : Signature} {syntax : Syntax} Γ x ϕ:
theory ⊆ Γ ->
well_formed (ex, ϕ) ->
Γ ⊢ (patt_free_evar x ∈ml (ex, ϕ)) <---> (ex, patt_free_evar x ∈ml ϕ).
Proof.
intros HΓ wfϕ.
unfold "∈ml".
toMyGoal.
{ wf_auto2. }
mgRewrite <- (@ceil_propagation_exists_iff Σ syntax Γ (patt_free_evar x and ϕ) HΓ ltac:(wf_auto2)) at 1.
fromMyGoal. intros _ _.
assert (Htmp: Γ ⊢ (patt_free_evar x and ex, ϕ) <---> (ex, (patt_free_evar x and ϕ))).
{ (* prenex-exists-and *)
  toMyGoal.
  { wf_auto2. }
  mgRewrite (@patt_and_comm Σ Γ (patt_free_evar x) (ex, ϕ) ltac:(wf_auto2) ltac:(wf_auto2)) at 1.
  mgRewrite <- (@prenex_exists_and_iff Σ Γ ϕ (patt_free_evar x) ltac:(wf_auto2) ltac:(wf_auto2)) at 1.
  remember (evar_fresh (elements ({[x]} ∪ (free_evars ϕ)))) as y.
  mgSplitAnd; fromMyGoal; intros _ _.
  - apply (@strip_exists_quantify_l Σ Γ y).
    { subst y. simpl.
      eapply not_elem_of_larger_impl_not_elem_of.
      2: { apply set_evar_fresh_is_fresh'. }
      clear. set_solver.
    }
    { wf_auto2. }
    apply (@strip_exists_quantify_r Σ Γ y).
    { subst y. simpl.
      eapply not_elem_of_larger_impl_not_elem_of.
      2: { apply set_evar_fresh_is_fresh'. }
      clear. set_solver.
    }
    { wf_auto2. }
    apply ex_quan_monotone.
    { wf_auto2. }
    { wf_auto2. }
    unfold evar_open. simpl_bevar_subst.
    toMyGoal.
    { wf_auto2. }
    mgIntro. mgDestructAnd 0. mgSplitAnd.
    + mgExactn 1.
    + mgExactn 0.
  - apply (@strip_exists_quantify_l Σ Γ y).
    { subst y. simpl.
      eapply not_elem_of_larger_impl_not_elem_of.
      2: { apply set_evar_fresh_is_fresh'. }
      clear. set_solver.
    }
    { wf_auto2. }
    apply (@strip_exists_quantify_r Σ Γ y).
    { subst y. simpl.
      eapply not_elem_of_larger_impl_not_elem_of.
      2: { apply set_evar_fresh_is_fresh'. }
      clear. set_solver.
    }
    { wf_auto2. }
    apply ex_quan_monotone.
    { wf_auto2. }
    { wf_auto2. }
    unfold evar_open. simpl_bevar_subst.
    toMyGoal.
    { wf_auto2. }
    mgIntro. mgDestructAnd 0. mgSplitAnd.
    + mgExactn 1.
    + mgExactn 0.   
}
toMyGoal.
{ wf_auto2. }
mgRewrite Htmp at 1.
fromMyGoal. intros _ _.
apply pf_iff_equiv_refl.
{ wf_auto2. }
Defined.


Lemma membership_symbol_ceil_aux_aux_0 {Σ : Signature} {syntax : Syntax} Γ x ϕ:
theory ⊆ Γ ->
well_formed ϕ ->
Γ ⊢ ((⌈ patt_free_evar x and ϕ ⌉) ---> (⌊ ⌈ patt_free_evar x and ϕ ⌉  ⌋)).
Proof.
intros HΓ wfϕ.
unfold patt_total.
eapply syllogism_intro.
{ wf_auto2. }
2: { wf_auto2. }
3: {
  apply ProofMode.modus_tollens.
  { wf_auto2. }
  2: {
    apply ceil_monotonic.
    { exact HΓ. }
    { wf_auto2. }
    2: {
      apply membership_not_2.
      { wf_auto2. }
      { exact HΓ. }
    }
    { wf_auto2. }
  }
  { wf_auto2. }
}
{ wf_auto2. }
toMyGoal.
{ wf_auto2. }

mgRewrite (@not_not_iff Σ Γ (⌈patt_free_evar x and ϕ ⌉) ltac:(wf_auto2)) at 1.
fold (! ⌈ patt_free_evar x and ϕ ⌉ or ! ⌈ patt_free_evar x ∈ml (! ϕ) ⌉).
mgRewrite (@not_not_iff Σ Γ (! ⌈ patt_free_evar x and ϕ ⌉ or ! ⌈ patt_free_evar x ∈ml (! ϕ) ⌉) ltac:(wf_auto2)) at 1.
fold ((⌈ patt_free_evar x and ϕ ⌉ and ⌈ patt_free_evar x ∈ml (! ϕ) ⌉)).
unfold "∈ml".
fromMyGoal. intros _ _.
eapply cast_proof.
{
  replace (⌈ patt_free_evar x and ϕ ⌉)
          with (subst_ctx AC_patt_defined (patt_free_evar x and ϕ))
               by reflexivity.
  replace (⌈ ⌈ patt_free_evar x and ! ϕ ⌉ ⌉)
          with (subst_ctx (@ctx_app_r Σ ((@patt_sym Σ (@Definedness_Syntax.inj Σ syntax definedness))) AC_patt_defined ltac:(wf_auto2)) (patt_free_evar x and ! ϕ))
    by reflexivity.
  reflexivity.
}
apply Singleton_ctx.
{ exact wfϕ. }
Defined.

Lemma ceil_compat_in_or {Σ : Signature} {syntax : Syntax} Γ ϕ₁ ϕ₂:
theory ⊆ Γ ->
well_formed ϕ₁ ->
well_formed ϕ₂ ->
Γ ⊢ ( (⌈ ϕ₁ or ϕ₂ ⌉) <---> (⌈ ϕ₁ ⌉ or ⌈ ϕ₂ ⌉)).
Proof.
intros HΓ wfϕ₁ wfϕ₂.
toMyGoal.
{ wf_auto2. }
mgSplitAnd; mgIntro.
- mgApplyMeta (Prop_disj_right Γ ϕ₁ ϕ₂ (patt_sym (Definedness_Syntax.inj definedness)) ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2) ).
  mgExactn 0.
- mgDestructOr 0.
  + unshelve (mgApplyMeta (Framing_right Γ ϕ₁ (ϕ₁ or ϕ₂) (patt_sym (Definedness_Syntax.inj definedness)) ltac:(wf_auto2) _)).
    { toMyGoal. wf_auto2. mgIntro. mgLeft. mgExactn 0. }
    mgExactn 0.
  + unshelve (mgApplyMeta (Framing_right Γ ϕ₂ (ϕ₁ or ϕ₂) (patt_sym (Definedness_Syntax.inj definedness)) ltac:(wf_auto2) _)).
    { toMyGoal. wf_auto2. mgIntro. mgRight. mgExactn 0. }
    mgExactn 0.
Defined.

Lemma membership_symbol_ceil_aux_0 {Σ : Signature} {syntax : Syntax} Γ x y ϕ:
theory ⊆ Γ ->
well_formed ϕ ->
Γ ⊢ (⌈ patt_free_evar x and ϕ ⌉) ---> ⌈ patt_free_evar y and ⌈ patt_free_evar x and ϕ ⌉ ⌉.
Proof.
intros HΓ wfϕ.

toMyGoal.
{ wf_auto2. }
mgIntro.
mgApplyMeta (@membership_symbol_ceil_aux_aux_0 Σ syntax Γ x ϕ HΓ wfϕ) in 0.
fromMyGoal. intros _ _.
unfold patt_total.
fold (⌈ ! ⌈ patt_free_evar x and ϕ ⌉ ⌉ or ⌈ patt_free_evar y and ⌈ patt_free_evar x and ϕ ⌉ ⌉).
toMyGoal.
{ wf_auto2. }
mgRewrite <- (@ceil_compat_in_or Σ syntax Γ (! ⌈ patt_free_evar x and ϕ ⌉) (patt_free_evar y and ⌈ patt_free_evar x and ϕ ⌉) HΓ ltac:(wf_auto2) ltac:(wf_auto2)) at 1.

unshelve (mgApplyMeta (@ceil_monotonic Σ syntax Γ
                             (patt_free_evar y)
                             (! ⌈ patt_free_evar x and ϕ ⌉ or patt_free_evar y and ⌈ patt_free_evar x and ϕ ⌉)
                             HΓ ltac:(wf_auto2) ltac:(wf_auto2) _
            )).
{

  assert (Helper: forall ϕ₁ ϕ₂, well_formed ϕ₁ -> well_formed ϕ₂ -> Γ ⊢ (! ϕ₁ or ϕ₂) ---> (! ϕ₁ or (ϕ₂ and ϕ₁))).
  {
    intros ϕ₁ ϕ₂ wfϕ₁ wfϕ₂.
    toMyGoal.
    { wf_auto2. }
    mgIntro.
    mgAdd (@A_or_notA Σ Γ ϕ₁ ltac:(wf_auto2)).
    mgDestructOr 0; mgDestructOr 1.
    - (* TODO: mgExFalso *)
      mgApplyMeta (@false_implies_everything Σ Γ (! ϕ₁ or (ϕ₂ and ϕ₁)) ltac:(wf_auto2)).
      mgApply 1. mgExactn 0.
    - mgRight. mgSplitAnd. mgExactn 1. mgExactn 0.
    - mgLeft. mgExactn 0.
    - mgLeft. mgExactn 0. 
  }
  toMyGoal.
  { wf_auto2. }
  mgIntro.
  mgApplyMeta (Helper (⌈ patt_free_evar x and ϕ ⌉) (patt_free_evar y) ltac:(wf_auto2) ltac:(wf_auto2)).
  mgRight.
  mgExactn 0.
}
fromMyGoal. intros _ _.
apply defined_evar.
{ exact HΓ. }
Defined.


Lemma membership_symbol_ceil_left_aux_0 {Σ : Signature} {syntax : Syntax} Γ ϕ:
theory ⊆ Γ ->
well_formed ϕ ->
Γ ⊢ ϕ ---> (ex, ⌈ b0 and ϕ ⌉).
Proof.
intros HΓ wfϕ.
apply membership_elimination.
{ wf_auto2. }
{ assumption. }
remember (fresh_evar ϕ) as x.
replace (b0 ∈ml (ϕ ---> ex , ⌈ b0 and ϕ ⌉))
  with (evar_quantify x 0 (evar_open 0 x (b0 ∈ml (ϕ ---> ex , ⌈ b0 and ϕ ⌉)))).
2: { rewrite evar_quantify_evar_open.
     {
       pose proof (@set_evar_fresh_is_fresh _ ϕ).
       unfold evar_is_fresh_in in H.
       simpl. set_solver.
     }
     wf_auto.
     1-2: eapply well_formed_closed_ex_aux_ind; try eassumption; lia.
     reflexivity.
}

apply universal_generalization.
{ wf_auto2. }
unfold evar_open. simpl_bevar_subst. simpl.
rewrite bevar_subst_not_occur.
{ wf_auto2. }
wf_auto2.
rewrite bevar_subst_not_occur.
{ wf_auto2. }
wf_auto2.
toMyGoal.
{ wf_auto2. }
mgRewrite (@membership_imp Σ syntax Γ x ϕ (ex, ⌈ b0 and ϕ ⌉) HΓ ltac:(wf_auto2) ltac:(wf_auto2)) at 1.
mgRewrite (@membership_exists Σ syntax Γ x (⌈ b0 and ϕ ⌉) HΓ ltac:(wf_auto2)) at 1.
mgIntro.
remember (fresh_evar ϕ) as y.
mgApplyMeta (@Ex_quan Σ Γ (patt_free_evar x ∈ml ⌈ b0 and ϕ ⌉) y ltac:(wf_auto2)).
unfold instantiate. simpl_bevar_subst. simpl.
rewrite bevar_subst_not_occur.
{ wf_auto2. }

mgApplyMeta (@membership_symbol_ceil_aux_0 Σ syntax Γ y x ϕ HΓ wfϕ).
subst y. subst x.
mgExactn 0.
Defined.

Lemma ceil_and_x_ceil_phi_impl_ceil_phi {Σ : Signature} {syntax : Syntax} Γ (ϕ : Pattern) x:
theory ⊆ Γ ->
well_formed ϕ ->
Γ ⊢ ( (⌈ patt_free_evar x and ⌈ ϕ ⌉ ⌉) ---> (⌈ ϕ ⌉)).
Proof.
intros HΓ wfϕ.
eapply syllogism_intro.
{ wf_auto2. }
2: { wf_auto2. }
3: {
  apply def_def_phi_impl_def_phi; assumption.
}
{ wf_auto2. }
apply ceil_monotonic.
{ exact HΓ. }
{ wf_auto2. }
{ wf_auto2. }
toMyGoal.
{ wf_auto2. }
mgIntro. mgDestructAnd 0. mgExactn 1.
Defined.

Lemma membership_monotone {Σ : Signature} {syntax : Syntax} Γ (ϕ₁ ϕ₂ : Pattern) x:
theory ⊆ Γ ->
well_formed ϕ₁ ->
well_formed ϕ₂ ->
Γ ⊢ (ϕ₁ ---> ϕ₂) ->
Γ ⊢ (patt_free_evar x ∈ml ϕ₁) ---> (patt_free_evar x ∈ml ϕ₂).
Proof.
intros HΓ wfϕ₁ wfϕ₂ H.
unfold patt_in.
apply ceil_monotonic.
{ exact HΓ. }
{ wf_auto2. }
{ wf_auto2. }
toMyGoal.
{ wf_auto2. }
mgIntro.
mgDestructAnd 0.
mgSplitAnd.
- mgExactn 0.
- mgApplyMeta H.
  mgExactn 1.
Defined.

Lemma membership_symbol_ceil_left {Σ : Signature} {syntax : Syntax} Γ ϕ x:
theory ⊆ Γ ->
well_formed ϕ ->
Γ ⊢ (patt_free_evar x ∈ml ⌈ ϕ ⌉) ---> (ex, (patt_bound_evar 0 ∈ml ϕ)).
Proof.
intros HΓ wfϕ.
eapply syllogism_intro.
{ wf_auto2. }
2: {wf_auto2. }
2: {
  apply membership_monotone.
  { exact HΓ. }
  { wf_auto2. }
  2: {
    apply ceil_monotonic.
    { exact HΓ. }
    { wf_auto2. }
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

eapply syllogism_intro.
{ wf_auto2. }
2: {wf_auto2. }
2: {
  apply membership_monotone.
  { exact HΓ. }
  { wf_auto2. }
  2: {
    apply ceil_propagation_exists_1.
    { exact HΓ. }
    { wf_auto2. }
  }
  { wf_auto2. }
}
{ wf_auto2. }

remember (evar_fresh (elements ({[x]} ∪ (free_evars ϕ)))) as y.
eapply syllogism_intro.
{ wf_auto2. }
2: {wf_auto2. }
2: {
  apply membership_monotone.
  { exact HΓ. }
  { wf_auto2. }
  2: {
    eapply cast_proof.
    {
      rewrite -[⌈ ⌈ b0 and ϕ ⌉ ⌉](@evar_quantify_evar_open Σ y 0).
      { simpl.
        pose proof (Hfr := @set_evar_fresh_is_fresh' Σ ({[x]} ∪ (free_evars ϕ))).
        subst y. clear -Hfr. set_solver.
      }
      simpl. split_and!; auto.
      unfold well_formed, well_formed_closed in wfϕ. destruct_and!.
      eapply well_formed_closed_ex_aux_ind; try eassumption; lia.
      reflexivity.
    }
    apply ex_quan_monotone.
    { wf_auto2. }
    2: {
      unfold evar_open. simpl_bevar_subst. simpl.
      rewrite bevar_subst_not_occur.
      { wf_auto2. }
      wf_auto2.
      apply def_def_phi_impl_def_phi.
      { exact HΓ. }
      { wf_auto2. }
    }
    { wf_auto2. }
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

toMyGoal.
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
pose proof (Htmp := @membership_exists Σ syntax Γ x (evar_quantify y 0 ⌈ patt_free_evar y and ϕ ⌉)).
specialize (Htmp HΓ).
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
mgRewrite -> Htmp at 1. clear Htmp.

fromMyGoal. intros _ _.
case_match; try congruence.
rewrite evar_quantify_fresh.
{ subst y. eapply evar_is_fresh_in_richer'.
  2: { apply set_evar_fresh_is_fresh'. }
  clear. set_solver.
}
fold (patt_not b0).
fold (patt_not (patt_not b0)).
fold (patt_not ϕ).
fold (! b0 or ! ϕ).
fold (!(! b0 or ! ϕ)).
fold (b0 and ϕ).
fold (patt_defined (b0 and ϕ)).
unfold patt_in.

apply (@strip_exists_quantify_l Σ Γ y).
{ simpl.
  pose proof (Hfr := @set_evar_fresh_is_fresh' Σ ({[x]} ∪ (free_evars ϕ))).
  rewrite -Heqy in Hfr.
  clear -Hfr.
  set_solver.
}
{ simpl. split_and!; auto; wf_auto2. }

apply (@strip_exists_quantify_r Σ Γ y).
{ simpl.
  pose proof (Hfr := @set_evar_fresh_is_fresh' Σ ({[x]} ∪ (free_evars ϕ))).
  rewrite -Heqy in Hfr.
  clear -Hfr.
  set_solver.
}
{ simpl. split_and!; auto; wf_auto2. }
apply ex_quan_monotone.
{ wf_auto2. }
{ wf_auto2. }
unfold evar_open. simpl_bevar_subst. simpl.
rewrite bevar_subst_not_occur.
{ wf_auto2. }

apply ceil_and_x_ceil_phi_impl_ceil_phi.
{ exact HΓ. }
{ wf_auto2. }
Defined.


Lemma membership_symbol_ceil_right_aux_0 {Σ : Signature} {syntax : Syntax} Γ ϕ:
theory ⊆ Γ ->
well_formed ϕ ->
Γ ⊢ (ex, (⌈ b0 and  ϕ ⌉ and b0)) ---> ϕ.
Proof.
intros HΓ wfϕ.
apply prenex_forall_imp.
1,2: wf_auto2.
remember (fresh_evar (⌈ b0 and ϕ ⌉ and b0 ---> ϕ)) as x.
eapply cast_proof.
{
  rewrite -[HERE in (all, HERE)](@evar_quantify_evar_open Σ x 0).
  { subst x. apply set_evar_fresh_is_fresh. }
  unfold well_formed, well_formed_closed in wfϕ. destruct_and!. simpl.
  split_and!; auto.
  1-2: eapply well_formed_closed_ex_aux_ind; try eassumption; lia.
  reflexivity.
}
apply universal_generalization.
{ wf_auto2. }
assert (Htmp: forall (ϕ₁ ϕ₂ ϕ₃ : Pattern),
           well_formed ϕ₁ ->
           well_formed ϕ₂ ->
           well_formed ϕ₃ ->
           Γ ⊢ ((! (ϕ₁ and (ϕ₂ and !ϕ₃))) ---> ((ϕ₁ and ϕ₂) ---> ϕ₃))).
{
  intros ϕ₁ ϕ₂ ϕ₃ wfϕ₁ wfϕ₂ wfϕ₃. toMyGoal.
  { wf_auto2. }
  do 2 mgIntro. mgDestructAnd 1.
  mgApplyMeta (@not_not_elim Σ Γ ϕ₃ wfϕ₃).
  mgIntro. mgApply 0. mgClear 0.
  mgSplitAnd.
  { mgExactn 0. }
  mgSplitAnd.
  { mgExactn 1. }
  { mgExactn 2. }
}
eapply Modus_ponens.
4: apply Htmp.
all: fold bevar_subst.
1,2,4,5,6: wf_auto2.
1,2,4,5,6: apply wfc_ex_aux_bevar_subst; wf_auto2.
{ apply wfc_ex_aux_bevar_subst. wf_auto2. simpl. reflexivity. }
simpl_bevar_subst. simpl.
rewrite bevar_subst_not_occur.
{ wf_auto2. }
replace (⌈ patt_free_evar x and ϕ ⌉) with (subst_ctx AC_patt_defined (patt_free_evar x and ϕ)) by reflexivity.
replace (patt_free_evar x and ! ϕ) with (subst_ctx box (patt_free_evar x and ! ϕ)) by reflexivity.
apply Singleton_ctx. exact wfϕ.
Defined.

Lemma membership_symbol_ceil_right {Σ : Signature} {syntax : Syntax} Γ ϕ x:
theory ⊆ Γ ->
well_formed ϕ ->
Γ ⊢ ((ex, (BoundVarSugar.b0 ∈ml ϕ)) ---> (patt_free_evar x ∈ml ⌈ ϕ ⌉)).
Proof.
intros HΓ wfϕ.
remember (evar_fresh (elements ({[x]} ∪ (free_evars ϕ)))) as y.
pose proof (Htmp := @set_evar_fresh_is_fresh' Σ ({[x]} ∪ free_evars ϕ)).
rewrite -Heqy in Htmp.
assert (x <> y).
{ solve_fresh_neq. }

eapply syllogism_intro.
1,3: wf_auto2.
2: {
  apply (@strip_exists_quantify_l Σ Γ y).
  { simpl. clear -Htmp. set_solver. }
  { simpl. split_and!; try reflexivity. wf_auto2. }
  apply ex_quan_monotone.
  { wf_auto2. }
  2: {
    unfold evar_open. simpl_bevar_subst. simpl.
    rewrite bevar_subst_not_occur.
    { wf_auto2. }
    apply membership_symbol_ceil_aux_0 with (y0 := x); assumption.
  }
  { wf_auto2. }
}
{ unfold exists_quantify. simpl. repeat case_match; try congruence; wf_auto2. }

eapply syllogism_intro.
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

eapply syllogism_intro.
1,3: wf_auto2.
2: {
  apply membership_monotone.
  { exact HΓ. }
  { wf_auto2. }
  2: {
  apply (@strip_exists_quantify_l Σ Γ y).
  { simpl.
    rewrite evar_quantify_noop.
    { apply count_evar_occurrences_0.
      subst y.
      eapply evar_is_fresh_in_richer'.
      2: { apply set_evar_fresh_is_fresh'. }
      clear. set_solver.
    }
    set_solver.
  }
  { simpl. split_and!; try reflexivity. wf_auto2. }
  apply ex_quan_monotone.
  { wf_auto2. }
  2: {
    eapply syllogism_intro.
    1: wf_auto2.
    3: {
      unfold evar_open. simpl_bevar_subst. simpl.
      rewrite bevar_subst_evar_quantify_free_evar.
      { wf_auto2. }
      apply membership_symbol_ceil_aux_0 with (y0 := y); assumption.
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
          apply patt_and_comm.
          { wf_auto2. }
          { wf_auto2. }
        }
        { wf_auto2. }
      }
      { wf_auto2. }
    }
    { wf_auto2. }
  }
  { wf_auto2. }
}
{ unfold exists_quantify. simpl. repeat case_match; try congruence; wf_auto2. }
}
{ unfold exists_quantify. simpl. repeat case_match; try congruence; wf_auto2. }

eapply syllogism_intro.
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
    rewrite evar_quantify_noop.
    { apply count_evar_occurrences_0.
      subst y.
      eapply evar_is_fresh_in_richer'.
      2: { apply set_evar_fresh_is_fresh'. }
      clear. set_solver.
    }
    apply ceil_propagation_exists_2.
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
apply membership_symbol_ceil_right_aux_0; assumption.
Defined.

Lemma def_phi_impl_tot_def_phi {Σ : Signature} {syntax : Syntax} Γ ϕ :
theory ⊆ Γ ->
well_formed ϕ ->
Γ ⊢ ⌈ ϕ ⌉ ---> ⌊ ⌈ ϕ ⌉ ⌋.
Proof.
intros HΓ wfϕ.
unfold patt_total.
apply double_not_ceil_alt.
{ assumption. }
{ assumption. }
apply membership_elimination.
{ wf_auto2. }
{ assumption. }

remember (fresh_evar ϕ) as x.
eapply cast_proof.
{ 
  rewrite -[b0 ∈ml _](@evar_quantify_evar_open Σ x 0).
  {
    simpl.
    pose proof (@set_evar_fresh_is_fresh _ ϕ).
    unfold evar_is_fresh_in in H.
    simpl. set_solver.
  }
  unfold well_formed, well_formed_closed in wfϕ. destruct_and!.
  simpl; split_and!; auto.
  1-2: eapply well_formed_closed_ex_aux_ind; try eassumption; lia.
  reflexivity.
}
apply universal_generalization.
{ wf_auto2. }
unfold evar_open. simpl_bevar_subst. simpl.
rewrite bevar_subst_not_occur.
{ wf_auto2. }

toMyGoal.
{ wf_auto2. }
mgRewrite (@membership_imp Σ syntax Γ x (⌈ ! ⌈ ϕ ⌉ ⌉) (! ⌈ ϕ ⌉) HΓ ltac:(wf_auto2) ltac:(wf_auto2)) at 1.
mgIntro.
mgApplyMeta (@membership_symbol_ceil_left Σ syntax Γ (! ⌈ ϕ ⌉) x HΓ ltac:(wf_auto2)) in 0.
mgRewrite (@membership_not_iff Σ syntax Γ (⌈ ϕ ⌉) x ltac:(wf_auto2) HΓ) at 1.

remember (evar_fresh (elements ({[x]} ∪ (free_evars ϕ)))) as y.
pose proof (Hfr := @set_evar_fresh_is_fresh' _ ({[x]} ∪ (free_evars ϕ))).
eapply cast_proof_mg_hyps.
{
  rewrite <- (@evar_quantify_evar_open Σ y 0 (b0 ∈ml (! ⌈ ϕ ⌉))).
  2: { simpl. rewrite <- Heqy in Hfr. clear -Hfr. set_solver. }
  reflexivity.
  unfold well_formed, well_formed_closed in wfϕ. destruct_and!.
  simpl; split_and!; auto.
  eapply well_formed_closed_ex_aux_ind; try eassumption; lia.
}

assert (Htmp: Γ ⊢ ((evar_open 0 y (b0 ∈ml (! ⌈ ϕ ⌉))) ---> (evar_open 0 y (! (b0 ∈ml ⌈ ϕ ⌉))))).
{
  unfold evar_open. simpl_bevar_subst. simpl. apply membership_not_1.
  { wf_auto2.
    apply wfc_ex_aux_bevar_subst. wf_auto2. reflexivity.
  }
  exact HΓ.
}

mgApplyMeta (ex_quan_monotone_nowf y Htmp) in 0.
clear Htmp.


eapply cast_proof_mg_hyps.
{
  unfold exists_quantify.
  rewrite -> (@evar_quantify_evar_open Σ y 0 (! b0 ∈ml (⌈ ϕ ⌉))).
  2: { simpl. rewrite <- Heqy in Hfr. clear -Hfr. set_solver. }
  reflexivity.
  unfold well_formed, well_formed_closed in wfϕ. destruct_and!.
  simpl; split_and!; auto.
  eapply well_formed_closed_ex_aux_ind; try eassumption; lia.
}

mgApplyMeta (@not_not_intro Σ Γ (ex , (! b0 ∈ml ⌈ ϕ ⌉)) ltac:(wf_auto2)) in 0.
eapply cast_proof_mg_hyps.
{
  replace (! ! ex , (! b0 ∈ml ⌈ ϕ ⌉)) with (! all , (b0 ∈ml ⌈ ϕ ⌉)) by reflexivity.
  reflexivity.
}

assert (Htmp: Γ ⊢ (! (ex, b0 ∈ml ϕ)) ---> (! (patt_free_evar x ∈ml ⌈ ϕ ⌉))).
{
  apply ProofMode.modus_tollens.
  { wf_auto2. }
  { wf_auto2. }
  apply membership_symbol_ceil_left; assumption.
}
mgApplyMeta Htmp.
fromMyGoal. intros _ _.
apply ProofMode.modus_tollens.
{ wf_auto2. }
{ wf_auto2. }

pose proof (Hfr' := @set_evar_fresh_is_fresh Σ ϕ).
eapply cast_proof.
{
  rewrite -[THIS in (patt_exists THIS)](@evar_quantify_evar_open Σ x 0).
  { simpl. 
    unfold evar_is_fresh_in in Hfr'. rewrite -Heqx in Hfr'. clear -Hfr'.
    set_solver.
  }
  {
    unfold well_formed, well_formed_closed in wfϕ. destruct_and!.
    simpl; split_and!; auto.
    eapply well_formed_closed_ex_aux_ind; try eassumption; lia.
  }
  rewrite -[THIS in (patt_forall THIS)](@evar_quantify_evar_open Σ y 0).
  { simpl. 
    unfold evar_is_fresh_in in Hfr'. rewrite -Heqy in Hfr. clear -Hfr.
    set_solver.
  }
  {
    unfold well_formed, well_formed_closed in wfϕ. destruct_and!.
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
  pose proof (Hsub := @free_evars_bevar_subst Σ ϕ (patt_free_evar (fresh_evar ϕ)) 0).
  rewrite !simpl_free_evars.
  set_solver.
}

rewrite evar_quantify_evar_open.
{ simpl. unfold evar_is_fresh_in in Hfr'. subst x. set_solver. }
{
  unfold well_formed, well_formed_closed in wfϕ. destruct_and!.
  simpl; split_and!; auto.
  eapply well_formed_closed_ex_aux_ind; try eassumption; lia.
}
unfold evar_open. simpl_bevar_subst. simpl. rewrite bevar_subst_not_occur.
{ wf_auto2. }
apply  membership_symbol_ceil_right; assumption.
Defined.

Lemma def_tot_phi_impl_tot_phi {Σ : Signature} {syntax : Syntax} Γ ϕ :
theory ⊆ Γ ->
well_formed ϕ ->
Γ ⊢ ⌈ ⌊ ϕ ⌋ ⌉ ---> ⌊ ϕ ⌋ .
Proof.
intros HΓ wfϕ.
toMyGoal.
{ wf_auto2. }
mgIntro.
mgApplyMeta (@not_not_intro Σ Γ (⌈ ⌊ ϕ ⌋ ⌉) ltac:(wf_auto2)) in 0.
mgIntro. mgApply 0. mgClear 0.
fromMyGoal. intros _ _.
apply def_phi_impl_tot_def_phi.
{ exact HΓ. }
{ wf_auto2. }
Defined.

Lemma floor_is_predicate {Σ : Signature} {syntax : Syntax} Γ ϕ :
theory ⊆ Γ ->
well_formed ϕ ->
Γ ⊢ is_predicate_pattern (⌊ ϕ ⌋).
Proof.
intros HΓ wfϕ.
unfold is_predicate_pattern.
unfold "=ml".
toMyGoal.
{ wf_auto2. }
mgRewrite (@pf_iff_equiv_sym Σ Γ (⌊ ϕ ⌋) (⌊ ϕ ⌋ <---> Top) ltac:(wf_auto2) ltac:(wf_auto2) (@phi_iff_phi_top _ Γ (⌊ ϕ ⌋) ltac:(wf_auto2))) at 1.

mgRewrite (@pf_iff_equiv_sym Σ Γ (! ⌊ ϕ ⌋) (⌊ ϕ ⌋ <---> ⊥) ltac:(wf_auto2) ltac:(wf_auto2) (@not_phi_iff_phi_bott _ Γ (⌊ ϕ ⌋) ltac:(wf_auto2))) at 1.
fromMyGoal. intros _ _.


unfold patt_total at 1.
unfold patt_total at 2.
unfold patt_or.
apply ProofMode.modus_tollens.
{ wf_auto2. }
{ wf_auto2. }

assert (Γ ⊢ (! ! ⌊ ϕ ⌋) <---> ⌊ ϕ ⌋).
{ toMyGoal.
  { wf_auto2. }
  mgSplitAnd; mgIntro.
  - fromMyGoal. intros _ _.
    apply not_not_elim.
    { wf_auto2. }
  - mgIntro. mgApply 1. mgClear 1. mgExactn 0.
}

toMyGoal.
{ wf_auto2. }
mgRewrite H at 1.
clear H.
mgIntro.
mgApplyMeta (@def_phi_impl_tot_def_phi Σ syntax Γ (⌊ ϕ ⌋) HΓ ltac:(wf_auto2)) in 0.
fromMyGoal. intros _ _.
apply floor_monotonic.
{ exact HΓ. }
{ wf_auto2. }
{ wf_auto2. }
apply def_tot_phi_impl_tot_phi; assumption.
Defined.

Lemma def_propagate_not {Σ : Signature} {syntax : Syntax} Γ ϕ:
theory ⊆ Γ ->
well_formed ϕ ->
Γ ⊢ (! ⌈ ϕ ⌉) <---> (⌊ ! ϕ ⌋).
Proof.
intros HΓ wfϕ.
toMyGoal.
{ wf_auto2. }
mgRewrite (@not_not_iff Σ Γ ϕ wfϕ) at 1.
mgSplitAnd; mgIntro; mgExactn 0.
Defined.

Lemma def_def_phi_impl_tot_def_phi {Σ : Signature} {syntax : Syntax} Γ ϕ :
theory ⊆ Γ ->
well_formed ϕ ->
Γ ⊢ ⌈ ⌈ ϕ ⌉ ⌉ ---> ⌊ ⌈ ϕ ⌉ ⌋.
Proof.
intros HΓ wfϕ.
eapply syllogism_intro.
1,3: wf_auto2.
2: { apply def_def_phi_impl_def_phi; assumption. }
{ wf_auto2. }
apply def_phi_impl_tot_def_phi; assumption.
Defined.


Lemma ceil_is_predicate {Σ : Signature} {syntax : Syntax} Γ ϕ :
theory ⊆ Γ ->
well_formed ϕ ->
Γ ⊢ is_predicate_pattern (⌈ ϕ ⌉).
Proof.
intros HΓ wfϕ.
unfold is_predicate_pattern.
apply or_comm_meta.
{ wf_auto2. }
{ wf_auto2. }
unfold patt_or.
apply syllogism_intro with (B := ⌈ ⌈ ϕ ⌉ ⌉).
1,2,3: wf_auto2.
- toMyGoal.
  { wf_auto2. }

  mgRewrite (@not_not_iff Σ Γ (⌈ ⌈ ϕ ⌉ ⌉) ltac:(wf_auto2)) at 1.
  do 2 mgIntro. mgApply 0. mgClear 0.
  fromMyGoal. intros _ _. toMyGoal. wf_auto2.
  mgRewrite (@def_propagate_not Σ syntax Γ (⌈ ϕ ⌉) HΓ ltac:(wf_auto2)) at 1.
  mgIntro. 
  mgApplyMeta (@total_phi_impl_phi Σ syntax Γ (! ⌈ ϕ ⌉) HΓ ltac:(wf_auto2)) in 0.
  fromMyGoal. intros _ _. toMyGoal. wf_auto2.
  mgRewrite (@def_propagate_not Σ syntax Γ ϕ HΓ ltac:(wf_auto2)) at 1.
  fromMyGoal. intros _ _.
  unshelve (eapply deduction_theorem_noKT).
  4: exact HΓ.
  2,3: wf_auto2.
  { apply patt_iff_implies_equal.
    1,2: wf_auto2.
    toMyGoal.
    { wf_auto2. }
    mgSplitAnd; mgIntro.
    2: { mgApplyMeta (@false_implies_everything Σ (Γ ∪ {[! ϕ]}) (⌈ ϕ ⌉) ltac:(wf_auto2)) in 0.
         mgExactn 0.
    }
    assert (Htmp: ((Γ ∪ {[! ϕ]})) ⊢ ! ϕ).
    { apply hypothesis. wf_auto2. set_solver. }
    apply phi_impl_total_phi_meta in Htmp.
    2: { wf_auto2. }
    mgAdd Htmp.  mgApply 0. mgClear 0.
    fromMyGoal. intros _ _.
    apply Framing_right.
    { wf_auto2. }
    apply not_not_intro.
    assumption.
  }
  { simpl.
    rewrite !orbF.
    rewrite orb_false_iff. split.
    {
      simpl.
      solve_indif.
    }

    {
      simpl.
      solve_indif; auto.
    }
  }

  { simpl.
    rewrite !orbF.
    rewrite orb_false_iff. split.
    {
      simpl.
      solve_indif.
    }

    {
      simpl.
      solve_indif; auto.
    }
  }

  { simpl.
    rewrite !orbF.
    rewrite orb_false_iff. split.
    {
      solve_indif.
    }

    {
      simpl.
      solve_indif; auto.
    }
  }
  - eapply syllogism_intro with (B := ⌊ ⌈ ϕ ⌉ ⌋).
    1,2,3: wf_auto2.
    { apply def_def_phi_impl_tot_def_phi; assumption. }
    unshelve (eapply deduction_theorem_noKT).
    2,3: wf_auto2.
    2: exact HΓ.
    {
      apply phi_impl_total_phi_meta.
      { wf_auto2. }
      apply pf_iff_split.
      1,2: wf_auto2.
      + toMyGoal. wf_auto2. mgIntro. mgClear 0. fromMyGoal. intros _ _. apply top_holds.
      + toMyGoal. wf_auto2. mgIntro. mgClear 0. fromMyGoal. intros _ _.
        apply hypothesis. wf_auto2. set_solver.
    }

  { simpl.
    rewrite !orbF.
    rewrite orb_false_iff. split.
    {
      solve_indif. reflexivity.
    }
    {
      solve_indif.
    }
  }

  { simpl.
    rewrite !orbF.
    rewrite orb_false_iff. split.
    {
      solve_indif. reflexivity.
    }
    {
      solve_indif.
    }
  }

  { simpl.
    rewrite !orbF.
    rewrite orb_false_iff. split.
    {
      solve_indif. reflexivity.
    }
    {
      solve_indif.
    }
  }

Defined.

Lemma disj_equals_greater_1 {Σ : Signature} {syntax : Syntax} Γ ϕ₁ ϕ₂:
theory ⊆ Γ ->
well_formed ϕ₁ ->
well_formed ϕ₂ ->
Γ ⊢ (ϕ₁ ⊆ml ϕ₂) ---> ((ϕ₁ or ϕ₂) =ml ϕ₂).
Proof.
intros HΓ wfϕ₁ wfϕ₂.
unshelve (eapply deduction_theorem_noKT).
2,3: wf_auto2.
2: exact HΓ.
{
  apply phi_impl_total_phi_meta.
  { wf_auto2. }
  apply pf_iff_split.
  1,2: wf_auto2.
  - toMyGoal. wf_auto2. mgIntro. mgDestructOr 0.
    + assert (Γ ∪ {[ϕ₁ ---> ϕ₂]} ⊢ ϕ₁ ---> ϕ₂).
      { apply hypothesis. wf_auto2. set_solver. }
      mgApplyMeta H. mgExactn 0.
    + mgExactn 0.
  - apply disj_right_intro; assumption.
}
{
  simpl. rewrite !orbF.
  solve_indif. reflexivity.
}
{
  simpl. rewrite !orbF.
  solve_indif. reflexivity.
}
{
  simpl. rewrite !orbF.
  solve_indif. reflexivity.
}
Defined.


Lemma disj_equals_greater_2_meta {Σ : Signature} {syntax : Syntax} Γ ϕ₁ ϕ₂:
theory ⊆ Γ ->
well_formed ϕ₁ ->
well_formed ϕ₂ ->
Γ ⊢ (ϕ₁ or ϕ₂) =ml ϕ₂ ->
Γ ⊢ ϕ₁ ⊆ml ϕ₂.
Proof.
intros HΓ wfϕ₁ wfϕ₂ Heq.
toMyGoal.
{ wf_auto2. }
unshelve (epose proof (Htmp := patt_equal_implies_iff HΓ _ _ Heq)).
{ wf_auto2. }
{ wf_auto2. }
apply pf_iff_equiv_sym in Htmp.
3: { wf_auto2. }
2: { wf_auto2. }
mgRewrite Htmp at 1.
fromMyGoal. intros _ _.
unfold "⊆ml".
apply phi_impl_total_phi_meta.
{ wf_auto2. }
toMyGoal.
{ wf_auto2. }
mgIntro. mgLeft. mgExactn 0.
Defined.

Lemma disj_equals_greater_2 {Σ : Signature} {syntax : Syntax} Γ ϕ₁ ϕ₂:
theory ⊆ Γ ->
well_formed ϕ₁ ->
well_formed ϕ₂ ->
mu_free ϕ₁ -> (* TODO get rid of it *)
Γ ⊢ ((ϕ₁ or ϕ₂) =ml ϕ₂) ---> (ϕ₁ ⊆ml ϕ₂).
Proof.
intros HΓ wfϕ₁ wfϕ₂ mfϕ₁.
toMyGoal.
{ wf_auto2. }
mgIntro.

unshelve(mgApplyMeta (patt_eq_sym _ _ _) in 0).
{ assumption. }
{ wf_auto2. }
{ wf_auto2. }
mgRewriteBy 0 at 1.
{ assumption. }
{ simpl. rewrite mfϕ₁. reflexivity. }
mgClear 0.

fromMyGoal. intros _ _.
unfold "⊆ml".
apply phi_impl_total_phi_meta.
{ wf_auto2. }
toMyGoal.
{ wf_auto2. }
mgIntro. mgLeft. mgExactn 0.
Defined.
