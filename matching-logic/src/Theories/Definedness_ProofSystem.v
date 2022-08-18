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

From MatchingLogic Require Import Logic
                                  DerivedOperators_Syntax
                                  ProofMode.
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

Definition BasicReasoningWithDefFP := ( (ExGen := ∅, SVSubst := ∅, KT := false, FP := defFP)). 

Lemma phi_impl_total_phi_meta Γ ϕ i:
  well_formed ϕ ->
  ProofInfoLe BasicReasoningWithDefFP i -> 
  Γ ⊢i ϕ using i ->
  Γ ⊢i ⌊ ϕ ⌋ using i.
Proof.
  intros wfϕ pile Hϕ.
  pose proof (ANNA := A_implies_not_not_A_ctx Γ (ϕ) AC_patt_defined).
  apply ANNA.
  { simpl.
    eapply pile_trans;[|apply pile].
    apply pile_evs_svs_kt; try set_solver.
  }
  { apply wfϕ. }
  exact Hϕ.
Defined.

Lemma patt_iff_implies_equal :
  forall (φ1 φ2 : Pattern) Γ i,
    well_formed φ1 ->
    well_formed φ2 ->
    ProofInfoLe BasicReasoningWithDefFP i ->
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
  using BasicReasoningWithDefFP.
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
  apply hypothesis; auto. unfold theory,theory_of_NamedAxioms in HΓ. simpl in HΓ.
  eapply elem_of_weaken.
  2: { apply HΓ. }
  unfold axiom.
  apply elem_of_PropSet.
  exists AxDefinedness.
  reflexivity.
Defined.

Definition BasicReasoningWithDefinedness := (ExGen := {[ev_x]}, SVSubst := ∅, KT := false, FP := defFP).

Lemma defined_evar Γ x:
  theory ⊆ Γ ->
  Γ ⊢i ⌈ patt_free_evar x ⌉
  using  (ExGen := {[ev_x]} ∪ {[x]}, SVSubst := ∅, KT := false, FP := defFP).
Proof.
  intros HΓ.
  assert(S1: Γ ⊢i patt_defined p_x using BasicReasoningWithDefinedness).
  {
    useBasicReasoning.
    apply use_defined_axiom.
    apply HΓ.
  }

  pose proof (S1' := S1).
  apply universal_generalization with (x := ev_x) in S1'.
  3: { wf_auto2. }
  2: { eapply pile_trans;[|apply pile_refl]. try_solve_pile. }
  replace ((patt_defined p_x)^{{evar: ev_x ↦ 0}})
    with (⌈ patt_free_evar x ⌉^{{evar: x ↦ 0}}) in S1'.
  2: { simpl. repeat case_match; auto; contradiction. }
  eapply MP.
  2: { eapply useGenericReasoning with (evs := {[x]}) (svs := ∅) (kt := false)(fp := ∅).
    apply pile_evs_svs_kt.
    { clear. unfold ev_x.
      rewrite elem_of_subseteq.
      intros x0 Hx0. rewrite elem_of_singleton in Hx0. subst x0.
      set_solver.
    }
    { apply reflexivity. }
    { reflexivity. }
    { clear. set_solver. }
    apply forall_variable_substitution with (x := x).
    wf_auto2.
  }
  eapply useGenericReasoning.
  2: { apply S1'. }
  apply pile_evs_svs_kt.
  { set_solver. }
  { apply reflexivity. }
  { reflexivity. }
  { apply reflexivity. }
Defined.
  
Lemma in_context_impl_defined Γ AC ϕ:
  theory ⊆ Γ ->
  well_formed ϕ ->
  Γ ⊢i (subst_ctx AC ϕ) ---> ⌈ ϕ ⌉
  using  (ExGen := {[ev_x]} ∪ {[(evar_fresh (elements (free_evars ϕ ∪ AC_free_evars AC )))]}, SVSubst := ∅, KT := false, FP := defFP ∪ frames_of_AC AC).
Proof.
  intros HΓ Hwfϕ.
  assert(S1: Γ ⊢i patt_defined p_x using BasicReasoning).
  {
    apply use_defined_axiom.
    apply HΓ.
  }

  remember (evar_fresh (elements (free_evars ϕ ∪ AC_free_evars AC ))) as x'.

  pose proof (S1' := S1).
  apply useBasicReasoning with (i := (ExGen := {[ev_x; x']}, SVSubst := ∅, KT := false, FP := defFP ∪ frames_of_AC AC)) in S1'.
  apply universal_generalization with (x := ev_x) in S1'.
  3: { wf_auto2. }
  2: {
    apply pile_evs_svs_kt.
    { set_solver. }
    { apply reflexivity. }
    { reflexivity. }
    { clear. set_solver. }
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
  
  remember ( (ExGen := {[ev_x; x']}, SVSubst := ∅, KT := false, FP := defFP ∪ frames_of_AC AC)) as i.
  assert (S1'' : Γ ⊢i ⌈ patt_free_evar x' ⌉ using i).
  {
    (* For some reason, Coq cannot infer the implicit argument 'syntax' automatically *)
    replace ((patt_defined p_x)^{{evar: ev_x ↦ 0}})
      with (⌈ patt_free_evar x' ⌉^{{evar: x' ↦ 0}}) in S1'.
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
    { clear. set_solver. }
  }
  
  assert(S2: Γ ⊢i ⌈ patt_free_evar x' ⌉ or ⌈ ϕ ⌉ using i).
  {
    toMLGoal.
    { wf_auto2. }
    mlLeft.
    fromMLGoal.
    apply S1''.
  }

  assert(S3: Γ ⊢i ⌈ patt_free_evar x' or ϕ ⌉ using i).
  {
    pose proof (Htmp := (prf_prop_or_iff Γ AC_patt_defined) (patt_free_evar x') ϕ ltac:(auto) ltac:(auto)).
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

  assert(S4: Γ ⊢i ⌈ ((patt_free_evar x') and (! ϕ)) or ϕ ⌉ using i).
  {
    assert(Htmp1: Γ ⊢i (patt_free_evar x' or ϕ) ---> (patt_free_evar x' and ! ϕ or ϕ) using i).
    {
      toMLGoal.
      { wf_auto2. }
      mlIntro.
      mlAdd (useBasicReasoning i (A_or_notA Γ ϕ Hwfϕ)).
      mlDestructOr "1".
      - mlRight. mlExactn 0.
      - mlLeft. mlIntro.
        mlDestructOr "0".
        + mlDestructOr "1".
          * mlApply "0". mlExactn 1.
          * mlApply "4". mlExactn 0.
        + mlApply "3".
          mlExactn 1.
    }

    assert(Htmp2: Γ ⊢i (⌈ patt_free_evar x' or ϕ ⌉) ---> (⌈ patt_free_evar x' and ! ϕ or ϕ ⌉) using i).
    {
      unshelve (eapply Framing_right).
      { wf_auto2. }
      {
        subst i.
        apply pile_evs_svs_kt.
        { set_solver. }
        { apply reflexivity. }
        { reflexivity. }
        { unfold defFP. clear. set_solver. }
      }
      apply Htmp1.
    }

    eapply MP.
    2: apply Htmp2.
    1: apply S3.
  }

  assert(S5: Γ ⊢i ⌈ (patt_free_evar x' and (! ϕ)) ⌉ or ⌈ ϕ ⌉ using i).
  {
    pose proof (Htmp := (prf_prop_or_iff Γ AC_patt_defined) (patt_free_evar x' and ! ϕ) ϕ ltac:(auto) ltac:(auto)).
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

  assert(S6: Γ ⊢i subst_ctx AC (patt_free_evar x' and ϕ) ---> ! ⌈ patt_free_evar x' and ! ϕ ⌉ using i).
  {
    pose proof (Htmp := Singleton_ctx Γ AC AC_patt_defined ϕ x').
    simpl in Htmp.
    unfold patt_and in Htmp at 1.
    apply not_not_elim_meta in Htmp.
    3: { wf_auto2. }
    2: { wf_auto2. }
    replace (patt_sym (Definedness_Syntax.inj definedness) $ (patt_free_evar x' and ! ϕ))%ml
      with (patt_defined (patt_free_evar x' and ! ϕ)) in Htmp by reflexivity.
    
    toMLGoal.
    { wf_auto2. }
    mlIntro.
    remember (ExGen := {[ev_x; x']}, SVSubst := ∅, KT := false, FP := defFP ∪ frames_of_AC AC) as gpi.
    rewrite Heqi.
    mlAdd (useBasicReasoning gpi Htmp).
    mlApply "1". mlIntro. mlApply "2".
    mlExactn 1.
  }

  pose proof (S7 := S5). unfold patt_or in S7.

  assert(S8: Γ ⊢i subst_ctx AC (patt_free_evar x' and ϕ) ---> ⌈ ϕ ⌉ using i).
  {
    eapply syllogism_meta.
    5: apply S7.
    4: apply S6.
    1-3: wf_auto2.
  }
  assert (S9: Γ ⊢i all, (subst_ctx AC (patt_bound_evar 0 and ϕ) ---> ⌈ ϕ ⌉) using i).
  {
    eapply universal_generalization with (x := x') in S8.
    3: { wf_auto2. }
    2: { subst i. apply pile_evs_svs_kt.
      { set_solver. }
      { apply reflexivity. }
      { reflexivity. }
      { clear. set_solver. }
    }
    simpl in S8.

    rewrite evar_quantify_subst_ctx in S8;[assumption|].

    simpl in S8.
    case_match; try contradiction.
    rewrite evar_quantify_fresh in S8; [assumption|].
    apply S8.
  }

  assert(S10: Γ ⊢i (ex, subst_ctx AC (b0 and ϕ)) ---> ⌈ ϕ ⌉ using i).
  {
    unfold patt_forall in S9.
    unfold patt_not in S9 at 1.

    assert (Heq: (subst_ctx AC (patt_free_evar x' and ϕ))^{{evar: x' ↦ 0}} = subst_ctx AC (b0 and ϕ)).
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
      { clear. set_solver. }
    }
    assumption.
  }

  assert (S11: Γ ⊢i ϕ ---> ((ex, patt_bound_evar 0) and ϕ) using i).
  {
    toMLGoal.
    { wf_auto2. }
    mlIntro.
    mlAdd (useBasicReasoning i (conj_intro Γ (ex, b0) ϕ ltac:(auto) ltac:(auto))).

    mlAssert ((ϕ ---> (ex , b0) and ϕ)).
    { wf_auto2. }
    {  mlApply "1".
        subst i.
       (* TODO mlAdd should do the cast automatically *)
       mlAdd (useBasicReasoning (ExGen := {[ev_x; x']}, SVSubst := ∅, KT := false, FP := defFP ∪ frames_of_AC AC) (Existence Γ)).
       mlExactn 0.
    }
    mlApply "2". mlExactn 1.
  }

  assert (well_formed (ex , (b0 and ϕ))).
  {
    unfold well_formed,well_formed_closed in *.
    destruct_and!.
    simpl; split_and!; auto.
    eapply well_formed_closed_ex_aux_ind. 2: eassumption. lia.
  }

  assert (S12: Γ ⊢i ϕ ---> ex, (b0 and ϕ) using i).
  {

    assert(well_formed (ex , ((patt_free_evar x')^{{evar: x' ↦ 0}} and ϕ))).
    {
      unfold well_formed,well_formed_closed in *. simpl in *.
      destruct_and!. split_and!; auto.
      all: repeat case_match; auto.
    }

    assert(Htmp: Γ ⊢i ((ex, b0) and ϕ ---> (ex, (b0 and ϕ))) using i).
    {
      toMLGoal.
      { wf_auto2. }
      mlIntro.
      mlDestructAnd "0".
      fromMLGoal.
      replace b0 with ((patt_free_evar x')^{{evar: x' ↦ 0}}).
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
        { clear. set_solver. }
      }
      toMLGoal.
      { wf_auto2. }
      do 2 mlIntro.
      mlAssert ((patt_free_evar x' and ϕ)) using first 2.
      { wf_auto2. }
      { unfold patt_and. unfold patt_not at 1. mlIntro.
        mlDestructOr "2".
        - mlApply "3". mlExactn 0.
        - mlApply "4". mlExactn 1.
      }
      mlClear "1". mlClear "0".
      fromMLGoal.
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

  assert(S13: Γ ⊢i (subst_ctx AC ϕ) ---> (subst_ctx AC (ex, (b0 and ϕ))) using i).
  {
    apply Framing.
    {
      subst i. apply pile_evs_svs_kt.
      { set_solver. }
      { set_solver. }
      { reflexivity. }
      { clear. set_solver. }
    }
    apply S12.
  }

  assert(S14: Γ ⊢i (subst_ctx AC (ex, (b0 and ϕ))) ---> (⌈ ϕ ⌉) using i).
  {
    pose proof (Htmp := prf_prop_ex_iff Γ AC (b0 and ϕ) x').
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
        { clear. set_solver. }
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
  Γ ⊢i ϕ ---> ⌈ ϕ ⌉
  using 
                     (ExGen := {[ev_x;
                               evar_fresh
                                 (elements (free_evars ϕ) )]},
                      SVSubst := ∅, KT := false, FP := defFP).
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
    {
      clear. set_solver.
    }
  }
Defined.

Lemma total_phi_impl_phi Γ ϕ:
  theory ⊆ Γ ->
  well_formed ϕ ->
  Γ ⊢i ⌊ ϕ ⌋ ---> ϕ
  using 
  (ExGen := {[ev_x;
            evar_fresh
              (elements (free_evars ϕ) )]},
   SVSubst := ∅, KT := false, FP := defFP).
Proof.
  intros HΓ wfϕ.
  unfold patt_total.
  pose proof (Htmp := phi_impl_defined_phi Γ (! ϕ) HΓ ltac:(wf_auto2)).
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
  ProofInfoLe (
  (ExGen := {[ev_x;
            evar_fresh
              (elements (free_evars ϕ) )]},
   SVSubst := ∅, KT := false, FP := defFP)) i ->
  Γ ⊢i ⌊ ϕ ⌋ using i ->
  Γ ⊢i ϕ using i.
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
    { apply reflexivity. }
  }
  1: exact HΓ.
  exact wfϕ.
Defined.

Definition dt_exgen_from_fp (ψ : Pattern) (gpi : ProofInfo) : coEVarSet :=
  match pi_framing_patterns gpi with
  | CoFinGset _ => ⊤
  | FinGSet fp => gset_to_coGset (list_to_set (map (fun (psi : wfPattern) => evar_fresh (elements (free_evars ψ ∪ free_evars (proj1_sig psi)))) (elements fp)))
  end.

  Theorem deduction_theorem_noKT Γ ϕ ψ
    (gpi : ProofInfo)
    (pf : Γ ∪ {[ ψ ]} ⊢i ϕ using  gpi) :
    well_formed ϕ ->
    well_formed ψ ->
    theory ⊆ Γ ->
    pi_generalized_evars gpi ## (gset_to_coGset (free_evars ψ)) ->
    pi_substituted_svars gpi ## (gset_to_coGset (free_svars ψ)) ->
    pi_uses_kt gpi = false ->
    Γ ⊢i ⌊ ψ ⌋ ---> ϕ
    using 
    (ExGen :=
      (
        {[ev_x; evar_fresh (elements (free_evars ψ))]}
        ∪ pi_generalized_evars gpi
        ∪ gset_to_coGset (free_evars ψ)
        ∪ (dt_exgen_from_fp ψ gpi)
      ),
     SVSubst := (pi_substituted_svars gpi ∪ (gset_to_coGset (free_svars ψ))),
     KT := false,
     FP := ⊤ (* TODO relax *)
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
          { clear. set_solver. }
        }

      + assert (axiom0 ∈ Γ).
        { clear -e n. set_solver. }
        toMLGoal.
        { wf_auto2. }
        mlIntro. mlClear "0". fromMLGoal.
        eapply useGenericReasoning.
        2: apply (hypothesis Γ axiom0 i H).
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
        { clear. set_solver. }
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

      destruct Hpf as [Hpf2 Hpf3 Hpf4].
      simpl in Hpf2, Hpf3, Hpf4.
      feed specialize IHpf1.
      {
        constructor; simpl.
        { set_solver. }
        { set_solver. }
        { unfold implb in *. repeat case_match; try reflexivity; simpl in *; try assumption. inversion Heqb. }
        { clear -pwi_pf_fp. set_solver. }
      }
      { assumption. }
      feed specialize IHpf2.
      {
        constructor; simpl.
        { set_solver. }
        { set_solver. }
        { unfold implb in *. repeat case_match; try reflexivity; simpl in *; try assumption. inversion Heqb.
          rewrite orb_comm in H2. simpl in H2. inversion H2.     
        }
        {
          clear -pwi_pf_fp. set_solver.
        }
      }
      { wf_auto2. }
      
      (*
      (* simplify the constraint *)
      unfold dt_exgen_from_fp. simpl.
      rewrite map_app.
      rewrite list_to_set_app_L.
      simpl.
      *)

      (*
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
      *)

      toMLGoal.
      { wf_auto2. }
      mlIntro.
      mlAdd IHpf2.
      mlAssert ((phi1 ---> phi2)).
      { wf_auto2. }
      { mlApply "1". mlExactn 1. }
      mlApply "2".
      mlAdd IHpf1.
      mlApply "3".
      mlExactn 2.
    - (* Existential Quantifier *)
      toMLGoal.
      { wf_auto2. }
      mlIntro. mlClear "0". fromMLGoal.
      useBasicReasoning.
      apply Ex_quan. wf_auto2.
    - (* Existential Generalization *)
      destruct Hpf as [Hpf2 Hpf3 Hpf4].
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
        { clear -pwi_pf_fp. set_solver. }
      }
      { wf_auto2. }

      apply reorder_meta in IHpf.
      2-4: wf_auto2.
      apply Ex_gen with (x := x) in IHpf.
      3: { simpl. set_solver. }
      2: { apply pile_evs_svs_kt.
        { set_solver. }
        { set_solver. }
        { reflexivity. }
        { clear. set_solver. }
      }
      apply reorder_meta in IHpf.
      2-4: wf_auto2.
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
      destruct Hpf as [Hpf2 Hpf3 Hpf4].
      simpl in Hpf2,Hpf3,Hpf4.
      feed specialize IHpf.
      {
        constructor; simpl.
        { set_solver. }
        { set_solver. }
        { apply Hpf4. }
        { clear -pwi_pf_fp. set_solver. }
      }
      { wf_auto2. }

      remember_constraint as i'.

      (*
      apply useGenericReasoning with (i0 := i') in IHpf.
      2: {
        subst i'.
        apply pile_evs_svs_kt.
        { clear. set_solver. }
        { apply reflexivity. }
        { reflexivity. }
      }
      *)
      assert (S2: Γ ⊢i phi1 ---> (phi2 or ⌈ ! ψ ⌉) using i').
      { toMLGoal.
        { wf_auto2. }
        mlAdd IHpf. mlIntro.
        mlAdd (useBasicReasoning i' (A_or_notA Γ (⌈ ! ψ ⌉) ltac:(wf_auto2))).
        mlDestructOr "0".
        - mlRight. mlExact "3".
        - mlLeft.
          mlApply "4". mlExact "1".
      }

      assert (S3: Γ ⊢i (⌈ ! ψ ⌉ $ psi) ---> ⌈ ! ψ ⌉ using i').
      {
        replace (⌈ ! ψ ⌉ $ psi)
          with (subst_ctx (ctx_app_l AC_patt_defined psi ltac:(assumption)) (! ψ))
          by reflexivity.
        subst i'.
        gapply in_context_impl_defined; auto.
        (*eapply useGenericReasoning. *)
        (*2: apply in_context_impl_defined; auto.*)
        apply pile_evs_svs_kt.
        {
          replace (free_evars (! ψ)) with (free_evars (ψ)).
          2: {
            simpl. set_solver.
          }
          simpl.
          replace (free_evars psi ∪ (∅ ∪ ∅)) with (free_evars psi) by (clear; set_solver).
          clear -pwi_pf_fp.
          unfold dt_exgen_from_fp.
          case_match.
          2: {
            set_solver.
          }
          set_solver.
        }
        { clear. set_solver. }
        { reflexivity. }
        { clear. set_solver. }
      }

      assert (S4: Γ ⊢i (phi1 $ psi) ---> ((phi2 or ⌈ ! ψ ⌉) $ psi) using i').
      { 
        unshelve (eapply Framing_left).
        { wf_auto2. } 2: exact S2.
        subst i'. clear. try_solve_pile.
      }

      assert (S5: Γ ⊢i (phi1 $ psi) ---> ((phi2 $ psi) or (⌈ ! ψ ⌉ $ psi)) using i').
      {
        pose proof (Htmp := prf_prop_or_iff Γ (ctx_app_l box psi ltac:(assumption)) phi2 (⌈! ψ ⌉)).
        feed specialize Htmp.
        { wf_auto2. }
        { wf_auto2. }
        simpl in Htmp.
        apply pf_iff_proj1 in Htmp.
        3: wf_auto2.
        2: wf_auto2.
        subst i'.
        eapply syllogism_meta.
        5: {
          gapply Htmp.
          clear. try_solve_pile.
        }
        4: assumption.
        all: wf_auto2.
      }

      assert (S6: Γ ⊢i ((phi2 $ psi) or (⌈ ! ψ ⌉ $ psi)) ---> ((phi2 $ psi) or (⌈ ! ψ ⌉)) using i').
      {
        toMLGoal.
        { wf_auto2. }
        mlIntro. mlAdd S3.
        (* TODO we need a tactic for adding  something with stronger constraint. *)
        mlAdd (useBasicReasoning i' (A_or_notA Γ (phi2 $ psi) ltac:(auto))).
        mlDestructOr "2".
        - mlLeft. mlExact "3".
        - mlRight. mlApply "1". mlApply "0". mlExactn 0.
      }

      assert (S7: Γ ⊢i (phi1 $ psi) ---> ((phi2 $ psi)  or ⌈ ! ψ ⌉) using i').
      {
        toMLGoal.
        { wf_auto2. }
        mlAdd S5. mlAdd S6. mlIntro.
        mlAssert (((phi2 $ psi) or (⌈ ! ψ ⌉ $ psi))).
        { wf_auto2. }
        { mlApply "0". mlExactn 2. }
        mlDestructOr "3".
        - mlLeft. mlExactn 3.
        - mlApply "1". mlRight. mlExactn 3.
      }

      toMLGoal.
      { wf_auto2. }
      do 2 mlIntro. mlAdd S7.
      mlAssert ((phi2 $ psi or ⌈ ! ψ ⌉)).
      { wf_auto2. }
      { mlApply "2". mlExactn 2. }
      mlDestructOr "3".
      + mlExactn 3.
      + mlAssert ((phi2 $ psi or ⌈ ! ψ ⌉)).
        { wf_auto2. }
        { mlApply "2". mlExactn 2. }
        mlAdd (useBasicReasoning i' (A_or_notA Γ (phi2 $ psi) ltac:(auto))).
        mlDestructOr "4".
        * mlExactn 0.
        * mlAdd (useBasicReasoning i' (bot_elim Γ (phi2 $ psi) ltac:(auto))).
          mlApply "4".
          mlApply "0".
          mlExactn 5.
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

      destruct Hpf as [Hpf2 Hpf3 Hpf4].
      simpl in Hpf2,Hpf3,Hpf4.
      feed specialize IHpf.
      {
        constructor; simpl.
        { set_solver. }
        { set_solver. }
        { apply Hpf4. }
        { clear -pwi_pf_fp. set_solver. }
      }
      { wf_auto2. }


      remember_constraint as i'.

      (*
      apply useGenericReasoning with (i := i') in IHpf.
      2: {
        subst i'.
        apply pile_evs_svs_kt.
        { clear. set_solver. }
        { apply reflexivity. }
        { reflexivity. }
      }
      *)
      assert (S2: Γ ⊢i phi1 ---> (phi2 or ⌈ ! ψ ⌉) using i').
      { toMLGoal.
        { wf_auto2. }
        mlAdd IHpf. mlIntro.
        mlAdd (useBasicReasoning i' (A_or_notA Γ (⌈ ! ψ ⌉) ltac:(wf_auto2))).
        mlDestructOr "2".
        - mlRight. mlExactn 0.
        - mlLeft.
          mlAssert((phi1 ---> phi2)).
          { wf_auto2. }
          { mlApply "0". mlExactn 0. }
          mlApply "2". mlExactn 2.
      }

      assert (S3: Γ ⊢i (psi $ ⌈ ! ψ ⌉) ---> ⌈ ! ψ ⌉ using i').
      {
        replace (psi $ ⌈ ! ψ ⌉)
          with (subst_ctx (ctx_app_r psi AC_patt_defined ltac:(assumption)) (! ψ))
          by reflexivity.
          subst i'.
          gapply in_context_impl_defined; auto.

          apply pile_evs_svs_kt.
          {
            replace (free_evars (! ψ)) with (free_evars (ψ)).
            2: {
              simpl. set_solver.
            }
            simpl.
            replace (free_evars psi ∪ (∅ ∪ ∅)) with (free_evars psi) by set_solver.

            clear -pwi_pf_fp.
            unfold dt_exgen_from_fp.
            case_match; set_solver.
          }
          { clear. set_solver. }
          { reflexivity. }
          { clear. set_solver. }
      }

      assert (S4: Γ ⊢i (psi $ phi1) ---> (psi $ (phi2 or ⌈ ! ψ ⌉)) using i').
      { 
        (* TODO: have a variant of apply which automatically solves all wf constraints.
           Like: unshelve (eapply H); try_wfauto
        *)
        unshelve (eapply Framing_right).
        { wf_auto2. }
        2: exact S2.
        subst i'. try_solve_pile.
      }

      assert (S5: Γ ⊢i (psi $ phi1) ---> ((psi $ phi2) or (psi $ ⌈ ! ψ ⌉)) using i').
      {
        pose proof (Htmp := prf_prop_or_iff Γ (ctx_app_r psi box ltac:(assumption)) phi2 (⌈! ψ ⌉)).
        feed specialize Htmp.
        { wf_auto2. }
        { wf_auto2. }
        simpl in Htmp.
        apply pf_iff_proj1 in Htmp.
        2,3: wf_auto2.
        subst i'.
        eapply syllogism_meta.
        5: gapply Htmp; try_solve_pile.
        4: assumption.
        all: wf_auto2.
      }

      assert (S6: Γ ⊢i ((psi $ phi2) or (psi $ ⌈ ! ψ ⌉)) ---> ((psi $ phi2) or (⌈ ! ψ ⌉)) using i').
      {
        toMLGoal.
        { wf_auto2. }
        mlIntro. mlAdd S3.
        mlAdd (useBasicReasoning i' (A_or_notA Γ (psi $ phi2) ltac:(auto))).
        mlDestructOr "2".
        - mlLeft. mlExactn 0.
        - mlRight. mlApply "1". mlApply "0". mlExactn 0.
      }

      assert (S7: Γ ⊢i (psi $ phi1) ---> ((psi $ phi2)  or ⌈ ! ψ ⌉) using i').
      {
        toMLGoal.
        { wf_auto2. }
        mlAdd S5. mlAdd S6. mlIntro.
        mlAssert (((psi $ phi2) or (psi $ ⌈ ! ψ ⌉))).
        { wf_auto2. }
        { mlApply "0". mlExactn 2. }
        mlDestructOr "3".
        - mlLeft. mlExactn 3.
        - mlApply "1". mlRight. mlExactn 3.
      }

      toMLGoal.
      { wf_auto2. }
      do 2 mlIntro. mlAdd S7.
      mlAssert ((psi $ phi2 or ⌈ ! ψ ⌉)).
      { wf_auto2. }
      { mlApply "2". mlExactn 2. }
      mlDestructOr "3".
      + mlExactn 3.
      + mlAssert ((psi $ phi2 or ⌈ ! ψ ⌉)).
        { wf_auto2. }
        { mlApply "2". mlExactn 2. }
        mlAdd (useBasicReasoning i' (A_or_notA Γ (psi $ phi2) ltac:(auto))).
        mlDestructOr "4".
        * mlExactn 0.
        * mlAdd (useBasicReasoning i' (bot_elim Γ (psi $ phi2) ltac:(auto))).
          mlApply "4".
          mlApply "0".
          mlExactn 5.
    - (* Set variable substitution *)
      simpl in HnoExGen. simpl in HnoSvarSubst. simpl in IHpf.
      destruct Hpf as [Hpf2 Hpf3 Hpf4].
      simpl in Hpf2, Hpf3, Hpf4.
      feed specialize IHpf.
      {
        constructor; simpl.
        { exact Hpf2. }
        { clear -Hpf3. set_solver. }
        { exact Hpf4. }
        { clear -pwi_pf_fp. set_solver. }
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
             clear -HnoSvarSubst Hpf3. unfold svar_is_fresh_in. set_solver.
           }
           reflexivity.
      }
      apply Svar_subst.
      3: {
        apply IHpf.
      }
      {
        subst i'.
        apply pile_evs_svs_kt.
        {
          clear. set_solver.
        }
        {
          clear -Hpf3. set_solver.
        }
        {
           reflexivity.
        }
        { clear. set_solver. }
      }
      { wf_auto2. }

    - (* Prefixpoint *)
      toMLGoal.
      { wf_auto2. }
      mlIntro. mlClear "0". fromMLGoal.
      apply useBasicReasoning.
      apply Pre_fixp. wf_auto2.
    - (* Knaster-Tarski *)
      simpl in HnoKT.
      destruct Hpf as [Hpf2 Hpf3 Hpf4].
      simpl in Hpf2, Hpf3, Hpf4.
      clear -Hpf4 HnoKT.
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

  Lemma membership_introduction Γ ϕ i:
    ProofInfoLe (
    (ExGen := {[ev_x; fresh_evar ϕ]},
     SVSubst := ∅,
     KT := false,
     FP := defFP
    )) i ->
    well_formed ϕ ->
    theory ⊆ Γ ->
    Γ ⊢i ϕ using i ->
    Γ ⊢i all, ((patt_bound_evar 0) ∈ml ϕ)
    using i.
  Proof.
    intros pile wfϕ HΓ Hϕ.

    remember (fresh_evar ϕ) as x.

    replace ϕ with (ϕ^{{evar: x ↦ 0}}).
    2: {
      rewrite evar_quantify_fresh.
      subst; auto. reflexivity.
    }
    
    assert (S2: Γ ⊢i (ϕ ---> (patt_free_evar x ---> ϕ)) using i).
    {
      useBasicReasoning.
      apply P1.
      { wf_auto2. }
      { wf_auto2. }
    }

    assert(S3: Γ ⊢i patt_free_evar x ---> ϕ using i).
    {
      eapply MP. 2: apply S2. apply Hϕ.
    }

    assert(S4: Γ ⊢i patt_free_evar x ---> patt_free_evar x using i).
    {
      useBasicReasoning.
      apply A_impl_A.
      wf_auto2.
    }

    assert(S5: Γ ⊢i patt_free_evar x ---> (patt_free_evar x and ϕ) using i).
    {
      toMLGoal.
      { wf_auto2. }
      mlIntro. unfold patt_and. mlIntro.
      mlAssert ((! ϕ)).
      { wf_auto2. }
      { mlApply "1". mlIntro. mlApply "2". mlExactn 0.  }
      mlApply "2".
      mlAdd Hϕ. mlExactn 0.
    }

    assert(S6: Γ ⊢i ⌈ patt_free_evar x ⌉ ---> ⌈ (patt_free_evar x and ϕ) ⌉ using i).
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
      apply pile.
    }

    assert(S9: Γ ⊢i (patt_free_evar x) ∈ml ϕ using i).
    {
      eapply MP. 2: apply S6.
      apply S7.
    }

    eapply universal_generalization with (x := x) in S9.
    3: { wf_auto2. }
    1: { simpl in S9. case_match;[|congruence]. exact S9. }
    eapply pile_trans. 2: apply pile.
    apply pile_evs_svs_kt.
    {
      clear. set_solver.
    }
    {
      apply reflexivity.
    }
    {
      reflexivity.
    }
    {
      clear. set_solver.
    }
  Defined.

  Lemma membership_elimination Γ ϕ i:
    ProofInfoLe (
    (ExGen := {[ev_x; fresh_evar ϕ]},
    SVSubst := ∅,
     KT := false,
     FP := defFP
    )) i ->

    well_formed ϕ ->
    theory ⊆ Γ ->
    Γ ⊢i all, ((patt_bound_evar 0) ∈ml ϕ) using i ->
    Γ ⊢i ϕ using i.
  Proof.
    intros pile wfϕ HΓ H.

    remember (fresh_evar ϕ) as x.
    assert(S1: Γ ⊢i all, ((patt_bound_evar 0) ∈ml (ϕ^{{evar: x ↦ 0}})) using i).
    {
      rewrite evar_quantify_fresh.
      { subst x.  apply set_evar_fresh_is_fresh'. }
      assumption.
    }

    assert(S2: Γ ⊢i (all, ((patt_bound_evar 0) ∈ml (ϕ^{{evar: x ↦ 0}}))) ---> (patt_free_evar x ∈ml ϕ) using i).
    {
      replace (b0 ∈ml ϕ^{{evar: x ↦ 0}})
        with ((patt_free_evar x ∈ml ϕ)^{{evar: x ↦ 0}})
      .
      2: {
        simpl. case_match;[|congruence]. reflexivity.
      }
      eapply useGenericReasoning.
      2: apply forall_variable_substitution.
      2: { wf_auto2. }
      eapply pile_trans. 2: apply pile.
      apply pile_evs_svs_kt.
      { clear. set_solver. }
      { apply reflexivity. }
      { reflexivity. }
      { clear. set_solver. }
    }

    assert(well_formed (all , b0 ∈ml ϕ^{{evar: x ↦ 0}})) by wf_auto2.

    assert(S3: Γ ⊢i patt_free_evar x ∈ml ϕ using i).
    {
      eapply MP. 2: apply S2.
      assumption.
    }

    pose proof (S5 := Singleton_ctx Γ AC_patt_defined box ϕ x ltac:(wf_auto2)).
    simpl in S5.

    eapply useGenericReasoning in S5.
    2: {
      eapply pile_trans. 2: apply pile.
      apply pile_evs_svs_kt.
      { clear. set_solver. }
      { apply reflexivity. }
      { reflexivity. }
      { clear. set_solver. }
    }

    assert (S6: Γ ⊢i ⌈ patt_free_evar x and ϕ ⌉ ---> (patt_free_evar x ---> ϕ) using i).
    {
      toMLGoal.
      { wf_auto2. }
      mlIntro. mlIntro.
      mlAdd S5. unfold patt_and at 1. unfold patt_or at 1.
      mlAssert((! ! patt_sym (Definedness_Syntax.inj definedness) $ (patt_free_evar x and ϕ) ---> ! (patt_free_evar x and ! ϕ)))
      using first 1.
      { wf_auto2. }
      {
        remember ((! ! patt_sym (Definedness_Syntax.inj definedness) $ (patt_free_evar x and ϕ) ---> ! (patt_free_evar x and ! ϕ)))
          as A.
        fromMLGoal.
        useBasicReasoning.
        apply not_not_elim. wf_auto2.
      }
      mlClear "2".

      mlAssert((! (patt_free_evar x and ! ϕ))) using first 2.
      { wf_auto2. }
      {
        mlApply "3". mlClear "3".
        fromMLGoal.
        useBasicReasoning.
        apply not_not_intro. wf_auto2.
      }
      mlClear "3". mlClear "0".

      unfold patt_and.
      mlAssert ((! patt_free_evar x or ! ! ϕ)) using first 1.
      { wf_auto2. }
      {
        fromMLGoal.
        useBasicReasoning.
        apply not_not_elim. wf_auto2.
      }
      mlClear "2".

      unfold patt_or.
      (* TODO we probably want mlApplyMetaRaw to implicitly perform the cast *)
      mlApplyMetaRaw (useBasicReasoning i (not_not_elim _ _ _)).
      mlApply "0".
      mlApplyMetaRaw (useBasicReasoning i (not_not_intro _ _ _)).
      mlExactn 1.
    }

    assert (S7: Γ ⊢i patt_free_evar x ---> ϕ using i).
    {
      eapply MP. 2: apply S6.
      1: assumption.
    }

    pose proof (S8 := S7).
    apply universal_generalization with (x := x) in S8.
    3: wf_auto2.
    2: {
      eapply pile_trans. 2: apply pile.
      apply pile_evs_svs_kt.
      { clear. set_solver. }
      { apply reflexivity. }
      { reflexivity. }
      { clear. set_solver. }
    }

    assert (S9: Γ ⊢i (ex, patt_bound_evar 0) ---> ϕ using i).
    {
      unfold patt_forall in S8.
      simpl in S8.
      case_match; [|congruence].
      
      replace b0 with ((patt_free_evar x)^{{evar: x ↦ 0}}).
      2: { simpl. case_match; [|congruence]. reflexivity. }
      
      apply Ex_gen.
      3: assumption.
      2: {
        subst x. apply set_evar_fresh_is_fresh'.
      }
      {
        eapply pile_trans.
        2: apply pile.
        apply pile_evs_svs_kt.
        {
          clear. set_solver.
        }
        {
          apply reflexivity.
        }
        {
          reflexivity.
        }
        {
          clear. set_solver.
        }
      }
    }

    eapply MP.
    2: apply S9.
    
    eapply useGenericReasoning.
    2: apply Existence.
    eapply pile_trans.
    2: apply pile.
    apply pile_basic_generic.
    Unshelve.
    all: wf_auto2.
  Defined.

  Lemma membership_not_1 Γ ϕ x:
    well_formed ϕ ->
    theory ⊆ Γ ->
    Γ ⊢i ((patt_free_evar x) ∈ml (! ϕ)) ---> ! ((patt_free_evar x) ∈ml ϕ)
    using BasicReasoning.
  Proof.
    intros Hwf HΓ.

    pose proof (S1 := Singleton_ctx Γ AC_patt_defined AC_patt_defined ϕ x ltac:(wf_auto2)).
    simpl in S1.

    assert (S2: Γ ⊢i ⌈ patt_free_evar x and ! ϕ ⌉ ---> ! ⌈ patt_free_evar x and ϕ ⌉ using BasicReasoning).
    {

      replace (patt_sym (Definedness_Syntax.inj definedness) $ (patt_free_evar x and ϕ))
        with (⌈ patt_free_evar x and ϕ ⌉) in S1 by reflexivity.

      replace (patt_sym (Definedness_Syntax.inj definedness) $ (patt_free_evar x and ! ϕ))
        with (⌈ patt_free_evar x and ! ϕ ⌉) in S1 by reflexivity.

      toMLGoal.
      { wf_auto2. }
      mlIntro. mlAdd S1.
      unfold patt_and at 1.
      mlAssert ((! ⌈ patt_free_evar x and ϕ ⌉ or ! ⌈ patt_free_evar x and ! ϕ ⌉))
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
      mlAssert ((! ⌈ patt_free_evar x and ! ϕ ⌉ or ! ⌈ patt_free_evar x and ϕ ⌉))
               using first 1.
      { wf_auto2. }
      {
        mlAdd (useBasicReasoning BasicReasoning (A_or_notA Γ (! ⌈ patt_free_evar x and ϕ ⌉) ltac:(wf_auto2))).
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

  Lemma membership_not_2 Γ (ϕ : Pattern) x:
    well_formed ϕ = true ->
    theory ⊆ Γ ->
    Γ ⊢i ((!(patt_free_evar x ∈ml ϕ)) ---> (patt_free_evar x ∈ml (! ϕ)))%ml
    using  (ExGen := {[ev_x; x]}, SVSubst := ∅, KT := false, FP := defFP).
  Proof.
    intros wfϕ HΓ.
    pose proof (S1 := defined_evar Γ x HΓ).
    remember_constraint as i.
    assert (S2: Γ ⊢i ⌈ (patt_free_evar x and ϕ) or (patt_free_evar x and (! ϕ)) ⌉ using i).
    {
      assert(H: Γ ⊢i (patt_free_evar x ---> ((patt_free_evar x and ϕ) or (patt_free_evar x and (! ϕ)))) using BasicReasoning).
      {
        toMLGoal.
        { wf_auto2. }
        mlIntro. mlAdd (A_or_notA Γ ϕ ltac:(auto)).
        mlDestructOr "1".
        - mlLeft. unfold patt_and. mlIntro. unfold patt_or.
          mlAssert ((! ϕ)).
          { wf_auto2. }
          {
            mlApply "1". mlClear "2". mlClear "1". fromMLGoal.
            apply not_not_intro; auto.
          }
          mlApply "3". mlExactn 0.
        - mlRight. unfold patt_and. mlIntro. unfold patt_or.
          mlApply "3". mlApplyMetaRaw (not_not_elim Γ ϕ ltac:(auto)).
          mlApply "1". mlIntro. mlApply "2". mlExactn 1.
      }
      apply useBasicReasoning with (i := i) in H.
      subst i.
      eapply Framing_right in H.
      eapply MP. 2: apply H.
      1: assumption.
      { unfold defFP. try_solve_pile. }
    }

    pose proof (Htmp := prf_prop_or_iff Γ AC_patt_defined (patt_free_evar x and ϕ) (patt_free_evar x and ! ϕ)
                                        ltac:(wf_auto2) ltac:(wf_auto2)).
    simpl in Htmp.
    apply pf_iff_proj1 in Htmp.
    2-3: wf_auto2.
    subst i.
    eapply MP.
    2: gapply Htmp; try_solve_pile.
    assumption.
  Defined.

  Lemma membership_not_iff Γ ϕ x:
    well_formed ϕ ->
    theory ⊆ Γ ->
    Γ ⊢i ((patt_free_evar x) ∈ml (! ϕ)) <---> ! ((patt_free_evar x) ∈ml ϕ)
    using  (ExGen := {[ev_x; x]}, SVSubst := ∅, KT := false, FP := defFP).
  Proof.
    intros Hwf HΓ.
    apply pf_iff_split.
    1,2: wf_auto2.
    - useBasicReasoning; apply membership_not_1; assumption.
    - apply membership_not_2; assumption.
  Defined.
  
  Lemma membership_or_1 Γ x ϕ₁ ϕ₂:
    well_formed ϕ₁ ->
    well_formed ϕ₂ ->
    theory ⊆ Γ ->
    Γ ⊢i (patt_free_evar x ∈ml (ϕ₁ or ϕ₂)) ---> ((patt_free_evar x ∈ml ϕ₁) or (patt_free_evar x ∈ml ϕ₂))
    using BasicReasoningWithDefFP.
  Proof.
    intros wfϕ₁ wfϕ₂ HΓ.
    unfold patt_in.
    eapply syllogism_meta.
    5: gapply Prop_disj_right; try_solve_pile.
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

  Lemma membership_or_2 Γ x ϕ₁ ϕ₂:
    well_formed ϕ₁ ->
    well_formed ϕ₂ ->
    theory ⊆ Γ ->
    Γ ⊢i ((patt_free_evar x ∈ml ϕ₁) or (patt_free_evar x ∈ml ϕ₂)) ---> (patt_free_evar x ∈ml (ϕ₁ or ϕ₂))
    using BasicReasoningWithDefFP.
  Proof.
    intros wfϕ₁ wfϕ₂ HΓ.
    unfold patt_in.
    pose proof (H1 := prf_prop_or_iff Γ AC_patt_defined (patt_free_evar x and ϕ₁) (patt_free_evar x and ϕ₂)
                                      ltac:(auto) ltac:(auto)).
    apply pf_iff_proj2 in H1.
    2,3: wf_auto2.
    eapply syllogism_meta.
    4: gapply H1; try_solve_pile.
    1-3: wf_auto2.
    simpl.
    unshelve (eapply Framing_right).
    { wf_auto2. }
    { unfold BasicReasoningWithDefFP. try_solve_pile. }

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

  Lemma membership_or_iff Γ x ϕ₁ ϕ₂:
    well_formed ϕ₁ ->
    well_formed ϕ₂ ->
    theory ⊆ Γ ->
    Γ ⊢i (patt_free_evar x ∈ml (ϕ₁ or ϕ₂)) <---> ((patt_free_evar x ∈ml ϕ₁) or (patt_free_evar x ∈ml ϕ₂))
    using BasicReasoningWithDefFP.
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
    Γ ⊢i (patt_free_evar x ∈ml (ϕ₁ and ϕ₂)) ---> ((patt_free_evar x ∈ml ϕ₁) and (patt_free_evar x ∈ml ϕ₂))
    using  (ExGen := {[ev_x; x]}, SVSubst := ∅, KT := false, FP := defFP).
  Proof.
    intros wfϕ₁ wfϕ₂ HΓ.

    epose proof (Htmp1 := (membership_or_2 _ _ _ _ _ _ HΓ)).
    (* TODO: [change constraint in _] should work even in proof mode! *)
    change constraint in Htmp1.
    remember_constraint as gpi.

    unfold patt_and.
    toMLGoal.
    { wf_auto2. }
    mlIntro.
    assert (wfϕ : well_formed (! ϕ₁ or ! ϕ₂)).
    { wf_auto2. }
    unshelve (mlApplyMetaRaw (useBasicReasoning gpi (membership_not_1 _ _ _ wfϕ HΓ)) in "0").
    mlIntro. mlApply "0". mlClear "0".
    mlApplyMetaRaw Htmp1.
    mlDestructOr "1"; subst gpi.
    - mlLeft.
      unshelve (mlApplyMetaRaw (membership_not_2 _ _ _ wfϕ₁ HΓ) in "0").
      mlExactn 0.
    - mlRight.
      unshelve (mlApplyMetaRaw (membership_not_2 _ _ _ wfϕ₂ HΓ) in "2").
      mlExactn 0.
      Unshelve. all: wf_auto2.
  Defined.

  Lemma membership_and_2 Γ x ϕ₁ ϕ₂:
    well_formed ϕ₁ ->
    well_formed ϕ₂ ->
    theory ⊆ Γ ->
    Γ ⊢i ((patt_free_evar x ∈ml ϕ₁) and (patt_free_evar x ∈ml ϕ₂)) ---> (patt_free_evar x ∈ml (ϕ₁ and ϕ₂))
    using  (ExGen := {[ev_x; x]}, SVSubst := ∅, KT := false, FP := defFP).
  Proof.
    intros wfϕ₁ wfϕ₂ HΓ.

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

    unshelve (mlApplyMetaRaw (membership_not_2 _ _ _ _ HΓ)).
    { wf_auto2. }
    mlIntro.

    mlApplyMetaRaw Htmp1 in "0".
    mlDestructOr "0".
    - mlApplyMetaRaw Htmp2 in "3".
      mlApply "3". mlExactn 0.
    -
      mlApplyMetaRaw Htmp3 in "4".
      mlApply "4". mlExactn 1.
      Unshelve. all: wf_auto2.
  Defined.

  Lemma membership_and_iff Γ x ϕ₁ ϕ₂:
    well_formed ϕ₁ ->
    well_formed ϕ₂ ->
    theory ⊆ Γ ->
    Γ ⊢i (patt_free_evar x ∈ml (ϕ₁ and ϕ₂)) <---> ((patt_free_evar x ∈ml ϕ₁) and (patt_free_evar x ∈ml ϕ₂))
    using  (ExGen := {[ev_x; x]}, SVSubst := ∅, KT := false, FP := defFP).
  Proof.
    intros wfϕ₁ wfϕ₂ HΓ.
    apply pf_iff_split.
    1,2: wf_auto2.
    + apply membership_and_1; assumption.
    + apply membership_and_2; assumption.
  Defined.

  Arguments frames_on_the_way_to_hole' {Σ} EvS SvS E ψ p q wfψ wfp wfq.

  Lemma equality_elimination_basic Γ φ1 φ2 C
    (HΓ : theory ⊆ Γ)
    (WF1 : well_formed φ1)
    (WF2 :  well_formed φ2)
    (WFC : PC_wf C) :
    mu_free (pcPattern C) ->
    Γ ⊢i (φ1 =ml φ2) --->
      (emplace C φ1) <---> (emplace C φ2)
    using (
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
    )).
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
          apply hypothesis.
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

      pose proof (evar_fresh_seq_disj (free_evars pcPattern ∪ free_evars φ1 ∪ free_evars φ2 ∪ {[pcEvar]}) (maximal_exists_depth_of_evar_in_pattern pcEvar pcPattern)).
      set_solver.
    }
    {
      simpl.
      unfold PC_wf in WFC.
      destruct C; simpl in *.

      pose proof (svar_fresh_seq_disj (free_svars pcPattern ∪ free_svars φ1 ∪ free_svars φ2) (maximal_mu_depth_of_evar_in_pattern pcEvar pcPattern)).
      set_solver.
    }
    {
      simpl.
      case_match.
      {
        reflexivity.
      }
      {
        exfalso.
        unfold PC_wf in WFC.
        destruct C; simpl in *.
        clear -n Hmf.
        unfold maximal_mu_depth_of_evar_in_pattern in *.
        apply n.
        cut (forall depth, depth >= maximal_mu_depth_of_evar_in_pattern' depth pcEvar pcPattern).
        {
          intros H.
          specialize (H 0). lia.
        }
        clear n.
        induction pcPattern; intros depth; simpl in *;
        try lia.
        {
          case_match; subst; lia.
        }
        {
          destruct_and!.
          specialize (IHpcPattern1 ltac:(assumption) depth).
          specialize (IHpcPattern2 ltac:(assumption) depth).
          destruct (maximal_mu_depth_of_evar_in_pattern' depth pcEvar pcPattern1);
          simpl in *; lia.
        }
        {
          destruct_and!.
          specialize (IHpcPattern1 ltac:(assumption) depth).
          specialize (IHpcPattern2 ltac:(assumption) depth).
          destruct (maximal_mu_depth_of_evar_in_pattern' depth pcEvar pcPattern1);
          simpl in *; lia.
        }
        {
          specialize (IHpcPattern ltac:(assumption) depth).
          assumption.
        }
        {
          inversion Hmf.
        }
      }
    }
  }
  {
    simpl.
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
    }
  }
  Defined.


  Lemma equality_elimination_basic_ar Γ φ1 φ2 C:
    theory ⊆ Γ ->
    well_formed φ1 ->
    well_formed φ2 ->
    PC_wf C ->
    mu_free (pcPattern C) ->
    Γ ⊢i (φ1 =ml φ2) --->
      (emplace C φ1) <---> (emplace C φ2)
    using AnyReasoning.
  Proof.
    intros.
    unshelve (gapply equality_elimination_basic); try assumption.
    unfold AnyReasoning.
    apply pile_evs_svs_kt.
    {
      clear. set_solver.
    }
    {
      clear. set_solver.
    }
    {
      case_match; simpl; reflexivity.
    }
    {
      clear. set_solver.
    }
  Defined.

  Lemma mu_free_maximal_mu_depth_of_evar_in_pattern' n x ψ:
    mu_free ψ ->
    maximal_mu_depth_of_evar_in_pattern' n x ψ <= n.
  Proof.
    move: n.
    induction ψ; intros n' Hmf; simpl in *; auto; try lia.
    {
      case_match; lia.
    }
    {
      destruct_and!.
      specialize (IHψ1 n' ltac:(assumption)).
      specialize (IHψ2 n' ltac:(assumption)).
      lia.
    }
    {
      destruct_and!.
      specialize (IHψ1 n' ltac:(assumption)).
      specialize (IHψ2 n' ltac:(assumption)).
      lia.
    }
    {
      inversion Hmf.
    }
  Qed.

  Lemma equality_elimination_basic_ar_iter_1 Γ ϕ₁ ϕ₂ l C :
    theory ⊆ Γ ->
    well_formed ϕ₁ ->
    well_formed ϕ₂ ->
    Pattern.wf l ->
    PC_wf C ->
    mu_free (pcPattern C) ->
    Γ ⊢i foldr patt_imp ((emplace C ϕ₁) <---> (emplace C ϕ₂)) ((ϕ₁ =ml ϕ₂) :: l)
    using AnyReasoning.
  Proof.
    intros HΓ wfϕ₁ wfϕ₂ wfl wfC Hmf.
    induction l; simpl.
    - apply equality_elimination_basic_ar; assumption.
    - pose proof (wfal := wfl). apply andb_prop in wfl as [wfa wfl].
      specialize (IHl wfl).
      simpl in IHl.
      pose proof (proved_impl_wf _ _ (proj1_sig IHl)).

      assert (well_formed (emplace C ϕ₁) = true) by (unfold emplace; wf_auto2).
      assert (well_formed (emplace C ϕ₂) = true) by (unfold emplace; wf_auto2).
      
      wf_auto2.
      toMLGoal.
      { wf_auto2. }
      mlIntro. mlIntro. mlClear "1".
      fromMLGoal.
      apply IHl.
  Defined.


  Lemma equality_elimination_basic_ar_iter Γ ϕ₁ ϕ₂ l₁ l₂ C :
    theory ⊆ Γ ->
    well_formed ϕ₁ ->
    well_formed ϕ₂ ->
    Pattern.wf l₁ ->
    Pattern.wf l₂ ->
    PC_wf C ->
    mu_free (pcPattern C) ->
    Γ ⊢i foldr patt_imp ((emplace C ϕ₁) <---> (emplace C ϕ₂)) (l₁ ++ (ϕ₁ =ml ϕ₂)::l₂)
    using AnyReasoning.
  Proof.
    intros HΓ wfϕ₁ wfϕ₂ wfl₁ wfl₂ wfC Hmf.
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

  Lemma equality_elimination_helper Γ φ1 φ2 ψ x :
    theory ⊆ Γ ->
    mu_free ψ ->
    well_formed φ1 -> well_formed φ2 -> well_formed ψ ->     
    Γ ⊢i (φ1 =ml φ2) ---> 
      (ψ^[[evar: x ↦ φ1]]) ---> (ψ^[[evar: x ↦ φ2]])
    using AnyReasoning.
  Proof.
    intros HΓ MF WF1 WF2 WFψ.
    unshelve (gapply (deduction_theorem_noKT)); try assumption.
    4,5 : abstract(wf_auto2).

    3: {

    remember (Γ ∪ {[ (φ1 <---> φ2) ]}) as Γ'.
    apply pf_iff_proj1; auto.

    unshelve(eapply (eq_prf_equiv_congruence _ Γ' φ1 φ2 WF1 WF2 ({[x]} ∪ free_evars ψ ∪ free_evars φ1 ∪ free_evars φ2)
        (free_svars ψ ∪ free_svars φ1 ∪ free_svars φ2) _ _ _ _ _ _ _ _ _ _ _ 0 0)); auto.
    1-7: abstract (set_solver).
    { apply pile_refl. }

    remember_constraint as i'.
    assert (Γ' ⊢i (φ1 <---> φ2) using i'). {
      subst i'. useBasicReasoning. apply hypothesis.
      - abstract (now apply well_formed_iff).
      - abstract (rewrite HeqΓ'; apply elem_of_union_r; constructor).
    }
    exact H.
    }
    {
      apply pile_any.
    }
    {
      simpl.
      cut (list_to_set
      (evar_fresh_seq ({[x]} ∪ free_evars ψ ∪ free_evars φ1 ∪ free_evars φ2)
         (maximal_exists_depth_of_evar_in_pattern' 0 x ψ))
    ## gset_to_coGset
         (free_evars φ1 ∪ free_evars φ2)).
      { set_solver. }
      pose proof (evar_fresh_seq_disj (({[x]} ∪ free_evars ψ ∪ free_evars φ1 ∪ free_evars φ2)) (maximal_exists_depth_of_evar_in_pattern' 0 x ψ)).
      set_solver.
    }
    {
      simpl.
      pose proof (svar_fresh_seq_disj ((free_svars ψ ∪ free_svars φ1 ∪ free_svars φ2)) (maximal_mu_depth_of_evar_in_pattern' 0 x ψ)).
      set_solver.
    }
    {
      simpl. case_match; simpl; try reflexivity.
      pose proof (mu_free_maximal_mu_depth_of_evar_in_pattern' 0 x ψ MF).
      lia.
    }
  Defined.


  Corollary equality_elimination2 Γ φ1 φ2 ψ:
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
    apply equality_elimination_helper; auto.
    { now apply mu_free_evar_open. }
    apply wf_evar_open_from_wf_ex.
    unfold well_formed, well_formed_closed; simpl.
    rewrite -> WF3, -> WF4, -> mu_free_wfp; auto.
  Defined.

  Lemma patt_eq_sym Γ φ1 φ2:
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
        apply hypothesis. apply well_formed_iff; auto.
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
  Qed.

  Lemma exists_functional_subst φ φ' Γ :
    theory ⊆ Γ ->
    mu_free φ -> well_formed φ' -> well_formed_closed_ex_aux φ 1 -> well_formed_closed_mu_aux φ 0 ->
    Γ ⊢i ((instantiate (patt_exists φ) φ') and (patt_exists (patt_equal φ' (patt_bound_evar 0)))) ---> (patt_exists φ)
    using AnyReasoning.
  Proof.
    intros HΓ MF WF WFB WFM.
    remember (fresh_evar (φ $ φ')) as Zvar.
    remember (patt_free_evar Zvar) as Z.
    assert (well_formed Z) as WFZ.
    { rewrite HeqZ. auto. }
    assert (Γ ⊢i (patt_equal φ' Z <---> patt_equal Z φ') using AnyReasoning).
    {
      pose proof (SYM1 := patt_eq_sym Γ φ' Z ltac:(auto) ltac:(auto) WFZ).
      pose proof (SYM2 := patt_eq_sym Γ Z φ' ltac:(assumption) WFZ ltac:(auto)).
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
    pose proof (equality_elimination2 Γ φ' Z φ HΓ MF WF WFZ WFB).
    apply pf_iff_iff in H. destruct H.
    assert (well_formed (ex, φ)) as WFEX.
    { wf_auto. now apply mu_free_wfp. }
    2,3: wf_auto2.
    pose proof (EQ := Ex_quan Γ φ Zvar WFEX).
    change constraint in EQ.
    epose proof (PC := prf_conclusion Γ (patt_equal φ' Z) (instantiate (ex , φ) (patt_free_evar Zvar) ---> ex , φ) AnyReasoning ltac:(apply well_formed_equal;wf_auto2) _ EQ).

    assert (Γ
              ⊢i patt_equal φ' Z ---> instantiate (ex , φ) φ' ---> ex , φ using AnyReasoning) as HSUB.
    {
      pose proof (EE := equality_elimination2 Γ φ' Z φ HΓ
                                               ltac:(auto) ltac:(auto) ltac:(auto) WFB).
      unfold instantiate in EE.
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
        { apply EE. wf_auto2. }
    }
    eapply MP. 2: useBasicReasoning; apply and_impl'; try_wfauto2.

    apply reorder_meta; try_wfauto2.
    eapply (Ex_gen Γ _ _ Zvar) in HSUB.
    2: { apply pile_any. }

    unfold exists_quantify in HSUB.
    mlSimpl in HSUB.
    rewrite -> HeqZ, -> HeqZvar in HSUB. simpl evar_quantify in HSUB.
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
      all: simpl; wf_auto.
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
    9: exact Γ.
    all: wf_auto2.
  Qed.

End ProofSystemTheorems.


Lemma MLGoal_rewriteBy {Σ : Signature} {syntax : Syntax}
    (Γ : Theory) (l₁ l₂ : hypotheses) name (ϕ₁ ϕ₂ : Pattern) (C : PatternCtx) :
  theory ⊆ Γ ->
  mu_free (pcPattern C) ->
  mkMLGoal Σ Γ (l₁ ++ (mkNH _ name (ϕ₁ =ml ϕ₂)) :: l₂) (emplace C ϕ₂) AnyReasoning ->
  mkMLGoal Σ Γ (l₁ ++ (mkNH _ name (ϕ₁ =ml ϕ₂)) :: l₂) (emplace C ϕ₁) AnyReasoning .
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

  _mlAssert_nocheck ((fresh names_of_l) : (emplace C' ϕ₁ <---> emplace C' ϕ₂)). (* !!! *)
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

  replace (l₁ ++ (mkNH _ name (ϕ₁ =ml ϕ₂)) :: l₂)
     with ((l₁ ++ (mkNH _ name (ϕ₁ =ml ϕ₂)) :: l₂) ++ [])
     in H
    by (rewrite app_nil_r; reflexivity).
  apply mlGoal_clear_hyp with (h := (mkNH _ (fresh names_of_l) ((emplace C' ϕ₂) ---> (emplace C' ϕ₁)))) in H.

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

  replace ((l₁ ++ (mkNH _ name (ϕ₁ =ml ϕ₂)) :: l₂)
            ++ [(mkNH _ (fresh names_of_l) ((emplace C' ϕ₂) ---> (emplace C' ϕ₁)));
                (mkNH _ (fresh names_of_l') (emplace C' ϕ₂))])
  with (((l₁ ++ (mkNH _ name (ϕ₁ =ml ϕ₂)) :: l₂)
        ++ [mkNH _ (fresh names_of_l) ((emplace C' ϕ₂) ---> (emplace C' ϕ₁))])
        ++ [mkNH _ (fresh names_of_l') (emplace C' ϕ₂)]).
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
            _mlReshapeHypsBack ()
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
  { simpl. assumption. }
  mlExactn 0.
Defined.

Lemma patt_equal_implies_iff
  {Σ : Signature} {syntax : Syntax} (ϕ1 ϕ2 : Pattern) (Γ : Theory) (i : ProofInfo) :
  theory ⊆ Γ ->
  ProofInfoLe
               (
                  (ExGen := {[ev_x; evar_fresh (elements (free_evars ϕ1 ∪ free_evars ϕ2))]},
                   SVSubst := ∅, KT := false, FP := defFP)) i ->
  well_formed ϕ1 ->
  well_formed ϕ2 ->
  Γ ⊢i ϕ1 =ml ϕ2 using i ->
  Γ ⊢i (ϕ1 <---> ϕ2) using i.
Proof.
  intros HΓ pile wfϕ1 wfϕ2 H.
  unfold "=ml" in H.
  apply total_phi_impl_phi_meta with (Γ := Γ) (i := i) in H.
  { assumption. }
  { assumption. }
  { wf_auto2. }
  { simpl.
    replace (free_evars ϕ1 ∪ free_evars ϕ2 ∪ ∅ ∪ ∅
    ∪ (free_evars ϕ2 ∪ free_evars ϕ1 ∪ ∅) ∪ ∅)
    with (free_evars ϕ1 ∪ free_evars ϕ2)
    by set_solver.
    apply pile.
  }
Defined.


Lemma disj_equals_greater_1_meta {Σ : Signature} {syntax : Syntax} Γ ϕ₁ ϕ₂ i:
  theory ⊆ Γ ->
  ProofInfoLe
    (
       (ExGen := {[ev_x; evar_fresh (elements (free_evars ϕ₁ ∪ free_evars ϕ₂))]},
        SVSubst := ∅, KT := false, FP := defFP)) i ->
  well_formed ϕ₁ ->
  well_formed ϕ₂ ->
  Γ ⊢i ϕ₁ ⊆ml ϕ₂ using i ->
  Γ ⊢i (ϕ₁ or ϕ₂) =ml ϕ₂ using i.
Proof.
  intros HΓ pile wfϕ₁ wfϕ₂ Hsub.
  apply patt_iff_implies_equal; try_wfauto2.
  { eapply pile_trans;[|apply pile].
    try_solve_pile.
  }
  apply pf_iff_split; try_wfauto2.
  + toMLGoal.
    { wf_auto2. }
    mlIntro "H0". mlDestructOr "H0".
    * apply total_phi_impl_phi_meta in Hsub;[|assumption|try_wfauto2|idtac].
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

Lemma def_not_phi_impl_not_total_phi {Σ : Signature} {syntax : Syntax} Γ ϕ:
  theory ⊆ Γ ->
  well_formed ϕ ->
  Γ ⊢i ⌈ ! ϕ ⌉ ---> ! ⌊ ϕ ⌋ using BasicReasoning.
Proof.
  intros HΓ wfϕ.
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
  {Σ : Signature} {syntax : Syntax} {Γ : Theory} (ϕ : Pattern) :
  theory ⊆ Γ ->
  well_formed ϕ ->
    Γ ⊢i ⌈ ⌈ ϕ ⌉ ⌉ ---> ⌈ ϕ ⌉
  using 
    (ExGen := {[ev_x; evar_fresh (elements (free_evars ϕ))]},
     SVSubst := ∅, KT := false, FP := defFP).
Proof.
  intros HΓ wfϕ.
  eapply (cast_proof').
  { 
    remember (ctx_app_r (patt_sym (Definedness_Syntax.inj definedness)) box ltac:(wf_auto2)) as AC1.
    remember (ctx_app_r (patt_sym (Definedness_Syntax.inj definedness)) AC1 ltac:(wf_auto2)) as AC2.
    replace (⌈ ⌈ ϕ ⌉ ⌉) with (subst_ctx AC2 ϕ) by (subst; reflexivity).
    subst. reflexivity.
  }
  gapply in_context_impl_defined.
  {
    simpl.
    apply pile_evs_svs_kt.
    {
      replace (free_evars ϕ ∪ (∅ ∪ (∅ ∪ ∅))) with (free_evars ϕ) by set_solver.
      apply reflexivity.
    }
    {
      apply reflexivity.
    }
    {
      reflexivity.
    }
    {
      set_solver.
    }
  }
  { exact HΓ. }
  { exact wfϕ. }
Defined.

Lemma bott_not_defined {Σ : Signature} {syntax : Syntax} Γ :
  Γ ⊢i ! ⌈ ⊥ ⌉ using BasicReasoning.
Proof.
  apply Prop_bott_right.
  { wf_auto2. }
Defined.

Lemma not_def_phi_impl_not_phi {Σ : Signature} {syntax : Syntax} Γ ϕ :
  theory ⊆ Γ ->
  well_formed ϕ ->
  Γ ⊢i ! ⌈ ϕ ⌉ ---> ! ϕ
  using 
  (ExGen := {[ev_x; evar_fresh (elements (free_evars ϕ))]},
   SVSubst := ∅, KT := false, FP := defFP).
Proof.
  intros HΓ wfϕ.
  toMLGoal.
  { wf_auto2. }
  mlIntro "H0".
  mlIntro "H1".
  mlApply "H0".
  mlClear "H0".
  mlApplyMeta phi_impl_defined_phi; auto. mlExact "H1".
Defined.

Lemma tot_phi_impl_tot_def_phi {Σ : Signature} {syntax : Syntax} Γ ϕ :
  theory ⊆ Γ ->
  well_formed ϕ ->
  Γ ⊢i ⌊ ϕ ⌋ ---> ⌊ ⌈ ϕ ⌉ ⌋
  using 
     (ExGen := {[ev_x; evar_fresh (elements (free_evars ϕ))]},
      SVSubst := ∅, KT := false, FP := defFP).
Proof.
  intros HΓ wfϕ.
  toMLGoal.
  { wf_auto2. }
  mlIntro "H0".
  mlIntro "H1".
  mlApply "H0".
  mlClear "H0".
  fromMLGoal.
  gapply Framing_right.
  { apply pile_refl. }
  {
    apply pile_evs_svs_kt.
    { clear. set_solver. }
    { clear. set_solver. }
    { reflexivity. }
    { apply reflexivity. }
  }
  apply not_def_phi_impl_not_phi; assumption.
Defined.

Lemma def_of_pred_impl_pred {Σ : Signature} {syntax : Syntax} Γ ψ :
  theory ⊆ Γ ->
  well_formed ψ ->
  mu_free ψ ->
  Γ ⊢i (ψ =ml patt_bott) or (ψ =ml patt_top) using AnyReasoning ->
  Γ ⊢i ⌈ ψ ⌉ ---> ψ using AnyReasoning.
Proof.
  intros HΓ wfψ Hmfψ H.
  toMLGoal.
  {wf_auto2. }
  mlAdd H as "H0".
  mlDestructOr "H0" as "H1" "H1".
  - mlRewriteBy "H1" at 2.
    { exact HΓ. }
    { simpl. rewrite Hmfψ.  reflexivity. }
    mlRewriteBy "H1" at 1.
    { exact HΓ. }
    { simpl. reflexivity. }
    mlClear "H1".
    fromMLGoal.
    aapply bott_not_defined.
  - mlRewriteBy "H1" at 2.
    { exact HΓ. }
    { simpl. rewrite Hmfψ.  reflexivity. }
    mlClear "H1".
    unfold patt_top. mlIntro. mlIntro. mlExactn 1.
Defined.

(* TODO need this non-meta *)
Lemma subseteq_antisym_meta {Σ : Signature} {syntax : Syntax} Γ ϕ₁ ϕ₂:
  theory ⊆ Γ ->
  well_formed ϕ₁ ->
  well_formed ϕ₂ ->
  Γ ⊢i (ϕ₁ ⊆ml ϕ₂) and (ϕ₂ ⊆ml ϕ₁) using AnyReasoning ->
  Γ ⊢i ϕ₁ =ml ϕ₂ using AnyReasoning.
Proof.
  intros HΓ wfϕ₁ wfϕ₂ H.
  unfold "=ml".
  apply phi_impl_total_phi_meta.
  { wf_auto2. }
  { apply pile_any. }
  toMLGoal.
  { wf_auto2. }
  mlAdd H as "H0".
  mlDestructAnd "H0" as "H1" "H2".

  epose proof (Htmp := (total_phi_impl_phi Γ _ HΓ _)).
  apply useGenericReasoning with (i := AnyReasoning) in Htmp.
  2: { apply pile_any. }
  mlApplyMetaRaw Htmp in "H1".
  clear Htmp.

  epose proof (Htmp := (total_phi_impl_phi Γ _ HΓ _)).
  apply useGenericReasoning with (i := AnyReasoning) in Htmp.
  2: { apply pile_any. }
  unshelve (mlApplyMetaRaw Htmp in "H2").
  clear Htmp.
  mlSplitAnd.
  - mlExact "H1".
  - mlExact "H2".
  Unshelve.
  all: wf_auto2.
Defined.

Lemma propagate_membership_conjunct_1 {Σ : Signature} {syntax : Syntax}
    Γ AC x ϕ₁ ϕ₂ :
  theory ⊆ Γ ->
  well_formed ϕ₁ ->
  well_formed ϕ₂ ->
  Γ ⊢i (subst_ctx AC (ϕ₁ and ((patt_free_evar x) ∈ml ϕ₂))) ---> ((patt_free_evar x) ∈ml ϕ₂)
  using AnyReasoning.
Proof.
  intros HΓ wfϕ₁ wfϕ₂.
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
  3: wf_auto2.
  2: apply pile_any.
  1: wf_auto2.
  gapply def_def_phi_impl_def_phi.
  { apply pile_any. }
  { assumption. }
  { wf_auto2. }
Defined.


Lemma ceil_monotonic {Σ : Signature} {syntax : Syntax} Γ ϕ₁ ϕ₂ i :
  theory ⊆ Γ ->
  ProofInfoLe BasicReasoningWithDefFP i ->
  well_formed ϕ₁ ->
  well_formed ϕ₂ ->
  Γ ⊢i ϕ₁ ---> ϕ₂ using i ->
  Γ ⊢i ⌈ ϕ₁ ⌉ ---> ⌈ ϕ₂ ⌉ using i.
Proof.
  intros HΓ pile wfϕ₁ wfϕ₂ H.
  unshelve (eapply Framing_right).
  { wf_auto2. }
  { apply pile. }
  exact H.
Defined.

Lemma floor_monotonic {Σ : Signature} {syntax : Syntax} Γ ϕ₁ ϕ₂ i :
  theory ⊆ Γ ->
  ProofInfoLe BasicReasoningWithDefFP i ->
  well_formed ϕ₁ ->
  well_formed ϕ₂ ->
  Γ ⊢i ϕ₁ ---> ϕ₂ using i ->
  Γ ⊢i ⌊ ϕ₁ ⌋ ---> ⌊ ϕ₂ ⌋ using i.
Proof.
  intros HΓ pile wfϕ₁ wfϕ₂ H.
  unfold patt_total.
  apply ProofMode_propositional.modus_tollens.
  apply ceil_monotonic.
  { assumption. }
  { exact pile. }
  { wf_auto2. }
  { wf_auto2. }
  apply ProofMode_propositional.modus_tollens.
  exact H.
Defined.

Lemma double_not_ceil_alt {Σ : Signature} {syntax : Syntax} Γ ϕ :
  theory ⊆ Γ ->
  well_formed ϕ ->
  Γ ⊢i ( ⌈ ! ⌈ ϕ ⌉ ⌉ ---> (! ⌈ ϕ ⌉)) using AnyReasoning ->
  Γ ⊢i ( ⌈ ϕ ⌉ ---> ! ( ⌈ ! ⌈ ϕ ⌉ ⌉)) using AnyReasoning.
Proof.
  intros HΓ wfϕ H.
  toMLGoal.
  { wf_auto2. }

  mlRewrite (useBasicReasoning AnyReasoning (not_not_iff Γ (⌈ ϕ ⌉) ltac:(wf_auto2))) at 1. 
  fromMLGoal.
  apply ProofMode_propositional.modus_tollens.
  exact H.
Defined.


Lemma membership_imp {Σ : Signature} {syntax : Syntax} Γ x ϕ₁ ϕ₂:
  theory ⊆ Γ ->
  well_formed ϕ₁ ->
  well_formed ϕ₂ ->
  Γ ⊢i (patt_free_evar x ∈ml (ϕ₁ ---> ϕ₂)) <---> ((patt_free_evar x ∈ml ϕ₁) ---> (patt_free_evar x ∈ml ϕ₂))
  using AnyReasoning.
Proof.
  intros HΓ wfϕ₁ wfϕ₂.

  toMLGoal.
  { wf_auto2. }
  mlRewrite (useBasicReasoning AnyReasoning (impl_iff_notp_or_q Γ ϕ₁ ϕ₂ ltac:(wf_auto2) ltac:(wf_auto2))) at 1.
  mlRewrite (useAnyReasoning (membership_or_iff Γ x (! ϕ₁) ϕ₂ ltac:(wf_auto2) ltac:(wf_auto2) HΓ)) at 1.
  mlRewrite (useAnyReasoning (membership_not_iff Γ ϕ₁ x ltac:(wf_auto2) HΓ)) at 1.
  mlRewrite <- (useBasicReasoning AnyReasoning (impl_iff_notp_or_q Γ (patt_free_evar x ∈ml ϕ₁) (patt_free_evar x ∈ml ϕ₂) ltac:(wf_auto2) ltac:(wf_auto2))) at 1.
  fromMLGoal.
  useBasicReasoning.
  apply pf_iff_equiv_refl.
  { wf_auto2. }
Defined.

Lemma ceil_propagation_exists_1 {Σ : Signature} {syntax : Syntax} Γ ϕ:
  theory ⊆ Γ ->
  well_formed (ex, ϕ) ->
  Γ ⊢i (⌈ ex, ϕ ⌉) ---> (ex, ⌈ ϕ ⌉)
  using BasicReasoning.
Proof.
  intros HΓ wfϕ.
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
   [fresh_vars : n_fresh_vars n [ϕ1; ϕ2]].
   And maybe the whole Definedness module should be parameterized by a variable
   which is used in the definedness axiom. This way, every lemma will be parameterized
   twice - or, in general, multiple times.

   This lemma is interesting in that the fresh variable that it generates
   may be the same as the fresh variable that is used for the definedness axiom.
   But in general, we may want to have a disjoint set of fresh variables...
 *)
Lemma ceil_propagation_exists_2 {Σ : Signature} {syntax : Syntax} Γ ϕ:
  theory ⊆ Γ ->
  well_formed (ex, ϕ) ->
  Γ ⊢i (ex, ⌈ ϕ ⌉) ---> (⌈ ex, ϕ ⌉)
  using  (ExGen := {[ev_x; fresh_evar ϕ]}, SVSubst := ∅, KT := false, FP := defFP).
Proof.
  intros HΓ wfϕ.

  remember (fresh_evar ϕ) as x.
  replace (⌈ ϕ ⌉) with (⌈ ϕ ⌉^{evar: 0 ↦ x}^{{evar: x ↦ 0}}).
  2: {
    rewrite evar_quantify_evar_open.
       {
         pose proof (set_evar_fresh_is_fresh ϕ).
         unfold evar_is_fresh_in in H.
         simpl. set_solver.
       }
       wf_auto.
       reflexivity.
  }
  apply Ex_gen.
  { try_solve_pile. }
  {  simpl.
        pose proof (Hfr := set_evar_fresh_is_fresh ϕ).
        unfold evar_is_fresh_in in Hfr.
        simpl. set_solver.
  }
  mlSimpl.
  apply ceil_monotonic.
  { assumption. }
  {
    unfold BasicReasoningWithDefFP.
    try_solve_pile.
  }
  { wf_auto2. }
  { wf_auto2. }
  useBasicReasoning.
  apply Ex_quan.
  { wf_auto2. }
Defined.

Lemma ceil_propagation_exists_iff {Σ : Signature} {syntax : Syntax} Γ ϕ:
  theory ⊆ Γ ->
  well_formed (ex, ϕ) ->
  Γ ⊢i (⌈ ex, ϕ ⌉) <---> (ex, ⌈ ϕ ⌉)
  using  (ExGen := {[ev_x; fresh_evar ϕ]}, SVSubst := ∅, KT := false, FP := defFP).
Proof.
  intros HΓ wfϕ.
  apply pf_iff_split.
  { wf_auto2. }
  { wf_auto2. }
  - useBasicReasoning. apply ceil_propagation_exists_1; assumption.
  - apply ceil_propagation_exists_2; assumption.
Defined.

Lemma membership_exists {Σ : Signature} {syntax : Syntax} Γ x ϕ:
  theory ⊆ Γ ->
  well_formed (ex, ϕ) ->
  Γ ⊢i (patt_free_evar x ∈ml (ex, ϕ)) <---> (ex, patt_free_evar x ∈ml ϕ)
  using AnyReasoning.
Proof.
  intros HΓ wfϕ.
  unfold "∈ml".
  toMLGoal.
  { wf_auto2. }
  mlRewrite <- (useAnyReasoning (ceil_propagation_exists_iff Γ (patt_free_evar x and ϕ) HΓ ltac:(wf_auto2))) at 1.
  fromMLGoal.
  assert (Htmp: Γ ⊢i (patt_free_evar x and ex, ϕ) <---> (ex, (patt_free_evar x and ϕ)) using AnyReasoning).
  { (* prenex-exists-and *)
    toMLGoal.
    { wf_auto2. }
    mlRewrite (useAnyReasoning (patt_and_comm Γ (patt_free_evar x) (ex, ϕ) ltac:(wf_auto2) ltac:(wf_auto2))) at 1.
    mlRewrite <- (useAnyReasoning (prenex_exists_and_iff Γ ϕ (patt_free_evar x) ltac:(wf_auto2) ltac:(wf_auto2))) at 1.
    remember (evar_fresh (elements ({[x]} ∪ (free_evars ϕ)))) as y.
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
  { wf_auto2. }
Defined.


Lemma membership_symbol_ceil_aux_aux_0 {Σ : Signature} {syntax : Syntax} Γ x ϕ:
  theory ⊆ Γ ->
  well_formed ϕ ->
  Γ ⊢i ((⌈ patt_free_evar x and ϕ ⌉) ---> (⌊ ⌈ patt_free_evar x and ϕ ⌉  ⌋))
  using AnyReasoning.
Proof.
  intros HΓ wfϕ.
  unfold patt_total.
  eapply syllogism_meta.
  { wf_auto2. }
  2: { wf_auto2. }
  3: {
    apply ProofMode_propositional.modus_tollens.
    {
      apply ceil_monotonic.
      { exact HΓ. }
      { apply pile_any. }
      { wf_auto2. }
      2: {
        gapply membership_not_2.
        { apply pile_any. }
        { wf_auto2. }
        { exact HΓ. }
      }
      { wf_auto2. }
    }
  }
  { wf_auto2. }
  toMLGoal.
  { wf_auto2. }

  mlRewrite (useAnyReasoning (not_not_iff Γ (⌈patt_free_evar x and ϕ ⌉) ltac:(wf_auto2))) at 1.
  fold (! ⌈ patt_free_evar x and ϕ ⌉ or ! ⌈ patt_free_evar x ∈ml (! ϕ) ⌉).
  mlRewrite (useAnyReasoning (not_not_iff Γ (! ⌈ patt_free_evar x and ϕ ⌉ or ! ⌈ patt_free_evar x ∈ml (! ϕ) ⌉) ltac:(wf_auto2))) at 1.
  fold ((⌈ patt_free_evar x and ϕ ⌉ and ⌈ patt_free_evar x ∈ml (! ϕ) ⌉)).
  unfold "∈ml".
  fromMLGoal.
  eapply cast_proof'.
  {
    replace (⌈ patt_free_evar x and ϕ ⌉)
            with (subst_ctx AC_patt_defined (patt_free_evar x and ϕ))
                 by reflexivity.
    replace (⌈ ⌈ patt_free_evar x and ! ϕ ⌉ ⌉)
            with (subst_ctx (ctx_app_r ((patt_sym (Definedness_Syntax.inj definedness))) AC_patt_defined ltac:(wf_auto2)) (patt_free_evar x and ! ϕ))
      by reflexivity.
    reflexivity.
  }
  gapply Singleton_ctx.
  { apply pile_any. }
  { exact wfϕ. }
Defined.

Lemma ceil_compat_in_or {Σ : Signature} {syntax : Syntax} Γ ϕ₁ ϕ₂:
  theory ⊆ Γ ->
  well_formed ϕ₁ ->
  well_formed ϕ₂ ->
  Γ ⊢i ( (⌈ ϕ₁ or ϕ₂ ⌉) <---> (⌈ ϕ₁ ⌉ or ⌈ ϕ₂ ⌉))
  using AnyReasoning.
Proof.
  intros HΓ wfϕ₁ wfϕ₂.
  toMLGoal.
  { wf_auto2. }
  mlSplitAnd; mlIntro "H0".
  - mlApplyMetaRaw (useAnyReasoning (Prop_disj_right Γ ϕ₁ ϕ₂ (patt_sym (Definedness_Syntax.inj definedness)) ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2) )).
    mlExact "H0".
  - mlDestructOr "H0" as "H1" "H2".
    + unshelve (mlApplyMetaRaw (useAnyReasoning (@Framing_right Σ Γ ϕ₁ (ϕ₁ or ϕ₂) (patt_sym (Definedness_Syntax.inj definedness)) ltac:(wf_auto2) _(pile_any _) _))).
      { wf_auto2. }
      { toMLGoal. wf_auto2. mlIntro "H0'". mlLeft. mlExact "H0'". }
      mlExactn 0.
    + unshelve (mlApplyMetaRaw (useAnyReasoning (@Framing_right Σ Γ ϕ₂ (ϕ₁ or ϕ₂) (patt_sym (Definedness_Syntax.inj definedness)) ltac:(wf_auto2) _ (pile_any _) _))).
      { wf_auto2. }
      { toMLGoal. wf_auto2. mlIntro "H0'". mlRight. mlExact "H0'". }
      mlExact "H2".
Defined.

Lemma membership_symbol_ceil_aux_0 {Σ : Signature} {syntax : Syntax} Γ x y ϕ:
  theory ⊆ Γ ->
  well_formed ϕ ->
  Γ ⊢i (⌈ patt_free_evar x and ϕ ⌉) ---> ⌈ patt_free_evar y and ⌈ patt_free_evar x and ϕ ⌉ ⌉
  using AnyReasoning.
Proof.
  intros HΓ wfϕ.

  toMLGoal.
  { wf_auto2. }
  mlIntro "H0".
  mlApplyMetaRaw (membership_symbol_ceil_aux_aux_0 Γ x ϕ HΓ wfϕ) in "H0".
  fromMLGoal.
  unfold patt_total.
  fold (⌈ ! ⌈ patt_free_evar x and ϕ ⌉ ⌉ or ⌈ patt_free_evar y and ⌈ patt_free_evar x and ϕ ⌉ ⌉).
  toMLGoal.
  { wf_auto2. }
  mlRewrite <- (ceil_compat_in_or Γ (! ⌈ patt_free_evar x and ϕ ⌉) (patt_free_evar y and ⌈ patt_free_evar x and ϕ ⌉) HΓ ltac:(wf_auto2) ltac:(wf_auto2)) at 1.

  unshelve (mlApplyMetaRaw (ceil_monotonic Γ
                               (patt_free_evar y)
                               (! ⌈ patt_free_evar x and ϕ ⌉ or patt_free_evar y and ⌈ patt_free_evar x and ϕ ⌉)
                               AnyReasoning HΓ _ ltac:(wf_auto2) ltac:(wf_auto2) _
              )).
  { apply pile_any. }
  {

    assert (Helper: forall ϕ₁ ϕ₂, well_formed ϕ₁ -> well_formed ϕ₂ -> Γ ⊢i (! ϕ₁ or ϕ₂) ---> (! ϕ₁ or (ϕ₂ and ϕ₁)) using AnyReasoning).
    {
      intros ϕ₁ ϕ₂ wfϕ₁ wfϕ₂.
      toMLGoal.
      { wf_auto2. }
      mlIntro "H0".
      mlAdd (useAnyReasoning (A_or_notA Γ ϕ₁ ltac:(wf_auto2))) as "H1".
      mlDestructOr "H0" as "H0'" "H0'"; mlDestructOr "H1" as "H1'" "H1'".
      - mlExFalso.
        mlApply "H0'". mlExact "H1'".
      - mlLeft. mlExactn 0.
      - mlRight.
        mlSplitAnd.
        + mlExact "H0'".
        + mlExact "H1'".
      - mlLeft.
        mlExact "H1'". 
    }
    toMLGoal.
    { wf_auto2. }
    mlIntro "H0".
    mlApplyMetaRaw (Helper (⌈ patt_free_evar x and ϕ ⌉) (patt_free_evar y) ltac:(wf_auto2) ltac:(wf_auto2)).
    mlRight.
    mlExact "H0".
  }
  fromMLGoal.
  gapply defined_evar.
  { apply pile_any. }
  { exact HΓ. }
Defined.


Lemma membership_symbol_ceil_left_aux_0 {Σ : Signature} {syntax : Syntax} Γ ϕ:
  theory ⊆ Γ ->
  well_formed ϕ ->
  Γ ⊢i ϕ ---> (ex, ⌈ b0 and ϕ ⌉)
  using AnyReasoning.
Proof.
  intros HΓ wfϕ.
  apply membership_elimination.
  { apply pile_any. }
  { wf_auto2. }
  { assumption. }
  remember (fresh_evar ϕ) as x.
  replace (b0 ∈ml (ϕ ---> ex , ⌈ b0 and ϕ ⌉))
    with ((b0 ∈ml (ϕ ---> ex , ⌈ b0 and ϕ ⌉))^{evar: 0 ↦ x}^{{evar: x ↦ 0}}).
  2: { rewrite evar_quantify_evar_open.
       {
         pose proof (set_evar_fresh_is_fresh ϕ).
         unfold evar_is_fresh_in in H.
         simpl. set_solver.
       }
       wf_auto.
       1-2: eapply well_formed_closed_ex_aux_ind; try eassumption; lia.
       reflexivity.
  }

  apply universal_generalization.
  { apply pile_any. }
  { wf_auto2. }
  unfold evar_open. mlSimpl. simpl.
  rewrite bevar_subst_not_occur.
  { wf_auto2. }
  rewrite bevar_subst_not_occur.
  { wf_auto2. }
  toMLGoal.
  { wf_auto2. }
  mlRewrite ((membership_imp Γ x ϕ (ex, ⌈ b0 and ϕ ⌉) HΓ ltac:(wf_auto2) ltac:(wf_auto2))) at 1.
  mlRewrite ((membership_exists Γ x (⌈ b0 and ϕ ⌉) HΓ ltac:(wf_auto2))) at 1.
  mlIntro "H0".
  remember (fresh_evar ϕ) as y.
  mlApplyMetaRaw (useAnyReasoning (Ex_quan Γ (patt_free_evar x ∈ml ⌈ b0 and ϕ ⌉) y ltac:(wf_auto2))).
  unfold instantiate. mlSimpl. simpl.
  rewrite bevar_subst_not_occur.
  { wf_auto2. }

  mlApplyMetaRaw (membership_symbol_ceil_aux_0 Γ y x ϕ HΓ wfϕ).
  subst y. subst x.
  mlExact "H0".
Defined.

Lemma ceil_and_x_ceil_phi_impl_ceil_phi {Σ : Signature} {syntax : Syntax} Γ (ϕ : Pattern) x:
  theory ⊆ Γ ->
  well_formed ϕ ->
  Γ ⊢i ( (⌈ patt_free_evar x and ⌈ ϕ ⌉ ⌉) ---> (⌈ ϕ ⌉))
  using AnyReasoning.
Proof.
  intros HΓ wfϕ.
  eapply syllogism_meta.
  { wf_auto2. }
  2: { wf_auto2. }
  3: {
    gapply def_def_phi_impl_def_phi.
    { apply pile_any. }
    { assumption. }
    { assumption. }
  }
  { wf_auto2. }
  apply ceil_monotonic.
  { exact HΓ. }
  { apply pile_any. }
  { wf_auto2. }
  { wf_auto2. }
  toMLGoal.
  { wf_auto2. }
  mlIntro "H0".
  mlDestructAnd "H0" as "H1" "H2".
  mlExact "H2".
Defined.

Lemma membership_monotone {Σ : Signature} {syntax : Syntax} Γ (ϕ₁ ϕ₂ : Pattern) x:
  theory ⊆ Γ ->
  well_formed ϕ₁ ->
  well_formed ϕ₂ ->
  Γ ⊢i (ϕ₁ ---> ϕ₂) using AnyReasoning ->
  Γ ⊢i (patt_free_evar x ∈ml ϕ₁) ---> (patt_free_evar x ∈ml ϕ₂) using AnyReasoning.
Proof.
  intros HΓ wfϕ₁ wfϕ₂ H.
  unfold patt_in.
  apply ceil_monotonic.
  { exact HΓ. }
  { apply pile_any. }
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

Lemma membership_symbol_ceil_left {Σ : Signature} {syntax : Syntax} Γ ϕ x:
  theory ⊆ Γ ->
  well_formed ϕ ->
  Γ ⊢i (patt_free_evar x ∈ml ⌈ ϕ ⌉) ---> (ex, (patt_bound_evar 0 ∈ml ϕ))
  using AnyReasoning.
Proof.
  intros HΓ wfϕ.
  eapply syllogism_meta.
  { wf_auto2. }
  2: {wf_auto2. }
  2: {
    apply membership_monotone.
    { exact HΓ. }
    { wf_auto2. }
    2: {
      apply ceil_monotonic.
      { exact HΓ. }
      { apply pile_any. }
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

  eapply syllogism_meta.
  { wf_auto2. }
  2: {wf_auto2. }
  2: {
    apply membership_monotone.
    { exact HΓ. }
    { wf_auto2. }
    2: {
      gapply ceil_propagation_exists_1.
      { apply pile_any. }
      { exact HΓ. }
      { wf_auto2. }
    }
    { wf_auto2. }
  }
  { wf_auto2. }

  remember (evar_fresh (elements ({[x]} ∪ (free_evars ϕ)))) as y.
  eapply syllogism_meta.
  { wf_auto2. }
  2: {wf_auto2. }
  2: {
    apply membership_monotone.
    { exact HΓ. }
    { wf_auto2. }
    2: {
      eapply cast_proof'.
      {
        rewrite -[⌈ ⌈ b0 and ϕ ⌉ ⌉](evar_quantify_evar_open y 0).
        { simpl.
          pose proof (Hfr := set_evar_fresh_is_fresh' ({[x]} ∪ (free_evars ϕ))).
          subst y. clear -Hfr. set_solver.
        }
        simpl. split_and!; auto.
        unfold well_formed, well_formed_closed in wfϕ. destruct_and!.
        eapply well_formed_closed_ex_aux_ind; try eassumption; lia.
        reflexivity.
      }
      apply ex_quan_monotone.
      { apply pile_any. }
      {
        unfold evar_open. mlSimpl. simpl.
        rewrite bevar_subst_not_occur.
        { wf_auto2. }
        gapply def_def_phi_impl_def_phi.
        { apply pile_any. }
        { exact HΓ. }
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
  pose proof (Htmp := membership_exists Γ x (⌈ patt_free_evar y and ϕ ⌉^{{evar: y ↦ 0}})).
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
  mlRewrite -> Htmp at 1. clear Htmp.

  fromMLGoal.
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

  apply (strip_exists_quantify_l Γ y).
  { simpl.
    pose proof (Hfr := set_evar_fresh_is_fresh' ({[x]} ∪ (free_evars ϕ))).
    rewrite -Heqy in Hfr.
    clear -Hfr.
    set_solver.
  }
  { simpl. split_and!; auto; wf_auto2. }

  apply (strip_exists_quantify_r Γ y).
  { simpl.
    pose proof (Hfr := set_evar_fresh_is_fresh' ({[x]} ∪ (free_evars ϕ))).
    rewrite -Heqy in Hfr.
    clear -Hfr.
    set_solver.
  }
  { simpl. split_and!; auto; wf_auto2. }
  apply ex_quan_monotone.
  { apply pile_any. }
  unfold evar_open. mlSimpl. simpl.
  rewrite bevar_subst_not_occur.
  { wf_auto2. }

  apply ceil_and_x_ceil_phi_impl_ceil_phi.
  { exact HΓ. }
  { wf_auto2. }
Defined.


Lemma membership_symbol_ceil_right_aux_0 {Σ : Signature} {syntax : Syntax} Γ ϕ:
  theory ⊆ Γ ->
  well_formed ϕ ->
  Γ ⊢i (ex, (⌈ b0 and  ϕ ⌉ and b0)) ---> ϕ
  using AnyReasoning.
Proof.
  intros HΓ wfϕ.
  apply prenex_forall_imp.
  1,2: wf_auto2.
  { apply pile_any. }
  remember (fresh_evar (⌈ b0 and ϕ ⌉ and b0 ---> ϕ)) as x.
  eapply cast_proof'.
  {
    rewrite -[HERE in (all, HERE)](evar_quantify_evar_open x 0).
    { subst x. apply set_evar_fresh_is_fresh. }
    unfold well_formed, well_formed_closed in wfϕ. destruct_and!. simpl.
    split_and!; auto.
    1-2: eapply well_formed_closed_ex_aux_ind; try eassumption; lia.
    reflexivity.
  }
  apply universal_generalization.
  { apply pile_any. }
  { wf_auto2. }
  assert (Htmp: forall (ϕ₁ ϕ₂ ϕ₃ : Pattern),
             well_formed ϕ₁ ->
             well_formed ϕ₂ ->
             well_formed ϕ₃ ->
             Γ ⊢i ((! (ϕ₁ and (ϕ₂ and !ϕ₃))) ---> ((ϕ₁ and ϕ₂) ---> ϕ₃)) using AnyReasoning).
  {
    intros ϕ₁ ϕ₂ ϕ₃ wfϕ₁ wfϕ₂ wfϕ₃.
    toMLGoal.
    { wf_auto2. }
    mlIntro "H0".
    mlIntro "H1".
    mlDestructAnd "H1" as "H2" "H3".
    mlApplyMetaRaw (useAnyReasoning (not_not_elim Γ ϕ₃ wfϕ₃)).
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
  2,3: apply wfc_ex_aux_bevar_subst; wf_auto2.
  mlSimpl. simpl.
  rewrite bevar_subst_not_occur.
  { wf_auto2. }
  replace (⌈ patt_free_evar x and ϕ ⌉) with (subst_ctx AC_patt_defined (patt_free_evar x and ϕ)) by reflexivity.
  replace (patt_free_evar x and ! ϕ) with (subst_ctx box (patt_free_evar x and ! ϕ)) by reflexivity.
  gapply Singleton_ctx.
  { apply pile_any. }
  exact wfϕ.
Defined.

Lemma membership_symbol_ceil_right {Σ : Signature} {syntax : Syntax} Γ ϕ x:
  theory ⊆ Γ ->
  well_formed ϕ ->
  Γ ⊢i ((ex, (BoundVarSugar.b0 ∈ml ϕ)) ---> (patt_free_evar x ∈ml ⌈ ϕ ⌉))
  using AnyReasoning.
Proof.
  intros HΓ wfϕ.
  remember (evar_fresh (elements ({[x]} ∪ (free_evars ϕ)))) as y.
  pose proof (Htmp := set_evar_fresh_is_fresh' ({[x]} ∪ free_evars ϕ)).
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
    { apply pile_any. }
    {
      unfold evar_open. mlSimpl. simpl.
      rewrite bevar_subst_not_occur.
      { wf_auto2. }
      apply membership_symbol_ceil_aux_0 with (y := x); assumption.
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
    { apply pile_any. }
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
        { apply pile_any. }
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
      rewrite evar_quantify_noop.
      { apply count_evar_occurrences_0.
        subst y.
        eapply evar_is_fresh_in_richer'.
        2: { apply set_evar_fresh_is_fresh'. }
        clear. set_solver.
      }
      gapply ceil_propagation_exists_2.
      { apply pile_any. }
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
  { apply pile_any. }
  { wf_auto2. }
  { wf_auto2. }  
  apply membership_symbol_ceil_right_aux_0; assumption.
Defined.

Lemma def_phi_impl_tot_def_phi {Σ : Signature} {syntax : Syntax} Γ ϕ :
  theory ⊆ Γ ->
  well_formed ϕ ->
  Γ ⊢i ⌈ ϕ ⌉ ---> ⌊ ⌈ ϕ ⌉ ⌋
  using AnyReasoning.
Proof.
  intros HΓ wfϕ.
  unfold patt_total.
  apply double_not_ceil_alt.
  { assumption. }
  { assumption. }
  apply membership_elimination.
  { apply pile_any. }
  { wf_auto2. }
  { assumption. }

  remember (fresh_evar ϕ) as x.
  eapply cast_proof'.
  { 
    rewrite -[b0 ∈ml _](evar_quantify_evar_open x 0).
    {
      simpl.
      pose proof (set_evar_fresh_is_fresh ϕ).
      unfold evar_is_fresh_in in H.
      simpl. set_solver.
    }
    unfold well_formed, well_formed_closed in wfϕ. destruct_and!.
    simpl; split_and!; auto.
    1-2: eapply well_formed_closed_ex_aux_ind; try eassumption; lia.
    reflexivity.
  }
  apply universal_generalization.
  { apply pile_any. }
  { wf_auto2. }
  unfold evar_open. mlSimpl. simpl.
  rewrite bevar_subst_not_occur.
  { wf_auto2. }

  toMLGoal.
  { wf_auto2. }
  mlRewrite (membership_imp Γ x (⌈ ! ⌈ ϕ ⌉ ⌉) (! ⌈ ϕ ⌉) HΓ ltac:(wf_auto2) ltac:(wf_auto2)) at 1.
  mlIntro "H0".
  mlApplyMetaRaw (membership_symbol_ceil_left Γ (! ⌈ ϕ ⌉) x HΓ ltac:(wf_auto2)) in "H0".
  mlRewrite (useAnyReasoning (membership_not_iff Γ (⌈ ϕ ⌉) x ltac:(wf_auto2) HΓ)) at 1.

  remember (evar_fresh (elements ({[x]} ∪ (free_evars ϕ)))) as y.
  pose proof (Hfr := set_evar_fresh_is_fresh' ({[x]} ∪ (free_evars ϕ))).
  eapply cast_proof_ml_hyps.
  {
    rewrite <- (evar_quantify_evar_open y 0 (b0 ∈ml (! ⌈ ϕ ⌉))).
    2: { simpl. rewrite <- Heqy in Hfr. clear -Hfr. set_solver. }
    reflexivity.
    unfold well_formed, well_formed_closed in wfϕ. destruct_and!.
    simpl; split_and!; auto.
    eapply well_formed_closed_ex_aux_ind; try eassumption; lia.
  }

  assert (Htmp: Γ ⊢i (((b0 ∈ml (! ⌈ ϕ ⌉))^{evar: 0 ↦ y}) ---> ((! (b0 ∈ml ⌈ ϕ ⌉))^{evar: 0 ↦ y})) using AnyReasoning).
  {
    unfold evar_open. mlSimpl. simpl. gapply membership_not_1.
    { apply pile_any. }
    { wf_auto2.
      apply wfc_ex_aux_bevar_subst. wf_auto2. reflexivity.
    }
    exact HΓ.
  }

  mlApplyMetaRaw (useAnyReasoning (ex_quan_monotone Γ  y _ _ AnyReasoning (pile_any _) Htmp)) in "H0".
  clear Htmp.


  eapply cast_proof_ml_hyps.
  {
    unfold exists_quantify.
    rewrite -> (evar_quantify_evar_open y 0 (! b0 ∈ml (⌈ ϕ ⌉))).
    2: { simpl. rewrite <- Heqy in Hfr. clear -Hfr. set_solver. }
    reflexivity.
    unfold well_formed, well_formed_closed in wfϕ. destruct_and!.
    simpl; split_and!; auto.
    eapply well_formed_closed_ex_aux_ind; try eassumption; lia.
  }

  mlApplyMetaRaw (useAnyReasoning (not_not_intro Γ (ex , (! b0 ∈ml ⌈ ϕ ⌉)) ltac:(wf_auto2))) in "H0".
  eapply cast_proof_ml_hyps.
  {
    replace (! ! ex , (! b0 ∈ml ⌈ ϕ ⌉)) with (! all , (b0 ∈ml ⌈ ϕ ⌉)) by reflexivity.
    reflexivity.
  }

  assert (Htmp: Γ ⊢i (! (ex, b0 ∈ml ϕ)) ---> (! (patt_free_evar x ∈ml ⌈ ϕ ⌉)) using AnyReasoning).
  {
    apply ProofMode_propositional.modus_tollens.
    apply membership_symbol_ceil_left; assumption.
  }
  mlApplyMetaRaw Htmp.
  fromMLGoal.
  apply ProofMode_propositional.modus_tollens.

  pose proof (Hfr' := set_evar_fresh_is_fresh ϕ).
  eapply cast_proof'.
  {
    rewrite -[THIS in (patt_exists THIS)](evar_quantify_evar_open x 0).
    { simpl. 
      unfold evar_is_fresh_in in Hfr'. rewrite -Heqx in Hfr'. clear -Hfr'.
      set_solver.
    }
    {
      unfold well_formed, well_formed_closed in wfϕ. destruct_and!.
      simpl; split_and!; auto.
      eapply well_formed_closed_ex_aux_ind; try eassumption; lia.
    }
    rewrite -[THIS in (patt_forall THIS)](evar_quantify_evar_open y 0).
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
    pose proof (Hsub := free_evars_bevar_subst ϕ (patt_free_evar (fresh_evar ϕ)) 0).
    rewrite !simpl_free_evars.
    set_solver.
  }
  { apply pile_any. }

  rewrite evar_quantify_evar_open.
  { simpl. unfold evar_is_fresh_in in Hfr'. subst x. set_solver. }
  {
    unfold well_formed, well_formed_closed in wfϕ. destruct_and!.
    simpl; split_and!; auto.
    eapply well_formed_closed_ex_aux_ind; try eassumption; lia.
  }
  mlSimpl. unfold evar_open. simpl. rewrite bevar_subst_not_occur.
  { wf_auto2. }
  apply  membership_symbol_ceil_right; assumption.
Defined.

Lemma def_tot_phi_impl_tot_phi {Σ : Signature} {syntax : Syntax} Γ ϕ :
  theory ⊆ Γ ->
  well_formed ϕ ->
  Γ ⊢i ⌈ ⌊ ϕ ⌋ ⌉ ---> ⌊ ϕ ⌋ using AnyReasoning.
Proof.
  intros HΓ wfϕ.
  toMLGoal.
  { wf_auto2. }
  mlIntro "H0".
  mlApplyMetaRaw (useAnyReasoning (not_not_intro Γ (⌈ ⌊ ϕ ⌋ ⌉) ltac:(wf_auto2))) in "H0".
  mlIntro "H1". mlApply "H0". mlClear "H0".
  fromMLGoal.
  apply def_phi_impl_tot_def_phi.
  { exact HΓ. }
  { wf_auto2. }
Defined.

Lemma floor_is_predicate {Σ : Signature} {syntax : Syntax} Γ ϕ :
  theory ⊆ Γ ->
  well_formed ϕ ->
  Γ ⊢i is_predicate_pattern (⌊ ϕ ⌋)
  using AnyReasoning.
Proof.
  intros HΓ wfϕ.
  unfold is_predicate_pattern.
  unfold "=ml".
  toMLGoal.
  { wf_auto2. }

  mlRewrite (useAnyReasoning (pf_iff_equiv_sym Γ (⌊ ϕ ⌋) (⌊ ϕ ⌋ <---> Top) _ ltac:(wf_auto2) ltac:(wf_auto2) (phi_iff_phi_top Γ (⌊ ϕ ⌋) ltac:(wf_auto2)))) at 1.

  mlRewrite (useAnyReasoning (pf_iff_equiv_sym Γ (! ⌊ ϕ ⌋) (⌊ ϕ ⌋ <---> ⊥) _ ltac:(wf_auto2) ltac:(wf_auto2) (not_phi_iff_phi_bott Γ (⌊ ϕ ⌋) ltac:(wf_auto2)))) at 1.
  fromMLGoal.


  unfold patt_total at 1.
  unfold patt_total at 2.
  unfold patt_or.
  apply ProofMode_propositional.modus_tollens.

  assert (Γ ⊢i (! ! ⌊ ϕ ⌋) <---> ⌊ ϕ ⌋ using AnyReasoning).
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
  mlApplyMetaRaw (def_phi_impl_tot_def_phi Γ (⌊ ϕ ⌋) HΓ ltac:(wf_auto2)) in "H0".
  fromMLGoal.
  apply floor_monotonic.
  { exact HΓ. }
  { apply pile_any. }
  { wf_auto2. }
  { wf_auto2. }
  apply def_tot_phi_impl_tot_phi; assumption.
Defined.

Lemma def_propagate_not {Σ : Signature} {syntax : Syntax} Γ ϕ:
  theory ⊆ Γ ->
  well_formed ϕ ->
  Γ ⊢i (! ⌈ ϕ ⌉) <---> (⌊ ! ϕ ⌋)
  using AnyReasoning.
Proof.
  intros HΓ wfϕ.
  toMLGoal.
  { wf_auto2. }
  mlRewrite (useAnyReasoning (not_not_iff Γ ϕ wfϕ)) at 1.
  mlSplitAnd; mlIntro; mlExactn 0.
Defined.

Lemma def_def_phi_impl_tot_def_phi {Σ : Signature} {syntax : Syntax} Γ ϕ :
  theory ⊆ Γ ->
  well_formed ϕ ->
  Γ ⊢i ⌈ ⌈ ϕ ⌉ ⌉ ---> ⌊ ⌈ ϕ ⌉ ⌋
  using AnyReasoning.
Proof.
  intros HΓ wfϕ.
  eapply syllogism_meta.
  1,3: wf_auto2.
  2: { gapply def_def_phi_impl_def_phi. apply pile_any. assumption. assumption. }
  { wf_auto2. }
  apply def_phi_impl_tot_def_phi; assumption.
Defined.


Lemma ceil_is_predicate {Σ : Signature} {syntax : Syntax} Γ ϕ :
  theory ⊆ Γ ->
  well_formed ϕ ->
  Γ ⊢i is_predicate_pattern (⌈ ϕ ⌉)
  using AnyReasoning.
Proof.
  intros HΓ wfϕ.
  unfold is_predicate_pattern.
  apply or_comm_meta.
  { wf_auto2. }
  { wf_auto2. }
  unfold patt_or.
  apply @syllogism_meta with (B := ⌈ ⌈ ϕ ⌉ ⌉).
  1,2,3: wf_auto2.
  - toMLGoal.
    { wf_auto2. }

    mlRewrite (useAnyReasoning (not_not_iff Γ (⌈ ⌈ ϕ ⌉ ⌉) ltac:(wf_auto2))) at 1.
    mlIntro "H0".
    mlIntro "H1".
    mlApply "H0".
    mlClear "H0".
    mlRevertLast.
    mlRewrite (useAnyReasoning (def_propagate_not Γ (⌈ ϕ ⌉) HΓ ltac:(wf_auto2))) at 1.
    mlIntro "H0". 
    mlApplyMetaRaw (useAnyReasoning (total_phi_impl_phi Γ (! ⌈ ϕ ⌉) HΓ ltac:(wf_auto2))) in "H0".
    mlRevertLast.
    mlRewrite (useAnyReasoning (def_propagate_not Γ ϕ HΓ ltac:(wf_auto2))) at 1.
    fromMLGoal.
    unshelve (gapply deduction_theorem_noKT).
    2: apply pile_any.
    5: exact HΓ.
    3,4: wf_auto2.
    2: { apply patt_iff_implies_equal.
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
      assert (Htmp: ((Γ ∪ {[! ϕ]})) ⊢i ! ϕ using i').
      { gapply hypothesis. subst i'. try_solve_pile. wf_auto2. clear. set_solver. }
      apply phi_impl_total_phi_meta in Htmp.
      2: { wf_auto2. }
      2: { subst i'. apply pile_refl.  }
      mlAdd Htmp as "H1".  mlApply "H1". mlClear "H1".
      fromMLGoal.
      subst i'. 
      gapply Framing_right.
      { apply pile_refl. }
      { unfold defFP. try_solve_pile. }
      useBasicReasoning.
      apply not_not_intro.
      assumption.
    }
    { simpl. clear. set_solver. }
    { simpl. clear. set_solver. }
    { reflexivity. }
    - eapply @syllogism_meta with (B := ⌊ ⌈ ϕ ⌉ ⌋).
      1,2,3: wf_auto2.
      { apply def_def_phi_impl_tot_def_phi; assumption. }
      unshelve (gapply deduction_theorem_noKT).
      2: apply pile_any.
      3,4: wf_auto2.
      3: exact HΓ.
      2: {
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
          gapply hypothesis.
          { try_solve_pile. }
          { wf_auto2. }
          clear. set_solver.
      }
      {
        simpl. clear. set_solver.
      }
      { simpl. clear. set_solver. }
      { reflexivity. }
Defined.

Lemma disj_equals_greater_1 {Σ : Signature} {syntax : Syntax} Γ ϕ₁ ϕ₂:
  theory ⊆ Γ ->
  well_formed ϕ₁ ->
  well_formed ϕ₂ ->
  Γ ⊢i (ϕ₁ ⊆ml ϕ₂) ---> ((ϕ₁ or ϕ₂) =ml ϕ₂)
  using AnyReasoning.
Proof.
  intros HΓ wfϕ₁ wfϕ₂.
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
      + assert (Γ ∪ {[ϕ₁ ---> ϕ₂]} ⊢i ϕ₁ ---> ϕ₂ using ( (ExGen := ∅, SVSubst := ∅, KT := false, FP := defFP))).
        {
          gapply hypothesis.
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


Lemma disj_equals_greater_2_meta {Σ : Signature} {syntax : Syntax} Γ ϕ₁ ϕ₂:
  theory ⊆ Γ ->
  well_formed ϕ₁ ->
  well_formed ϕ₂ ->
  Γ ⊢i (ϕ₁ or ϕ₂) =ml ϕ₂ using AnyReasoning ->
  Γ ⊢i ϕ₁ ⊆ml ϕ₂ using AnyReasoning.
Proof.
  intros HΓ wfϕ₁ wfϕ₂ Heq.
  toMLGoal.
  { wf_auto2. }
  unshelve (epose proof (Htmp := patt_equal_implies_iff _ _ _ _ HΓ _ _ _ Heq)).
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

Lemma disj_equals_greater_2 {Σ : Signature} {syntax : Syntax} Γ ϕ₁ ϕ₂:
  theory ⊆ Γ ->
  well_formed ϕ₁ ->
  well_formed ϕ₂ ->
  mu_free ϕ₁ -> (* TODO get rid of it *)
  Γ ⊢i ((ϕ₁ or ϕ₂) =ml ϕ₂) ---> (ϕ₁ ⊆ml ϕ₂)
  using AnyReasoning.
Proof.
  intros HΓ wfϕ₁ wfϕ₂ mfϕ₁.
  toMLGoal.
  { wf_auto2. }
  mlIntro "H0".

  unshelve(mlApplyMeta patt_eq_sym in "H0").
  2: { assumption. }
  mlRewriteBy "H0" at 1.
  { assumption. }
  { simpl. rewrite mfϕ₁. reflexivity. }
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
  mlApplyMetaRaw (useAnyReasoning (phi_impl_defined_phi _ (! ⊥) SubTheory ltac:(wf_auto2))).
  mlIntro "H1". mlExact "H1".
Defined.

Lemma defined_not_iff_not_total {Σ : Signature} {syntax : Syntax}:
  ∀ (Γ : Theory) (ϕ : Pattern),
  theory ⊆ Γ → well_formed ϕ → Γ ⊢i ⌈ ! ϕ ⌉ <---> ! ⌊ ϕ ⌋
  using AnyReasoning.
Proof.
  intros Γ φ HΓ Wf. toMLGoal. wf_auto2.
  mlSplitAnd.
  * mlIntro "H0".
    mlApplyMetaRaw (useAnyReasoning (def_not_phi_impl_not_total_phi Γ φ HΓ Wf)).
    mlExact "H0".
  * unfold patt_total.
    pose proof (useAnyReasoning (not_not_iff Γ ⌈ ! φ ⌉ ltac:(wf_auto2))) as H.
    mlRewrite <- H at 1.
    mlIntro "H0".
    mlExact "H0".
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
  * pose proof (useAnyReasoning (disj_left_intro Γ φ ψ Wf1 Wf2)) as H.
    apply floor_monotonic in H. 4,5: try wf_auto2.
    2: { exact HΓ. }
    2: { apply pile_any. }
    mlApplyMetaRaw H.
    mlExact "H0'".
  * pose proof (useAnyReasoning (disj_right_intro Γ φ ψ Wf1 Wf2)) as H.
    apply floor_monotonic in H.
    4,5: wf_auto2.
    3: { apply pile_any. }
    2: { exact HΓ. }
    mlApplyMetaRaw H.
    mlExact "H0'".
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
  mlRewrite (useAnyReasoning (defined_not_iff_not_total Γ (! φ or ! ψ) HΓ ltac:(wf_auto2))) at 1.
  mlIntro "H0".
  mlIntro "H1".
  mlApply "H0".
  mlClear "H0".
  mlApplyMeta (patt_or_total _ (! φ) (! ψ) HΓ).
  mlDestructOr "H1" as "H1'" "H1'".
  * mlLeft. unfold patt_total.
    mlRewrite <- (useAnyReasoning (not_not_iff Γ φ Wf1)) at 1.
    mlExact "H1'".
  * mlRight. unfold patt_total.
    mlRewrite <- (useAnyReasoning (not_not_iff Γ ψ Wf2)) at 1.
    mlExact "H1'".
Defined.

Lemma patt_total_and {Σ : Signature} {syntax : Syntax}:
  forall Γ φ ψ,
  theory ⊆ Γ ->
  well_formed φ -> well_formed ψ ->
  Γ ⊢i ⌊ φ and ψ ⌋ <---> ⌊ φ ⌋ and ⌊ ψ ⌋
  using AnyReasoning.
Proof.
  intros Γ φ ψ HΓ Wf1 Wf2. toMLGoal. wf_auto2.
  mlSplitAnd.
  * unfold patt_and.
    mlRewrite <- (def_propagate_not Γ (! φ or ! ψ) HΓ ltac:(wf_auto2)) at 1.
    mlIntro "H1".
    mlIntro "H2".
    mlApply "H1".
    mlClear "H1".
    mlRewrite (ceil_compat_in_or Γ (! φ) (! ψ) HΓ ltac:(wf_auto2) ltac:(wf_auto2)) at 1.
    mlDestructOr "H2" as "H2'" "H2'".
    - mlLeft. mlRevertLast. unfold patt_total.
      mlRewrite <- (useAnyReasoning (not_not_iff Γ ⌈ ! φ ⌉ ltac:(wf_auto2))) at 1.
      mlIntro "H3". mlExact "H3".
    - mlRight. mlRevertLast. unfold patt_total.
      mlRewrite <- (useAnyReasoning (not_not_iff Γ ⌈ ! ψ ⌉ ltac:(wf_auto2))) at 1.
      mlIntro "H3". mlExact "H3".
  * mlIntro "H0". mlDestructAnd "H0" as "H1" "H2".
    unfold patt_and.
    mlRewrite <- (def_propagate_not Γ (! φ or ! ψ) HΓ ltac:(wf_auto2)) at 1.
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
  mlRewrite (patt_total_and Γ
                            (pY ---> pX)
                            (pX ---> pY) HΓ
                            ltac:(wf_auto2) ltac:(wf_auto2)) at 1.
  fold AnyReasoning.
  mlIntro "H0".
  mlIntro "H1".
  mlDestructOr "H1" as "H1'" "H1'".
  * mlApply "H1'".
    mlClear "H1'".
    mlIntro "H2".
    pose proof (MH := ProofMode_propositional.nimpl_eq_and Γ pY pX
                  ltac:(wf_auto2) ltac:(wf_auto2)).
    apply useAnyReasoning in MH.
    mlRevertLast.
    mlRewrite MH at 1. fold AnyReasoning.
    unshelve (epose proof (MH1 := Singleton_ctx Γ 
           (⌈_⌉ $ᵣ □)
           (⌈_⌉ $ᵣ □) pX y ltac:(wf_auto2))). 1-2: wf_auto2.
    rewrite -HeqpY in MH1.
    apply useAnyReasoning in MH1. simpl in MH1.
    (* TODO: having mlExactMeta would help here *)
    mlRevertLast. unfold patt_defined. unfold patt_not in *.
    mlIntro "H1". mlIntro "H2".
    mlApplyMeta MH1. simpl. mlSplitAnd. mlExact "H1". mlExact "H2".
  * mlApply "H1'".
    mlClear "H1'".
    mlIntro "H2".
    pose proof (MH := ProofMode_propositional.nimpl_eq_and Γ pX pY
                  ltac:(wf_auto2) ltac:(wf_auto2)).
    mlRevertLast. apply useAnyReasoning in MH. mlRewrite MH at 1.
    pose proof (MH1 := patt_and_comm Γ pY pX ltac:(wf_auto2) ltac:(wf_auto2)).
    mlRevertLast. apply useAnyReasoning in MH1. mlRewrite MH1 at 1.
    unshelve (epose proof (Singleton_ctx Γ 
           (⌈_⌉ $ᵣ □)
           (⌈_⌉ $ᵣ □) pY x ltac:(wf_auto2)) as MH2). 1-2: wf_auto2.
    rewrite -HeqpX in MH2.
    apply useAnyReasoning in MH2.
    mlIntro "H1". mlIntro "H2".
    mlApplyMeta MH2. simpl. mlSplitAnd. mlExact "H1". mlExact "H2".
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
  Unshelve. all: auto. all: wf_auto.
Defined.

Tactic Notation "mgSpecMeta" ident(hyp) "with" constr(t) := 
  unshelve (eapply (@mlSpecializeMeta _ _ _ _ t) in hyp); try wf_auto2.

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
  unfold of_MLGoal in *. simpl in *. wf_auto2.
  assert (well_formed (ex , p)). {
    unfold patterns_of in H0. rewrite map_app in H0.
    apply wfl₁hl₂_proj_h in H0; simpl in H0.
    apply andb_true_iff in H0 as [H0'' H0'].
    apply andb_true_iff in H0' as [H0_1 H0_2]; simpl in *; repeat rewrite andb_true_r in H0_1, H0_2; repeat rewrite andb_true_iff in H0_1, H0_2; wf_auto2.
  }
  epose proof (MG H _) as MG'.
  unfold patterns_of in *. rewrite -> map_app in *. simpl.
  eapply prf_strenghten_premise_iter_meta_meta.
  7: exact MG'. all: auto.
  1: now apply wfl₁hl₂_proj_l₁ in H0.
  1: now apply wfl₁hl₂_proj_l₂ in H0.
  apply wfl₁hl₂_proj_h in H0. wf_auto2.
  apply wfl₁hl₂_proj_h in H0. wf_auto2.
  apply forall_functional_subst. 1-3: auto. all: wf_auto2.
  Unshelve.
  all: unfold patterns_of in *; rewrite -> map_app in *; simpl in H0; wf_auto2.
  1: now apply wfl₁hl₂_proj_l₁ in H0.
  apply wfl₁hl₂_proj_l₂ in H0 as H0'; simpl.
  apply wfl₁hl₂_proj_h in H0.
  apply wf_cons; wf_auto2.
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
  Γ ⊢i all , φ ---> (ex , t =ml b0) ---> φ^[evar: 0 ↦ t] using AnyReasoning.
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
  ProofInfoLe ( (ExGen := {[ev_x]}, SVSubst := ∅, KT := false, FP := defFP)) i  ->
  Γ ⊢i all , ⌈b0⌉ using i.
Proof.
  intros Γ i HΓ PI.
  (* remember (fresh_evar ⊥) as x. *)
  toMLGoal. wf_auto2.
  epose proof (Ex_gen Γ (! ⌈patt_free_evar ev_x⌉) ⊥ ev_x i _ _).
  unfold exists_quantify in H. cbn in H. case_match. 2: congruence.
  mlIntro "H". mlApplyMeta H. fold (patt_defined b0) (patt_not ⌈b0⌉).
  mlExact "H".
    Unshelve.
    * eapply pile_trans. 2: exact PI. try_solve_pile.
    * set_solver.
    * toMLGoal. wf_auto2. mlIntro "H". mlApply "H".
      pose proof (defined_evar _ ev_x HΓ).
      eapply liftPi in H. mlExactMeta H.
      eapply pile_trans. 2: exact PI.
      apply pile_evs_subseteq. set_solver.
Defined.

Lemma membership_refl {Σ : Signature} {syntax : Syntax}:
  forall Γ t, well_formed t -> 
  theory ⊆ Γ-> Γ ⊢i ((ex , t =ml b0) ---> t ∈ml t) using AnyReasoning.
Proof.
  intros Γ t WF HΓ.
  unfold "∈ml". toMLGoal. wf_auto2.
  mlIntro "mH".
  pose proof (and_singleton Γ t WF). apply useAnyReasoning in H.
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

Close Scope ml_scope.
Close Scope string_scope.
Close Scope list_scope.
