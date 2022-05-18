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

From MatchingLogic Require Import Syntax NamedAxioms DerivedOperators_Syntax ProofSystem ProofMode IndexManipulation Substitution.
From MatchingLogic.Theories Require Import Definedness_Syntax Definedness_ProofSystem.
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
    {syntax : Syntax}.

  Lemma Prop₃_left: forall Γ φ φ',
      theory ⊆ Γ -> mu_free φ ->
      well_formed φ -> well_formed φ' ->
      Γ ⊢ (φ and (φ' =ml φ)) ---> (φ and φ').
  Proof.
    intros Γ φ φ' SubTheory Mufree Wf1 Wf2.
    toMyGoal. wf_auto2.
    mgIntro. mgDestructAnd 0.
    mgRewriteBy 1 at 1. auto. wf_auto.
    mgSplitAnd; mgExactn 0.
  Defined.

  Lemma membership_imp_equal :
    forall Γ φ φ',
      theory ⊆ Γ -> mu_free φ' ->
      well_formed φ -> well_formed φ' ->
      Γ ⊢ (ex , (φ =ml b0)) ->
      Γ ⊢ (ex , (φ' =ml b0)) ->
      Γ ⊢ (φ ∈ml φ') ---> (φ =ml φ').
  Proof.
    intros Γ φ φ' HΓ Mufree Wf1 Wf2 Funφ Funφ'.
    unfold patt_in, patt_equal.
    toMyGoal. wf_auto2.

    (* TODO: proposal: functional_reasoning tactic, which replaces a pattern with a 
                       free variable *)
    epose proof (@forall_functional_subst _ _ (⌈ b0 and φ' ⌉ ---> ⌊ b0 <---> φ' ⌋) φ 
                    Γ HΓ ltac:(wf_auto2) ltac:(wf_auto2) _ ltac:(wf_auto2)) as H.
    Unshelve. 2: { cbn. case_match; auto. apply andb_true_iff in Wf2 as [_ Wf2].
                   apply andb_true_iff in Wf2 as [_ Wf2].
                   (* NOTE: using eapply breaks the proof *)
                   apply well_formed_closed_ex_aux_ind with (ind_evar2 := 1)in Wf2.
                   rewrite Wf2. auto. lia. } (* TODO: this should be auto... *)
    simpl in H.
    repeat rewrite bevar_subst_not_occur in H. wf_auto2. (* TODO: cast_proof? *)
    mgApplyMeta H. clear H.
    mgSplitAnd. 2: fromMyGoal; wf_auto2.
    epose proof (@forall_functional_subst _ _ (all, (⌈ b0 and b1 ⌉ ---> ⌊ b0 <---> b1 ⌋)) φ'
                    Γ HΓ ltac:(wf_auto2) ltac:(wf_auto2) _ ltac:(wf_auto2)) as H.
    Unshelve. 2: { cbn. do 2 case_match; auto; lia. }
    mgApplyMeta H. clear H.

    mgSplitAnd. 2: fromMyGoal; wf_auto2.
    remember (fresh_evar patt_bott) as x.
    remember (fresh_evar (patt_free_evar x)) as y.
    assert (x <> y) as XY.
    { intro. apply x_eq_fresh_impl_x_notin_free_evars in Heqy.
      subst. set_solver. } (* TODO: this should be auto... *)
    fromMyGoal. wf_auto2.


   (* TODO: mgIntro for supporting 'all' *)


    pose proof (@universal_generalization _ Γ (all , (⌈ b0 and patt_free_evar x ⌉ ---> ⌊ b0 <---> patt_free_evar x ⌋)) x ltac:(wf_auto2)) as H1.
    simpl in H1. case_match; auto. apply H1. clear H1.
    pose proof (@universal_generalization _ Γ (⌈ (patt_free_evar y) and (patt_free_evar x) ⌉ ---> ⌊ (patt_free_evar y) <---> (patt_free_evar x) ⌋) y ltac:(wf_auto2)) as H1.
    simpl in H1. clear H Heqs. do 2 case_match; auto; try congruence.
    2-3: exfalso; apply n; reflexivity. (* TODO: congruence does not work... *)
    apply H1. clear H1.
    now apply defined_variables_equal.
  Defined.

  Lemma functional_pattern_defined :
    forall Γ φ, theory ⊆ Γ -> well_formed φ ->
       Γ ⊢ (ex , (φ =ml b0)) ---> ⌈ φ ⌉.
  Proof.
    intros Γ φ HΓ Wf.
    toMyGoal. wf_auto2.
    mgIntro.
    mgApplyMeta (@forall_functional_subst _ _ ⌈ b0 ⌉ φ _ HΓ ltac:(wf_auto2)
                 ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2)).
    mgSplitAnd.
    * mgClear 0. fromMyGoal. wf_auto2.
      remember (fresh_evar patt_bott) as x.
      pose proof (@universal_generalization _ Γ ⌈patt_free_evar x⌉ x ltac:(wf_auto2)) 
        as H1.
      cbn in H1. case_match. 2: congruence. apply H1.
      now apply defined_evar.
    * mgExactn 0.
  Defined.

  Lemma equal_imp_membership :
    forall Γ φ φ',
      theory ⊆ Γ -> mu_free φ' ->
      well_formed φ -> well_formed φ' ->
      Γ ⊢ ⌈ φ' ⌉ ->
      Γ ⊢ (φ =ml φ') ---> (φ ∈ml φ').
  Proof.
    intros Γ φ φ' HΓ MF WF1 WF2 Def.
    toMyGoal. wf_auto2.
    mgIntro.
    mgRewriteBy 0 at 1; cbn; wf_auto2.
      mgClear 0. unfold patt_in.
      assert (Γ ⊢ ( φ' and φ' <---> φ')) as H1.
      {
        toMyGoal. wf_auto2.
        mgSplitAnd; mgIntro.
        - mgDestructAnd 0. mgExactn 0.
        - mgSplitAnd; mgExactn 0.
      }
      now mgRewrite H1 at 1.
  Defined.

  Lemma membership_equal_equal :
    forall Γ φ φ',
      theory ⊆ Γ -> mu_free φ' ->
      well_formed φ -> well_formed φ' ->
      Γ ⊢ (ex , (φ =ml b0)) ->
      Γ ⊢ (ex , (φ' =ml b0)) ->
      Γ ⊢ (φ ∈ml φ') =ml (φ =ml φ').
  Proof.
    intros Γ φ φ' HΓ Mufree Wf1 Wf2 Func1 Func2.
    unfold patt_equal at 1.

    toMyGoal. wf_auto2.
    mgIntro.
    mgApplyMeta (@bott_not_defined _ _ Γ).
    fromMyGoal. wf_auto2.
    
    apply ceil_monotonic; auto. wf_auto2.

    toMyGoal. wf_auto2.
    mgApplyMeta (@not_not_intro _ Γ ((φ ∈ml φ' <---> φ =ml φ' ))
                    ltac:(wf_auto2)).
    mgSplitAnd; mgIntro.
    * mgApplyMeta (membership_imp_equal HΓ Mufree Wf1 Wf2 Func1 Func2). mgExactn 0.
    * mgApplyMeta (equal_imp_membership HΓ Mufree Wf1 Wf2 _). mgExactn 0.
      Unshelve.
      toMyGoal. wf_auto2.
      now mgApplyMeta (functional_pattern_defined HΓ Wf2).
  Defined.

  Lemma Prop₃_right : forall Γ φ φ',
      theory ⊆ Γ ->
      well_formed φ -> well_formed φ' -> mu_free φ' ->
      Γ ⊢ (ex , (φ =ml b0)) ->
      Γ ⊢ (ex , (φ' =ml b0)) ->
      Γ ⊢ (φ and φ') ---> (φ and (φ =ml φ')).
  Proof.
    intros Γ φ φ' HΓ Wf1 Wf2 MF Func1 Func2.
    toMyGoal. wf_auto2.
    mgIntro.
    mgAssert (⌈ φ and φ' ⌉). wf_auto2.
    (* Why can we only mgApplyMeta here, and not after mgRevert? *)
    mgApplyMeta (@phi_impl_defined_phi Σ syntax Γ (φ and φ') HΓ ltac:(wf_auto2)).
    mgExactn 0.
    replace (⌈ φ and φ' ⌉) with (φ ∈ml φ') by auto.
    mgDestructAnd 0. mgSplitAnd.
    * mgExactn 0.
    * mgApplyMeta (membership_imp_equal HΓ MF Wf1 Wf2 Func1 Func2).
      mgExactn 2.
  Defined.

  Corollary delete : forall φ φ' Γ,
    well_formed φ -> well_formed φ'
  ->
    Γ ⊢ φ and φ' =ml φ' ---> φ.
  Proof.
    intros φ φ' Γ WF1 WF2.
    toMyGoal. wf_auto2.
    mgIntro. mgDestructAnd 0. mgExactn 0.
  Defined.

  Lemma free_evar_subst_id :
    forall φ x, φ.[[evar: x ↦ patt_free_evar x]] = φ.
  Proof.
    induction φ; intros x'; simpl; auto.
    * case_match; subst; auto.
    * rewrite IHφ1. now rewrite IHφ2.
    * rewrite IHφ1. now rewrite IHφ2.
    * now rewrite IHφ.
    * now rewrite IHφ.
  Qed.

  Theorem elimination : forall φ φ' x Γ, x ∉ free_evars φ ->
    theory ⊆ Γ -> mu_free φ ->
    well_formed_closed_ex_aux φ 1 ->
    well_formed_closed_mu_aux φ 0 ->
    well_formed φ' ->
    Γ ⊢ φ.[evar: 0 ↦ patt_free_evar x] and φ' =ml patt_free_evar x ---> 
        φ.[evar: 0 ↦ φ'] and φ' =ml patt_free_evar x.
  Proof.
    intros φ φ' x Γ NotIn HΓ MF WFp1 WFp2 WF2.
    assert (well_formed (φ.[evar:0↦φ'])) as WFF.
    { wf_auto2. apply bevar_subst_positive; auto.
        now apply mu_free_wfp. }
    assert (well_formed (φ.[evar:0↦patt_free_evar x])) as WFFF. {
      wf_auto2. apply bevar_subst_positive; auto.
        now apply mu_free_wfp. }
    toMyGoal. wf_auto2.
    mgIntro. mgDestructAnd 0. mgSplitAnd. 2: mgExactn 1.
    epose proof (@equality_elimination_basic _ _ Γ φ' (patt_free_evar x)
            {|pcEvar := x; pcPattern := φ.[evar: 0 ↦ patt_free_evar x]|} 
            HΓ WF2 ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2)).
    cbn in H.
    pose proof (@bound_to_free_variable_subst _ φ x 1 0 φ' ltac:(lia) ltac:(wf_auto2) WFp1 NotIn) as H0.
    unfold evar_open in H0. rewrite <- H0 in H. (* TODO: cast_proof? *)
    rewrite free_evar_subst_id in H.
    assert (Γ ⊢ φ.[evar:0↦φ'] <---> φ.[evar:0↦patt_free_evar x] --->
                φ.[evar:0↦patt_free_evar x] ---> φ.[evar:0↦φ']) as Hiff. {
      toMyGoal; wf_auto2.
      mgIntro. unfold patt_iff. mgDestructAnd 0. mgExactn 1.
    }
    epose proof (@syllogism_intro _ Γ _ _ _ _ _ _ H Hiff).
    (* TODO: mgApplyMeta buggy?
             Tries to match the longest conclusion, not the shortest *)
    apply reorder_meta in H1.
    mgRevert. mgApplyMeta H1. mgExactn 0.
    Unshelve. all: wf_auto2.
    cbn. rewrite mu_free_bevar_subst; wf_auto2.
  Defined.

  Theorem elimination_reverse : forall φ φ' x Γ, x ∉ free_evars φ ->
    theory ⊆ Γ -> mu_free φ ->
    well_formed_closed_ex_aux φ 1 ->
    well_formed_closed_mu_aux φ 0 ->
    well_formed φ' ->
    Γ ⊢ φ.[evar: 0 ↦ φ'] and φ' =ml patt_free_evar x --->
        φ.[evar: 0 ↦ patt_free_evar x] and φ' =ml patt_free_evar x.
  Proof.
    intros φ φ' x Γ NotIn HΓ MF WFp1 WFp2 WF2.
    assert (well_formed (φ.[evar:0↦φ'])) as WFF.
    { wf_auto2. apply bevar_subst_positive; auto.
        now apply mu_free_wfp. }
    assert (well_formed (φ.[evar:0↦patt_free_evar x])) as WFFF. {
      wf_auto2. apply bevar_subst_positive; auto.
        now apply mu_free_wfp. }
    toMyGoal. wf_auto2.
    mgIntro. mgDestructAnd 0. mgSplitAnd. 2: mgAssumption.
    epose proof (@equality_elimination_basic _ _ Γ φ' (patt_free_evar x)
            {|pcEvar := x; pcPattern := φ.[evar: 0 ↦ patt_free_evar x]|} 
            HΓ WF2 ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2)).
    cbn in H.
    pose proof (@bound_to_free_variable_subst _ φ x 1 0 φ' ltac:(lia) ltac:(wf_auto2) WFp1 NotIn) as H0.
    unfold evar_open in H0. rewrite <- H0 in H. (* TODO: cast_proof? *)
    rewrite free_evar_subst_id in H.
    assert (Γ ⊢ φ.[evar:0↦φ'] <---> φ.[evar:0↦patt_free_evar x] --->
                φ.[evar:0↦φ'] ---> φ.[evar:0↦patt_free_evar x]) as Hiff. {
      toMyGoal; wf_auto2.
      mgIntro. unfold patt_iff. mgDestructAnd 0. mgExactn 0.
    }
    epose proof (@syllogism_intro _ Γ _ _ _ _ _ _ H Hiff).
    (* TODO: mgApplyMeta buggy?
             Tries to match the longest conclusion, not the shortest *)
    apply reorder_meta in H1.
    mgRevert. mgApplyMeta H1. mgExactn 0.
    Unshelve. all: wf_auto2.
    cbn. rewrite mu_free_bevar_subst; wf_auto2.
  Defined.




  (**
     Should be a consequence of the injectivity axiom:

      f(x₁,...,xₙ) = f(x₁',...,xₙ') → x₁ = x₁' ∧ ... ∧ xₙ = xₙ'

     The question is, why can we assume this axiom?
  *)
  Definition application_chain (φ : Pattern) (φs : list Pattern) : Pattern :=
    fold_left (fun Acc φ => patt_app Acc φ) φs φ.

  Theorem application_equal : forall φs ψ φ's Γ,
    length φs = length φ's ->
    well_formed ψ -> (* Forall well_formed φs -> Forall well_formed φ's *)
    (forall i, i < length φs -> well_formed (nth i φs ⊥)) ->
    (forall i, i < length φ's -> well_formed (nth i φ's ⊥))
  ->
    Γ ⊢ application_chain ψ φs =ml application_chain ψ φ's --->
         fold_right (fun '(x, y) Acc => Acc and x =ml y) Top (zip φs φ's).
  Proof.
    induction φs;
    intros ψ φ's Γ Len WF WFs1 WFs2.
    * apply eq_sym, length_zero_iff_nil in Len. subst. cbn.
      toMyGoal. wf_auto2. mgIntro. mgClear 0. (* TODO: mgExact for meta theorems *)
      fromMyGoal. wf_auto2.
      apply (top_holds Γ).
    * destruct φ's. simpl in Len. congruence.
      simpl in Len. inversion Len. clear Len.
      cbn.
      admit.
  Abort.

End ProofSystemTheorems.