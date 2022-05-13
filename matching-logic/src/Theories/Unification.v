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

  Lemma patt_or_total :
    forall Γ φ ψ,
    theory ⊆ Γ ->
    well_formed φ -> well_formed ψ ->
    Γ ⊢  ⌊ φ ⌋ or ⌊ ψ ⌋ ---> ⌊ φ or ψ ⌋.
  Proof.
    intros Γ φ ψ HΓ Wf1 Wf2. toMyGoal. wf_auto2.
    mgIntro. mgDestructOr 0.
    * pose proof (@disj_left_intro _ Γ φ ψ Wf1 Wf2) as H.
      apply floor_monotonic in H. 2-4: try wf_auto2.
      mgApplyMeta H. mgExactn 0.
    * pose proof (@disj_right_intro _ Γ φ ψ Wf1 Wf2) as H.
      apply floor_monotonic in H. 2-4: try wf_auto2.
      mgApplyMeta H. mgExactn 0.
  Defined.

  Lemma patt_defined_and:
    forall Γ φ ψ,
    theory ⊆ Γ ->
    well_formed φ -> well_formed ψ ->
    Γ ⊢ ⌈ φ and ψ ⌉ ---> ⌈ φ ⌉ and ⌈ ψ ⌉.
  Proof.
    intros Γ φ ψ HΓ Wf1 Wf2. toMyGoal. wf_auto2.
    unfold patt_and.
    mgRewrite (@defined_not_iff_not_total _ _ Γ (! φ or ! ψ) HΓ ltac:(wf_auto2)) at 1.
    do 2 mgIntro. mgApply 0. mgClear 0.
    mgApplyMeta (@patt_or_total _ (! φ) (! ψ) HΓ ltac:(wf_auto2) ltac:(wf_auto2)).
    mgDestructOr 0.
    * mgLeft. unfold patt_total.
      mgRewrite <- (@not_not_iff _ Γ φ Wf1) at 1. mgExactn 0.
    * mgRight. unfold patt_total.
      mgRewrite <- (@not_not_iff _ Γ ψ Wf2) at 1. mgExactn 0.
  Defined.

  Lemma patt_total_and:
    forall Γ φ ψ,
    theory ⊆ Γ ->
    well_formed φ -> well_formed ψ ->
    Γ ⊢ ⌊ φ and ψ ⌋ <---> ⌊ φ ⌋ and ⌊ ψ ⌋.
  Proof.
    intros Γ φ ψ HΓ Wf1 Wf2. toMyGoal. wf_auto2.
    mgSplitAnd.
    * unfold patt_and.
      mgRewrite <- (@def_propagate_not _ _ Γ (! φ or ! ψ) HΓ ltac:(wf_auto2)) at 1.
      mgIntro. mgIntro. mgApply 0.
      mgClear 0.
      mgRewrite (@ceil_compat_in_or _ _ Γ (! φ) (! ψ) HΓ ltac:(wf_auto2) ltac:(wf_auto2)) at 1.
      mgDestructOr 0.
      - mgLeft. mgRevert. unfold patt_total.
        mgRewrite <- (@not_not_iff _ Γ ⌈ ! φ ⌉ ltac:(wf_auto2)) at 1.
        mgIntro. mgExactn 0.
      - mgRight. mgRevert. unfold patt_total.
        mgRewrite <- (@not_not_iff _ Γ ⌈ ! ψ ⌉ ltac:(wf_auto2)) at 1.
        mgIntro. mgExactn 0.
    * mgIntro. mgDestructAnd 0.
      unfold patt_and.
      mgRewrite <- (@def_propagate_not _ _ Γ (! φ or ! ψ) HΓ ltac:(wf_auto2)) at 1.
      mgRewrite (@ceil_compat_in_or _ _ Γ (! φ) (! ψ) HΓ ltac:(wf_auto2) ltac:(wf_auto2)) at 1.
      mgIntro. mgDestructOr 2.
      - mgRevert. mgExactn 0.
      - mgRevert. mgExactn 1.
  Defined.

  Lemma defined_variables_equal :
    forall x y Γ,
    theory ⊆ Γ ->
    Γ ⊢ ⌈ patt_free_evar y and patt_free_evar x ⌉ ---> patt_free_evar y =ml patt_free_evar x.
  Proof.
    intros x y Γ HΓ.
    toMyGoal. wf_auto2.
    unfold patt_equal, patt_iff.
    pose proof (@patt_total_and _ (patt_free_evar y ---> patt_free_evar x)
                                  (patt_free_evar x ---> patt_free_evar y) HΓ ltac:(wf_auto2) ltac:(wf_auto2)) as H.
    apply pf_iff_proj2 in H. 2-3: wf_auto2.
    mgIntro.
    mgApplyMeta H. clear H.
    mgIntro. mgDestructOr 1.
    * mgApply 1. mgClear 1. mgIntro.
      pose proof (H := @ProofMode.nimpl_eq_and _ Γ (patt_free_evar y) (patt_free_evar x)
                    ltac:(wf_auto2) ltac:(wf_auto2)).
      epose proof (H0 := @prf_equiv_congruence _ Γ 
      _ _ {| pcEvar := x; pcPattern := ⌈ patt_free_evar x ⌉  |} ltac:(wf_auto2) H).
      cbn in H0. case_match. 2: congruence.
      apply pf_iff_proj1 in H0. 2-3: wf_auto2.
      mgApplyMeta H0 in 1.
      (* TODO: it is increadibly inconvienient to define concrete contexts *)
      pose proof (H1 := @Singleton_ctx _ Γ 
             (@ctx_app_r _ (patt_sym (Definedness_Syntax.inj definedness)) box 
                  ltac:(wf_auto2))
             (@ctx_app_r _ (patt_sym (Definedness_Syntax.inj definedness)) box 
                  ltac:(wf_auto2)) (patt_free_evar x) y ltac:(wf_auto2)).
      mgApplyMeta H1. simpl. mgSplitAnd. mgExactn 0. mgExactn 1.
    * mgApply 1. mgClear 1. mgIntro.
      pose proof (H := @ProofMode.nimpl_eq_and _ Γ (patt_free_evar x) (patt_free_evar y)
                    ltac:(wf_auto2) ltac:(wf_auto2)).
      epose proof (H0 := @prf_equiv_congruence _ Γ 
      _ _ {| pcEvar := x; pcPattern := ⌈ patt_free_evar x ⌉  |} ltac:(wf_auto2) H).
      cbn in H0. case_match. 2: congruence.
      apply pf_iff_proj1 in H0. 2-3: wf_auto2.
      mgApplyMeta H0 in 1.
      (* TODO: mgRewriteBy does not work for free evars :( *)
      pose proof (H1 := @patt_and_comm _ Γ (patt_free_evar y) (patt_free_evar x) ltac:(wf_auto2) ltac:(wf_auto2)).
      epose proof (H2 := @prf_equiv_congruence _ Γ 
      _ _ {| pcEvar := x; pcPattern := ⌈ patt_free_evar x ⌉  |} ltac:(wf_auto2) H1).
      cbn in H2. case_match. 2: congruence.
      apply pf_iff_proj1 in H2. 2-3: wf_auto2.
      mgAssert (⌈ patt_free_evar x and patt_free_evar y ⌉). wf_auto2.
      mgClear 1. mgApplyMeta H2. mgExactn 0.
      (* TODO: it is increadibly inconvienient to define concrete contexts *)
      pose proof (@Singleton_ctx _ Γ 
             (@ctx_app_r _ (patt_sym (Definedness_Syntax.inj definedness)) box 
                  ltac:(wf_auto2))
             (@ctx_app_r _ (patt_sym (Definedness_Syntax.inj definedness)) box 
                  ltac:(wf_auto2)) (patt_free_evar y) x ltac:(wf_auto2)) as H3.
      mgApplyMeta H3. simpl. mgSplitAnd. mgExactn 2. mgExactn 1.
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
    Check forall_functional_subst.
    epose proof (@forall_functional_subst _ _ (⌈ b0 and φ' ⌉ ---> ⌊ b0 <---> φ' ⌋) φ 
                    Γ HΓ ltac:(wf_auto2) ltac:(wf_auto2) _ ltac:(wf_auto2)) as H.
    Unshelve. 2: { cbn. case_match; auto. apply andb_true_iff in Wf2 as [_ Wf2].
                   apply andb_true_iff in Wf2 as [_ Wf2].
                   (* NOTE: using eapply breaks the proof *)
                   apply well_formed_closed_ex_aux_ind with (ind_evar2 := 1)in Wf2.
                   rewrite Wf2. auto. lia. } (* TODO: this should be auto... *)
    simpl in H.
    repeat rewrite bevar_subst_not_occur in H. wf_auto2.
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
    Search patt_in ML_proof_system.

    toMyGoal. wf_auto2. Search "∈ml".
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
    Search patt_free_evar ML_proof_system.
    mgIntro.
    mgAssert (⌈ φ and φ' ⌉). wf_auto2.
    Search patt_defined ML_proof_system.
    (* Why can we only mgApplyMeta here, and not after mgRevert? *)
    mgApplyMeta (@phi_impl_defined_phi Σ syntax Γ (φ and φ') HΓ ltac:(wf_auto2)).
    mgExactn 0.
    replace (⌈ φ and φ' ⌉) with (φ ∈ml φ') by auto.
    mgDestructAnd 0. mgSplitAnd.
    * mgExactn 0.
    * mgApplyMeta (membership_imp_equal HΓ MF Wf1 Wf2 Func1 Func2).
      mgExactn 2.
  Defined.
