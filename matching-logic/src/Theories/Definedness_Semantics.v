From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Equations.Prop.Equations.

From Coq Require Import String Ensembles Setoid.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.Classical_Prop.
From Coq.Logic Require Import FunctionalExtensionality Eqdep_dec.
From Coq.Classes Require Import Morphisms_Prop.
From Coq.Unicode Require Import Utf8.
From Coq.micromega Require Import Lia.

From MatchingLogic
Require Import
  Syntax
  NamedAxioms
  Semantics
  DerivedOperators_Syntax
  DerivedOperators_Semantics
  IndexManipulation
  PrePredicate
.
From MatchingLogic.Utils Require Import stdpp_ext.

From stdpp Require Import base fin_sets sets propset proof_irrel option list.

Import extralibrary.

Require Import MatchingLogic.Theories.Definedness_Syntax.

Import MatchingLogic.Syntax.Notations.
Import MatchingLogic.Semantics.Notations.
Import MatchingLogic.DerivedOperators_Syntax.Notations.
Import MatchingLogic.Syntax.BoundVarSugar.

Import Definedness_Syntax.Notations.

Section definedness.
  Context
    {Σ : Signature}
    {syntax : Syntax}
  .

  Let sym (s : Symbols) : Pattern :=
    @patt_sym Σ (inj s).
  
  Lemma definedness_model_application :
    forall (M : @Model Σ) (ρₑ : @EVarVal Σ M) (ρₛ : @SVarVal Σ M),
      M ⊨ᵀ theory ->
      forall (m: Domain M),
                 (app_ext (pattern_interpretation ρₑ ρₛ (sym definedness)) {[m]}) = ⊤.
  Proof.
    intros.
    unfold app_ext.
    rewrite -> set_eq_subseteq.
    split.
    { apply top_subseteq. }
    rewrite -> elem_of_subseteq.
    intros x _.
    unfold theory in H.
    pose proof (H' := proj1 (satisfies_theory_iff_satisfies_named_axioms named_axioms M)).
    specialize (H' H AxDefinedness).
    simpl in H'.
    clear H. rename H' into H.
    unfold satisfies_model in H.
    remember (update_evar_val ev_x m ρₑ) as ρₑ'.
    specialize (H ρₑ' ρₛ).
    rewrite -> set_eq_subseteq in H.
    destruct H as [_ H].
    rewrite -> elem_of_subseteq in H.
    specialize (H x).
    feed specialize H.
    { apply elem_of_top'. }
    unfold patt_defined in H.
    rewrite -> pattern_interpretation_app_simpl in H.
    rewrite -> pattern_interpretation_sym_simpl in H.
    unfold sym.
    unfold p_x in H.
    rewrite -> pattern_interpretation_free_evar_simpl in H.
    rewrite -> Heqρₑ' in H.
    unfold update_evar_val in H. simpl in H.
    destruct (decide (ev_x = ev_x)).
    2: { contradiction. }
    unfold app_ext in H. unfold In in H.
    destruct H as [m1 [m2 Hm1m2] ].
    destruct Hm1m2. destruct H0.
    inversion H0. clear H0. simpl in H2. subst.
    exists m1. exists m2. split. 2: { split. 2: { apply H1. } constructor. }
    rewrite -> pattern_interpretation_sym_simpl. apply H.
  Qed.

  Lemma definedness_not_empty_1 : forall (M : @Model Σ),
      M ⊨ᵀ theory ->
      forall (ϕ : Pattern) (ρₑ : @EVarVal Σ M) (ρₛ : @SVarVal Σ M),
        (@pattern_interpretation Σ M ρₑ ρₛ ϕ) <> ∅ ->
        (@pattern_interpretation Σ M ρₑ ρₛ ⌈ ϕ ⌉ ) = ⊤.
  Proof.
    intros.
    pose (H' := stdpp_ext.Not_Empty_Contains_Elements (pattern_interpretation ρₑ ρₛ ϕ) H0).
    destruct H'.
    unfold patt_defined.
    rewrite -> pattern_interpretation_app_simpl.
    
    pose proof (H'' := @definedness_model_application M ρₑ ρₛ H x).
    unfold sym in H''.
    rewrite -> set_eq_subseteq in H''.
    destruct H'' as [_ H''].
    assert (Hincl: {[x]} ⊆ (pattern_interpretation ρₑ ρₛ ϕ) ).
    { rewrite -> elem_of_subseteq. intros.  inversion H2. subst. assumption. }

    pose proof (Hincl' := @app_ext_monotonic_r
                            Σ
                            M
                            (pattern_interpretation ρₑ ρₛ (patt_sym (inj definedness)))
                            {[x]}
                            (pattern_interpretation ρₑ ρₛ ϕ)
                            Hincl
               ).

    rewrite -> set_eq_subseteq.
    split.
    { apply top_subseteq. }
    eapply transitivity.
    apply H''.
    assumption.
  Qed.

  Lemma definedness_empty_1 : forall (M : @Model Σ),
      M ⊨ᵀ theory ->
      forall (ϕ : Pattern) (ρₑ : @EVarVal Σ M) (ρₛ : @SVarVal Σ M),
      @pattern_interpretation Σ M ρₑ ρₛ ϕ = ∅ ->
      @pattern_interpretation Σ M ρₑ ρₛ ⌈ ϕ ⌉ = ∅.
  Proof.
    intros M H ϕ ρₑ ρₛ H0. unfold patt_defined.
    rewrite -> pattern_interpretation_app_simpl.
    rewrite -> H0.
    apply app_ext_bot_r.
  Qed.

  Theorem modus_tollens: forall (P Q : Prop), (P -> Q) -> ~Q -> ~P.
  Proof. auto. Qed.

  Lemma definedness_empty_2 : forall (M : @Model Σ),
      M ⊨ᵀ theory ->
      forall (ϕ : Pattern) (ρₑ : @EVarVal Σ M) (ρₛ : @SVarVal Σ M),
        @pattern_interpretation Σ M ρₑ ρₛ ⌈ ϕ ⌉ = ∅ ->
        @pattern_interpretation Σ M ρₑ ρₛ ϕ = ∅.
  Proof.
    intros M H ϕ ρₑ ρₛ H0.
    pose proof (H1 := @empty_impl_not_full Σ M _ H0).
    pose proof (H2 := @modus_tollens _ _ (@definedness_not_empty_1 M H ϕ ρₑ ρₛ) H1).
    apply NNPP in H2. apply H2.
  Qed.

  Lemma definedness_not_empty_2 : forall (M : @Model Σ),
      M ⊨ᵀ theory ->
      forall (ϕ : Pattern) (ρₑ : @EVarVal Σ M) (ρₛ : @SVarVal Σ M),
        @pattern_interpretation Σ M ρₑ ρₛ ⌈ ϕ ⌉ = ⊤ ->
        @pattern_interpretation Σ M ρₑ ρₛ ϕ <> ∅.
  Proof.
    intros M H ϕ ρₑ ρₛ H0.
    pose proof (H1 := full_impl_not_empty H0).
    exact (@modus_tollens _ _ (@definedness_empty_1 M H ϕ ρₑ ρₛ) H1).
  Qed.

  Lemma totality_not_full : forall (M : @Model Σ),
      M ⊨ᵀ theory ->
      forall (ϕ : Pattern) (ρₑ : @EVarVal Σ M) (ρₛ : @SVarVal Σ M),
        @pattern_interpretation Σ M ρₑ ρₛ ϕ <> ⊤ ->
        @pattern_interpretation Σ M ρₑ ρₛ ⌊ ϕ ⌋ = ∅.
  Proof.
    intros.
    assert (Hnonempty : pattern_interpretation ρₑ ρₛ (patt_not ϕ) <> ∅).
    { unfold not. unfold not in H0. intros. rewrite -> pattern_interpretation_not_simpl in H1.
      apply H0. clear H0.
      rewrite -> set_eq_subseteq.
      split.
      { apply top_subseteq. }
      rewrite -> complement_empty_iff_full in H1.
      rewrite H1.
      apply top_subseteq.
    }
    unfold patt_total. rewrite -> pattern_interpretation_not_simpl.
    rewrite -> complement_empty_iff_full.

    apply definedness_not_empty_1.
    { apply H. }
    apply Hnonempty.
  Qed.

  Lemma totality_full : forall (M : @Model Σ),
      M ⊨ᵀ theory ->
      forall (ϕ : Pattern) (ρₑ : @EVarVal Σ M) (ρₛ : @SVarVal Σ M),
        @pattern_interpretation Σ M ρₑ ρₛ ϕ = ⊤ ->
        @pattern_interpretation Σ M ρₑ ρₛ ⌊ ϕ ⌋ = ⊤.
  Proof.
    intros M H ϕ ρₑ ρₛ H0.
    unfold patt_total.
    rewrite -> pattern_interpretation_not_simpl.
    assert(H1: pattern_interpretation ρₑ ρₛ (patt_not ϕ) = ∅).
    { rewrite -> pattern_interpretation_not_simpl.
      rewrite -> H0.
      clear. set_solver.
    }

    pose proof (H2 := @definedness_empty_1 M H (patt_not ϕ) ρₑ ρₛ H1).
    rewrite -> H2.
    clear. set_solver.
  Qed.

  Lemma totality_result_empty : forall (M : @Model Σ),
      M ⊨ᵀ theory ->
      forall (ϕ : Pattern) (ρₑ : @EVarVal Σ M) (ρₛ : @SVarVal Σ M),
        @pattern_interpretation Σ M ρₑ ρₛ ⌊ ϕ ⌋ = ∅ ->
        @pattern_interpretation Σ M ρₑ ρₛ ϕ <> ⊤.
  Proof.
    intros M H ϕ ρₑ ρₛ H0.
    pose proof (H1 := empty_impl_not_full H0).
    pose proof (H2 := @modus_tollens _ _ (@totality_full M H ϕ ρₑ ρₛ) H1).
    apply H2.
  Qed.

  Lemma totality_result_nonempty : forall (M : @Model Σ),
      M ⊨ᵀ theory ->
      forall (ϕ : Pattern) (ρₑ : @EVarVal Σ M) (ρₛ : @SVarVal Σ M),
        @pattern_interpretation Σ M ρₑ ρₛ ⌊ ϕ ⌋ <> ∅ ->
        @pattern_interpretation Σ M ρₑ ρₛ ϕ = ⊤.
  Proof.
    intros M H ϕ ρₑ ρₛ H0.
    pose proof (H2 := @modus_tollens _ _ (@totality_not_full M H ϕ ρₑ ρₛ) H0).
    apply NNPP in H2. apply H2.
  Qed.
  
  Lemma equal_iff_both_subseteq : forall (M : @Model Σ),        
      M ⊨ᵀ theory ->
      forall (ϕ1 ϕ2 : Pattern) (ρₑ : @EVarVal Σ M) (ρₛ : @SVarVal Σ M),
        @pattern_interpretation Σ M ρₑ ρₛ (ϕ1 =ml ϕ2) = ⊤ <->
        (
          @pattern_interpretation Σ M ρₑ ρₛ (patt_subseteq ϕ1 ϕ2) = ⊤ /\
          @pattern_interpretation Σ M ρₑ ρₛ (patt_subseteq ϕ2 ϕ1) = ⊤).
  Proof.
    intros M H ϕ1 ϕ2 ρₑ ρₛ.
    split.
    - intros H0.
      unfold patt_equal in H0.
      apply full_impl_not_empty in H0.
      apply (@totality_result_nonempty _ H) in H0.
      unfold "<--->" in H0.
      rewrite -> pattern_interpretation_and_simpl in H0.
      rewrite -> intersection_full_iff_both_full in H0.
      destruct H0 as [H1 H2].
      unfold patt_subseteq.
      apply (@totality_full _ H) in H1.
      apply (@totality_full _ H) in H2.
      split; assumption.
    - intros [H0 H1].
      unfold patt_subseteq.
      apply full_impl_not_empty in H0.
      apply full_impl_not_empty in H1.
      apply (@totality_result_nonempty _ H) in H0.
      apply (@totality_result_nonempty _ H) in H1.
      unfold patt_equal.
      apply (@totality_full _ H).
      unfold "<--->".
      rewrite -> pattern_interpretation_and_simpl.
      rewrite -> H0.
      rewrite -> H1.
      clear. set_solver.
  Qed.

  Lemma subseteq_iff_interpr_subseteq : forall (M : @Model Σ),
      M ⊨ᵀ theory ->
      forall (ϕ1 ϕ2 : Pattern) (ρₑ : @EVarVal Σ M) (ρₛ : @SVarVal Σ M),
        @pattern_interpretation Σ M ρₑ ρₛ (patt_subseteq ϕ1 ϕ2) = ⊤ <->
        (@pattern_interpretation Σ M ρₑ ρₛ ϕ1)
          ⊆ (@pattern_interpretation Σ M ρₑ ρₛ ϕ2).
  Proof.
    intros M H ϕ1 ϕ2 ρₑ ρₛ.
    split.
    - intros H0.
      unfold patt_subseteq in H0.
      apply full_impl_not_empty in H0.
      apply (@totality_result_nonempty _ H) in H0.
      rewrite -> pattern_interpretation_imp_simpl in H0.
      rewrite -> set_eq_subseteq in H0.
      destruct H0 as [_ H0].
      rewrite -> elem_of_subseteq in H0.
      intros x H1. specialize (H0 x).
      feed specialize H0.
      { apply elem_of_top'. }
      remember (pattern_interpretation ρₑ ρₛ ϕ1) as Xϕ1.
      remember (pattern_interpretation ρₑ ρₛ ϕ2) as Xϕ2.
      clear -H0 H1.
      set_solver.
    - intros H0.
      unfold patt_subseteq.
      apply (@totality_full _ H).
      rewrite -> pattern_interpretation_imp_simpl.
      rewrite -> set_eq_subseteq.
      split.
      { apply top_subseteq. }
      rewrite -> elem_of_subseteq.
      intros x _. specialize (H0 x).
      destruct (classic (x ∈ (pattern_interpretation ρₑ ρₛ ϕ1))).
      + right. auto.
      + left. apply elem_of_compl. assumption.
  Qed.
  
  Lemma equal_iff_interpr_same : forall (M : @Model Σ),
      M ⊨ᵀ theory ->
      forall (ϕ1 ϕ2 : Pattern) (ρₑ : @EVarVal Σ M) (ρₛ : @SVarVal Σ M),
        @pattern_interpretation Σ M ρₑ ρₛ (ϕ1 =ml ϕ2) = ⊤ <->
        @pattern_interpretation Σ M ρₑ ρₛ ϕ1
        = @pattern_interpretation Σ M ρₑ ρₛ ϕ2.
  Proof.
    intros M H ϕ1 ϕ2 ρₑ ρₛ.
    split.
    - intros H0.
      apply (@equal_iff_both_subseteq _ H) in H0.
      destruct H0 as [Hsub1 Hsub2].
      apply (@subseteq_iff_interpr_subseteq _ H) in Hsub1.
      apply (@subseteq_iff_interpr_subseteq _ H) in Hsub2.
      rewrite -> set_eq_subseteq.
      split; assumption.
    - intros H0.
      rewrite -> set_eq_subseteq in H0.
      destruct H0 as [Hincl1 Hincl2].
      apply (@subseteq_iff_interpr_subseteq _ H) in Hincl1.
      apply (@subseteq_iff_interpr_subseteq _ H) in Hincl2.
      apply equal_iff_both_subseteq. auto. split; auto.
  Qed.

  Lemma equal_refl : forall (M : @Model Σ),
      M ⊨ᵀ theory ->
      forall (ϕ : Pattern) (ρₑ : @EVarVal Σ M) (ρₛ : @SVarVal Σ M),
        @pattern_interpretation Σ M ρₑ ρₛ (patt_equal ϕ ϕ) = ⊤.
  Proof.
    intros M H ϕ ρₑ ρₛ.
    apply (@equal_iff_interpr_same _ H).
    auto.
  Qed.

  Lemma equal_sym : forall (M : @Model Σ),
      M ⊨ᵀ theory ->
      forall (ϕ1 ϕ2 : Pattern) (ρₑ : @EVarVal Σ M) (ρₛ : @SVarVal Σ M),
        @pattern_interpretation Σ M ρₑ ρₛ (ϕ1 =ml ϕ2) = ⊤ ->
        @pattern_interpretation Σ M ρₑ ρₛ (patt_equal ϕ2 ϕ1) = ⊤.
  Proof.
    intros M H ϕ1 ϕ2 ρₑ ρₛ H0.
    apply (@equal_iff_interpr_same _ H).
    apply (@equal_iff_interpr_same _ H) in H0.
    symmetry. auto.
  Qed.

  Lemma equal_trans : forall (M : @Model Σ),
      M ⊨ᵀ theory ->
      forall (ϕ1 ϕ2 ϕ3 : Pattern) (ρₑ : @EVarVal Σ M) (ρₛ : @SVarVal Σ M),
        @pattern_interpretation Σ M ρₑ ρₛ (ϕ1 =ml ϕ2) = ⊤ ->
        @pattern_interpretation Σ M ρₑ ρₛ (patt_equal ϕ2 ϕ3) = ⊤ ->
        @pattern_interpretation Σ M ρₑ ρₛ (patt_equal ϕ1 ϕ3) = ⊤.
  Proof.
    intros M H ϕ1 ϕ2 ϕ3 ρₑ ρₛ H0 H1.
    apply (@equal_iff_interpr_same _ H).
    apply (@equal_iff_interpr_same _ H) in H0.
    apply (@equal_iff_interpr_same _ H) in H1.
    rewrite -> H0. auto.
  Qed.

  Lemma free_evar_in_patt : forall (M : @Model Σ),
      M ⊨ᵀ theory ->
      forall (x : evar)(ϕ : Pattern) (ρₑ : @EVarVal Σ M) (ρₛ : @SVarVal Σ M),
        ((ρₑ x) ∈ (@pattern_interpretation Σ M ρₑ ρₛ ϕ)) <->
        @pattern_interpretation Σ M ρₑ ρₛ (patt_in (patt_free_evar x) ϕ) = ⊤.
  Proof.
    intros M H x ϕ ρₑ ρₛ.
    split.
    - intros H0.
      unfold patt_in.
      apply (@definedness_not_empty_1 _ H).
      intros Contra.
      apply Contains_Elements_Not_Empty in Contra. exact Contra.
      exists (ρₑ x).
      rewrite -> pattern_interpretation_and_simpl.
      split.
      + rewrite -> pattern_interpretation_free_evar_simpl. constructor.
      + assumption.
    - intros H0.
      unfold patt_in in H0.
      apply (@definedness_not_empty_2 _ H) in H0.
      unfold not in H0.
      assert (H0': (pattern_interpretation ρₑ ρₛ (patt_free_evar x and ϕ)) = ∅ -> False).
      { intros Contra. apply H0. auto. }
      apply Not_Empty_Contains_Elements in H0'.
      destruct H0' as [x0 H0'].
      rewrite -> pattern_interpretation_and_simpl in H0'.
      destruct H0'.
      rewrite -> pattern_interpretation_free_evar_simpl in H1.
      inversion H1. subst. assumption.
  Qed.
  
  Lemma T_predicate_defined : forall ϕ, T_predicate theory ⌈ ϕ ⌉.
  Proof.
    intros ϕ. unfold T_predicate. intros. unfold M_predicate. intros.
    pose proof (Hlr := classic ( pattern_interpretation ρₑ ρ ϕ = ∅ )).
    destruct Hlr.
    + apply definedness_empty_1 in H0. right. apply H0. apply H.
    + apply definedness_not_empty_1 in H0. left. apply H0. apply H.
  Qed.

  Lemma T_pre_predicate_defined : forall ϕ, T_pre_predicate theory ⌈ ϕ ⌉.
  Proof.
    intros ϕ. unfold T_pre_predicate. intros M HM.
    unfold M_pre_predicate. intros l Hwf.
    intros Hfa Hci Hwf'.
    unfold patt_defined. rewrite bcmcloseex_app.
    rewrite bcmcloseex_sym. apply T_predicate_defined.
    exact HM.
  Qed.

  Hint Resolve T_predicate_defined : core.

  Lemma T_predicate_total : forall ϕ, T_predicate theory ⌊ ϕ ⌋.
  Proof.
    intros ϕ. unfold patt_total.
    apply T_predicate_not.
    apply T_predicate_defined.
  Qed.

  Lemma T_pre_predicate_total : forall ϕ, T_pre_predicate theory ⌊ ϕ ⌋.
  Proof.
    intros ϕ. unfold patt_total.
    unfold T_pre_predicate. intros M HM.
    apply M_pre_predicate_not.
    apply T_pre_predicate_defined.
    exact HM.
  Qed.

  Hint Resolve T_predicate_total : core.

  Lemma T_predicate_subseteq : forall ϕ₁ ϕ₂, T_predicate theory (patt_subseteq ϕ₁ ϕ₂).
  Proof.
    intros ϕ₁ ϕ₂. unfold patt_subseteq. apply T_predicate_total.
  Qed.

  Lemma T_pre_predicate_subseteq : forall ϕ₁ ϕ₂, T_pre_predicate theory (patt_subseteq ϕ₁ ϕ₂).
  Proof.
    intros ϕ₁ ϕ₂. apply T_pre_predicate_total.
  Qed.

  Hint Resolve T_predicate_subseteq : core.
  
  Lemma T_predicate_equals : forall ϕ₁ ϕ₂, T_predicate theory (patt_equal ϕ₁ ϕ₂).
  Proof.
    intros ϕ₁ ϕ₂. unfold patt_equal. apply T_predicate_total.
  Qed.

  Lemma T_pre_predicate_equal : forall ϕ₁ ϕ₂, T_pre_predicate theory (patt_equal ϕ₁ ϕ₂).
  Proof.
    intros ϕ₁ ϕ₂. apply T_pre_predicate_total.
  Qed.

  Hint Resolve T_predicate_equals : core.

  Lemma T_predicate_in : forall ϕ₁ ϕ₂, T_predicate theory (patt_in ϕ₁ ϕ₂).
  Proof.
    intros ϕ₁ ϕ₂. unfold patt_equal. apply T_predicate_defined.
  Qed.

  Hint Resolve T_predicate_in : core.


  Lemma T_predicate_eq_inversion : forall ϕ₁ ϕ₂,
    T_predicate theory (patt_eq_inversion_of ϕ₁ ϕ₂).
  Proof.
    intros ϕ₁ ϕ₂ M Hm.
    unfold patt_eq_inversion_of.
    apply M_predicate_forall.
    match goal with
    | |- context G [fresh_evar ?t] => remember (fresh_evar t) as X
    end.
    
    unfold evar_open.
    simpl_bevar_subst.
    apply T_predicate_equals.
    apply Hm.
  Qed.

  Lemma pattern_interpretation_eq_inversion_of ϕ₁ ϕ₂ M ρₑ ρₛ :
    M ⊨ᵀ theory ->
    @pattern_interpretation Σ M ρₑ ρₛ (patt_eq_inversion_of ϕ₁ ϕ₂) = ⊤
    <-> (forall m₁ m₂,
            m₂ ∈ rel_of ρₑ ρₛ ϕ₁ m₁ <-> m₁ ∈ rel_of ρₑ ρₛ ϕ₂ m₂ (* TODO make rel_of take one more parameter. *)
        ).
  Proof.
    intros Htheory.
    rewrite pattern_interpretation_forall_predicate.
    2: { unfold evar_open. simpl_bevar_subst. apply T_predicate_equals. apply Htheory. }
    apply all_iff_morphism. intros m₁.
    remember ((fresh_evar
          (patt_equal (nest_ex ϕ₁ $ BoundVarSugar.b0)
             (ex ,
              (BoundVarSugar.b0
                 and patt_in BoundVarSugar.b1 (nest_ex (nest_ex ϕ₂) $ BoundVarSugar.b0)))))) as x.
    unfold evar_open.
    simpl_bevar_subst.
    rewrite equal_iff_interpr_same.
    2: { apply Htheory. }

    rewrite pattern_interpretation_set_builder.
    { unfold evar_open. simpl_bevar_subst. apply T_predicate_in. apply Htheory. }

    assert (Hpi: ∀ M ev sv ϕ rhs,
               @pattern_interpretation _ M ev sv ϕ = rhs
               <-> (∀ m, m ∈ @pattern_interpretation _ M ev sv ϕ <-> m ∈ rhs)).
    { split; intros H.
      + rewrite H. auto.
      + rewrite -> set_eq_subseteq. repeat rewrite elem_of_subseteq.
        split.
        * intros x0. specialize (H x0). destruct H as [H1 H2].
          apply H1.
        * intros x0. specialize (H x0). destruct H as [H1 H2].
          apply H2.
    }
    rewrite Hpi.
    apply all_iff_morphism. intros m₂.
    rewrite pattern_interpretation_app_simpl.

    rewrite nest_ex_same.
(*     {
      subst x.
      eapply evar_is_fresh_in_richer.
      2: { apply set_evar_fresh_is_fresh. }
      solve_free_evars_inclusion 5.
    } *)
    unfold evar_open, nest_ex.
    remember (fresh_evar
                (patt_free_evar x
                 ∈ml (nest_ex_aux 0 1 (nest_ex_aux 0 1 ϕ₂)).[evar:1↦patt_free_evar x] $ b0)) as y.
    rewrite fuse_nest_ex_same.
    rewrite nest_ex_same_general. 1-2: lia.
    simpl_bevar_subst. simpl. rewrite nest_ex_same.
(*
    do 3 rewrite evar_open_bound_evar.
    repeat case_match; try lia.
*)
(*
    rewrite simpl_evar_open.
    rewrite evar_open_free_evar.
*)
    repeat rewrite elem_of_PropSet.
   (*  rewrite <- free_evar_in_patt.
    2: { apply Htheory. } *)
    rewrite pattern_interpretation_free_evar_simpl.
    rewrite update_evar_val_same.
    fold (m₂ ∈ rel_of ρₑ ρₛ ϕ₁ m₁).

    (*rewrite simpl_evar_open.*)
    rewrite <- free_evar_in_patt; auto.
    rewrite pattern_interpretation_app_simpl.
    repeat rewrite pattern_interpretation_free_evar_simpl.
    rewrite pattern_interpretation_free_evar_independent.
    {
      subst.
      eapply evar_is_fresh_in_richer'.
      2: apply set_evar_fresh_is_fresh'.
      solve_free_evars_inclusion 5.
    }
    rewrite pattern_interpretation_free_evar_independent.
    {
      subst.
      eapply evar_is_fresh_in_richer'.
      2: apply set_evar_fresh_is_fresh'. unfold nest_ex.
      rewrite fuse_nest_ex_same. simpl.
      solve_free_evars_inclusion 5.
    }
    rewrite pattern_interpretation_free_evar_independent.
    {
      subst.
      eapply evar_is_fresh_in_richer'.
      2: apply set_evar_fresh_is_fresh'.
      solve_free_evars_inclusion 5.
    }
    rewrite update_evar_val_comm.
    { solve_fresh_neq. }

    rewrite update_evar_val_same.
    rewrite update_evar_val_comm.
    { solve_fresh_neq. }

    rewrite update_evar_val_same.
    unfold app_ext.
    rewrite elem_of_PropSet.
    fold (rel_of ρₑ ρₛ ϕ₂ m₂).
    auto.
  Qed.

  Lemma single_element_definedness_impl_satisfies_definedness (M : @Model Σ) :
    (exists (hashdef : Domain M),
        sym_interp M (inj definedness) = {[hashdef]}
        /\ forall x, app_interp hashdef x = ⊤
    ) ->
        satisfies_model M (axiom AxDefinedness).
  Proof.
    intros [hashdef [Hhashdefsym Hhashdeffull] ].
    unfold satisfies_model. intros ρₑ ρₛ.
    unfold axiom.
    unfold sym.
    unfold patt_defined.
    unfold p_x.
    rewrite -> pattern_interpretation_app_simpl.
    rewrite -> pattern_interpretation_sym_simpl.
    rewrite -> set_eq_subseteq.
    split.
    { apply top_subseteq. }
    rewrite -> elem_of_subseteq.
    intros x _.
    intros.
    unfold Ensembles.In.
    unfold app_ext.
    exists hashdef.
    rewrite Hhashdefsym.
    rewrite -> pattern_interpretation_free_evar_simpl.
    exists (ρₑ ev_x).
    split.
    { constructor. }
    split.
    { constructor. }
    rewrite Hhashdeffull.
    constructor.
  Qed.

  Lemma satisfies_definedness_implies_has_element_for_every_element
    (M : @Model Σ):
    M ⊨ᵀ theory ->
    forall (x y : Domain M),
      exists (z : Domain M),
        z ∈ sym_interp M (inj definedness)
        /\ y ∈ app_interp z x.
  Proof.
    intros HM x y.
    unfold theory in HM.
    rewrite satisfies_theory_iff_satisfies_named_axioms in HM.
    specialize (HM AxDefinedness). simpl in HM.
    unfold satisfies_model in HM.
    remember (λ (ev : evar), x) as ρₑ.
    specialize (HM ρₑ).
    specialize (HM (λ (sv : svar), ∅)).
    unfold patt_defined in HM.
    rewrite pattern_interpretation_app_simpl in HM.
    rewrite pattern_interpretation_sym_simpl in HM.
    rewrite pattern_interpretation_free_evar_simpl in HM.
    unfold app_ext in HM.
    rewrite set_eq_subseteq in HM.
    destruct HM as [_ HM].
    rewrite elem_of_subseteq in HM.
    specialize (HM y).
    feed specialize HM.
    {
      clear. set_solver.
    }
    rewrite elem_of_PropSet in HM.
    destruct HM as [le [re [HM1 [HM2 HM3] ] ] ].
    subst ρₑ.
    rewrite elem_of_singleton in HM2. subst re.
    exists le.
    split; assumption.
  Qed.

  Lemma not_equal_iff_not_interpr_same_1 : forall (M : @Model Σ),
    M ⊨ᵀ theory ->
    forall (ϕ1 ϕ2 : Pattern) (ρₑ : @EVarVal Σ M) (ρₛ : @SVarVal Σ M),
      @pattern_interpretation Σ M ρₑ ρₛ (ϕ1 =ml ϕ2) = ∅ <->
      @pattern_interpretation Σ M ρₑ ρₛ ϕ1
      <> @pattern_interpretation Σ M ρₑ ρₛ ϕ2.
  Proof.
    intros M H ϕ1 ϕ2 ρₑ ρₛ.
    rewrite -predicate_not_full_iff_empty.
    2: { apply T_predicate_equals. apply H. }
    rewrite equal_iff_interpr_same.
    2: { apply H. }
    split; intros H'; exact H'.
  Qed.

  Lemma not_subseteq_iff_not_interpr_subseteq_1 : forall (M : @Model Σ),
    M ⊨ᵀ theory ->
    forall (ϕ1 ϕ2 : Pattern) (ρₑ : @EVarVal Σ M) (ρₛ : @SVarVal Σ M),
      @pattern_interpretation Σ M ρₑ ρₛ (patt_subseteq ϕ1 ϕ2) = ∅ <->
      ~(@pattern_interpretation Σ M ρₑ ρₛ ϕ1)
        ⊆ (@pattern_interpretation Σ M ρₑ ρₛ ϕ2).
  Proof.
    intros M H ϕ1 ϕ2 ρₑ ρₛ.
    rewrite -predicate_not_full_iff_empty.
    2: { apply T_predicate_subseteq. apply H. }
    rewrite subseteq_iff_interpr_subseteq.
    2: { apply H. }
    split; intros H'; exact H'.
  Qed.

End definedness.


#[export]
Hint Resolve T_predicate_defined : core.
#[export]
Hint Resolve T_predicate_total : core.
#[export]
Hint Resolve T_predicate_subseteq : core.
#[export]
Hint Resolve T_predicate_equals : core.
#[export]
Hint Resolve T_predicate_in : core.
