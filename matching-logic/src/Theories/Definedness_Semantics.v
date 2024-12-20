From Coq Require Import Logic.Classical_Prop
                        Classes.Morphisms_Prop.
From MatchingLogic Require Export Logic
                                  Definedness_Syntax.
Import MatchingLogic.Logic.Notations
       MatchingLogic.Theories.Definedness_Syntax.Notations.

Set Default Proof Mode "Classic".

Section definedness.
  Context
    {Σ : Signature}
    {syntax : Syntax}
  .
  Open Scope ml_scope.

  Let sym (s : Symbols) : Pattern :=
    @patt_sym Σ (sym_inj s).

  Lemma definedness_app_ext_not_empty : forall (M : Model),
    M ⊨ᵀ theory ->
      forall S, S ≠ ∅ ->
        app_ext (sym_interp M (sym_inj def_sym)) S = ⊤.
  Proof.
    intros.
    pose proof (H' := proj1 (satisfies_theory_iff_satisfies_named_axioms named_axioms M)).
    specialize (H' H AxDefinedness).
    simpl in H'.
    clear H. rename H' into H.
    unfold satisfies_model in H.
    apply stdpp_ext.Not_Empty_Contains_Elements in H0 as [s H0].
    unfold app_ext in *.
    apply set_eq. split; intros. 1: set_solver.
    specialize (H {| evar_valuation := fun _ => s;
                       svar_valuation := fun _ => ∅;  |}).
    unfold patt_defined in H. simp eval in H.
    unfold app_ext in H.
    apply propset_top_elem_of with (t := x) in H.
    destruct H as [le [re [E1 [E2 E3] ] ] ].
    unfold p_x in E2. simp eval in E2. cbn in E2.
    do 2 eexists. split_and!. 1-2: eassumption. set_solver.
  Qed.

  Lemma definedness_not_empty_1 : forall (M : Model),
      M ⊨ᵀ theory ->
      forall (ϕ : Pattern) (ρ : Valuation),
        (eval ρ ϕ) <> ∅ ->
        (@eval Σ M ρ ⌈ ϕ ⌉ ) = ⊤.
  Proof.
    intros.
    pose (H' := stdpp_ext.Not_Empty_Contains_Elements (eval ρ ϕ) H0).
    destruct H'.
    unfold patt_defined.
    rewrite -> eval_app_simpl.

    pose proof definedness_app_ext_not_empty M H {[x]} ltac:(set_solver) as H''.
    rewrite -> set_eq_subseteq in H''.
    destruct H'' as [_ H''].
    assert (Hincl: {[x]} ⊆ (eval ρ ϕ) ).
    { rewrite -> elem_of_subseteq. intros.  inversion H2. subst. assumption. }

    pose proof (Hincl' := app_ext_monotonic_r
                            (eval ρ definedness)
                            {[x]}
                            (eval ρ ϕ)
                            Hincl
               ).

    rewrite -> set_eq_subseteq.
    split.
    { apply top_subseteq. }
    eapply transitivity.
    apply H''.
    assumption.
  Qed.

  Lemma definedness_empty_1 : forall (M : Model),
      M ⊨ᵀ theory ->
      forall (ϕ : Pattern) (ρ : Valuation),
      eval ρ ϕ = ∅ ->
      @eval Σ M ρ ⌈ ϕ ⌉ = ∅.
  Proof.
    intros M H ϕ ρ H0. unfold patt_defined.
    rewrite -> eval_app_simpl.
    rewrite -> H0.
    apply app_ext_bot_r.
  Qed.

  Theorem modus_tollens: forall (P Q : Prop), (P -> Q) -> ~Q -> ~P.
  Proof. auto. Qed.

  Lemma definedness_empty_2 : forall (M : Model),
      M ⊨ᵀ theory ->
      forall (ϕ : Pattern) (ρ : Valuation),
        eval ρ ⌈ ϕ ⌉ = ∅ ->
        @eval Σ M ρ ϕ = ∅.
  Proof.
    intros M H ϕ ρ H0.
    pose proof (H1 := empty_impl_not_full _ H0).
    pose proof (H2 := modus_tollens _ _ (definedness_not_empty_1 M H ϕ ρ) H1).
    apply Classical_Prop.NNPP in H2. apply H2.
  Qed.

  Lemma definedness_not_empty_2 : forall (M : Model),
      M ⊨ᵀ theory ->
      forall (ϕ : Pattern) (ρ : Valuation),
        eval ρ ⌈ ϕ ⌉ = ⊤ ->
        @eval Σ M ρ ϕ <> ∅.
  Proof.
    intros M H ϕ ρ H0.
    pose proof (H1 := full_impl_not_empty _ H0).
    exact (modus_tollens _ _ (definedness_empty_1 M H ϕ ρ) H1).
  Qed.

  Lemma definedness_not_empty_iff : forall (M : Model),
    M ⊨ᵀ theory ->
    forall (ϕ : Pattern) (ρ : Valuation),
      (eval ρ ϕ) <> ∅ <->
      (@eval Σ M ρ ⌈ ϕ ⌉ ) = ⊤.
  Proof.
    intros M HM ϕ ρ.
    split; intros H'.
    {
      apply definedness_not_empty_1. exact HM. exact H'.
    }
    {
      apply definedness_not_empty_2. exact HM. exact H'.
    }
  Qed.

  Lemma totality_not_full : forall (M : Model),
      M ⊨ᵀ theory ->
      forall (ϕ : Pattern) (ρ : Valuation),
        eval ρ ϕ <> ⊤ ->
        @eval Σ M ρ ⌊ ϕ ⌋ = ∅.
  Proof.
    intros.
    assert (Hnonempty : eval ρ (patt_not ϕ) <> ∅).
    { unfold not. unfold not in H0. intros. rewrite -> eval_not_simpl in H1.
      apply H0. clear H0.
      rewrite -> set_eq_subseteq.
      split.
      { apply top_subseteq. }
      rewrite -> complement_empty_iff_full in H1.
      rewrite H1.
      apply top_subseteq.
    }
    unfold patt_total. rewrite -> eval_not_simpl.
    rewrite -> complement_empty_iff_full.

    apply definedness_not_empty_1.
    { apply H. }
    apply Hnonempty.
  Qed.

  Lemma totality_full : forall (M : Model),
      M ⊨ᵀ theory ->
      forall (ϕ : Pattern) (ρ : Valuation),
        eval ρ ϕ = ⊤ ->
        @eval Σ M ρ ⌊ ϕ ⌋ = ⊤.
  Proof.
    intros M H ϕ ρ H0.
    unfold patt_total.
    rewrite -> eval_not_simpl.
    assert(H1: eval ρ (patt_not ϕ) = ∅).
    { rewrite -> eval_not_simpl.
      rewrite -> H0.
      clear. set_solver.
    }

    pose proof (H2 := definedness_empty_1 M H (patt_not ϕ) ρ H1).
    rewrite -> H2.
    clear. set_solver.
  Qed.

  Lemma totality_result_empty : forall (M : Model),
      M ⊨ᵀ theory ->
      forall (ϕ : Pattern) (ρ : Valuation),
        eval ρ ⌊ ϕ ⌋ = ∅ ->
        @eval Σ M ρ ϕ <> ⊤.
  Proof.
    intros M H ϕ ρ H0.
    pose proof (H1 := empty_impl_not_full _ H0).
    pose proof (H2 := modus_tollens _ _ (totality_full M H ϕ ρ) H1).
    apply H2.
  Qed.

  Lemma totality_not_full_iff : forall (M : Model),
      M ⊨ᵀ theory ->
      forall (ϕ : Pattern) (ρ : Valuation),
        eval ρ ϕ <> ⊤ <->
        @eval Σ M ρ ⌊ ϕ ⌋ = ∅.
  Proof.
    intros M HM ϕ ρ.
    split; intros H'.
    {
      apply totality_not_full. exact HM. exact H'.
    }
    {
      apply totality_result_empty. exact HM. exact H'.
    }
  Qed.

  Lemma totality_result_nonempty : forall (M : Model),
      M ⊨ᵀ theory ->
      forall (ϕ : Pattern) (ρ : Valuation),
        eval ρ ⌊ ϕ ⌋ <> ∅ ->
        @eval Σ M ρ ϕ = ⊤.
  Proof.
    intros M H ϕ ρ H0.
    pose proof (H2 := modus_tollens _ _ (totality_not_full M H ϕ ρ) H0).
    apply NNPP in H2. apply H2.
  Qed.
  
  Lemma equal_iff_both_subseteq : forall (M : Model),
      M ⊨ᵀ theory ->
      forall (ϕ1 ϕ2 : Pattern) (ρ : Valuation),
        eval ρ (ϕ1 =ml ϕ2) = ⊤ <->
        (
          eval ρ (ϕ1 ⊆ml ϕ2) = ⊤ /\
          @eval Σ M ρ (patt_subseteq ϕ2 ϕ1) = ⊤).
  Proof.
    intros M H ϕ1 ϕ2 ρ.
    split.
    - intros H0.
      unfold patt_equal in H0.
      apply full_impl_not_empty in H0.
      apply (totality_result_nonempty _ H) in H0.
      unfold "<--->" in H0.
      rewrite -> eval_and_simpl in H0.
      rewrite -> intersection_full_iff_both_full in H0.
      destruct H0 as [H1 H2].
      unfold patt_subseteq.
      apply (totality_full _ H) in H1.
      apply (totality_full _ H) in H2.
      split; assumption.
    - intros [H0 H1].
      unfold patt_subseteq.
      apply full_impl_not_empty in H0.
      apply full_impl_not_empty in H1.
      apply (totality_result_nonempty _ H) in H0.
      apply (totality_result_nonempty _ H) in H1.
      unfold patt_equal.
      apply (totality_full _ H).
      unfold "<--->".
      rewrite -> eval_and_simpl.
      rewrite -> H0.
      rewrite -> H1.
      clear. set_solver.
  Qed.

  Lemma subseteq_iff_interpr_subseteq : forall (M : Model),
      M ⊨ᵀ theory ->
      forall (ϕ1 ϕ2 : Pattern) (ρ : Valuation),
        eval ρ (ϕ1 ⊆ml ϕ2) = ⊤ <->
        (eval ρ ϕ1)
          ⊆ (@eval Σ M ρ ϕ2).
  Proof.
    intros M H ϕ1 ϕ2 ρ.
    split.
    - intros H0.
      unfold patt_subseteq in H0.
      apply full_impl_not_empty in H0.
      apply (totality_result_nonempty _ H) in H0.
      rewrite -> eval_imp_simpl in H0.
      rewrite -> set_eq_subseteq in H0.
      destruct H0 as [_ H0].
      rewrite -> elem_of_subseteq in H0.
      intros x H1. specialize (H0 x).
      ospecialize* H0.
      { apply elem_of_top'. }
      remember (eval ρ ϕ1) as Xϕ1.
      remember (eval ρ ϕ2) as Xϕ2.
      clear -H0 H1.
      set_solver.
    - intros H0.
      unfold patt_subseteq.
      apply (totality_full _ H).
      rewrite -> eval_imp_simpl.
      rewrite -> set_eq_subseteq.
      split.
      { apply top_subseteq. }
      rewrite -> elem_of_subseteq.
      intros x _. specialize (H0 x).
      destruct (classic (x ∈ (eval ρ ϕ1))).
      + right. auto.
      + left. apply elem_of_compl. assumption.
  Qed.

  Lemma equal_iff_interpr_same : forall (M : Model),
      M ⊨ᵀ theory ->
      forall (ϕ1 ϕ2 : Pattern) (ρ : Valuation),
        eval ρ (ϕ1 =ml ϕ2) = ⊤ <->
        eval ρ ϕ1
        = @eval Σ M ρ ϕ2.
  Proof.
    intros M H ϕ1 ϕ2 ρ.
    split.
    - intros H0.
      apply (equal_iff_both_subseteq _ H) in H0.
      destruct H0 as [Hsub1 Hsub2].
      apply (subseteq_iff_interpr_subseteq _ H) in Hsub1.
      apply (subseteq_iff_interpr_subseteq _ H) in Hsub2.
      rewrite -> set_eq_subseteq.
      split; assumption.
    - intros H0.
      rewrite -> set_eq_subseteq in H0.
      destruct H0 as [Hincl1 Hincl2].
      apply (subseteq_iff_interpr_subseteq _ H) in Hincl1.
      apply (subseteq_iff_interpr_subseteq _ H) in Hincl2.
      apply equal_iff_both_subseteq. auto. split; auto.
  Qed.

  Lemma equal_refl : forall (M : Model),
      M ⊨ᵀ theory ->
      forall (ϕ : Pattern) (ρ : Valuation),
        @eval Σ M ρ (patt_equal ϕ ϕ) = ⊤.
  Proof.
    intros M H ϕ ρ.
    apply (equal_iff_interpr_same _ H).
    auto.
  Qed.

  Lemma equal_sym : forall (M : Model),
      M ⊨ᵀ theory ->
      forall (ϕ1 ϕ2 : Pattern) (ρ : Valuation),
        eval ρ (ϕ1 =ml ϕ2) = ⊤ ->
        @eval Σ M ρ (patt_equal ϕ2 ϕ1) = ⊤.
  Proof.
    intros M H ϕ1 ϕ2 ρ H0.
    apply (equal_iff_interpr_same _ H).
    apply (equal_iff_interpr_same _ H) in H0.
    symmetry. auto.
  Qed.

  Lemma equal_trans : forall (M : Model),
      M ⊨ᵀ theory ->
      forall (ϕ1 ϕ2 ϕ3 : Pattern) (ρ : Valuation),
        eval ρ (ϕ1 =ml ϕ2) = ⊤ ->
        eval ρ (patt_equal ϕ2 ϕ3) = ⊤ ->
        @eval Σ M ρ (patt_equal ϕ1 ϕ3) = ⊤.
  Proof.
    intros M H ϕ1 ϕ2 ϕ3 ρ H0 H1.
    apply (equal_iff_interpr_same _ H).
    apply (equal_iff_interpr_same _ H) in H0.
    apply (equal_iff_interpr_same _ H) in H1.
    rewrite -> H0. auto.
  Qed.

  Lemma free_evar_in_patt : forall (M : Model),
      M ⊨ᵀ theory ->
      forall (x : evar)(ϕ : Pattern) (ρ : Valuation),
        (evar_valuation ρ x ∈ (eval ρ ϕ)) <->
        @eval Σ M ρ (patt_in (patt_free_evar x) ϕ) = ⊤.
  Proof.
    intros M H x ϕ ρ.
    split.
    - intros H0.
      unfold patt_in.
      apply (definedness_not_empty_1 _ H).
      intros Contra.
      apply Contains_Elements_Not_Empty in Contra. exact Contra.
      exists (evar_valuation ρ x).
      rewrite -> eval_and_simpl.
      split.
      + rewrite -> eval_free_evar_simpl. constructor.
      + assumption.
    - intros H0.
      unfold patt_in in H0.
      apply (definedness_not_empty_2 _ H) in H0.
      unfold not in H0.
      assert (H0': (eval ρ (patt_free_evar x and ϕ)) = ∅ -> False).
      { intros Contra. apply H0. auto. }
      apply Not_Empty_Contains_Elements in H0'.
      destruct H0' as [x0 H0'].
      rewrite -> eval_and_simpl in H0'.
      destruct H0'.
      rewrite -> eval_free_evar_simpl in H1.
      inversion H1. subst. assumption.
  Qed.
  
  Lemma T_predicate_defined : forall ϕ, T_predicate theory ⌈ ϕ ⌉.
  Proof.
    intros ϕ. unfold T_predicate. intros. unfold M_predicate. intros.
    pose proof (Hlr := classic ( eval ρ ϕ = ∅ )).
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

    mlSimpl.
    apply T_predicate_equals.
    apply Hm.
  Qed.

  Lemma eval_eq_inversion_of ϕ₁ ϕ₂ M ρ :
    M ⊨ᵀ theory ->
    @eval Σ M ρ (patt_eq_inversion_of ϕ₁ ϕ₂) = ⊤
    <-> (forall m₁ m₂,
            m₂ ∈ rel_of ρ ϕ₁ m₁ <-> m₁ ∈ rel_of ρ ϕ₂ m₂ (* TODO make rel_of take one more parameter. *)
        ).
  Proof.
    intros Htheory.
    rewrite eval_forall_predicate.
    { mlSimpl. apply T_predicate_equals. apply Htheory. }
    apply all_iff_morphism. intros m₁.
    remember ((fresh_evar
          (patt_equal (nest_ex ϕ₁ ⋅ BoundVarSugar.b0)
             (ex ,
              (BoundVarSugar.b0
                 and patt_in BoundVarSugar.b1 (nest_ex (nest_ex ϕ₂) ⋅ BoundVarSugar.b0)))))) as x.
    unfold evar_open.
    mlSimpl.
    rewrite equal_iff_interpr_same.
    { apply Htheory. }

    rewrite eval_set_builder.
    { mlSimpl. apply T_predicate_in. apply Htheory. }

    assert (Hpi: ∀ M ρ ϕ rhs,
               eval ρ ϕ = rhs
               <-> (∀ m, m ∈ @eval _ M ρ ϕ <-> m ∈ rhs)).
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
    rewrite eval_app_simpl.

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
                 ∈ml (nest_ex_aux 0 1 (nest_ex_aux 0 1 ϕ₂))^[evar:1↦patt_free_evar x] ⋅ b0)) as y.
    rewrite fuse_nest_ex_same.
    rewrite nest_ex_same_general. 1-2: cbn; lia.
    mlSimpl. rewrite nest_ex_same.
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
    rewrite eval_free_evar_simpl.
    rewrite update_evar_val_same.
    fold (m₂ ∈ rel_of ρ ϕ₁ m₁). simpl.

    (*rewrite simpl_evar_open.*)
    rewrite <- free_evar_in_patt; auto.
    rewrite eval_app_simpl.
    repeat rewrite eval_free_evar_simpl.
    rewrite eval_free_evar_independent.
    {
      subst.
      eapply evar_is_fresh_in_richer'.
      2: apply set_evar_fresh_is_fresh'.
      solve_free_evars_inclusion 5.
    }
    rewrite eval_free_evar_independent.
    {
      subst.
      eapply evar_is_fresh_in_richer'.
      2: apply set_evar_fresh_is_fresh'. unfold nest_ex.
      rewrite fuse_nest_ex_same. simpl.
      solve_free_evars_inclusion 5.
    }
    rewrite eval_free_evar_independent.
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
    fold (rel_of ρ ϕ₂ m₂).
    auto.
  Qed.

  Lemma single_element_definedness_impl_satisfies_definedness (M : Model) :
    (exists (hashdef : Domain M),
        sym_interp M (sym_inj def_sym) = {[hashdef]}
        /\ forall x, app_interp _ hashdef x = ⊤
    ) ->
        satisfies_model M (axiom AxDefinedness).
  Proof.
    intros [hashdef [Hhashdefsym Hhashdeffull] ].
    unfold satisfies_model. intros ρ.
    unfold axiom.
    unfold sym.
    unfold patt_defined.
    unfold p_x.
    rewrite -> eval_app_simpl.
    setoid_rewrite -> eval_sym_simpl.
    rewrite -> set_eq_subseteq.
    split.
    { apply top_subseteq. }
    rewrite -> elem_of_subseteq.
    intros x _.
    intros.
    unfold app_ext.
    exists hashdef.
    rewrite Hhashdefsym.
    rewrite -> eval_free_evar_simpl.
    exists (evar_valuation ρ ev_x).
    split.
    { constructor. }
    split.
    { constructor. }
    rewrite Hhashdeffull.
    constructor.
  Qed.

  Lemma satisfies_definedness_implies_has_element_for_every_element
    (M : Model):
    M ⊨ᵀ theory ->
    forall (x y : Domain M),
      exists (z : Domain M),
        z ∈ sym_interp M (sym_inj def_sym)
        /\ y ∈ app_interp _ z x.
  Proof.
    intros HM x y.
    unfold theory in HM.
    rewrite satisfies_theory_iff_satisfies_named_axioms in HM.
    specialize (HM AxDefinedness). simpl in HM.
    unfold satisfies_model in HM.
    remember (λ (ev : evar), x) as ρₑ.
    specialize (HM (mkValuation ρₑ (λ (sv : svar), ∅))).
    unfold patt_defined in HM.
    rewrite eval_app_simpl in HM.
    rewrite eval_sym_simpl in HM.
    rewrite eval_free_evar_simpl in HM.
    unfold app_ext in HM.
    rewrite set_eq_subseteq in HM.
    destruct HM as [_ HM].
    rewrite elem_of_subseteq in HM.
    specialize (HM y).
    ospecialize* HM.
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

  Lemma not_equal_iff_not_interpr_same_1 : forall (M : Model),
    M ⊨ᵀ theory ->
    forall (ϕ1 ϕ2 : Pattern) (ρ : Valuation),
      @eval Σ M ρ (ϕ1 =ml ϕ2) = ∅ <->
      eval ρ ϕ1
      <> eval ρ ϕ2.
  Proof.
    intros M H ϕ1 ϕ2 ρ.
    rewrite -predicate_not_full_iff_empty.
    { apply T_predicate_equals. apply H. }
    rewrite equal_iff_interpr_same.
    { apply H. }
    split; intros H'; exact H'.
  Qed.

  Lemma not_subseteq_iff_not_interpr_subseteq_1 : forall (M : Model),
    M ⊨ᵀ theory ->
    forall (ϕ1 ϕ2 : Pattern) (ρ : Valuation),
      eval ρ (ϕ1 ⊆ml ϕ2) = ∅ <->
      ~(eval ρ ϕ1)
        ⊆ (@eval Σ M ρ ϕ2).
  Proof.
    intros M H ϕ1 ϕ2 ρ.
    rewrite -predicate_not_full_iff_empty.
    { apply T_predicate_subseteq. apply H. }
    rewrite subseteq_iff_interpr_subseteq.
    { apply H. }
    split; intros H'; exact H'.
  Qed.

  Lemma patt_defined_dec : forall (M : Model),
    M ⊨ᵀ theory ->
    forall φ ρ,
      @eval _ M ρ ⌈φ⌉ = ⊤ \/
      @eval _ M ρ ⌈φ⌉ = ∅.
  Proof.
    intros.
    destruct (classic ((eval ρ φ) = ∅)).
    * apply definedness_empty_1 in H0. by right. assumption.
    * apply definedness_not_empty_1 in H0. by left. assumption.
  Qed.

  Lemma patt_total_dec : forall (M : Model),
    M ⊨ᵀ theory ->
    forall φ ρ,
      @eval _ M ρ ⌊φ⌋ = ⊤ \/
      @eval _ M ρ ⌊φ⌋ = ∅.
  Proof.
    intros.
    unfold patt_total, patt_not.
    simp eval.
    destruct (patt_defined_dec M H (φ ---> ⊥) ρ) as [H0 | H0]; rewrite H0; set_solver.
  Qed.

  Lemma eval_equal_emplace : forall (M : Model),
    M ⊨ᵀ theory ->
    forall C (φ1 φ2 : Pattern) (ρ : Valuation),
      well_formed φ1 ->
      well_formed φ2 ->
      @eval _ M ρ φ1 = eval ρ φ2 ->
      eval ρ (emplace C φ1) = eval ρ (emplace C φ2).
  Proof.
    intros. destruct C as [y C]. cbn.
    revert ρ H2.
    size_induction C; intros; simp eval; simpl;
      try reflexivity.
    * by case_match.
    * simp eval.
      rewrite IHsz. lia. assumption.
      rewrite IHsz. lia. assumption.
      reflexivity.
    * simp eval.
      rewrite IHsz. lia. assumption.
      rewrite IHsz. lia. assumption.
      reflexivity.
    * simp eval. cbn.
      apply propset_fa_union_same. intros.
      destruct (decide (y ∈ free_evars C)).
      2: {
        rewrite free_evar_subst_no_occurrence. assumption.
        rewrite free_evar_subst_no_occurrence. assumption.
        reflexivity.
      }
      remember (fresh_evar (C ⋅ φ1 ⋅ φ2 ⋅ patt_free_evar y)) as z.
      rewrite (eval_fresh_evar_open _ _ z).
      3: rewrite (eval_fresh_evar_open _ _ z).
      1-4: unfold evar_is_fresh_in.
      1,3: solve_fresh.
      1-2: subst z; pose proof free_evars_free_evar_subst as X; eapply not_elem_of_weaken; try apply X; solve_fresh.
      assert (z ≠ y). {
        subst z.
        pose proof set_evar_fresh_is_fresh (C ⋅ φ1 ⋅ φ2 ⋅ patt_free_evar y).
        unfold evar_is_fresh_in in H3. set_solver.
      }
      rewrite evar_open_free_evar_subst_swap; try assumption.
      rewrite evar_open_free_evar_subst_swap; try assumption.
      apply IHsz.
      - setoid_rewrite <- evar_open_size. lia.
      - rewrite !eval_free_evar_independent.
        1-2: unfold evar_is_fresh_in; subst z; solve_fresh.
        assumption.
    * simp eval. cbn.
      f_equal. extensionality S. (** FUN_EXT axiom *)
      remember (fresh_svar (C ⋅ φ1 ⋅ φ2)) as Z.
      rewrite (eval_fresh_svar_open _ _ Z).
      3: rewrite (eval_fresh_svar_open _ _ Z).
      1-4: unfold svar_is_fresh_in.
      1,3: solve_sfresh.
      1-2: subst Z; pose proof free_svars_free_evar_subst as X; eapply not_elem_of_weaken; try apply X; solve_sfresh.
      unfold svar_open.
      rewrite -free_evar_subst_bsvar_subst. wf_auto2. unfold evar_is_fresh_in. set_solver.
      rewrite -free_evar_subst_bsvar_subst. wf_auto2. unfold evar_is_fresh_in. set_solver.
      apply IHsz.
      - setoid_rewrite <- svar_open_size. lia.
      - rewrite !eval_free_svar_independent.
        1-2: unfold evar_is_fresh_in; subst Z; solve_sfresh.
        assumption.
  Qed.

  Lemma eq_elim_is_top : forall (M : Model),
    M ⊨ᵀ theory ->
    forall C (φ1 φ2 : Pattern) (ρ : Valuation),
      well_formed φ1 ->
      well_formed φ2 ->
      @eval _ M ρ (φ1 =ml φ2 ---> emplace C φ1 ---> emplace C φ2) = ⊤.
  Proof.
    intros. destruct C as [y C]. cbn. simp eval.
    (** classic axiom: *)
    destruct (patt_total_dec M H (φ1 <---> φ2) ρ) as [Heq | Heq]; rewrite Heq.
    2: set_solver.
    apply equal_iff_interpr_same in Heq. 2: assumption.
    apply eval_equal_emplace with (C := {|pcPattern := C; pcEvar := y|}) in Heq.
    2-4: assumption.
    cbn in Heq. rewrite Heq.
    rewrite union_with_complement. set_solver.
  Qed.
End definedness.

From MatchingLogic Require Import StringSignature.
Module equivalence_insufficient.

  Open Scope ml_scope.
  Inductive exampleSymbols : Set :=
  | sym_f.

  Local
  Instance exampleSymbols_eqdec : EqDecision exampleSymbols.
  Proof. unfold EqDecision. intros x y. unfold Decision. decide equality. Defined.

  Local
  Program Instance exampleSymbols_fin : Finite exampleSymbols :=
  {|
    enum := [sym_f] ;
  |}.
  Next Obligation.
    apply NoDup_cons.
    split.
    {
      intros HContra. inversion HContra.
    }
    {
      apply NoDup_nil. exact I.
    }
  Defined.
  Next Obligation.
  intros []. set_solver.
  Defined.

  #[local]
  Instance mySignature : Signature :=
  {| variables := StringMLVariables;
     ml_symbols := {|
      symbols := exampleSymbols;
      sym_eqdec := exampleSymbols_eqdec;
     |};
  |}.

  Inductive exampleDomain : Set :=
  | one | two | f.

  Theorem exampleDomain_Inhabited : Inhabited exampleDomain.
  Proof. constructor. apply one. Defined.

  Definition example_app_interp (d1 d2 : exampleDomain) : propset exampleDomain :=
  match d1, d2 with
  | f, one => ⊤
  | f, two => ∅
  | _, _ => ∅
  end.

  Definition exampleModel : @Model mySignature :=
  {|
    Domain := exampleDomain;
    Domain_inhabited := exampleDomain_Inhabited;
    sym_interp := fun (x : symbols) =>
                      {[ f ]};
    app_interp := example_app_interp;
  |}.

  Example equiv_not_eq :
    forall ρ, @eval _ exampleModel ρ (ex , (patt_sym sym_f ⋅ patt_free_evar "x"%string <---> b0)) = ⊤.
  Proof.
    intros ρ. unfold_leibniz.
    rewrite set_equiv_subseteq. split.
    apply top_subseteq.
    rewrite eval_simpl. simpl.
    unfold evar_open. simpl.
    unfold propset_fa_union.

    apply elem_of_subseteq. intros x _.
    rewrite elem_of_PropSet.
    destruct (evar_valuation ρ "x"%string) eqn:Eqx.
    * destruct x.
      - exists one.
        repeat rewrite eval_simpl.
        rewrite update_evar_val_same.
        rewrite app_ext_singleton.
        rewrite update_evar_val_neq.
        { set_solver. }
        simpl. rewrite Eqx.
        set_unfold. intuition.
      - exists two.
        repeat rewrite eval_simpl.
        rewrite update_evar_val_same.
        rewrite app_ext_singleton.
        rewrite update_evar_val_neq.
        { set_solver. }
        simpl. rewrite Eqx.
        set_unfold. intuition.
      - exists f.
        repeat rewrite eval_simpl.
        rewrite update_evar_val_same.
        rewrite app_ext_singleton.
        rewrite update_evar_val_neq.
        { set_solver. }
        simpl. rewrite Eqx.
        set_unfold. intuition.
    * destruct x.
      - exists two.
        repeat rewrite eval_simpl.
        rewrite update_evar_val_same.
        rewrite app_ext_singleton.
        rewrite update_evar_val_neq.
        { set_solver. }
        simpl. rewrite Eqx.
        set_unfold. intuition.
        left. intuition. apply H. intro. congruence.
      - exists one.
        repeat rewrite eval_simpl.
        rewrite update_evar_val_same.
        rewrite app_ext_singleton.
        rewrite update_evar_val_neq.
        { set_solver. }
        simpl. rewrite Eqx.
        set_unfold. intuition.
        left. intuition. apply H. intro. congruence.
      - exists two.
        repeat rewrite eval_simpl.
        rewrite update_evar_val_same.
        rewrite app_ext_singleton.
        rewrite update_evar_val_neq.
        { set_solver. }
        simpl. rewrite Eqx.
        set_unfold. intuition.
        left. intuition. apply H. intro. congruence.
   * destruct x.
      - exists two.
        repeat rewrite eval_simpl.
        rewrite update_evar_val_same.
        rewrite app_ext_singleton.
        rewrite update_evar_val_neq.
        { set_solver. }
        simpl. rewrite Eqx.
        set_unfold. intuition.
        left. intuition. apply H. intro. congruence.
      - exists one.
        repeat rewrite eval_simpl.
        rewrite update_evar_val_same.
        rewrite app_ext_singleton.
        rewrite update_evar_val_neq.
        { set_solver. }
        simpl. rewrite Eqx.
        set_unfold. intuition.
        left. intuition. apply H. intro. congruence.
      - exists two.
        repeat rewrite eval_simpl.
        rewrite update_evar_val_same.
        rewrite app_ext_singleton.
        rewrite update_evar_val_neq.
        { set_solver. }
        simpl. rewrite Eqx.
        set_unfold. intuition.
        left. intuition. apply H. intro. congruence.
  Qed.
  Close Scope ml_scope.
End equivalence_insufficient.


Module equivalence_insufficient2.
  Open Scope ml_scope.
  Inductive exampleSymbols : Set :=
  | sym_f
  | sym_g.

  Local
  Instance exampleSymbols_eqdec : EqDecision exampleSymbols.
  Proof. unfold EqDecision. intros x y. unfold Decision. decide equality. Defined.

  Local
  Program Instance exampleSymbols_fin : Finite exampleSymbols :=
  {|
    enum := [sym_f; sym_g] ;
  |}.
  Next Obligation.
    apply NoDup_cons.
    split.
    {
      intros HContra. inversion HContra.
      subst. inversion H1.
    }
    apply NoDup_cons. split.
    {
      intro. inversion H.
    }
    {
      apply NoDup_nil. exact I.
    }
  Defined.
  Next Obligation.
    intros []; set_solver.
  Defined.

  #[local]
  Instance mySignature : Signature :=
  {| variables := StringMLVariables;
     ml_symbols := {|
      symbols := exampleSymbols;
      sym_eqdec := exampleSymbols_eqdec;
     |};
  |}.

  Inductive exampleDomain : Set :=
  | one | two | f | g.

  Instance exampleDomain_Inhabited : Inhabited exampleDomain.
  Proof. constructor. apply one. Defined.

  Definition example_sym_interp (x : symbols) : propset exampleDomain :=
    match x with
    | sym_f => {[f]}
    | sym_g => {[g]}
    end.

  Definition example_app_interp (d1 d2 : exampleDomain) : propset exampleDomain :=
  match d1, d2 with
  | g, f => {[two]}
  | g, g => {[f]}
  | _, _ => ∅
  end.

  Definition exampleModel : @Model mySignature :=
  {|
    Domain := exampleDomain;
    Domain_inhabited := exampleDomain_Inhabited;
    sym_interp := example_sym_interp;
    app_interp := example_app_interp;
  |}.

  Theorem app_ext_singleton : forall x y,
    app_ext {[x]} {[y]} = @app_interp mySignature exampleModel x y.
  Proof.
    intros x y. unfold app_ext.
    apply set_eq. set_solver.
  Qed.

  Example equiv_elim_not :
    forall ρ,
        @eval _ exampleModel ρ
          (patt_sym sym_f <---> patt_sym sym_g --->
          patt_sym sym_g ⋅ patt_sym sym_f ---> patt_sym sym_g ⋅ patt_sym sym_g) ≠ ⊤.
  Proof.
    intros.
    (** First, we simplify the interpretation *)
    rewrite eval_imp_simpl eval_imp_simpl.
    rewrite eval_iff_simpl.
    repeat rewrite eval_simpl.
    (** Next, we simplify the model-specific parts:*)
    cbn.
    rewrite 2!app_ext_singleton.
    cbn. intro.
    (**
      Now we derive a counterexample by showing that the element "two"
      won't be in the LHS of H. This only involves simplification of set
      operations.
    *)
    epose proof (proj1 (set_eq _ _) H two) as [_ ?]. Unshelve.
    2: { apply (@propset_leibniz_equiv mySignature exampleModel). } (* why is this not automatic?? *)
    clear H.
    specialize (H0 ltac:(set_solver)).
    (* set_solver should work at this point... *)
    apply elem_of_union in H0 as [|].
    * apply elem_of_difference in H as [? ?].
      apply H0.
      apply elem_of_intersection. split.
      - apply elem_of_union_r. set_solver.
      - apply elem_of_union_l. set_solver.
    * apply elem_of_union in H as [|].
      - apply elem_of_difference in H as [? ?].
        set_solver.
      - set_solver.
  Qed.

End equivalence_insufficient2.

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
