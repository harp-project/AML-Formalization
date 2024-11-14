From MatchingLogic Require Export Substitution
                                  Freshness
                                  ApplicationContext.

Import Substitution.Notations.

Section lemmas.
  Context {Σ : Signature}.
  Open Scope ml_scope.

  Lemma evar_is_fresh_in_subst_ctx x AC p:
    evar_is_fresh_in x (subst_ctx AC p)
    <-> (evar_is_fresh_in x p /\ x ∉ AC_free_evars AC).
  Proof.
    induction AC.
    - simpl. split; set_solver.
    - simpl. split; intros H.
      + assert (Hfr1: evar_is_fresh_in x (subst_ctx AC p)).
        { eapply evar_is_fresh_in_richer. 2: apply H. cbn. set_solver. }
        assert (Hfr2: evar_is_fresh_in x p0).
        { eapply evar_is_fresh_in_richer. 2: apply H. cbn. set_solver. }
        rewrite -> IHAC in Hfr1.
        split; [apply Hfr1|].
        clear -Hfr1 Hfr2.
        unfold evar_is_fresh_in in Hfr2.
        set_solver.
      + destruct H as [H1 H2].
        rewrite -> evar_is_fresh_in_app.
        split.
        * rewrite -> IHAC. set_solver.
        * unfold evar_is_fresh_in. set_solver.
    - simpl. split; intros H.
      + assert (Hfr1: evar_is_fresh_in x (subst_ctx AC p)).
        { eapply evar_is_fresh_in_richer. 2: apply H. cbn. set_solver. }
        assert (Hfr2: evar_is_fresh_in x p0).
        { eapply evar_is_fresh_in_richer. 2: apply H. cbn. set_solver. }
        rewrite -> IHAC in Hfr1.
        split; [apply Hfr1|].
        clear -Hfr1 Hfr2.
        unfold evar_is_fresh_in in Hfr2.
        set_solver.
      + destruct H as [H1 H2].
        rewrite -> evar_is_fresh_in_app.
        split.
        * unfold evar_is_fresh_in. set_solver.
        * rewrite -> IHAC. set_solver.
  Qed.


  Lemma wf_ex_eq_sctx_eo AC x p:
    well_formed (patt_exists p) = true ->
    well_formed (patt_exists ((subst_ctx AC (p^{evar: 0 ↦ x}))^{{evar: x ↦ 0}})) = true.
  Proof.
    intros Hwf.
    unfold well_formed in Hwf.
    apply andb_prop in Hwf.
    destruct Hwf as [Hwfp Hwfc].
    simpl in Hwfp.
    unfold well_formed.
    apply andb_true_intro.
    split.
    - simpl. apply evar_quantify_positive.
      apply wp_sctx.
      apply wfp_evar_open.
      apply Hwfp.
    - unfold well_formed_closed.
      simpl.
      unfold well_formed_closed in *.
      destruct_andb! Hwfc.
      apply andb_true_iff; split.
      + apply evar_quantify_closed_mu. apply wcmu_sctx.
        apply wfc_mu_aux_body_ex_imp1. simpl in *. assumption.
      + apply evar_quantify_closed_ex. apply wcex_sctx.
        apply wfc_ex_aux_body_ex_imp1. simpl in *. assumption.
  Qed.


  Lemma subst_ctx_bevar_subst AC p q n:
  subst_ctx AC (p^[evar: n ↦ q]) = (subst_ctx AC p)^[evar: n ↦ q].
Proof.
  induction AC.
  - reflexivity.
  - simpl. rewrite IHAC. clear IHAC.
    rewrite [p0^[evar: n ↦ q] ]bevar_subst_not_occur.
    2: { reflexivity. }
    unfold well_formed,well_formed_closed in Prf.
    destruct_andb! Prf.
    auto. eapply well_formed_closed_ex_aux_ind. 2: exact H2. lia.
  - simpl. rewrite IHAC. clear IHAC.
    rewrite [p0^[evar: n ↦ q] ]bevar_subst_not_occur.
    2: { reflexivity. }
    unfold well_formed,well_formed_closed in Prf.
    destruct_andb! Prf.
    auto. eapply well_formed_closed_ex_aux_ind. 2: exact H2. lia.
Qed.

End lemmas.