From Coq Require Import Logic.Classical_Prop.

From MatchingLogic Require Export
  SyntaxLemmas.PatternCtxApplicationCtx
  SyntaxLemmas.FreshnessApplicationCtx
  wftactics
.

Import MatchingLogic.Substitution.Notations.

Close Scope boolean_if_scope.

Section syntax.
  Context {Σ : Signature}.
  Open Scope ml_scope.

  Inductive is_subformula_of_ind : Pattern -> Pattern -> Prop :=
  | sub_eq ϕ₁ ϕ₂ : ϕ₁ = ϕ₂ -> is_subformula_of_ind ϕ₁ ϕ₂
  | sub_app_l ϕ₁ ϕ₂ ϕ₃ : is_subformula_of_ind ϕ₁ ϕ₂ -> is_subformula_of_ind ϕ₁ (patt_app ϕ₂ ϕ₃)
  | sub_app_r ϕ₁ ϕ₂ ϕ₃ : is_subformula_of_ind ϕ₁ ϕ₃ -> is_subformula_of_ind ϕ₁ (patt_app ϕ₂ ϕ₃)
  | sub_imp_l ϕ₁ ϕ₂ ϕ₃ : is_subformula_of_ind ϕ₁ ϕ₂ -> is_subformula_of_ind ϕ₁ (patt_imp ϕ₂ ϕ₃)
  | sub_imp_r ϕ₁ ϕ₂ ϕ₃ : is_subformula_of_ind ϕ₁ ϕ₃ -> is_subformula_of_ind ϕ₁ (patt_imp ϕ₂ ϕ₃)
  | sub_exists ϕ₁ ϕ₂ : is_subformula_of_ind ϕ₁ ϕ₂ -> is_subformula_of_ind ϕ₁ (patt_exists ϕ₂)
  | sub_mu ϕ₁ ϕ₂ : is_subformula_of_ind ϕ₁ ϕ₂ -> is_subformula_of_ind ϕ₁ (patt_mu ϕ₂)
  .

  Fixpoint is_subformula_of ϕ₁ ϕ₂ : bool :=
    (decide_rel (=) ϕ₁ ϕ₂)
    || match ϕ₂ with
       | patt_app l r | patt_imp l r => is_subformula_of ϕ₁ l || is_subformula_of ϕ₁ r
       | patt_exists phi | patt_mu phi => is_subformula_of ϕ₁ phi
       | _ => false
       end.

  Lemma is_subformula_of_P ϕ₁ ϕ₂ : reflect (is_subformula_of_ind ϕ₁ ϕ₂) (is_subformula_of ϕ₁ ϕ₂).
  Proof.
    unfold is_subformula_of.
    remember ϕ₂. revert p Heqp.

    (* TODO *)
    induction ϕ₂; move=> p Heqp; destruct (decide_rel (=) ϕ₁ p) eqn:Heq2;
                           rewrite Heqp; rewrite -Heqp; rewrite Heq2; simpl; rewrite Heqp;
                             try (apply ReflectT; subst; apply sub_eq; reflexivity);
                             try (apply ReflectF; intros Contra; inversion Contra; subst; contradiction).
    all: fold is_subformula_of in *.
    - destruct (IHϕ₂1 ϕ₂1),(IHϕ₂2 ϕ₂2); simpl; try reflexivity.
      + apply ReflectT. apply sub_app_l. assumption.
      + apply ReflectT. apply sub_app_l. assumption.
      + apply ReflectT. apply sub_app_r. assumption.
      + apply ReflectF. intros Contra. inversion Contra; subst; contradiction.
    - destruct (IHϕ₂1 ϕ₂1),(IHϕ₂2 ϕ₂2); simpl; try reflexivity.
      + apply ReflectT. apply sub_imp_l. assumption.
      + apply ReflectT. apply sub_imp_l. assumption.
      + apply ReflectT. apply sub_imp_r. assumption.
      + apply ReflectF. intros Contra. inversion Contra; subst; contradiction.
    - destruct (IHϕ₂ ϕ₂). reflexivity.
      + apply ReflectT. apply sub_exists. assumption.
      + apply ReflectF. intros Contra. inversion Contra; subst; contradiction.
    - destruct (IHϕ₂ ϕ₂). reflexivity.
      + apply ReflectT. apply sub_mu. assumption.
      + apply ReflectF. intros Contra. inversion Contra; subst; contradiction.
  Qed.

  Lemma is_subformula_of_refl ϕ:
    is_subformula_of ϕ ϕ = true.
  Proof.
    destruct (is_subformula_of_P ϕ ϕ).
    - reflexivity.
    - assert (H: is_subformula_of_ind ϕ ϕ).
      apply sub_eq. reflexivity. contradiction.
  Qed.

  Lemma bsvar_subst_contains_subformula ϕ₁ ϕ₂ dbi :
    bsvar_occur ϕ₁ dbi = true ->
    is_subformula_of_ind ϕ₂ (ϕ₁^[svar: dbi ↦ ϕ₂]).
  Proof.
    generalize dependent dbi.
    induction ϕ₁; intros dbi H; simpl; simpl in H; try inversion H.
    - case_match; subst.
      + case_match; try lia. constructor. reflexivity.
      + congruence.
    - specialize (IHϕ₁1 dbi). specialize (IHϕ₁2 dbi).
      move: H H1 IHϕ₁1 IHϕ₁2.
      case: (bsvar_occur ϕ₁1 dbi); case: (bsvar_occur ϕ₁2 dbi); move=> H H1 IHϕ₁₁ IHϕ₁₂.
      + apply sub_app_l. auto.
      + apply sub_app_l. auto.
      + apply sub_app_r. auto.
      + done.
    - specialize (IHϕ₁1 dbi). specialize (IHϕ₁2 dbi).
      move: H H1 IHϕ₁1 IHϕ₁2.
      case: (bsvar_occur ϕ₁1 dbi); case: (bsvar_occur ϕ₁2 dbi); move=> H H1 IHϕ₁₁ IHϕ₁₂.
      + apply sub_imp_l. auto.
      + apply sub_imp_l. auto.
      + apply sub_imp_r. auto.
      + done.
    - apply sub_exists. auto.
    - apply sub_mu. apply IHϕ₁. auto.
  Qed.

  Lemma bevar_subst_contains_subformula ϕ₁ ϕ₂ dbi :
    bevar_occur ϕ₁ dbi = true ->
    is_subformula_of_ind ϕ₂ (ϕ₁^[evar: dbi ↦ ϕ₂]).
  Proof.
    generalize dependent dbi.
    induction ϕ₁; intros dbi H; simpl; simpl in H; try inversion H.
    - case_match; subst.
      + case_match; try lia. constructor. reflexivity.
      + congruence.
    - specialize (IHϕ₁1 dbi). specialize (IHϕ₁2 dbi).
      move: H H1 IHϕ₁1 IHϕ₁2.
      case: (bevar_occur ϕ₁1 dbi); case: (bevar_occur ϕ₁2 dbi); move=> H H1 IHϕ₁₁ IHϕ₁₂.
      + apply sub_app_l. auto.
      + apply sub_app_l. auto.
      + apply sub_app_r. auto.
      + done.
    - specialize (IHϕ₁1 dbi). specialize (IHϕ₁2 dbi).
      move: H H1 IHϕ₁1 IHϕ₁2.
      case: (bevar_occur ϕ₁1 dbi); case: (bevar_occur ϕ₁2 dbi); move=> H H1 IHϕ₁₁ IHϕ₁₂.
      + apply sub_imp_l. auto.
      + apply sub_imp_l. auto.
      + apply sub_imp_r. auto.
      + done.
    - apply sub_exists. auto.
    - apply sub_mu. apply IHϕ₁. auto.
  Qed.


  Lemma free_evars_subformula ϕ₁ ϕ₂ :
    is_subformula_of_ind ϕ₁ ϕ₂ -> free_evars ϕ₁ ⊆ free_evars ϕ₂.
  Proof.
    intros H. induction H.
    * subst. apply PreOrder_Reflexive.
    * simpl. eapply PreOrder_Transitive.
      apply IHis_subformula_of_ind.
      apply union_subseteq_l.
    * simpl. eapply PreOrder_Transitive.
      apply IHis_subformula_of_ind.
      apply union_subseteq_r.
    * simpl. eapply PreOrder_Transitive.
      apply IHis_subformula_of_ind.
      apply union_subseteq_l.
    * simpl. eapply PreOrder_Transitive.
      apply IHis_subformula_of_ind.
      apply union_subseteq_r.
    * simpl. auto.
    * simpl. auto.
  Qed.

  Corollary evar_fresh_in_subformula x ϕ₁ ϕ₂ :
    is_subformula_of_ind ϕ₁ ϕ₂ ->
    evar_is_fresh_in x ϕ₂ ->
    evar_is_fresh_in x ϕ₁.
  Proof.
    unfold evar_is_fresh_in.
    intros Hsub Hfresh.
    apply free_evars_subformula in Hsub.
    auto.
  Qed.

  Corollary evar_fresh_in_subformula' x ϕ₁ ϕ₂ :
    is_subformula_of ϕ₁ ϕ₂ ->
    evar_is_fresh_in x ϕ₂ ->
    evar_is_fresh_in x ϕ₁.
  Proof.
    intros Hsub Hfr.
    pose proof (H := elimT (is_subformula_of_P ϕ₁ ϕ₂) Hsub).
    eapply evar_fresh_in_subformula. eauto. auto.
  Qed.

  Lemma free_svars_subformula ϕ₁ ϕ₂ :
    is_subformula_of_ind ϕ₁ ϕ₂ -> free_svars ϕ₁ ⊆ free_svars ϕ₂.
  Proof.
    intros H. induction H.
    * subst. apply PreOrder_Reflexive.
    * simpl. eapply PreOrder_Transitive.
      apply IHis_subformula_of_ind.
      apply union_subseteq_l.
    * simpl. eapply PreOrder_Transitive.
      apply IHis_subformula_of_ind.
      apply union_subseteq_r.
    * simpl. eapply PreOrder_Transitive.
      apply IHis_subformula_of_ind.
      apply union_subseteq_l.
    * simpl. eapply PreOrder_Transitive.
      apply IHis_subformula_of_ind.
      apply union_subseteq_r.
    * simpl. auto.
    * simpl. auto.
  Qed.

  Corollary svar_fresh_in_subformula x ϕ₁ ϕ₂ :
    is_subformula_of_ind ϕ₁ ϕ₂ ->
    svar_is_fresh_in x ϕ₂ ->
    svar_is_fresh_in x ϕ₁.
  Proof.
    unfold svar_is_fresh_in.
    intros Hsub Hfresh.
    apply free_svars_subformula in Hsub.
    auto.
  Qed.

  Lemma free_evars_bsvar_subst ϕ₁ ϕ₂ dbi:
    free_evars (ϕ₁^[svar: dbi ↦ ϕ₂]) ⊆ free_evars ϕ₁ ∪ free_evars ϕ₂.
  Proof.
    generalize dependent dbi.
    induction ϕ₁; intros db; simpl.
    - apply union_subseteq_l.
    - apply empty_subseteq.
    - apply empty_subseteq.
    - case_match; set_solver.
    - apply empty_subseteq.
    - specialize (IHϕ₁1 db).
      specialize (IHϕ₁2 db).
      remember (free_evars (ϕ₁1^[svar: db ↦ ϕ₂])) as A1.
      remember (free_evars (ϕ₁2^[svar: db ↦ ϕ₂])) as A2.
      remember (free_evars ϕ₁1) as B1.
      remember (free_evars ϕ₁2) as B2.
      remember (free_evars ϕ₂) as C.
      rewrite <- union_assoc_L.
      rewrite {1}[B2 ∪ C]union_comm_L.
      rewrite -{1}[C]union_idemp_L.
      rewrite -[C ∪ C ∪ B2]union_assoc_L.
      rewrite [B1 ∪ _]union_assoc_L.
      rewrite [C ∪ B2]union_comm_L.
      apply union_mono; auto.
    - apply empty_subseteq.
    - specialize (IHϕ₁1 db).
      specialize (IHϕ₁2 db).
      remember (free_evars (ϕ₁1^[svar: db ↦ ϕ₂])) as A1.
      remember (free_evars (ϕ₁2^[svar: db ↦ ϕ₂])) as A2.
      remember (free_evars ϕ₁1) as B1.
      remember (free_evars ϕ₁2) as B2.
      remember (free_evars ϕ₂) as C.
      rewrite <- union_assoc_L.
      rewrite {1}[B2 ∪ C]union_comm_L.
      rewrite -{1}[C]union_idemp_L.
      rewrite -[C ∪ C ∪ B2]union_assoc_L.
      rewrite [B1 ∪ _]union_assoc_L.
      rewrite [C ∪ B2]union_comm_L.
      apply union_mono; auto.
    - auto.
    - auto.
  Qed.

  Lemma free_svars_bevar_subst ϕ₁ ϕ₂ dbi:
    free_svars (ϕ₁^[evar: dbi ↦ ϕ₂]) ⊆ free_svars ϕ₁ ∪ free_svars ϕ₂.
  Proof.
    generalize dependent dbi.
    induction ϕ₁; intros db; simpl.
    - apply empty_subseteq.
    - apply union_subseteq_l.
    - case_match; set_solver.
    - apply empty_subseteq.
    - apply empty_subseteq.
    - specialize (IHϕ₁1 db).
      specialize (IHϕ₁2 db).
      remember (free_svars (ϕ₁1^[evar: db ↦ ϕ₂])) as A1.
      remember (free_svars (ϕ₁2^[evar: db ↦ ϕ₂])) as A2.
      remember (free_svars ϕ₁1) as B1.
      remember (free_svars ϕ₁2) as B2.
      remember (free_svars ϕ₂) as C.
      rewrite <- union_assoc_L.
      rewrite {1}[B2 ∪ C]union_comm_L.
      rewrite -{1}[C]union_idemp_L.
      rewrite -[C ∪ C ∪ B2]union_assoc_L.
      rewrite [B1 ∪ _]union_assoc_L.
      rewrite [C ∪ B2]union_comm_L.
      apply union_mono; auto.
    - apply empty_subseteq.
    - specialize (IHϕ₁1 db).
      specialize (IHϕ₁2 db).
      remember (free_svars (ϕ₁1^[evar: db ↦ ϕ₂])) as A1.
      remember (free_svars (ϕ₁2^[evar: db ↦ ϕ₂])) as A2.
      remember (free_svars ϕ₁1) as B1.
      remember (free_svars ϕ₁2) as B2.
      remember (free_svars ϕ₂) as C.
      rewrite <- union_assoc_L.
      rewrite {1}[B2 ∪ C]union_comm_L.
      rewrite -{1}[C]union_idemp_L.
      rewrite -[C ∪ C ∪ B2]union_assoc_L.
      rewrite [B1 ∪ _]union_assoc_L.
      rewrite [C ∪ B2]union_comm_L.
      apply union_mono; auto.
    - auto.
    - auto.
  Qed.

  Lemma free_evars_bsvar_subst_1 ϕ₁ ϕ₂ dbi:
    free_evars ϕ₁ ⊆ free_evars (ϕ₁^[svar: dbi ↦ ϕ₂]).
  Proof.
    generalize dependent dbi.
    induction ϕ₁; intros dbi; simpl; try apply reflexivity.
    - apply empty_subseteq.
    - apply union_mono; auto.
    - apply union_mono; auto.
    - auto.
    - auto.
  Qed.

  Lemma free_svars_bevar_subst_1 ϕ₁ ϕ₂ dbi:
    free_svars ϕ₁ ⊆ free_svars (ϕ₁^[evar: dbi ↦ ϕ₂]).
  Proof.
    generalize dependent dbi.
    induction ϕ₁; intros dbi; simpl; try apply reflexivity.
    - apply empty_subseteq.
    - apply union_mono; auto.
    - apply union_mono; auto.
    - auto.
    - auto.
  Qed.

  Corollary free_evars_bsvar_subst_eq ϕ₁ ϕ₂ dbi:
    bsvar_occur ϕ₁ dbi ->
    free_evars (ϕ₁^[svar: dbi ↦ ϕ₂]) = free_evars ϕ₁ ∪ free_evars ϕ₂.
  Proof.
    intros H.
    apply (anti_symm subseteq).
    - apply free_evars_bsvar_subst.
    - apply union_least.
      + apply free_evars_bsvar_subst_1.
      + pose proof (Hsub := bsvar_subst_contains_subformula ϕ₁ ϕ₂ dbi H).
        apply free_evars_subformula. auto.
  Qed.

  Corollary free_svars_bevar_subst_eq ϕ₁ ϕ₂ dbi:
    bevar_occur ϕ₁ dbi ->
    free_svars (ϕ₁^[evar: dbi ↦ ϕ₂]) = free_svars ϕ₁ ∪ free_svars ϕ₂.
  Proof.
    intros H.
    apply (anti_symm subseteq).
    - apply free_svars_bevar_subst.
    - apply union_least.
      + apply free_svars_bevar_subst_1.
      + pose proof (Hsub := bevar_subst_contains_subformula ϕ₁ ϕ₂ dbi H).
        apply free_svars_subformula. auto.
  Qed.

  Lemma wfc_mu_aux_implies_not_bsvar_occur phi ns :
    well_formed_closed_mu_aux phi ns ->
    bsvar_occur phi ns = false.
  Proof.
    move: ns.
    induction phi; intros ns Hwfc; simpl; simpl in Hwfc; auto.
    - repeat case_match; try lia. congruence.
    - apply andb_true_iff in Hwfc.
      destruct Hwfc as [Hwfc1 Hwfc2].
      destruct (bsvar_occur phi1 ns) eqn:Heq1, (bsvar_occur phi2 ns) eqn:Heq2; simpl.
      rewrite IHphi1 in Heq1. assumption. congruence.
      rewrite IHphi1 in Heq1. assumption. congruence.
      rewrite IHphi2 in Heq2. assumption. congruence.
      rewrite IHphi2 in Heq2. assumption. congruence.
    - apply andb_true_iff in Hwfc.
      destruct Hwfc as [Hwfc1 Hwfc2].
      destruct (bsvar_occur phi1 ns) eqn:Heq1, (bsvar_occur phi2 ns) eqn:Heq2; simpl.
      rewrite IHphi1 in Heq1. assumption. congruence.
      rewrite IHphi1 in Heq1. assumption. congruence.
      rewrite IHphi2 in Heq2. assumption. congruence.
      rewrite IHphi2 in Heq2. assumption. congruence.
  Qed.

  Lemma wfc_ex_aux_implies_not_bevar_occur phi ne :
    well_formed_closed_ex_aux phi ne ->
    bevar_occur phi ne = false.
  Proof.
    move: ne.
    induction phi; intros ne Hwfc; simpl; simpl in Hwfc; auto.
    - apply bool_decide_eq_false.
      case_match;[lia|congruence].
    - apply andb_true_iff in Hwfc.
      destruct Hwfc as [Hwfc1 Hwfc2].
      erewrite IHphi1; eauto.
    - apply andb_true_iff in Hwfc.
      destruct Hwfc as [Hwfc1 Hwfc2].
      erewrite IHphi1, IHphi2; eauto.
  Qed.

  Corollary wfc_mu_implies_not_bsvar_occur phi n :
    well_formed_closed_mu_aux phi 0 ->
    ~ bsvar_occur phi n.
  Proof.
    intros H.
    erewrite wfc_mu_aux_implies_not_bsvar_occur. exact notF.
    unfold well_formed_closed in H.
    eapply well_formed_closed_mu_aux_ind.
    2: eassumption. lia.
  Qed.

  Lemma wfc_ex_implies_not_bevar_occur phi n :
    well_formed_closed_ex_aux phi 0 ->
    bevar_occur phi n = false.
  Proof.
    intros H.
    erewrite wfc_ex_aux_implies_not_bevar_occur.
    { reflexivity. }
    eapply well_formed_closed_ex_aux_ind.
    2: apply H.
    lia.
  Qed.


  Lemma not_bsvar_occur_bsvar_subst_2 phi psi n:
    well_formed_closed_mu_aux psi 0 -> well_formed_closed_mu_aux phi (S n) ->
    bsvar_occur (phi^[svar: n ↦ psi]) n = false
  .
  Proof.
    move: psi n.
    induction phi; cbn; intros psi n' Hwfpsi Hwfphi; try reflexivity.
    {
      repeat case_match; cbn in *; repeat case_match; try reflexivity; try lia.
      {
        subst.
        pose proof (Htmp :=  wfc_mu_implies_not_bsvar_occur psi n' Hwfpsi).
        unfold is_true in Htmp.
        apply not_true_is_false in Htmp.
        exact Htmp.
      }
      {
        congruence.
      }
    }
    {
      unfold is_true in Hwfphi.
      rewrite andb_true_iff in Hwfphi.
      destruct Hwfphi as [Hwf1 Hwf2].
      rewrite orb_false_iff.
      naive_solver.
    }
    {
      unfold is_true in Hwfphi.
      rewrite andb_true_iff in Hwfphi.
      destruct Hwfphi as [Hwf1 Hwf2].
      rewrite orb_false_iff.
      naive_solver.
    }
    {
      naive_solver.
    }
    {
      naive_solver.
    }
  Qed.

  Lemma not_bsvar_occur_bsvar_subst phi psi n:
    well_formed_closed_mu_aux psi 0 -> well_formed_closed_mu_aux phi n ->
    ~ bsvar_occur (phi^[svar: n ↦ psi]) n.
  Proof.
    move: n.
    induction phi; intros n' H H0; simpl; auto.
    - intros Hcontra.
      case_match.
      + subst. simpl in Hcontra. case_match.
        * lia.
        * congruence.
      + apply wfc_mu_implies_not_bsvar_occur with (n := n') in H. congruence.
      + subst. simpl in Hcontra. inversion H0. case_match.
        * lia.
        * congruence.
    - intros Hcontra.
      destruct (bsvar_occur (phi1^[svar: n' ↦ psi]) n') eqn:Heq1, (bsvar_occur (phi2^[svar: n' ↦ psi]) n') eqn:Heq2.
      + eapply IHphi2; eauto. now apply andb_true_iff in H0.
      + eapply IHphi1; eauto. now apply andb_true_iff in H0.
      + eapply IHphi2; eauto. now apply andb_true_iff in H0.
      + simpl in Hcontra. congruence.
    - intros Hcontra.
      destruct (bsvar_occur ((phi1^[svar: n' ↦ psi])) n')
               eqn:Heq1, (bsvar_occur ((phi2^[svar: n' ↦ psi])) n') eqn:Heq2.
      + eapply IHphi1; eauto. now apply andb_true_iff in H0.
      + eapply IHphi1; eauto. now apply andb_true_iff in H0.
      + eapply IHphi2; eauto. now apply andb_true_iff in H0.
      + simpl in Hcontra. congruence.
  Qed.

  Lemma not_bsvar_occur_impl_no_neg_occ_and_no_pos_occ phi n:
    ~ bsvar_occur phi n ->
    no_negative_occurrence_db_b n phi && no_positive_occurrence_db_b n phi.
  Proof.
    move: n.
    induction phi; intros n' H; simpl; simpl in H; cbn; auto.
    - unfold not in H.
      case_match; auto.
    - destruct (bsvar_occur phi1 n') eqn: Heq3;
        destruct (bsvar_occur phi2 n') eqn:Heq4;
        simpl; auto.
      specialize (IHphi1 n'). specialize (IHphi2 n').
      rewrite Heq3 in IHphi1. rewrite Heq4 in IHphi2. clear Heq3 Heq4.
      specialize (IHphi1 ssrbool.not_false_is_true).
      specialize (IHphi2 ssrbool.not_false_is_true).
      apply andb_true_iff in IHphi1.
      apply andb_true_iff in IHphi2.
      destruct IHphi1 as [H1n H1p].
      destruct IHphi2 as [H2n H2p].
      rewrite H1n. rewrite H1p. rewrite H2n. rewrite H2p.
      simpl. reflexivity.
    - destruct (bsvar_occur phi1 n') eqn: Heq3;
        destruct (bsvar_occur phi2 n') eqn:Heq4;
        simpl; auto.
      specialize (IHphi1 n'). specialize (IHphi2 n').
      rewrite Heq3 in IHphi1. rewrite Heq4 in IHphi2. clear Heq3 Heq4.
      specialize (IHphi1 ssrbool.not_false_is_true).
      specialize (IHphi2 ssrbool.not_false_is_true).
      apply andb_true_iff in IHphi1.
      apply andb_true_iff in IHphi2.
      destruct IHphi1 as [H1n H1p].
      destruct IHphi2 as [H2n H2p].
      fold no_negative_occurrence_db_b no_positive_occurrence_db_b.
      rewrite H1n. rewrite H1p. rewrite H2n. rewrite H2p.
      simpl. reflexivity.
  Qed.

  Corollary not_bsvar_occur_impl_pos_occ_db phi n:
    ~ bsvar_occur phi n ->
    no_positive_occurrence_db_b n phi.
  Proof.
    intros H.
    pose proof (H1 := not_bsvar_occur_impl_no_neg_occ_and_no_pos_occ _ _ H).
    now apply andb_true_iff in H1.
  Qed.

  Corollary not_bsvar_occur_impl_neg_occ_db phi n:
    ~ bsvar_occur phi n ->
    no_negative_occurrence_db_b n phi.
  Proof.
    intros H.
    pose proof (H1 := not_bsvar_occur_impl_no_neg_occ_and_no_pos_occ _ _ H).
    now apply andb_true_iff in H1.
  Qed.

End syntax.

Module Notations.

Export MatchingLogic.Pattern.Notations.
Export MatchingLogic.PatternContext.Notations.

End Notations.

#[export]
 Hint Resolve
 evar_is_fresh_in_richer
 set_evar_fresh_is_fresh
 set_svar_fresh_is_fresh
 x_eq_fresh_impl_x_notin_free_evars
  : core.

#[export]
 Hint Extern 0 (is_true (@well_formed _ _)) => unfold is_true : core.

#[export]
 Hint Resolve well_formed_bott : core.

#[export]
 Hint Resolve well_formed_imp : core.

#[export]
 Hint Resolve well_formed_app : core.

#[export]
 Hint Resolve wf_sctx : core.

#[export]
 Hint Resolve well_formed_ex_app : core.

#[export]
 Hint Resolve well_formed_impl_well_formed_ex : core.

#[export]
 Hint Resolve well_formed_free_evar_subst : core.

#[export]
 Hint Resolve well_formed_free_evar_subst_0 : core.

#[export]
 Hint Resolve <- evar_is_fresh_in_exists : core.

#[export]
 Hint Resolve evar_is_fresh_in_evar_quantify : core.

(* Tactics for resolving goals involving sets *)
(*
        eauto 5 using @sets.elem_of_union_l, @sets.elem_of_union_r with typeclass_instances.
 *)
(*
  eauto depth using @sets.union_subseteq_l, @sets.union_subseteq_r
    with typeclass_instances.
 *)

(*
#[export]
 Hint Extern 10 (free_evars _ ⊆ free_evars _) => solve_free_evars_inclusion : core.
 *)


#[export]
 Hint Resolve wf_imp_wfc : core.

#[export]
 Hint Resolve wfc_ex_implies_not_bevar_occur : core.

Section with_signature.
  Context {Σ : Signature}.
  Open Scope ml_scope.

  Definition evar_quantify_ctx (x : evar) (n : db_index) (C : PatternCtx) : PatternCtx :=
    match decide (x = pcEvar C)  with
    | left _ => C
    | right pf => Build_PatternCtx (pcEvar C) ((pcPattern C)^{{evar: x ↦ n}})
    end.

  Lemma is_linear_context_evar_quantify (x : evar) (n : db_index) (C : PatternCtx) :
    is_linear_context C ->
    is_linear_context (evar_quantify_ctx x n C).
  Proof.
    intros Hlin. unfold evar_quantify_ctx.
    unfold is_linear_context in *.
    destruct (decide (x = pcEvar C)); simpl.
    - assumption.
    - destruct C. simpl in *.
      rename pcEvar into pcEvar0. rename pcPattern into pcPattern0.
      assert (count_evar_occurrences pcEvar0 (pcPattern0^{{evar: x ↦ n}})
              = count_evar_occurrences pcEvar0 pcPattern0).
      {
        clear Hlin.
        move: n.
        induction pcPattern0; intros n'; simpl in *; try lia.
        + destruct (decide (x0 = pcEvar0)); subst; simpl in *.
          * destruct (decide (x = pcEvar0)); try contradiction; simpl in *.
            destruct (decide (pcEvar0 = pcEvar0)); try contradiction. reflexivity.
          * destruct (decide (x = x0)); simpl; try reflexivity.
            destruct (decide (x0 = pcEvar0)); try contradiction.
            reflexivity.
        + rewrite IHpcPattern0_1. rewrite IHpcPattern0_2. reflexivity.
        + rewrite IHpcPattern0_1. rewrite IHpcPattern0_2. reflexivity.
        + rewrite IHpcPattern0. reflexivity.
        + rewrite IHpcPattern0. reflexivity.
      }
      congruence.
  Qed.

  Definition svar_quantify_ctx (X : svar) (n : db_index) (C : PatternCtx) : PatternCtx :=
    Build_PatternCtx (pcEvar C) ((pcPattern C)^{{svar: X ↦ n}}).

  Lemma is_linear_context_svar_quantify (X : svar) (n : db_index) (C : PatternCtx) :
    is_linear_context C ->
    is_linear_context (svar_quantify_ctx X n C).
  Proof.
    intros Hlin. unfold svar_quantify_ctx. unfold is_linear_context in *.
    destruct C. simpl in *.
    rename pcEvar into pcEvar0. rename pcPattern into pcPattern0.
    assert (count_evar_occurrences pcEvar0 (pcPattern0^{{svar: X ↦ n}})
            = count_evar_occurrences pcEvar0 pcPattern0).
    {
      clear Hlin.
      move: n.
      induction pcPattern0; intros n'; simpl in *; try lia.
      + case_match; subst; simpl in *; reflexivity.
      + rewrite IHpcPattern0_1. rewrite IHpcPattern0_2. reflexivity.
      + rewrite IHpcPattern0_1. rewrite IHpcPattern0_2. reflexivity.
      + rewrite IHpcPattern0. reflexivity.
      + rewrite IHpcPattern0. reflexivity.
    }
    congruence.
  Qed.

  Lemma svar_quantify_free_evar_subst ψ ϕ x X n:
    ψ^[[evar: x ↦ ϕ]]^{{svar: X ↦ n}} =
    ψ^{{svar: X ↦ n}}^[[evar: x ↦ ϕ^{{svar: X ↦ n}}]].
  Proof.
    move: n.
    induction ψ; intros n'; simpl; auto.
    - case_match.
      + auto.
      + simpl. reflexivity.
    - case_match; reflexivity.
    - rewrite IHψ1. rewrite IHψ2. reflexivity.
    - rewrite IHψ1. rewrite IHψ2. reflexivity.
    - rewrite IHψ. reflexivity.
    - rewrite IHψ. Fail reflexivity.
  Abort. (* OOPS, does not hold. The problem is that [free_evar_subst'] does not wrap the target
            in nest_mu. *)


  Lemma svar_quantify_emplace X n C ϕ:
    (emplace C ϕ)^{{svar: X ↦ n}} = emplace (svar_quantify_ctx X n C) (ϕ^{{svar: X ↦ n}}).
  Proof.
    destruct C.
    unfold svar_quantify_ctx,emplace. simpl.
  Abort.

  Lemma evar_quantify_subst_ctx x n AC ϕ:
    x ∉ AC_free_evars AC ->
    (subst_ctx AC ϕ)^{{evar: x ↦ n}} = subst_ctx AC (ϕ^{{evar: x ↦ n}}).
  Proof.
    intros Hx.
    induction AC.
    - reflexivity.
    - simpl. simpl in Hx.
      rewrite IHAC.
      { set_solver. }
      rewrite [p^{{evar: x ↦ n}}]evar_quantify_fresh.
      unfold evar_is_fresh_in. set_solver.
      reflexivity.
    - simpl. simpl in Hx.
      rewrite IHAC.
      { set_solver. }
      rewrite [p^{{evar: x ↦ n}}]evar_quantify_fresh.
      unfold evar_is_fresh_in. set_solver.
      reflexivity.
  Qed.

  

   Lemma wfp_free_svar_subst ϕ ψ X:
    well_formed_closed_mu_aux ψ 0 ->
    well_formed_positive ψ = true ->
    well_formed_positive ϕ = true ->
    svar_has_negative_occurrence X ϕ = false ->
    well_formed_positive (ϕ^[[svar: X ↦ ψ]]) = true
  with wfp_neg_free_svar_subst ϕ ψ X:
    well_formed_closed_mu_aux ψ 0 ->
    well_formed_positive ψ = true ->
    well_formed_positive ϕ = true ->
    svar_has_positive_occurrence X ϕ = false ->
    well_formed_positive (ϕ^[[svar: X ↦ ψ]]) = true.
  Proof.
    - intros Hwfcψ Hwfpψ Hwfpϕ Hnoneg.
      induction ϕ; simpl; auto.
      + case_match; [|reflexivity].
        assumption.
      + cbn in Hnoneg. cbn in Hwfpϕ.
        apply orb_false_iff in Hnoneg.
        destruct_and!. destruct_andb! Hwfpϕ.
        specialize (IHϕ1 ltac:(assumption) ltac:(assumption)).
        specialize (IHϕ2 ltac:(assumption) ltac:(assumption)).
        naive_bsolver.
      + cbn in Hnoneg. cbn in Hwfpϕ.
        apply orb_false_iff in Hnoneg.
        destruct_and!. destruct_andb! Hwfpϕ.
        pose proof (IH1 := wfp_neg_free_svar_subst ϕ1 ψ X ltac:(assumption)).
        ospecialize* IH1.
        { assumption. }
        { assumption. }
        { assumption. }
        specialize (IHϕ2 ltac:(assumption)).
        naive_bsolver.
      + cbn in Hnoneg. cbn in Hwfpϕ. destruct_andb! Hwfpϕ.
        rewrite IHϕ. assumption. assumption.
        rewrite nno_free_svar_subst; naive_bsolver.
    -
      intros Hwfcψ Hwfpψ Hwfpϕ Hnoneg.
      induction ϕ; simpl; auto.
      + case_match; [|reflexivity].
        assumption.
      + cbn in Hnoneg. cbn in Hwfpϕ.
        apply orb_false_iff in Hnoneg.
        destruct_and!. destruct_andb! Hwfpϕ.
        specialize (IHϕ1 ltac:(assumption) ltac:(assumption)).
        specialize (IHϕ2 ltac:(assumption) ltac:(assumption)).
        naive_bsolver.
      + cbn in Hnoneg. cbn in Hwfpϕ.
        apply orb_false_iff in Hnoneg.
        destruct_and!. destruct_andb! Hwfpϕ.
        pose proof (IH1 := wfp_free_svar_subst ϕ1 ψ X ltac:(assumption)).
        ospecialize* IH1.
        { assumption. }
        { assumption. }
        { assumption. }
        specialize (IHϕ2 ltac:(assumption)).
        naive_bsolver.
      + cbn in Hnoneg. cbn in Hwfpϕ. destruct_andb! Hwfpϕ.
        rewrite IHϕ. assumption. assumption.
        rewrite nno_free_svar_subst; naive_bsolver.
  Qed.

  Lemma count_evar_occurrences_bevar_subst pcEvar ϕ ψ k:
    count_evar_occurrences pcEvar ψ = 0 ->
    count_evar_occurrences pcEvar (ϕ^[evar: k ↦ ψ]) = count_evar_occurrences pcEvar ϕ.
  Proof.
    intros H.
    move: k.
    induction ϕ; intros k; simpl; auto.
    - case_match; auto.
  Qed.

  Lemma count_evar_occurrences_evar_open pcEvar ϕ x:
    pcEvar <> x ->
    count_evar_occurrences pcEvar (ϕ^{evar: 0 ↦ x}) = count_evar_occurrences pcEvar ϕ.
  Proof.
    intros H. apply count_evar_occurrences_bevar_subst. simpl. case_match; congruence.
  Qed.


  Lemma count_evar_occurrences_svar_open x dbi ϕ ψ:
    count_evar_occurrences x ψ = 0 ->
    count_evar_occurrences x (ϕ^[svar: dbi ↦ ψ]) = count_evar_occurrences x ϕ.
  Proof.
    move: dbi.
    induction ϕ; intros dbi H; simpl; auto.
    case_match; auto.
  Qed.

  Lemma free_evar_subst_bsvar_subst ϕ ψ ξ x dbi:
    well_formed_closed_mu_aux ξ 0 ->
    evar_is_fresh_in x ψ ->
    (ϕ^[svar: dbi ↦ ψ])^[[evar:x ↦ ξ]]
    = (ϕ^[[evar:x ↦ ξ]])^[svar: dbi ↦ ψ].
  Proof.
    move: dbi.
    induction ϕ; intros dbi H1 H2; simpl; auto.
    - repeat case_match; auto.
      erewrite well_formed_bsvar_subst. reflexivity.
      2: eassumption.
      lia.
    - repeat case_match; auto.
      apply free_evar_subst_no_occurrence. assumption.
    - rewrite IHϕ1; auto. rewrite IHϕ2; auto.
    - rewrite IHϕ1; auto. rewrite IHϕ2; auto.
    - rewrite IHϕ; auto.
    - rewrite IHϕ; auto.
  Qed.

  Lemma wf_svar_open_from_wf_mu X ϕ:
    well_formed (patt_mu ϕ) ->
    well_formed (ϕ^{svar: 0 ↦ X}).
  Proof.
    intros H.
    wf_auto2.
    (*compoundDecomposeWfGoal.
    apply (unary_wfxy_compose _).*) (* wf_auto2. *)
    (*
    wf_auto2_fast_done.
    compositeSimplifyAllWfHyps.
    wf_auto2_composite_step.
    (* wf_auto2_composite_step. *)
    Set Printing All.
    Search well_formed svar_open.
    wf_auto2.
    destruct_and!;
        [ (apply wfp_svar_open; auto)
        | (apply wfc_mu_aux_body_mu_imp1; assumption)
        | (apply wfc_ex_aux_body_mu_imp1; assumption)
        ].
    *)
  Qed.


  Lemma wfcex_after_subst_impl_wfcex_before ϕ ψ x dbi:
    well_formed_closed_ex_aux (ϕ^[[evar:x ↦ ψ]]) dbi = true ->
    well_formed_closed_ex_aux ϕ dbi = true.
  Proof.
    intros Hsubst.
    move: dbi Hsubst.
    induction ϕ; intros dbi Hsubst; simpl in *; try reflexivity; auto with nocore.
    - apply andb_prop in Hsubst. destruct Hsubst as [Hsubst1 Hsubst2].
      specialize (IHϕ1 dbi Hsubst1).
      specialize (IHϕ2 dbi Hsubst2).
      rewrite IHϕ1 IHϕ2.
      reflexivity.
    - apply andb_prop in Hsubst. destruct Hsubst as [Hsubst1 Hsubst2].
      specialize (IHϕ1 dbi Hsubst1).
      specialize (IHϕ2 dbi Hsubst2).
      rewrite IHϕ1 IHϕ2.
      reflexivity.
  Qed.

  Lemma wfcmu_after_subst_impl_wfcmu_before ϕ ψ x dbi:
    well_formed_closed_mu_aux (ϕ^[[evar:x ↦ ψ]]) dbi = true ->
    well_formed_closed_mu_aux ϕ dbi = true.
  Proof.
    intros Hsubst.
    move: dbi Hsubst.
    induction ϕ; intros dbi Hsubst; simpl in *; try reflexivity; auto with nocore.
    - apply andb_prop in Hsubst. destruct Hsubst as [Hsubst1 Hsubst2].
      specialize (IHϕ1 dbi Hsubst1).
      specialize (IHϕ2 dbi Hsubst2).
      rewrite IHϕ1 IHϕ2.
      reflexivity.
    - apply andb_prop in Hsubst. destruct Hsubst as [Hsubst1 Hsubst2].
      specialize (IHϕ1 dbi Hsubst1).
      specialize (IHϕ2 dbi Hsubst2).
      rewrite IHϕ1 IHϕ2.
      reflexivity.
  Qed.

  Lemma nno_after_subst_impl_nno_before ϕ ψ x dbi:
    no_negative_occurrence_db_b dbi (ϕ^[[evar:x ↦ ψ]]) = true ->
    no_negative_occurrence_db_b dbi ϕ = true
  with npo_after_subst_impl_npo_before ϕ ψ x dbi:
    no_positive_occurrence_db_b dbi (ϕ^[[evar:x ↦ ψ]]) = true ->
    no_positive_occurrence_db_b dbi ϕ = true.
  Proof.
    - move: dbi.
      induction ϕ; intros dbi Hsubst; cbn in *; try reflexivity; auto with nocore.
      + apply andb_prop in Hsubst. destruct Hsubst as [Hsubst1 Hsubst2].
        specialize (IHϕ1 dbi Hsubst1).
        specialize (IHϕ2 dbi Hsubst2).
        rewrite IHϕ1. rewrite IHϕ2.
        reflexivity.
      + apply andb_prop in Hsubst. destruct Hsubst as [Hsubst1 Hsubst2].
        fold no_positive_occurrence_db_b in Hsubst1.
        fold no_positive_occurrence_db_b.
        specialize (IHϕ2 dbi Hsubst2).
        rewrite IHϕ2.
        erewrite npo_after_subst_impl_npo_before.
        reflexivity. eassumption.
    - move: dbi.
      induction ϕ; intros dbi Hsubst; cbn in *; try reflexivity; auto with nocore.
      + apply andb_prop in Hsubst. destruct Hsubst as [Hsubst1 Hsubst2].
        specialize (IHϕ1 dbi Hsubst1).
        specialize (IHϕ2 dbi Hsubst2).
        rewrite IHϕ1. rewrite IHϕ2.
        reflexivity.
      + apply andb_prop in Hsubst. destruct Hsubst as [Hsubst1 Hsubst2].
        fold no_negative_occurrence_db_b in Hsubst1.
        fold no_negative_occurrence_db_b.
        specialize (IHϕ2 dbi Hsubst2).
        rewrite IHϕ2.
        erewrite nno_after_subst_impl_nno_before.
        reflexivity. eassumption.
  Qed.

  Lemma wfp_after_subst_impl_wfp_before ϕ ψ x:
    well_formed_positive (ϕ^[[evar:x ↦ ψ]]) = true ->
    well_formed_positive ϕ = true.
  Proof.
    intros Hsubst.
    move: Hsubst.
    induction ϕ; intros Hsubst; simpl in *; try reflexivity; auto with nocore.
    - apply andb_prop in Hsubst. destruct Hsubst as [Hsubst1 Hsubst2].
      specialize (IHϕ1 Hsubst1).
      specialize (IHϕ2 Hsubst2).
      rewrite IHϕ1. rewrite IHϕ2.
      reflexivity.
    - apply andb_prop in Hsubst. destruct Hsubst as [Hsubst1 Hsubst2].
      specialize (IHϕ1 Hsubst1).
      specialize (IHϕ2 Hsubst2).
      rewrite IHϕ1. rewrite IHϕ2.
      reflexivity.
    - apply andb_prop in Hsubst. destruct Hsubst as [Hnno Hsubst]. 
      specialize (IHϕ Hsubst).
      rewrite IHϕ.
      erewrite nno_after_subst_impl_nno_before.
      reflexivity. eassumption.
  Qed.

  Lemma wf_after_subst_impl_wf_before ϕ ψ x:
    well_formed (ϕ^[[evar:x ↦ ψ]]) = true ->
    well_formed ϕ = true.
  Proof.
    intros H.
    unfold well_formed,well_formed_closed in *.
    destruct_andb! H.
    eapply wfp_after_subst_impl_wfp_before in H0.
    eapply wfcmu_after_subst_impl_wfcmu_before in H.
    eapply wfcex_after_subst_impl_wfcex_before in H2.
    naive_bsolver.
  Qed.

  Lemma wf_emplaced_impl_wf_context (C : PatternCtx) (ψ : Pattern) :
    well_formed (emplace C ψ) = true ->
    PC_wf C.
  Proof.
    intros H.
    unfold emplace in H. unfold PC_wf.
    eapply wf_after_subst_impl_wf_before.
    eassumption.
  Qed.

  Global Instance evar_is_fresh_in_dec (x : evar) (p : Pattern) :
    Decision (evar_is_fresh_in x p).
  Proof.
    unfold evar_is_fresh_in.
    apply not_dec. apply gset_elem_of_dec.
  Defined.

  Definition evar_is_fresh_in_list (x : evar) (l : list Pattern) :=
    Forall (evar_is_fresh_in x) l.

  Global Instance evar_is_fresh_in_list_dec (x : evar) (l : list Pattern) :
    Decision (evar_is_fresh_in_list x l).
  Proof.
    unfold Decision. unfold evar_is_fresh_in_list.
    apply Forall_dec.
    intros p.
    apply evar_is_fresh_in_dec.
  Defined.

  Lemma evar_fresh_in_foldr x g l:
  evar_is_fresh_in x (foldr patt_imp g l) <-> evar_is_fresh_in x g /\ evar_is_fresh_in_list x l.
  Proof.
  induction l; simpl; split; intros H.
  - split;[assumption|]. unfold evar_is_fresh_in_list. by apply Forall_nil.
  - destruct H as [H _]. exact H.
  - unfold evar_is_fresh_in_list,evar_is_fresh_in in *. simpl in *.
    split;[set_solver|].
    apply Forall_cons.
    destruct IHl as [IHl1 IHl2].
    set_solver.
  - unfold evar_is_fresh_in_list,evar_is_fresh_in in *. simpl in *.
    destruct IHl as [IHl1 IHl2].
    destruct H as [H1 H2].
    inversion H2; subst.
    specialize (IHl2 (conj H1 H4)).
    set_solver.
  Qed.

  Global Instance svar_is_fresh_in_dec (X : svar) (p : Pattern) :
    Decision (svar_is_fresh_in X p).
  Proof.
    unfold svar_is_fresh_in.
    apply not_dec. apply gset_elem_of_dec.
  Defined.

  Definition svar_is_fresh_in_list (X : svar) (l : list Pattern) :=
    Forall (svar_is_fresh_in X) l.

  Global Instance svar_is_fresh_in_list_dec (X : svar) (l : list Pattern) :
    Decision (svar_is_fresh_in_list X l).
  Proof.
    unfold Decision. unfold svar_is_fresh_in_list.
    apply Forall_dec.
    intros p.
    apply svar_is_fresh_in_dec.
  Defined.

  Lemma wfc_ex_lower ϕ n:
    bevar_occur ϕ n = false ->
    well_formed_closed_ex_aux ϕ (S n) = true ->
    well_formed_closed_ex_aux ϕ n = true.
  Proof.
    revert n.
    induction ϕ; intros n' H1 H2; simpl in *; auto.
    - repeat case_match; auto. lia.
    - apply orb_false_elim in H1. destruct_and!.
      erewrite -> IHϕ1.
      erewrite -> IHϕ2.
      reflexivity.
      all: try assumption.
      1-2: naive_bsolver.
    - apply orb_false_elim in H1. destruct_and!.
      erewrite -> IHϕ1.
      erewrite -> IHϕ2.
      reflexivity.
      all: try assumption.
      1-2: naive_bsolver.
  Qed.

  Lemma wfc_mu_lower ϕ n:
    bsvar_occur ϕ n = false ->
    well_formed_closed_mu_aux ϕ (S n) = true ->
    well_formed_closed_mu_aux ϕ n = true.
  Proof.
    intros H1 H2.
    move: n H1 H2.
    induction ϕ; intros n' H1 H2; simpl in *; auto.
    - repeat case_match; auto. lia.
   - apply orb_false_elim in H1. destruct_and!.
      erewrite -> IHϕ1.
      erewrite -> IHϕ2.
      reflexivity.
      all: try assumption.
      1-2: naive_bsolver.
    - apply orb_false_elim in H1. destruct_and!.
      erewrite -> IHϕ1.
      erewrite -> IHϕ2.
      reflexivity.
      all: try assumption.
      1-2: naive_bsolver.
  Qed.

  Lemma wf_ex_quan_impl_wf (x : evar) (ϕ : Pattern):
    bevar_occur ϕ 0 = false ->
    well_formed (exists_quantify x ϕ) = true ->
    well_formed ϕ = true.
  Proof.
    intros H0 H. unfold exists_quantify in H.
    unfold well_formed, well_formed_closed in *. destruct_andb! H. simpl in *.
    apply wfp_evar_quan_impl_wfp in H1.
    apply wfcmu_evar_quan_impl_wfcmu in H.
    apply wfcex_evar_quan_impl_wfcex in H3.
    apply wfc_ex_lower in H3. 2: assumption.
    naive_bsolver.
  Qed.

  Lemma bevar_occur_evar_open_2 dbi x ϕ:
    well_formed_closed_ex_aux ϕ dbi ->
    bevar_occur (ϕ^{evar: dbi ↦ x}) dbi = false.
  Proof.
    move: dbi.
    unfold evar_open.
    induction ϕ; intros dbi Hwf; simpl; try reflexivity.
    - case_match; simpl; auto.
      case_match; try lia. simpl in Hwf. case_match; [lia | congruence ].
    - simpl in Hwf. destruct_andb! Hwf.
      rewrite IHϕ1; auto. rewrite IHϕ2; auto.
    - simpl in Hwf. destruct_andb! Hwf.
      rewrite IHϕ1; auto. rewrite IHϕ2; auto.
    - rewrite IHϕ; auto.
    - rewrite IHϕ; auto.
  Qed.

  Lemma bsvar_occur_svar_open_2 dbi X ϕ:
    well_formed_closed_mu_aux ϕ dbi ->
    bsvar_occur (ϕ^{svar: dbi ↦ X}) dbi = false.
  Proof.
    move: dbi.
    unfold svar_open.
    induction ϕ; intros dbi Hwf; simpl; try reflexivity.
    - case_match; simpl; auto.
      case_match; try lia. simpl in Hwf. case_match; [lia | congruence ].
    - simpl in Hwf. destruct_andb! Hwf.
      rewrite IHϕ1; auto. rewrite IHϕ2; auto.
    - simpl in Hwf. destruct_andb! Hwf.
      rewrite IHϕ1; auto. rewrite IHϕ2; auto.
    - rewrite IHϕ; auto.
    - rewrite IHϕ; auto.
  Qed.

  Lemma svar_has_negative_occurrence_free_evar_subst
    (ϕ ψ: Pattern) (x : evar) (X : svar) :
    svar_is_fresh_in X ψ ->
    svar_has_negative_occurrence X ϕ^[[evar:x↦ψ]] = svar_has_negative_occurrence X ϕ
  with svar_has_positive_occurrence_free_evar_subst
    (ϕ ψ: Pattern) (x : evar) (X : svar) :
    svar_is_fresh_in X ψ ->
    svar_has_positive_occurrence X ϕ^[[evar:x↦ψ]] = svar_has_positive_occurrence X ϕ
  .
  Proof.
    {
      intros HXψ.
      induction ϕ; cbn in *; try reflexivity.
      {
        destruct (decide (x = x0)).
        {
          apply svar_hno_false_if_fresh.
          exact HXψ.
        }
        {
          cbn. reflexivity.
        }
      }
      {
        by rewrite IHϕ1 IHϕ2.
      }
      {
        fold svar_has_positive_occurrence.
        rewrite IHϕ2.
        rewrite svar_has_positive_occurrence_free_evar_subst.
        { exact HXψ. }
        reflexivity.
      }
      {
        exact IHϕ.
      }
      {
        exact IHϕ.
      }
    }
    {
      intros HXψ.
      induction ϕ; cbn in *; try reflexivity.
      {
        destruct (decide (x = x0)).
        {
          apply svar_hpo_false_if_fresh.
          exact HXψ.
        }
        {
          cbn. reflexivity.
        }
      }
      {
        by rewrite IHϕ1 IHϕ2.
      }
      {
        fold svar_has_negative_occurrence.
        rewrite IHϕ2.
        rewrite svar_has_negative_occurrence_free_evar_subst.
        { exact HXψ. }
        reflexivity.
      }
      {
        exact IHϕ.
      }
      {
        exact IHϕ.
      }
    }
  Qed.
    

  Fixpoint maximal_mu_depth_to (depth : nat) (E : evar) (ψ : Pattern) : nat :=
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
        (maximal_mu_depth_to depth E ψ₁)
        (maximal_mu_depth_to depth E ψ₂)
    | patt_app ψ₁ ψ₂
      => Nat.max
        (maximal_mu_depth_to depth E ψ₁)
        (maximal_mu_depth_to depth E ψ₂)
    | patt_exists ψ' =>
      maximal_mu_depth_to depth E ψ'
    | patt_mu ψ' =>
      maximal_mu_depth_to (S depth) E ψ'
    end.


  Fixpoint maximal_mu_depth_to_sv (depth : nat) (V : svar) (ψ : Pattern) : nat :=
    match ψ with
    | patt_bott => 0
    | patt_sym _ => 0
    | patt_bound_evar _ => 0
    | patt_bound_svar _ => 0
    | patt_free_evar _ => 0
    | patt_free_svar V' =>
      match (decide (V' = V)) with
      | left _ => depth
      | right _ => 0
      end
    | patt_imp ψ₁ ψ₂
      => Nat.max
        (maximal_mu_depth_to_sv depth V ψ₁)
        (maximal_mu_depth_to_sv depth V ψ₂)
    | patt_app ψ₁ ψ₂
      => Nat.max
        (maximal_mu_depth_to_sv depth V ψ₁)
        (maximal_mu_depth_to_sv depth V ψ₂)
    | patt_exists ψ' =>
      maximal_mu_depth_to_sv depth V ψ'
    | patt_mu ψ' =>
      maximal_mu_depth_to_sv (S depth) V ψ'
    end.

  Lemma maximal_mu_depth_to_svar_open depth E n X ψ:
  maximal_mu_depth_to depth E (ψ^{svar: n ↦ X})
    = maximal_mu_depth_to depth E ψ.
  Proof.
    unfold svar_open.
    move: depth n.
    induction ψ; intros depth n'; simpl; try reflexivity; auto.
    {
      case_match; simpl; try reflexivity.
    }
  Qed.


  Lemma maximal_mu_depth_to_sv_evar_open depth V n X ψ:
    maximal_mu_depth_to_sv depth V (ψ^{evar: n ↦ X})
    = maximal_mu_depth_to_sv depth V ψ.
  Proof.
    unfold evar_open.
    move: depth n.
    induction ψ; intros depth n'; simpl; try reflexivity; auto.
    {
      case_match; simpl; try reflexivity.
    }
  Qed.

  Lemma evar_open_mu_depth depth E n x ψ:
    E <> x ->
    maximal_mu_depth_to depth E (ψ^{evar: n ↦ x})
    = maximal_mu_depth_to depth E ψ.
  Proof.
    intros Hne.
    unfold evar_open.
    move: depth n.
    induction ψ; intros depth n'; simpl; try reflexivity; auto.
    {
      case_match; simpl; try reflexivity.
      case_match; simpl; try reflexivity.
      subst. contradiction.
    }
  Qed.

  Lemma svar_open_mu_depth_sc depth V n x ψ:
  V <> x ->
  maximal_mu_depth_to_sv depth V (ψ^{svar: n ↦ x})
  = maximal_mu_depth_to_sv depth V ψ.
  Proof.
    intros Hne.
    unfold svar_open.
    move: depth n.
    induction ψ; intros depth n'; simpl; try reflexivity; auto.
    {
      case_match; simpl; try reflexivity.
      case_match; simpl; try reflexivity.
      subst. contradiction.
    }
  Qed.

  Lemma svar_open_mu_depth depth E n X ψ:
    maximal_mu_depth_to depth E (ψ^{svar: n ↦ X})
    = maximal_mu_depth_to depth E ψ.
  Proof.
    unfold svar_open.
    move: depth n.
    induction ψ; intros depth n'; simpl; try reflexivity; auto.
    {
      case_match; simpl; try reflexivity.
    }
  Qed.

  Lemma maximal_mu_depth_to_0 E ψ depth:
    E ∉ free_evars ψ ->
    maximal_mu_depth_to depth E ψ = 0.
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

  Lemma maximal_mu_depth_to_sv_0 V ψ depth:
    V ∉ free_svars ψ ->
    maximal_mu_depth_to_sv depth V ψ = 0.
  Proof.
    intros Hnotin.
    move: V depth Hnotin.
    induction ψ; intros E depth Hnotin; simpl in *; try reflexivity.
    { case_match. set_solver. reflexivity. }
    { rewrite IHψ1. set_solver. rewrite IHψ2. set_solver. reflexivity. }
    { rewrite IHψ1. set_solver. rewrite IHψ2. set_solver. reflexivity. }
    { rewrite IHψ. exact Hnotin. reflexivity. }
    { rewrite IHψ. exact Hnotin. reflexivity. }
  Qed.

  Lemma maximal_mu_depth_to_S E ψ depth:
    E ∈ free_evars ψ ->
    maximal_mu_depth_to (S depth) E ψ
    = S (maximal_mu_depth_to depth E ψ).
  Proof.
    intros Hin.
    move: E depth Hin.
    induction ψ; intros E depth Hin; simpl in *; try set_solver.
    { case_match. reflexivity. set_solver. }
    {
      destruct (decide (E ∈ free_evars ψ1)),(decide (E ∈ free_evars ψ2)).
      {
        rewrite IHψ1. assumption. rewrite IHψ2. assumption. simpl. reflexivity.
      }
      {
        rewrite IHψ1. assumption.
        apply maximal_mu_depth_to_0 with (depth := S depth) in n
          as n'.
        apply maximal_mu_depth_to_0 with (depth := depth) in n.
        rewrite n. lia. 
      }
      {
        rewrite IHψ2. assumption.
        apply maximal_mu_depth_to_0 with (depth := S depth) in n
          as n'.
        apply maximal_mu_depth_to_0 with (depth := depth) in n.
        rewrite n. lia. 
      }
      {
        exfalso. set_solver.
      }
    }
    {
      destruct (decide (E ∈ free_evars ψ1)),(decide (E ∈ free_evars ψ2)).
      {
        rewrite IHψ1. assumption. rewrite IHψ2. assumption. simpl. reflexivity.
      }
      {
        rewrite IHψ1. assumption.
        apply maximal_mu_depth_to_0 with (depth := S depth) in n
          as n'.
        apply maximal_mu_depth_to_0 with (depth := depth) in n.
        rewrite n. lia. 
      }
      {
        rewrite IHψ2. assumption.
        apply maximal_mu_depth_to_0 with (depth := S depth) in n
          as n'.
        apply maximal_mu_depth_to_0 with (depth := depth) in n.
        rewrite n. lia. 
      }
      {
        exfalso. set_solver.
      }
    }
  Qed.

  Lemma maximal_mu_depth_to_sv_S V ψ depth:
    V ∈ free_svars ψ ->
    maximal_mu_depth_to_sv (S depth) V ψ
    = S (maximal_mu_depth_to_sv depth V ψ).
  Proof.
    intros Hin.
    move: V depth Hin.
    induction ψ; intros V depth Hin; simpl in *; try set_solver.
    { case_match. reflexivity. set_solver. }
    {
      destruct (decide (V ∈ free_svars ψ1)),(decide (V ∈ free_svars ψ2)).
      {
        rewrite IHψ1. assumption. rewrite IHψ2. assumption. simpl. reflexivity.
      }
      {
        rewrite IHψ1. assumption.
        apply maximal_mu_depth_to_sv_0 with (depth := S depth) in n
          as n'.
        apply maximal_mu_depth_to_sv_0 with (depth := depth) in n.
        rewrite n. lia. 
      }
      {
        rewrite IHψ2. assumption.
        apply maximal_mu_depth_to_sv_0 with (depth := S depth) in n
          as n'.
        apply maximal_mu_depth_to_sv_0 with (depth := depth) in n.
        rewrite n. lia. 
      }
      {
        exfalso. set_solver.
      }
    }
    {
      destruct (decide (V ∈ free_svars ψ1)),(decide (V ∈ free_svars ψ2)).
      {
        rewrite IHψ1. assumption. rewrite IHψ2. assumption. simpl. reflexivity.
      }
      {
        rewrite IHψ1. assumption.
        apply maximal_mu_depth_to_sv_0 with (depth := S depth) in n
          as n'.
        apply maximal_mu_depth_to_sv_0 with (depth := depth) in n.
        rewrite n. lia. 
      }
      {
        rewrite IHψ2. assumption.
        apply maximal_mu_depth_to_sv_0 with (depth := S depth) in n
          as n'.
        apply maximal_mu_depth_to_sv_0 with (depth := depth) in n.
        rewrite n. lia. 
      }
      {
        exfalso. set_solver.
      }
    }
  Qed.

  Definition mu_in_evar_path E ψ sdepth
  := negb (Nat.eqb 0 (maximal_mu_depth_to sdepth E ψ)).


  Lemma hbvum_impl_mmdt0 phi dbi x y k:
    evar_is_fresh_in x phi ->
    evar_is_fresh_in y phi ->
    well_formed_closed_mu_aux phi (S dbi) ->
    maximal_mu_depth_to k y phi^[svar:dbi↦patt_free_evar y] = 0 ->
    maximal_mu_depth_to k x phi^[svar:dbi↦patt_free_evar x] = 0
  .
  Proof.
    move: x y dbi k.
    induction phi; intros x' y dbi k Hfrx' Hfry Hwf H; cbn in *; try reflexivity.
    {
      unfold evar_is_fresh_in in *. cbn in *.
      repeat case_match; subst; try reflexivity.
      set_solver. 
    }
    {
      repeat case_match; cbn in *; try reflexivity;
      rewrite decide_eq_same; try reflexivity; subst;
      case_match; subst; cbn in *; try reflexivity; contradiction.
    }
    {
      unfold evar_is_fresh_in in *. cbn in *.
      rewrite -> IHphi1 with (y := y).
      5: lia.
      4: wf_auto2.
      3: set_solver.
      2: set_solver.
      cbn. apply IHphi2 with (y := y).
      { set_solver. }
      { set_solver. }
      { wf_auto2. }
      { lia. }
    }
    {
      unfold evar_is_fresh_in in *. cbn in *.
      rewrite -> IHphi1 with (y := y).
      5: lia.
      4: wf_auto2.
      3: set_solver.
      2: set_solver.
      cbn. apply IHphi2 with (y := y).
      { set_solver. }
      { set_solver. }
      { wf_auto2. }
      { lia. }
    }
    {
      eauto with nocore.
    }
    {
      eauto with nocore.
    }
  Qed.


  Lemma fresh_impl_no_mu_in_evar_path x phi k:
    evar_is_fresh_in x phi ->
    mu_in_evar_path x phi k = false.
  Proof.
    move: k x.
    induction phi; intros k x' Hx'; unfold mu_in_evar_path in *;
      cbn in *; try reflexivity.
    {
      destruct (decide (x = x')); try reflexivity.
      unfold evar_is_fresh_in in Hx'. cbn in Hx'.
      exfalso. set_solver.
    }
    {
      unfold evar_is_fresh_in in *.
      cbn in Hx'.
      specialize (IHphi1 k x' ltac:(set_solver)).
      specialize (IHphi2 k x' ltac:(set_solver)).
      repeat case_match; try reflexivity; cbn in *; lia.
    }
    {
      unfold evar_is_fresh_in in *.
      cbn in Hx'.
      specialize (IHphi1 k x' ltac:(set_solver)).
      specialize (IHphi2 k x' ltac:(set_solver)).
      repeat case_match; try reflexivity; cbn in *; lia.
    }
    {
      unfold evar_is_fresh_in in *.
      cbn in Hx'.
      specialize (IHphi k x' ltac:(set_solver)).
      exact IHphi.
    }
    {
      unfold evar_is_fresh_in in *.
      cbn in Hx'.
      specialize (IHphi (S k) x' ltac:(set_solver)).
      exact IHphi.
    }
  Qed.
  (*
  Fixpoint bound_svar_depth_is_max
    {Σ : Signature}
    (ϕ : Pattern)
    (dbi : db_index)
    (max_depth : nat)
  : Prop
  :=
  match ϕ with
  | patt_bound_evar _ => True
  | patt_bound_svar idx => 
    match (decide (idx = dbi)) with
    | left _ => False
    | right _ => True
    end
  | patt_free_evar _ => True
  | patt_free_svar _ => True
  | patt_bott => True
  | patt_sym _ => True
  | patt_imp ϕ₁ ϕ₂
    => (bound_svar_depth_is_max ϕ₁ dbi max_depth)
    /\ (bound_svar_depth_is_max ϕ₂ dbi max_depth)
  | patt_app ϕ₁ ϕ₂
    => (bound_svar_depth_is_max ϕ₁ dbi max_depth)
    /\ (bound_svar_depth_is_max ϕ₂ dbi max_depth)
  | patt_exists ϕ'
    => bound_svar_depth_is_max ϕ' dbi max_depth
  | patt_mu ϕ'
    =>
    match max_depth with
    | 0 => bsvar_occur ϕ' (S dbi) = false
    | S (max_depth') => bound_svar_depth_is_max ϕ' (S dbi) max_depth'
    end
  end.

  Fixpoint all_mu_bound_svars_have_max_depth
    (ϕ : Pattern)
    (max_depth : nat)
    : Prop
  :=
    match ϕ with
    | patt_bound_evar _ => True
    | patt_bound_svar _ => True
    | patt_free_evar _ => True
    | patt_free_svar _ => True
    | patt_bott => True
    | patt_sym _ => True
    | patt_imp ϕ₁ ϕ₂
      => (all_mu_bound_svars_have_max_depth ϕ₁ max_depth)
      /\ (all_mu_bound_svars_have_max_depth ϕ₂ max_depth)
    | patt_app ϕ₁ ϕ₂
      => (all_mu_bound_svars_have_max_depth ϕ₁ max_depth)
      /\ (all_mu_bound_svars_have_max_depth ϕ₂ max_depth)
    | patt_exists ϕ' =>
      all_mu_bound_svars_have_max_depth ϕ' max_depth
    | patt_mu ϕ'
      => bound_svar_depth_is_max ϕ' 0 max_depth
      /\ all_mu_bound_svars_have_max_depth ϕ' max_depth
    end
  . *)


  Fixpoint bound_svar_is_lt 
  {Σ : Signature}
  (ϕ : Pattern)
  (limit : nat)
  : Prop
  :=
  match ϕ with
  | patt_bound_evar idx => True
  | patt_bound_svar idx => idx < limit
  | patt_free_evar _ => True
  | patt_free_svar _ => True
  | patt_bott => True
  | patt_sym _ => True
  | patt_imp ϕ₁ ϕ₂
  => (bound_svar_is_lt ϕ₁ limit)
  /\ (bound_svar_is_lt ϕ₂ limit)
  | patt_app ϕ₁ ϕ₂
  => (bound_svar_is_lt ϕ₁ limit)
  /\ (bound_svar_is_lt ϕ₂ limit)
  | patt_exists ϕ' => bound_svar_is_lt ϕ' limit
  | patt_mu ϕ' => bound_svar_is_lt ϕ' limit
  end.

  Lemma maximal_mu_depth_to_not_0 ϕ x m:
    maximal_mu_depth_to m x ϕ <> 0 ->
    x ∈ free_evars ϕ
  .
  Proof.
    move: m.
    induction ϕ; cbn; intros m H; repeat case_match; try set_solver.
    {
      destruct (maximal_mu_depth_to m x ϕ1) eqn:Heq; cbn in *.
      { set_solver. }
      specialize (IHϕ1 m ltac:(lia)).
      rewrite elem_of_union. left. exact IHϕ1.
    }
    {
      destruct (maximal_mu_depth_to m x ϕ1) eqn:Heq; cbn in *.
      { set_solver. }
      specialize (IHϕ1 m ltac:(lia)).
      rewrite elem_of_union. left. exact IHϕ1.
    }
  Qed.

  Lemma bound_svar_is_lt_lt ϕ dbi1 dbi2:
    dbi1 < dbi2 ->
    bound_svar_is_lt ϕ dbi1 ->
    bound_svar_is_lt ϕ dbi2
  .
  Proof.
    induction ϕ; cbn; intros Hlt H; try exact I.
    { lia. }
    { naive_solver. }
    { naive_solver. }
    { naive_solver. }
    { naive_solver. }
  Qed.


  Lemma bound_svar_is_lt_notfree x ϕ dbi:
    well_formed_closed_mu_aux ϕ (S dbi) ->
    x ∉ free_evars ϕ ->
    bound_svar_is_lt ϕ dbi ->
    x ∉ free_evars ϕ^[svar:dbi↦patt_free_evar x]
  .
  Proof.
    move: dbi.
    induction ϕ; cbn; intros dbi Hwf Hxϕ Hϕdbi Hcontra.
    1,2,3: set_solver.
    {
      repeat case_match; cbn in *; try set_solver; subst; lia.
    }
    1: set_solver.
    {
      unfold is_true in Hwf.
      rewrite andb_true_iff in Hwf.
      destruct Hwf as [Hwf1 Hwf2].
      destruct Hϕdbi as [Hϕdbi1 Hϕdbi2].
      rewrite elem_of_union in Hxϕ.
      rewrite elem_of_union in Hcontra.
      destruct Hcontra; naive_solver.
    }
    1: set_solver.
    {
      unfold is_true in Hwf.
      rewrite andb_true_iff in Hwf.
      destruct Hwf as [Hwf1 Hwf2].
      destruct Hϕdbi as [Hϕdbi1 Hϕdbi2].
      rewrite elem_of_union in Hxϕ.
      rewrite elem_of_union in Hcontra.
      destruct Hcontra; naive_solver.
    }
    1: set_solver.
    {
      eapply IHϕ.
      { apply Hwf. }
      { exact Hxϕ. }
      {
        eapply bound_svar_is_lt_lt.
        2: { apply Hϕdbi. }
        { lia. }
      }
      { exact Hcontra. }
    }
  Qed.

  (* patt_bound_svar 1 *)
  (* patt_mu (patt_bound_svar 1)*)
  Lemma mu_in_evar_path_svar_subst_evar x ϕ dbi:
    well_formed_closed_mu_aux ϕ (S dbi) ->
    evar_is_fresh_in x ϕ ->
    bound_svar_is_lt ϕ (S dbi) ->
    mu_in_evar_path x ϕ^[svar:dbi↦patt_free_evar x] 0 = false
  .
  Proof.
    unfold evar_is_fresh_in.
    unfold mu_in_evar_path. unfold maximal_mu_depth_to.
    move: dbi.
    induction ϕ; cbn; intros dbi Hwf Hfr H; try reflexivity.
    {
      (* patt_free_evar *)
      repeat case_match; subst; cbn; try reflexivity; try lia.
    }
    {
      repeat case_match; subst; cbn; try reflexivity; try lia.
    }
    {
      fold maximal_mu_depth_to in *.
      specialize (IHϕ1 dbi).
      rewrite negb_false_iff in IHϕ1.
      rewrite Nat.eqb_eq in IHϕ1.
      rewrite <- IHϕ1.
      4: { naive_solver. }
      3: { cbn in Hfr. set_solver. }
      2: { wf_auto2. }
      specialize (IHϕ2 dbi).
      rewrite negb_false_iff in IHϕ2.
      rewrite Nat.eqb_eq in IHϕ2.
      rewrite <- IHϕ2.
      4: { naive_solver. }
      3: { cbn in Hfr. set_solver. }
      2: { wf_auto2. }
      cbn.
      reflexivity.
    }
    {
      fold maximal_mu_depth_to in *.
      specialize (IHϕ1 dbi).
      rewrite negb_false_iff in IHϕ1.
      rewrite Nat.eqb_eq in IHϕ1.
      rewrite <- IHϕ1.
      4: { naive_solver. }
      3: { cbn in Hfr. set_solver. }
      2: { wf_auto2. }
      specialize (IHϕ2 dbi).
      rewrite negb_false_iff in IHϕ2.
      rewrite Nat.eqb_eq in IHϕ2.
      rewrite <- IHϕ2.
      4: { naive_solver. }
      3: { cbn in Hfr. set_solver. }
      2: { wf_auto2. }
      cbn.
      reflexivity.
    }
    {
      fold maximal_mu_depth_to in *.
      specialize (IHϕ dbi).
      rewrite negb_false_iff in IHϕ.
      rewrite Nat.eqb_eq in IHϕ.
      rewrite <- IHϕ.
      4: { naive_solver. }
      3: { cbn in Hfr. set_solver. }
      2: { wf_auto2. }
      reflexivity.
    }
    {
      fold maximal_mu_depth_to in *.
      specialize (IHϕ (S dbi)).
      rewrite negb_false_iff in IHϕ.
      rewrite Nat.eqb_eq in IHϕ.
      case_match; cbn; try reflexivity.
      specialize (IHϕ Hwf Hfr).
      ospecialize* IHϕ.
      {
        eapply bound_svar_is_lt_lt.
        2: apply H.
        { lia. }
      }
      exfalso.
      pose proof (Htmp1 := maximal_mu_depth_to_not_0 (ϕ^[svar:(S dbi)↦patt_free_evar x]) x 1 ltac:(lia)).
      pose proof (Htmp2 := bound_svar_is_lt_notfree x ϕ (S dbi) Hwf Hfr H).
      clear -Htmp1 Htmp2.
      contradiction.
    }
  Qed.


  Fixpoint mu_depth_to_fev_limited
    (E : evar)
    (ψ : Pattern)
    (limit : nat)
    : Prop
  :=
  match ψ with
  | patt_free_evar _ => True
  | patt_free_svar _ => True
  | patt_bound_evar _ => True
  | patt_bound_svar _ => True
  | patt_bott => True
  | patt_sym _ => True
  | patt_imp ϕ₁ ϕ₂
    => mu_depth_to_fev_limited E ϕ₁ limit
    /\ mu_depth_to_fev_limited E ϕ₂ limit
  | patt_app ϕ₁ ϕ₂
    => mu_depth_to_fev_limited E ϕ₁ limit
    /\ mu_depth_to_fev_limited E ϕ₂ limit
  | patt_exists ϕ'
    => mu_depth_to_fev_limited E ϕ' limit
  | patt_mu ϕ'
    => match limit with
      | 0 => evar_is_fresh_in E ϕ'
      | S limit' => mu_depth_to_fev_limited E ϕ' limit'
      end
  end.

  (*
  Lemma l x ϕ limit:
    evar_is_fresh_in x ϕ ->
    mu_depth_to_fev_limited x ϕ limit ->
    mu_in_evar_path x ϕ^[svar:0↦patt_free_evar x] 0 = false
  .
*)

  Lemma mu_depth_to_fev_limited_evar_open
  (E X : evar)
  (ϕ : Pattern)
  (dbi : db_index)
  (mudepth : nat)
  :
  E <> X ->
  mu_depth_to_fev_limited E ϕ mudepth ->
  mu_depth_to_fev_limited E ϕ^{evar:dbi↦X} mudepth
  .
  Proof.
  move: dbi mudepth.
  induction ϕ; cbn; intros dbi mudepth Hneq Hmd; try exact I.
  {
    case_match; cbn; try exact I.
  }
  {
    naive_solver.
  }
  {
    naive_solver.
  }
  {
    naive_solver.
  }
  {
    repeat case_match; subst.
    {
      apply evar_is_fresh_in_evar_open.
      { exact Hneq. }
      { exact Hmd. }
    }
    { naive_solver. }
  }
  Qed.



  Fixpoint mu_depth_to_fsv_limited
    (X : svar)
    (ψ : Pattern)
    (limit : nat)
    : Prop
  :=
  match ψ with
  | patt_free_evar _ => True
  | patt_free_svar _ => True
  | patt_bound_evar _ => True
  | patt_bound_svar _ => True
  | patt_bott => True
  | patt_sym _ => True
  | patt_imp ϕ₁ ϕ₂
    => mu_depth_to_fsv_limited X ϕ₁ limit
    /\ mu_depth_to_fsv_limited X ϕ₂ limit
  | patt_app ϕ₁ ϕ₂
    => mu_depth_to_fsv_limited X ϕ₁ limit
    /\ mu_depth_to_fsv_limited X ϕ₂ limit
  | patt_exists ϕ'
    => mu_depth_to_fsv_limited X ϕ' limit
  | patt_mu ϕ'
    => match limit with
      | 0 => svar_is_fresh_in X ϕ'
      | S limit' => mu_depth_to_fsv_limited X ϕ' limit'
      end
  end.

  (*
  Lemma mu_depth_to_fsv_limited_svar_has_positive_negative_occurrence X ϕ:
    mu_depth_to_fsv_limited X ϕ 0 ->
    svar_has_positive_occurrence X ϕ = false
    /\ svar_has_negative_occurrence X ϕ = false
  .
  Proof.
    induction ϕ; cbn; intros H; split; try reflexivity.
    {
      destruct (decide (X = x)).
    }
  Qed.
  *)

  Lemma mu_depth_to_fsv_limited_svar_open
  (E X : svar)
  (ϕ : Pattern)
  (dbi : db_index)
  (mudepth : nat)
  :
  E <> X ->
  mu_depth_to_fsv_limited E ϕ mudepth ->
  mu_depth_to_fsv_limited E ϕ^{svar:dbi↦X} mudepth
  .
  Proof.
    move: dbi mudepth.
    induction ϕ; cbn; intros dbi mudepth Hneq Hmd; try exact I.
    {
      case_match; cbn; try exact I.
    }
    {
      naive_solver.
    }
    {
      naive_solver.
    }
    {
      naive_solver.
    }
    {
      repeat case_match; subst.
      {
        apply svar_is_fresh_in_svar_open.
        { exact Hneq. }
        { exact Hmd. }
      }
      { naive_solver. }
    }
    Qed.

  Example ex_not_wfcmu_impl_bound_svar_is_lt:
    exists
    (ϕ : Pattern)
    (mudepth : nat),
    well_formed_closed_mu_aux ϕ 0 /\
    ~ bound_svar_is_lt ϕ (S mudepth)
  .
  Proof.
    exists (patt_mu (patt_mu (patt_bound_svar 1))).
    exists 0.
    cbn.
    case_match; cbn; split.
    { reflexivity. }
    { lia. }
    { lia. }
    { lia. }
  Qed.

  (* cpatt ==  cvar ---> ⊥ *)
  Lemma bound_svar_is_lt_free_evar_subst
    ϕ iter dbi cvar cpatt:
    (* without this assumption, a counter example would be:
      ϕ ≡ B0, iter ≡ 0, dbi ≡ 0, cpatt ≡ patt_free_evar cvar
    *)
    bound_svar_is_lt ϕ (iter + dbi) ->
    well_formed_closed_mu_aux cpatt (dbi) ->
    cvar ∈ free_evars cpatt ->
    maximal_mu_depth_to 0 cvar cpatt <= iter ->
    bound_svar_is_lt cpatt (iter + dbi) ->
    bound_svar_is_lt cpatt^[[evar:cvar↦ϕ]] (iter + dbi)
  .
  Proof.
    intros Hltϕ Hwf Hin Hmaxmu Hltcpatt.
    move: dbi iter Hwf Hin Hmaxmu Hltϕ Hltcpatt.
    induction cpatt;
      cbn;
      intros dbi iter Hwf Hin Hmaxmu Hltϕ Hltcpatt; try exact I.
    {
      repeat case_match; subst; cbn; try exact I.
      2: { contradiction. }
      exact Hltϕ.
    }
    {
      case_match; try lia.
    }
    {
      destruct
        (decide (cvar ∈ free_evars cpatt1)) as [Hin1|Hnotin1],
        (decide (cvar ∈ free_evars cpatt2)) as [Hin2|Hnotin2].
      4: { exfalso. clear -Hin Hnotin1 Hnotin2. set_solver. }
      {
        split.
        {
          apply IHcpatt1.
          { naive_bsolver. }
          { exact Hin1. }
          { lia. }
          { exact Hltϕ. }
          { apply Hltcpatt. }
        }
        {
          apply IHcpatt2.
          { naive_bsolver. }
          { exact Hin2. }
          { lia. }
          { exact Hltϕ. }
          { apply Hltcpatt. }
        }
      }
      {
        split.
        {
          apply IHcpatt1.
          { naive_bsolver. }
          { exact Hin1. }
          { lia. }
          { exact Hltϕ. }
          { apply Hltcpatt. }
        }
        {
          rewrite free_evar_subst_no_occurrence.
          { exact Hnotin2. }
          { apply Hltcpatt. }
        }
      }
      {
        split.
        {
          rewrite free_evar_subst_no_occurrence.
          { exact Hnotin1. }
          { apply Hltcpatt. }
        }
        {
          apply IHcpatt2.
          { naive_bsolver. }
          { exact Hin2. }
          { lia. }
          { exact Hltϕ. }
          { apply Hltcpatt. }
        }
      }
    }
    {
      destruct
        (decide (cvar ∈ free_evars cpatt1)) as [Hin1|Hnotin1],
        (decide (cvar ∈ free_evars cpatt2)) as [Hin2|Hnotin2].
      4: { exfalso. clear -Hin Hnotin1 Hnotin2. set_solver. }
      {
        split.
        {
          apply IHcpatt1.
          { naive_bsolver. }
          { exact Hin1. }
          { lia. }
          { exact Hltϕ. }
          { apply Hltcpatt. }
        }
        {
          apply IHcpatt2.
          { naive_bsolver. }
          { exact Hin2. }
          { lia. }
          { exact Hltϕ. }
          { apply Hltcpatt. }
        }
      }
      {
        split.
        {
          apply IHcpatt1.
          { naive_bsolver. }
          { exact Hin1. }
          { lia. }
          { exact Hltϕ. }
          { apply Hltcpatt. }
        }
        {
          rewrite free_evar_subst_no_occurrence.
          { exact Hnotin2. }
          { apply Hltcpatt. }
        }
      }
      {
        split.
        {
          rewrite free_evar_subst_no_occurrence.
          { exact Hnotin1. }
          { apply Hltcpatt. }
        }
        {
          apply IHcpatt2.
          { naive_bsolver. }
          { exact Hin2. }
          { lia. }
          { exact Hltϕ. }
          { apply Hltcpatt. }
        }
      }
    }
    {
      apply IHcpatt; assumption.
    }
    {
      rewrite maximal_mu_depth_to_S in Hmaxmu.
      { assumption. }
      destruct iter;[lia|].
      replace (S iter + dbi) with (iter + S dbi) by lia.
      apply IHcpatt; try assumption.
      {
        lia.
      }
      {
        replace (iter + S dbi) with (S iter + dbi) by lia.
        exact Hltϕ.
      }
      {
        replace (iter + S dbi) with (S iter + dbi) by lia.
        exact Hltcpatt.
      }
    }
  Qed.

  Lemma bound_svar_is_lt_bevar_subst cpatt x0 dbi limit:
    bound_svar_is_lt cpatt (limit) ->
    bound_svar_is_lt cpatt^[evar:dbi↦patt_free_evar x0] limit
  .
  Proof.
    move: dbi limit.
    induction cpatt;
      cbn;
      intros dbi limit Hbs;
      try exact I.
    {
      case_match; cbn in *; lia.
    }
    {
      lia.
    }
    {
      naive_solver.
    }
    {
      naive_solver.
    }
    {
      naive_solver.
    }
    {
      naive_solver.
    }
  Qed.

  Lemma bound_svar_is_lt_bsvar_subst ϕ dbi limit Z:
    bound_svar_is_lt ϕ limit ->
    bound_svar_is_lt ϕ^[svar:dbi↦patt_free_svar Z] limit
  .
  Proof.
    move: dbi limit.
    induction ϕ; cbn; intros dbi limit Hbs; try exact I;
      try naive_solver.
    {
      repeat case_match; cbn; try lia.
    }
  Qed.

  Fixpoint bound_svar_is_banned_under_mus
  (ϕ : Pattern)
  (depth : nat)
  (banned : db_index)
  : bool
  :=
  match ϕ with
  | patt_bound_evar idx => true
  | patt_bound_svar idx => true
  | patt_free_evar _ => true
  | patt_free_svar _ => true
  | patt_bott => true
  | patt_sym _ => true
  | patt_imp ϕ₁ ϕ₂
  => (bound_svar_is_banned_under_mus ϕ₁ depth banned)
  && (bound_svar_is_banned_under_mus ϕ₂ depth banned)
  | patt_app ϕ₁ ϕ₂
  => (bound_svar_is_banned_under_mus ϕ₁ depth banned)
  && (bound_svar_is_banned_under_mus ϕ₂ depth banned)
  | patt_exists ϕ' => bound_svar_is_banned_under_mus ϕ' depth banned
  | patt_mu ϕ' =>
    match depth with
    | 0 => ~~ (bsvar_occur ϕ' (S banned))
    | (S depth') => bound_svar_is_banned_under_mus ϕ' depth' (S banned)
    end
  end.

  Lemma bsvar_occur_false_impl_banned ϕ banned n:
    bsvar_occur ϕ banned = false ->
    bound_svar_is_banned_under_mus ϕ n banned = true
  .
  Proof.
    move: banned n.
    induction ϕ; cbn; intros banned n' H; try reflexivity.
    {
      rewrite orb_false_iff in H.
      rewrite IHϕ1. apply H.
      rewrite IHϕ2. apply H.
      reflexivity.
    }
    {
      rewrite orb_false_iff in H.
      rewrite IHϕ1. apply H.
      rewrite IHϕ2. apply H.
      reflexivity.
    }
    {
      naive_solver.
    }
    {
      destruct n'.
      { rewrite negb_true_iff. assumption. }
      { naive_solver. }
    }
  Qed.

  Lemma bound_svar_is_banned_under_mus_lt
    (ϕ : Pattern) (depth1 depth2 : nat) (banned : db_index)
  :
    depth1 <= depth2 ->
    bound_svar_is_banned_under_mus ϕ depth1 banned = true ->
    bound_svar_is_banned_under_mus ϕ depth2 banned = true
  .
  Proof.
    move: depth1 depth2 banned.
    induction ϕ; cbn; intros depth1 depth2 banned Hlt H;
      try reflexivity.
    {
      destruct_andb! H. erewrite IHϕ1, IHϕ2; try eassumption.
      reflexivity.
    }
    {
      destruct_andb! H. erewrite IHϕ1, IHϕ2; try eassumption.
      reflexivity.
    }
    {
      erewrite IHϕ; try eassumption. reflexivity.
    }
    {
      repeat case_match; subst; try lia; try assumption.
      {
        apply bsvar_occur_false_impl_banned.
        rewrite negb_true_iff in H.
        exact H.
      }
      {
        eapply IHϕ.
        2: apply H.
        lia.
      }
    }
  Qed.

  Lemma bound_svar_is_banned_notfree x ϕ dbi dbi':
    dbi > dbi' ->
    well_formed_closed_mu_aux ϕ dbi' ->
    x ∉ free_evars ϕ ->
    bound_svar_is_banned_under_mus ϕ dbi dbi' = true ->
    x ∉ free_evars ϕ^[svar:dbi↦patt_free_evar x]
  .
  Proof.
    move: dbi dbi'.
    induction ϕ; cbn; intros dbi dbi' Hdbidbi' Hwf Hxϕ Hϕdbi Hcontra.
    1-3: set_solver.
    {
      repeat case_match; cbn in *; try set_solver; subst; try lia.
    }
    1: set_solver.
    {
      unfold is_true in Hwf.
      rewrite andb_true_iff in Hwf.
      destruct Hwf as [Hwf1 Hwf2].
      rewrite andb_true_iff in Hϕdbi.
      destruct Hϕdbi as [Hϕdbi1 Hϕdbi2].
      rewrite elem_of_union in Hxϕ.
      rewrite elem_of_union in Hcontra.
      destruct Hcontra; naive_solver.
    }
    1: set_solver.
    {
      unfold is_true in Hwf.
      rewrite andb_true_iff in Hwf.
      destruct Hwf as [Hwf1 Hwf2].
      rewrite andb_true_iff in Hϕdbi.
      destruct Hϕdbi as [Hϕdbi1 Hϕdbi2].
      rewrite elem_of_union in Hxϕ.
      rewrite elem_of_union in Hcontra.
      destruct Hcontra; naive_solver.
    }
    1: set_solver.
    { 
      destruct dbi;[lia|].
      eapply bound_svar_is_banned_under_mus_lt with (depth2 := (S (S dbi))) in Hϕdbi.
      2: lia.
      eapply IHϕ.
      4: {
        apply Hϕdbi.
      }
      { lia. }
      { apply Hwf. }
      { exact Hxϕ. }
      { apply Hcontra. }
    }
  Qed.

  Lemma maximal_mu_depth_to_svar_subst_evar_banned x ϕ dbi level d:
    well_formed_closed_mu_aux ϕ (S dbi) ->
    evar_is_fresh_in x ϕ ->
    bound_svar_is_banned_under_mus ϕ level dbi = true ->
    maximal_mu_depth_to d x ϕ^[svar:dbi↦patt_free_evar x] <= (d + level)
  .
  Proof.
    unfold evar_is_fresh_in.
    move: d dbi level.
    induction ϕ; cbn; intros d dbi level (*Hdbidbi'*) Hwf Hfr Hbs; try lia.
    {
      (* patt_free_evar *)
      case_match; subst.
      { clear -Hfr. set_solver. }
      { lia. }
    }
    {
      repeat case_match; subst; cbn; try reflexivity; try lia.
      rewrite decide_eq_same. lia.
    }
    {
      rewrite elem_of_union in Hfr.
      apply not_or_and in Hfr.
      destruct Hfr as [Hfr1 Hfr2].
      rewrite andb_true_iff in Hbs.
      destruct Hbs as [Hbs1 Hbs2].
      destruct_andb! Hwf.
      specialize (IHϕ1 d dbi level ltac:(wf_auto2) Hfr1 Hbs1).
      specialize (IHϕ2 d dbi level ltac:(wf_auto2) Hfr2 Hbs2).
      lia.
    }
    {
      rewrite elem_of_union in Hfr.
      apply not_or_and in Hfr.
      destruct Hfr as [Hfr1 Hfr2].
      rewrite andb_true_iff in Hbs.
      destruct Hbs as [Hbs1 Hbs2].
      destruct_andb! Hwf.
      specialize (IHϕ1 d dbi level ltac:(wf_auto2) Hfr1 Hbs1).
      specialize (IHϕ2 d dbi level ltac:(wf_auto2) Hfr2 Hbs2).
      lia.
    }
    {
      apply IHϕ; assumption.
    }
    {
      destruct level.
      {
        rewrite bsvar_subst_not_occur.
        { 
          rewrite negb_true_iff in Hbs.
          apply wfc_mu_lower; assumption.
        }
        rewrite maximal_mu_depth_to_0.
        { exact Hfr. }
        { lia. }
      }
      {
        replace (d + S level) with (S d + level) by lia.
        apply IHϕ; assumption.
      }
    }
  Qed.

  Lemma maximal_mu_depth_to_lt a b x ϕ:
    a > b ->
    maximal_mu_depth_to a x ϕ <= b ->
    evar_is_fresh_in x ϕ
  .
  Proof.
    unfold evar_is_fresh_in.
    move: a b.
    induction ϕ; cbn; intros a b Hab H.
    2-5,7: set_solver.
    {
      destruct (decide (x0 = x)); subst; try lia; try set_solver.
    }
    {
      specialize (IHϕ1 a b Hab ltac:(lia)).
      specialize (IHϕ2 a b Hab ltac:(lia)).
      set_solver.
    }
    {
      specialize (IHϕ1 a b Hab ltac:(lia)).
      specialize (IHϕ2 a b Hab ltac:(lia)).
      set_solver.
    }
    {
      eapply IHϕ.
      2: apply H.
      lia.
    }
    {
      eapply IHϕ.
      2: apply H.
      lia.
    }
  Qed.

  Lemma maximal_mu_depth_to_svar_subst_evar_banned_back x ϕ dbi level d:
    well_formed_closed_mu_aux ϕ (S dbi) ->
    evar_is_fresh_in x ϕ ->
    maximal_mu_depth_to d x ϕ^[svar:dbi↦patt_free_evar x] <= (d + level) ->
    bound_svar_is_banned_under_mus ϕ level dbi = true
  .
  Proof.
    unfold evar_is_fresh_in.
    move: dbi level d.
    induction ϕ; cbn; intros dbi level d Hwf Hfr H; try reflexivity.
    {
      unfold is_true in Hwf.
      rewrite andb_true_iff in Hwf.
      destruct Hwf as [Hwf1 Hwf2].
      rewrite elem_of_union in Hfr.
      apply not_or_and in Hfr.
      destruct Hfr as [Hfr1 Hfr2].
      specialize (IHϕ1 dbi level d Hwf1 Hfr1 ltac:(lia)).
      specialize (IHϕ2 dbi level d Hwf2 Hfr2 ltac:(lia)).
      rewrite andb_true_iff.
      split; assumption.
    }
    {
      unfold is_true in Hwf.
      rewrite andb_true_iff in Hwf.
      destruct Hwf as [Hwf1 Hwf2].
      rewrite elem_of_union in Hfr.
      apply not_or_and in Hfr.
      destruct Hfr as [Hfr1 Hfr2].
      specialize (IHϕ1 dbi level d Hwf1 Hfr1 ltac:(lia)).
      specialize (IHϕ2 dbi level d Hwf2 Hfr2 ltac:(lia)).
      rewrite andb_true_iff.
      split; assumption.
    }
    {
      eapply IHϕ.
      3: apply H.
      1,2: assumption.
    }
    {
      destruct level.
      {
        pose proof (H'' := maximal_mu_depth_to_lt (S d) d x ϕ^[svar:S dbi↦patt_free_evar x] ltac:(lia) ltac:(lia)).      
        unfold evar_is_fresh_in in H''.
        rewrite free_evars_bsvar_subst' in H''.
        apply not_or_and in H''.
        destruct H'' as [H1 H2].
        cbn in H1.
        apply not_and_or in H1.
        destruct H1 as [H1|H1].
        {
          exfalso. clear -H1. set_solver.
        }
        {
          unfold is_true in H1.
          apply not_true_is_false in H1.
          rewrite negb_true_iff.
          exact H1.
        }
      }
      {
        apply IHϕ with (d := S d).
        { exact Hwf. }
        { exact Hfr. }
        lia.
      }
    }
  Qed.

  Lemma maximal_mu_depth_to_svar_subst_evar_banned_back_2 x ϕ dbi level d:
    well_formed_closed_mu_aux ϕ (S dbi) ->
    evar_is_fresh_in x ϕ ->
    maximal_mu_depth_to d x ϕ <= (d + level) ->
    bound_svar_is_banned_under_mus ϕ^[svar:dbi↦patt_free_evar x] level dbi = true
  .
  Proof.
    unfold evar_is_fresh_in.
    move: dbi level d.
    induction ϕ; cbn; intros dbi level d Hwf Hwefr Hmd; try reflexivity.
    {
      repeat case_match; cbn in *; try reflexivity.
    }
    {
      unfold is_true in Hwf.
      rewrite andb_true_iff in Hwf.
      destruct Hwf as [Hwf1 Hwf2].
      rewrite elem_of_union in Hwefr.
      apply not_or_and in Hwefr.
      destruct Hwefr as [Hfr1 Hfr2].
      specialize (IHϕ1 dbi level d Hwf1 Hfr1 ltac:(lia)).
      specialize (IHϕ2 dbi level d Hwf2 Hfr2 ltac:(lia)).
      rewrite andb_true_iff.
      split; assumption.
    }
    {
      unfold is_true in Hwf.
      rewrite andb_true_iff in Hwf.
      destruct Hwf as [Hwf1 Hwf2].
      rewrite elem_of_union in Hwefr.
      apply not_or_and in Hwefr.
      destruct Hwefr as [Hfr1 Hfr2].
      specialize (IHϕ1 dbi level d Hwf1 Hfr1 ltac:(lia)).
      specialize (IHϕ2 dbi level d Hwf2 Hfr2 ltac:(lia)).
      rewrite andb_true_iff.
      split; assumption.
    }
    {
      eapply IHϕ.
      3: apply Hmd.
      2: exact Hwefr.
      1: exact Hwf.
    }
    {
      destruct level.
      {
        pose proof (Htmp := not_bsvar_occur_bsvar_subst_2 ϕ (patt_free_evar x) (S dbi) ltac:(reflexivity) Hwf).
        rewrite negb_true_iff.
        apply Htmp.
      }
      {
        eapply IHϕ with (d := (S d)).
        { assumption. }
        { assumption. }
        { lia. }
      }
    }
  Qed.

  Lemma bsvar_occur_bevar_subst ϕ ψ edbi sdbi:
    well_formed_closed_mu_aux ψ sdbi ->
    bsvar_occur ϕ sdbi = false ->
    bsvar_occur ϕ^[evar:edbi↦ψ] sdbi = false
  .
  Proof.
    move: edbi sdbi.
    induction ϕ; cbn; intros edbi sdbi Hwf Hnbo; try reflexivity.
    {
      case_match; try assumption.
      subst.
      apply wfc_mu_aux_implies_not_bsvar_occur.
      exact Hwf.
    }
    {
      exact Hnbo.
    }
    {
      rewrite orb_false_iff in Hnbo.
      rewrite orb_false_iff.
      naive_solver.
    }
    {
      rewrite orb_false_iff in Hnbo.
      rewrite orb_false_iff.
      naive_solver.
    }
    {
      naive_solver.
    }
    {
      apply IHϕ.
      {
        eapply well_formed_closed_mu_aux_ind.
        2: apply Hwf.
        { lia. }
      }
      {
        exact Hnbo.
      }
    }
  Qed.

  Lemma bound_svar_is_banned_under_mus_bevar_subst ϕ ψ dbi level dbi':
    well_formed_closed_mu_aux ψ (S dbi') ->
    bound_svar_is_banned_under_mus ψ level dbi' = true ->
    bound_svar_is_banned_under_mus ϕ level dbi' = true ->
    bound_svar_is_banned_under_mus ϕ^[evar:dbi↦ψ] level dbi' = true
  .
  Proof.
    move: dbi dbi' level.
    induction ϕ; cbn; intros dbi dbi' level H1 H2 H3; try reflexivity.
    {
      repeat case_match; cbn in *; subst; try reflexivity.
      assumption.
    }
    {
      destruct_andb! H3.
      rewrite IHϕ1; try assumption.
      rewrite IHϕ2; try assumption.
      reflexivity.
    }
    {
      destruct_andb! H3.
      rewrite IHϕ1; try assumption.
      rewrite IHϕ2; try assumption.
      reflexivity.
    }
    {
      naive_solver.
    }
    {
      destruct level; cbn in *.
      {
        rewrite negb_true_iff.
        rewrite negb_true_iff in H3.
        apply bsvar_occur_bevar_subst; try assumption.
      }
      {
        apply IHϕ.
        {
          eapply well_formed_closed_mu_aux_ind.
          2: apply H1.
          { lia. }
        }
        {
          apply bsvar_occur_false_impl_banned.
          apply wfc_mu_aux_implies_not_bsvar_occur.
          assumption.
        }
        {
          assumption.
        }
      }
    }
  Qed.


  Lemma bsvar_occur_free_evar_subst ϕ cvar ψ dbi:
    well_formed_closed_mu_aux ψ dbi ->
    bsvar_occur ϕ dbi = false ->
    bsvar_occur ϕ^[[evar:cvar↦ψ]] dbi = false
  .
  Proof.
    move: dbi.
    induction ϕ; cbn; intros dbi H1 H2; try reflexivity.
    {
      destruct (decide (cvar = x)).
      {
        apply wfc_mu_aux_implies_not_bsvar_occur.
        assumption.
      }
      {
        cbn. reflexivity.
      }
    }
    {
      exact H2.
    }
    {
      rewrite orb_false_iff in H2.
      rewrite orb_false_iff.
      naive_solver.
    }
    {
      rewrite orb_false_iff in H2.
      rewrite orb_false_iff.
      naive_solver.
    }
    {
      naive_solver.
    }
    {
      apply IHϕ.
      {
        eapply well_formed_closed_mu_aux_ind.
        2: apply H1.
        lia.
      }
      {
        assumption.
      }
    }
  Qed.

  (* ϕ ≡ (mu, 0) ---> cvar  *)
  Lemma bound_svar_is_banned_under_mus_fevar_subst_alternative ϕ ψ cvar level dbi':
    well_formed_closed_mu_aux ψ (S dbi') = true  ->
    bound_svar_is_banned_under_mus ψ level dbi' = true ->
    bound_svar_is_banned_under_mus ϕ level dbi' = true ->
    bound_svar_is_banned_under_mus ϕ^[[evar:cvar↦ψ]] level dbi' = true
  .
  Proof.
    move: dbi' level.
    induction ϕ; cbn; intros dbi' level H0 H1 H2 (*H3*); try reflexivity.
    {
      repeat case_match; cbn in *; subst; try reflexivity.
      assumption.
    }
    {
      naive_bsolver.
    }
    {
      naive_bsolver.
    }
    {
      naive_solver.
    }
    {
      destruct level; cbn in *.
      {
        rewrite negb_true_iff.
        rewrite negb_true_iff in H2.
        apply bsvar_occur_free_evar_subst; try assumption.
      }
      {
        apply IHϕ.
        {
          eapply well_formed_closed_mu_aux_ind.
          2: apply H0.
          { lia. }
        }
        (* {
          eapply well_formed_closed_mu_aux_ind.
          2: apply H1.
          { lia. }
        } *)
        {
          apply bsvar_occur_false_impl_banned.
          apply wfc_mu_aux_implies_not_bsvar_occur.
          assumption.
        }
        {
          assumption.
        }
      }
    }
  Qed.

  (* ϕ ≡ (mu, 0) ---> cvar  *)
  Lemma bound_svar_is_banned_under_mus_fevar_subst ϕ ψ cvar level dbi':
    well_formed_closed_mu_aux ϕ (dbi') = true ->
    well_formed_closed_mu_aux ψ (S dbi') = true  ->
    bound_svar_is_banned_under_mus ψ level dbi' = true ->
    bound_svar_is_banned_under_mus ϕ^[[evar:cvar↦ψ]] level dbi' = true
  .
  Proof.
    move: dbi' level.
    induction ϕ; cbn; intros dbi' level H0 H1 H2 (*H3*); try reflexivity.
    {
      repeat case_match; cbn in *; subst; try reflexivity.
      assumption.
    }
    {
      naive_bsolver.
    }
    {
      naive_bsolver.
    }
    {
      naive_solver.
    }
    {
      destruct level; cbn in *.
      {
        rewrite negb_true_iff.
        apply bsvar_occur_free_evar_subst; try assumption.
        apply wfc_mu_aux_implies_not_bsvar_occur.
        apply H0.
      }
      {
        apply IHϕ.
        {
          eapply well_formed_closed_mu_aux_ind.
          2: apply H0.
          { lia. }
        }
        {
          eapply well_formed_closed_mu_aux_ind.
          2: apply H1.
          { lia. }
        }
        {
          apply bsvar_occur_false_impl_banned.
          apply wfc_mu_aux_implies_not_bsvar_occur.
          assumption.
        }
      }
    }
  Qed.

  Lemma bound_svar_is_banned_under_mus_evar_open x ϕ dbi level dbi':
    bound_svar_is_banned_under_mus ϕ level dbi' = true ->
    bound_svar_is_banned_under_mus ϕ^[evar:dbi↦patt_free_evar x] level dbi' = true
  .
  Proof.
    move: dbi dbi' level.
    induction ϕ; cbn; intros dbi dbi' level H; try reflexivity.
    {
      repeat case_match; cbn in *; try reflexivity.
    }
    {
      destruct_andb! H.
      rewrite IHϕ1; try assumption.
      rewrite IHϕ2; try assumption.
      reflexivity.
    }
    {
      destruct_andb! H.
      rewrite IHϕ1; try assumption.
      rewrite IHϕ2; try assumption.
      reflexivity.
    }
    {
      naive_solver.
    }
    {
      destruct level; cbn in *.
      {
        rewrite negb_true_iff in H.
        rewrite negb_true_iff.
        apply bsvar_occur_evar_open.
        assumption.
      }
      {
        apply IHϕ.
        apply H.
      }
    }
  Qed.

  Lemma bound_svar_is_lt_implies_bound_svar_is_banned_under_mus ϕ level dbi n:
    well_formed_closed_mu_aux ϕ (dbi + n) ->
    bound_svar_is_lt ϕ (level + n) ->
    bound_svar_is_banned_under_mus ϕ level (dbi + n) = true
  .
  Proof.
    move: level dbi n.
    induction ϕ; cbn; intros level dbi n' H1 H2; try reflexivity.
    {
      destruct_andb! H1. destruct H2.
      rewrite IHϕ1; try assumption.
      rewrite IHϕ2; try assumption.
      reflexivity.
    }
    {
      destruct_andb! H1. destruct H2.
      rewrite IHϕ1; try assumption.
      rewrite IHϕ2; try assumption.
      reflexivity.
    }
    {
      naive_bsolver.
    }
    {
      destruct level.
      {
        rewrite negb_true_iff.
        apply wfc_mu_aux_implies_not_bsvar_occur.
        { wf_auto2. }
      }
      {
        replace (S (dbi + n')) with (dbi + S n') by lia.
        apply IHϕ.
        {
          replace (dbi + S n') with (S (dbi + n')) by lia.
          exact H1.
        }
        {
          replace (level + S n') with (S (level + n')) by lia.
          cbn in H2.
          exact H2.
        }
      }
    }
  Qed.

  Example counterexample_1:
    exists cvar cpatt ϕ dbi iter,
      well_formed_closed_mu_aux cpatt (S dbi) /\
      maximal_mu_depth_to 0 cvar cpatt <= iter /\
      bound_svar_is_banned_under_mus ϕ iter dbi /\
      bound_svar_is_banned_under_mus cpatt^[[evar:cvar↦ϕ]] iter dbi
    .
  Proof.
    exists (evar_fresh []).
    exists (patt_imp (patt_mu (patt_bound_svar 0)) (patt_bound_svar 0)).
    exists (patt_free_evar (evar_fresh [(evar_fresh [])])).
    exists (0).
    exists (0).
    repeat split.
    {
      cbn. lia.
    }
  Qed.


  Fixpoint pattern_kt_well_formed (φ : Pattern) :=
  match φ with
   | patt_free_evar x => true
   | patt_free_svar x => true
   | patt_bound_evar n => true
   | patt_bound_svar n => true
   | patt_sym sigma => true
   | patt_app phi1 phi2 => pattern_kt_well_formed phi1 && pattern_kt_well_formed phi2
   | patt_bott => true
   | patt_imp phi1 phi2 => pattern_kt_well_formed phi1 && pattern_kt_well_formed phi2
   | patt_exists phi => pattern_kt_well_formed phi
   | patt_mu phi => bound_svar_is_banned_under_mus phi 0 0 &&
                    pattern_kt_well_formed phi
  end.

  Lemma kt_well_formed_evar_open (φ : Pattern) x dbi:
    pattern_kt_well_formed φ ->
    pattern_kt_well_formed φ^{evar:dbi↦x}.
  Proof.
    revert x dbi.
    induction φ; simpl; intros; try reflexivity.
    * cbn. case_match; by simpl.
    * specialize (IHφ1 x dbi). specialize (IHφ2 x dbi). naive_bsolver.
    * specialize (IHφ1 x dbi). specialize (IHφ2 x dbi). naive_bsolver.
    * by apply IHφ.
    * rewrite IHφ. naive_bsolver.
      rewrite bound_svar_is_banned_under_mus_evar_open; naive_bsolver.
  Qed.

  Lemma bsvar_occur_bsvar_subst_wf :
    forall φ ψ dbi x,
      well_formed_closed_mu_aux φ (S x) ->
      ~~ bsvar_occur φ dbi ->
      well_formed_closed_mu_aux ψ 0 ->
      ~~ bsvar_occur (bsvar_subst ψ x φ) dbi.
  Proof.
    induction φ; simpl; intros; try reflexivity.
    * case_match. by simpl in H.
      case_match. 2: by simpl in *.
      case_match; simpl; try assumption.
      case_match. lia. reflexivity.
      rewrite wfc_mu_aux_implies_not_bsvar_occur.
      eapply well_formed_closed_mu_aux_ind. 2: eassumption.
      lia.
      reflexivity.
      case_match. lia. reflexivity.
    * rewrite negb_or. rewrite negb_or in H0.
      rewrite IHφ1. 1-3: wf_auto2.
      rewrite IHφ2; wf_auto2.
    * rewrite negb_or. rewrite negb_or in H0.
      rewrite IHφ1. 1-3: wf_auto2.
      rewrite IHφ2; wf_auto2.
    * rewrite IHφ; wf_auto2.
    * rewrite IHφ; wf_auto2.
  Qed.

  Lemma bound_svar_is_banned_bsvar_subst :
    forall φ ψ level dbi x,
      well_formed_closed_mu_aux ψ 0 ->
      well_formed_closed_mu_aux φ (S x) ->
      bound_svar_is_banned_under_mus φ level dbi ->
      bound_svar_is_banned_under_mus (bsvar_subst ψ x φ) level dbi.
  Proof.
    induction φ; intros; simpl in *; try reflexivity.
    * case_match; try reflexivity. 2: congruence. subst.
      case_match; simpl; try reflexivity.
      apply bsvar_occur_false_impl_banned.
      apply wfc_mu_aux_implies_not_bsvar_occur.
      eapply well_formed_closed_mu_aux_ind. 2: eassumption.
      lia.
    * rewrite IHφ1. 4: rewrite IHφ2.
      all: try wf_auto2.
    * rewrite IHφ1. 4: rewrite IHφ2.
      all: try wf_auto2.
    * apply IHφ; wf_auto2.
    * case_match.
      - (* apply negb_true_iff. apply negb_true_iff in H1. *)
        rewrite bsvar_occur_bsvar_subst_wf; wf_auto2.
      - apply IHφ; wf_auto2.
  Qed.

  Lemma kt_well_formed_svar_open (φ : Pattern) X dbi:
    well_formed_closed_mu_aux φ (S dbi) ->
    pattern_kt_well_formed φ ->
    pattern_kt_well_formed φ^{svar:dbi↦X}.
  Proof.
    revert X dbi.
    induction φ; simpl; intros; try reflexivity.
    * cbn. case_match; try by simpl. case_match; try by simpl.
    * specialize (IHφ1 X dbi). specialize (IHφ2 X dbi). naive_bsolver.
    * specialize (IHφ1 X dbi). specialize (IHφ2 X dbi). naive_bsolver.
    * by apply IHφ.
    * destruct_andb! H0. rewrite IHφ. 1-2: naive_bsolver.
      apply andb_true_iff; split. 2: reflexivity.
      rewrite bound_svar_is_banned_bsvar_subst; wf_auto2.
  Qed.

  (* Mu-freeness is a stricter property. *)
  Lemma mf_imp_ktwf φ : mu_free φ -> pattern_kt_well_formed φ.
  Proof.
    intros.
    induction φ; auto.
    all: inversion H; apply andb_true_iff in H1 as [?%IHφ1 ?%IHφ2]; now apply andb_true_iff.
  Defined.

End with_signature.


(* TODO remove these hints *)

#[export]
 Hint Resolve well_formed_positive_svar_quantify : core.

#[export]
 Hint Resolve no_positive_occurrence_svar_quantify : core.

#[export]
 Hint Resolve no_negative_occurrence_svar_quantify : core.

#[export]
 Hint Resolve wfc_impl_no_neg_occ : core.

#[export]
 Hint Resolve wfp_free_svar_subst : core.

#[export]
 Hint Resolve wfp_neg_free_svar_subst : core.


#[export]
 Hint Resolve svar_quantify_closed_ex : core.

#[export]
 Hint Resolve svar_quantify_closed_mu : core.

#[export]
 Hint Resolve evar_quantify_positive : core.

#[export]
 Hint Resolve evar_quantify_closed_mu : core.

#[export]
 Hint Resolve evar_quantify_closed_ex : core.

#[export]
 Hint Resolve wfp_evar_open : core.

#[export]
 Hint Resolve wfc_mu_aux_body_ex_imp1 : core.

#[export]
 Hint Resolve wfc_ex_aux_body_ex_imp1 : core.

#[export]
Hint Resolve bevar_subst_positive_2 : core.

#[export]
Hint Resolve wfc_mu_aux_bevar_subst : core.

#[export]
Hint Resolve wfc_ex_aux_bevar_subst : core.

#[export]
Hint Resolve wfp_svar_open : core.

#[export]
 Hint Resolve wfc_mu_free_evar_subst : core.