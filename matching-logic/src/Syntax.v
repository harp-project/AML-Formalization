From Coq Require Import ssreflect ssrfun ssrbool.
Require Import Setoid.
Require Import List.
Require Import Ensembles.
Require Import Coq.Strings.String.

From Coq Require Import Logic.Classical_Prop.
From stdpp Require Import countable infinite.
From stdpp Require Import pmap gmap mapset fin_sets propset.
Require Import stdpp_ext.

Require Import extralibrary.

From MatchingLogic Require Export
  Signature
  Pattern
  Substitution
  Freshness
  SyntacticConstruct
  PatternContext
  ApplicationContext
  SyntaxLemmas.FreshnessSubstitution
  SyntaxLemmas.PatternCtxApplicationCtx
  SyntaxLemmas.FreshnessApplicationCtx
  SyntaxLemmas.ApplicationCtxSubstitution
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




  Lemma x_eq_fresh_impl_x_notin_free_evars x ϕ:
    x = fresh_evar ϕ ->
    x ∉ free_evars ϕ.
  Proof.
    intros H.
    rewrite H.
    unfold fresh_evar.
    apply set_evar_fresh_is_fresh'.
  Qed.

  Hint Resolve x_eq_fresh_impl_x_notin_free_evars : core.

End syntax.

Module Notations.
  (* TODO: change Bot and Top to unicode symbols *)
  (* TODO: this associativity is wrong! However, stdpp disallows defining it otherwise. We could use @ instead, associated to the left *)
  Notation "a $ b" := (patt_app a b) (at level 65, right associativity) : ml_scope.
  Notation "'Bot'" := patt_bott : ml_scope.
  Notation "⊥" := patt_bott : ml_scope.
  Notation "a ---> b"  := (patt_imp a b) (at level 75, right associativity) : ml_scope.
  Notation "'ex' , phi" := (patt_exists phi) (at level 80) : ml_scope.
  Notation "'mu' , phi" := (patt_mu phi) (at level 80) : ml_scope.

  (*Notation "AC [ p ]" := (subst_ctx AC p) (at level 90) : ml_scope.*)
  Notation "C [ p ]" := (emplace C p) (at level 90) : ml_scope.

End Notations.

Module BoundVarSugar.
  (* Element variables - bound *)
  Notation b0 := (patt_bound_evar 0).
  Notation b1 := (patt_bound_evar 1).
  Notation b2 := (patt_bound_evar 2).
  Notation b3 := (patt_bound_evar 3).
  Notation b4 := (patt_bound_evar 4).
  Notation b5 := (patt_bound_evar 5).
  Notation b6 := (patt_bound_evar 6).
  Notation b7 := (patt_bound_evar 7).
  Notation b8 := (patt_bound_evar 8).
  Notation b9 := (patt_bound_evar 9).

  Notation B0 := (patt_bound_svar 0).
  Notation B1 := (patt_bound_svar 1).
  Notation B2 := (patt_bound_svar 2).
  Notation B3 := (patt_bound_svar 3).
  Notation B4 := (patt_bound_svar 4).
  Notation B5 := (patt_bound_svar 5).
  Notation B6 := (patt_bound_svar 6).
  Notation B7 := (patt_bound_svar 7).
  Notation B8 := (patt_bound_svar 8).
  Notation B9 := (patt_bound_svar 9).

End BoundVarSugar.

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
        destruct_and!.
        specialize (IHϕ1 ltac:(assumption) ltac:(assumption)).
        specialize (IHϕ2 ltac:(assumption) ltac:(assumption)).
        split_and!; auto.
      + cbn in Hnoneg. cbn in Hwfpϕ.
        apply orb_false_iff in Hnoneg.
        destruct_and!.
        pose proof (IH1 := wfp_neg_free_svar_subst ϕ1 ψ X ltac:(assumption)).
        feed specialize IH1.
        { assumption. }
        { assumption. }
        { assumption. }
        specialize (IHϕ2 ltac:(assumption)).
        split_and!; auto.
      + cbn in Hnoneg. cbn in Hwfpϕ. destruct_and!.
        rewrite IHϕ. assumption. assumption. split_and!; auto.
        rewrite nno_free_svar_subst.
        assumption. assumption.
    -
      intros Hwfcψ Hwfpψ Hwfpϕ Hnoneg.
      induction ϕ; simpl; auto.
      + case_match; [|reflexivity].
        assumption.
      + cbn in Hnoneg. cbn in Hwfpϕ.
        apply orb_false_iff in Hnoneg.
        destruct_and!.
        specialize (IHϕ1 ltac:(assumption) ltac:(assumption)).
        specialize (IHϕ2 ltac:(assumption) ltac:(assumption)).
        split_and!; auto.
      + cbn in Hnoneg. cbn in Hwfpϕ.
        apply orb_false_iff in Hnoneg.
        destruct_and!.
        pose proof (IH1 := wfp_free_svar_subst ϕ1 ψ X ltac:(assumption)).
        feed specialize IH1.
        { assumption. }
        { assumption. }
        { assumption. }
        specialize (IHϕ2 ltac:(assumption)).
        split_and!; auto.
      + cbn in Hnoneg. cbn in Hwfpϕ. destruct_and!.
        rewrite IHϕ. assumption. assumption. split_and!; auto.
        rewrite nno_free_svar_subst.
        assumption. assumption.
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
    intros H. (*compoundDecomposeWfGoal.
    apply (unary_wfxy_compose _).*) wf_auto2.
    (*
    wf_auto2_fast_done.
    compositeSimplifyAllWfHyps.
    wf_auto2_composite_step.
    wf_auto2_composite_step.
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
    destruct_and!.
    split_and!.
    - eapply wfp_after_subst_impl_wfp_before. eassumption.
    - eapply wfcmu_after_subst_impl_wfcmu_before. eassumption.
    - eapply wfcex_after_subst_impl_wfcex_before. eassumption.
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
  - split;[assumption|]. unfold evar_is_fresh_in_list. apply Forall_nil. exact I.
  - destruct H as [H _]. exact H.
  - unfold evar_is_fresh_in_list,evar_is_fresh_in in *. simpl in *.
    split;[set_solver|].
    apply Forall_cons.
    destruct IHl as [IHl1 IHl2].
    split;[set_solver|].
    apply IHl1. set_solver.
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
    intros H1 H2.
    move: n H1 H2.
    induction ϕ; intros n' H1 H2; simpl in *; auto.
    - repeat case_match; auto. lia.
    - apply orb_false_elim in H1. destruct_and!.
      erewrite -> IHϕ1 by eassumption.
      erewrite -> IHϕ2 by eassumption.
      reflexivity.
    - apply orb_false_elim in H1. destruct_and!.
      erewrite -> IHϕ1 by eassumption.
      erewrite -> IHϕ2 by eassumption.
      reflexivity.
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
      erewrite -> IHϕ1 by eassumption.
      erewrite -> IHϕ2 by eassumption.
      reflexivity.
    - apply orb_false_elim in H1. destruct_and!.
      erewrite -> IHϕ1 by eassumption.
      erewrite -> IHϕ2 by eassumption.
      reflexivity.
  Qed.

  Lemma wf_ex_quan_impl_wf (x : evar) (ϕ : Pattern):
    bevar_occur ϕ 0 = false ->
    well_formed (exists_quantify x ϕ) = true ->
    well_formed ϕ = true.
  Proof.
    intros H0 H. unfold exists_quantify in H.
    unfold well_formed, well_formed_closed in *. destruct_and!. simpl in *.
    split_and!.
    - eapply wfp_evar_quan_impl_wfp. eassumption.
    - eapply wfcmu_evar_quan_impl_wfcmu. eassumption.
    - apply wfcex_evar_quan_impl_wfcex in H3.
      apply wfc_ex_lower; assumption.
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
    - simpl in Hwf. destruct_and!.
      rewrite IHϕ1; auto. rewrite IHϕ2; auto.
    - simpl in Hwf. destruct_and!.
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
    - simpl in Hwf. destruct_and!.
      rewrite IHϕ1; auto. rewrite IHϕ2; auto.
    - simpl in Hwf. destruct_and!.
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