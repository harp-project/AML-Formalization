From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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
.

Import Substitution.Notations.

Definition Theory {Σ : Signature} := propset Pattern.

Close Scope boolean_if_scope.

Section syntax.
  Context {Σ : Signature}.


    

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
    is_subformula_of_ind ϕ₂ (bsvar_subst ϕ₁ ϕ₂ dbi).
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
    is_subformula_of_ind ϕ₂ (bevar_subst ϕ₁ ϕ₂ dbi).
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
    free_evars (bsvar_subst ϕ₁ ϕ₂ dbi) ⊆ free_evars ϕ₁ ∪ free_evars ϕ₂.
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
      remember (free_evars (bsvar_subst ϕ₁1 ϕ₂ db)) as A1.
      remember (free_evars (bsvar_subst ϕ₁2 ϕ₂ db)) as A2.
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
      remember (free_evars (bsvar_subst ϕ₁1 ϕ₂ db)) as A1.
      remember (free_evars (bsvar_subst ϕ₁2 ϕ₂ db)) as A2.
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
    free_svars (bevar_subst ϕ₁ ϕ₂ dbi) ⊆ free_svars ϕ₁ ∪ free_svars ϕ₂.
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
      remember (free_svars (bevar_subst ϕ₁1 ϕ₂ db)) as A1.
      remember (free_svars (bevar_subst ϕ₁2 ϕ₂ db)) as A2.
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
      remember (free_svars (bevar_subst ϕ₁1 ϕ₂ db)) as A1.
      remember (free_svars (bevar_subst ϕ₁2 ϕ₂ db)) as A2.
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
    free_evars ϕ₁ ⊆ free_evars (bsvar_subst ϕ₁ ϕ₂ dbi).
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
    free_svars ϕ₁ ⊆ free_svars (bevar_subst ϕ₁ ϕ₂ dbi).
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
    free_evars (bsvar_subst ϕ₁ ϕ₂ dbi) = free_evars ϕ₁ ∪ free_evars ϕ₂.
  Proof.
    intros H.
    apply (anti_symm subseteq).
    - apply free_evars_bsvar_subst.
    - apply union_least.
      + apply free_evars_bsvar_subst_1.
      + pose proof (Hsub := @bsvar_subst_contains_subformula ϕ₁ ϕ₂ dbi H).
        apply free_evars_subformula. auto.
  Qed.

  Corollary free_svars_bevar_subst_eq ϕ₁ ϕ₂ dbi:
    bevar_occur ϕ₁ dbi ->
    free_svars (bevar_subst ϕ₁ ϕ₂ dbi) = free_svars ϕ₁ ∪ free_svars ϕ₂.
  Proof.
    intros H.
    apply (anti_symm subseteq).
    - apply free_svars_bevar_subst.
    - apply union_least.
      + apply free_svars_bevar_subst_1.
      + pose proof (Hsub := @bevar_subst_contains_subformula ϕ₁ ϕ₂ dbi H).
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
    ~ bsvar_occur (bsvar_subst phi psi n) n.
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
      destruct (bsvar_occur (bsvar_subst phi1 psi n') n') eqn:Heq1, (bsvar_occur (bsvar_subst phi2 psi n') n') eqn:Heq2.
      + eapply IHphi2; eauto. now apply andb_true_iff in H0.
      + eapply IHphi1; eauto. now apply andb_true_iff in H0.
      + eapply IHphi2; eauto. now apply andb_true_iff in H0.
      + simpl in Hcontra. congruence.
    - intros Hcontra.
      destruct (bsvar_occur (bsvar_subst phi1 psi n') n')
               eqn:Heq1, (bsvar_occur (bsvar_subst phi2 psi n') n') eqn:Heq2.
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
    pose proof (H1 := not_bsvar_occur_impl_no_neg_occ_and_no_pos_occ H).
    now apply andb_true_iff in H1.
  Qed.

  Corollary not_bsvar_occur_impl_neg_occ_db phi n:
    ~ bsvar_occur phi n ->
    no_negative_occurrence_db_b n phi.
  Proof.
    intros H.
    pose proof (H1 := not_bsvar_occur_impl_no_neg_occ_and_no_pos_occ H).
    now apply andb_true_iff in H1.
  Qed.

  Lemma no_neg_occ_db_bsvar_subst phi psi dbi1 dbi2:
    well_formed_closed_mu_aux psi 0 = true -> dbi1 < dbi2 ->
    (no_negative_occurrence_db_b dbi1 phi = true ->
     no_negative_occurrence_db_b dbi1 (bsvar_subst phi psi dbi2) = true)
    /\ (no_positive_occurrence_db_b dbi1 phi = true ->
        no_positive_occurrence_db_b dbi1 (bsvar_subst phi psi dbi2) = true).
  Proof.
    intros Hwfcpsi.
    move: dbi1 dbi2.

    induction phi; intros dbi1 dbi2 H; simpl; auto.
    -
      case_match; auto.
      + split; intros H0.
        * apply wfc_impl_no_neg_occ. apply Hwfcpsi.
        * apply wfc_impl_no_pos_occ. apply Hwfcpsi.
      + split; intros H0.
        * auto.
        * cbn. repeat case_match. lia. reflexivity.
    - specialize (IHphi1 dbi1 dbi2).
      specialize (IHphi2 dbi1 dbi2).
      destruct (IHphi1 H) as [IHphi11 IHphi12].
      destruct (IHphi2 H) as [IHphi21 IHphi22].
      split; intro H0.
      + eapply elimT in H0.
        2: apply andP.
        destruct H0 as [H1 H2].
        specialize (IHphi11 H1).
        specialize (IHphi21 H2).
        cbn.
        rewrite IHphi11 IHphi21. reflexivity.
      + eapply elimT in H0.
        2: apply andP.
        destruct H0 as [H1 H2].
        specialize (IHphi12 H1).
        specialize (IHphi22 H2).
        cbn.
        rewrite IHphi12 IHphi22. reflexivity.
    - specialize (IHphi1 dbi1 dbi2).
      specialize (IHphi2 dbi1 dbi2).
      destruct (IHphi1 H) as [IHphi11 IHphi12].
      destruct (IHphi2 H) as [IHphi21 IHphi22].
      split; intro H0.
      + eapply elimT in H0.
        2: apply andP.
        destruct H0 as [H1 H2].
        specialize (IHphi12 H1).
        specialize (IHphi21 H2).
        cbn. fold no_negative_occurrence_db_b no_positive_occurrence_db_b.
        rewrite IHphi12 IHphi21. reflexivity.
      + eapply elimT in H0.
        2: apply andP.
        destruct H0 as [H1 H2].
        specialize (IHphi11 H1).
        specialize (IHphi22 H2).
        cbn. fold no_negative_occurrence_db_b no_positive_occurrence_db_b.
        rewrite IHphi11 IHphi22. reflexivity.
    - split; intros H0; apply IHphi; auto; lia.
    - apply IHphi. lia.
  Qed.


  Lemma Private_wfp_bsvar_subst (phi psi : Pattern) (n : nat) :
    well_formed_positive psi ->
    well_formed_closed_mu_aux psi 0 ->
    well_formed_positive phi ->
    (
      no_negative_occurrence_db_b n phi ->
      well_formed_positive (bsvar_subst phi psi n) )
    /\ (no_positive_occurrence_db_b n phi ->
        forall phi',
          well_formed_positive phi' ->
          well_formed_positive (patt_imp (bsvar_subst phi psi n) phi')
       )
  .
  Proof.
    intros Hwfppsi Hwfcpsi.
    move: n.
    induction phi; intros n' Hwfpphi; cbn in *; auto.
    - split.
      + intros _. case_match; auto.
      + intros H phi' Hwfphi'.
        cbn in *.
        do 2 case_match; auto.
    - split.
      + intros Hnoneg.
        apply andb_prop in Hnoneg. destruct Hnoneg as [Hnoneg1 Hnoneg2].
        apply andb_prop in Hwfpphi. destruct Hwfpphi as [Hwfpphi1 Hwfpphi2].
        
        specialize (IHphi1 n' Hwfpphi1).
        destruct IHphi1 as [IHphi11 IHphi12].
        specialize (IHphi11 Hnoneg1).
        rewrite IHphi11.

        specialize (IHphi2 n' Hwfpphi2).
        destruct IHphi2 as [IHphi21 IHphi22].
        specialize (IHphi21 Hnoneg2).
        rewrite IHphi21.
        auto.
        
      + intros Hnopos.
        apply andb_prop in Hnopos. destruct Hnopos as [Hnopos1 Hnopos2].
        apply andb_prop in Hwfpphi. destruct Hwfpphi as [Hwfpphi1 Hwfpphi2].
        intros phi' Hwfpphi'.

        specialize (IHphi1 n' Hwfpphi1).
        specialize (IHphi2 n' Hwfpphi2).
        destruct IHphi1 as [IHphi11 IHphi12].
        destruct IHphi2 as [IHphi21 IHphi22].
        rewrite IHphi12. fold no_negative_occurrence_db_b no_positive_occurrence_db_b in *.
        { rewrite Hnopos1. auto. }
        specialize (IHphi22 Hnopos2 phi' Hwfpphi').
        apply andb_prop in IHphi22. destruct IHphi22 as [IHphi221 IHphi222].
        rewrite IHphi221. auto.
        rewrite Hwfpphi'. auto.

    - split.
      + intros Hnoposneg.
        apply andb_prop in Hnoposneg. destruct Hnoposneg as [Hnopos1 Hnoneg2].
        apply andb_prop in Hwfpphi. destruct Hwfpphi as [Hwfpphi1 Hwfpphi2].
        specialize (IHphi1 n' Hwfpphi1).
        specialize (IHphi2 n' Hwfpphi2).
        destruct IHphi1 as [IHphi11 IHphi12].
        destruct IHphi2 as [IHphi21 IHphi22].
        specialize (IHphi12 Hnopos1). clear IHphi11.
        specialize (IHphi21 Hnoneg2). clear IHphi22.
        rewrite IHphi21.

        specialize (IHphi12 patt_bott). simpl in IHphi12.
        assert (Htrue: is_true true).
        { auto. }
        specialize (IHphi12 Htrue).
        rewrite IHphi12.
        auto.
      + intros Hnoposneg phi' Hwfpphi'.
        apply andb_prop in Hnoposneg. destruct Hnoposneg as [Hnopos1 Hnoneg2].
        apply andb_prop in Hwfpphi. destruct Hwfpphi as [Hwfpphi1 Hwfpphi2].
        specialize (IHphi1 n' Hwfpphi1).
        specialize (IHphi2 n' Hwfpphi2).
        destruct IHphi1 as [IHphi11 IHphi12].
        destruct IHphi2 as [IHphi21 IHphi22].
        specialize (IHphi11 Hnopos1). clear IHphi12.
        specialize (IHphi22 Hnoneg2). clear IHphi21.
        rewrite IHphi11. rewrite IHphi22; auto.
    - apply andb_prop in Hwfpphi. destruct Hwfpphi as [Hwfpphi1 Hwfpphi2].
      pose proof (IHphi' := IHphi (S n') Hwfpphi2).
      destruct IHphi' as [IHphi1' IHphi2'].
      assert (H: no_negative_occurrence_db_b 0 (bsvar_subst phi psi (S n'))).
      { clear IHphi1' IHphi2'.
        apply no_neg_occ_db_bsvar_subst; auto. lia.
      }
      split.
      + intros Hnonegphi.
        specialize (IHphi1' Hnonegphi).
        rewrite IHphi1'.
        rewrite H.
        auto.
      + intros Hnopos phi' Hwfpphi'.
        rewrite H.
        rewrite IHphi2'.
        rewrite Hnopos.
        2: rewrite Hwfpphi'.
        1,2,3: auto.
  Qed.

  Corollary wfp_bsvar_subst (phi psi : Pattern) :
    well_formed_positive (patt_mu phi) ->
    well_formed_positive psi ->
    well_formed_closed_mu_aux psi 0 ->
    well_formed_positive (bsvar_subst phi psi 0).
  Proof.
    intros H1 H2 H3.
    simpl in H1.
    eapply elimT in H1. 2: apply andP.
    destruct H1 as [Hnonegphi Hwfpphi].
    pose proof (H4 := Private_wfp_bsvar_subst).
    specialize (H4 phi psi 0 H2 H3 Hwfpphi).
    destruct H4 as [H41 H42].
    apply H41.
    apply Hnonegphi.
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
  Declare Scope ml_scope.
  Delimit Scope ml_scope with ml.
  (* TODO: change Bot and Top to unicode symbols *)
  Notation "a $ b" := (patt_app a b) (at level 65, right associativity) : ml_scope.
  Notation "'Bot'" := patt_bott : ml_scope.
  Notation "⊥" := patt_bott : ml_scope.
  Notation "a ---> b"  := (patt_imp a b) (at level 75, right associativity) : ml_scope.
  Notation "'ex' , phi" := (patt_exists phi) (at level 70) : ml_scope.
  Notation "'mu' , phi" := (patt_mu phi) (at level 70) : ml_scope.

  (*Notation "AC [ p ]" := (subst_ctx AC p) (at level 90) : ml_scope.*)
  Notation "C [ p ]" := (emplace C p) (at level 90) : ml_scope.

  (* TODO check whether this is a duplicate of Substitution.Notations *)
  Notation "e .[ 'evar:' dbi ↦ e' ]" := (bevar_subst e e' dbi) (at level 2, e' at level 200, left associativity,
   format "e .[ 'evar:' dbi ↦ e' ]" ).
  Notation "e .[ 'svar:' dbi ↦ e' ]" := (bsvar_subst e e' dbi) (at level 2, e' at level 200, left associativity,
   format "e .[ 'svar:' dbi ↦ e' ]" ).
  Notation "e .[[ 'evar:' x ↦ e' ]]" := (free_evar_subst e e' x) (at level 2, e' at level 200, left associativity,
   format "e .[[ 'evar:' x ↦ e' ]]" ).
  Notation "e .[[ 'svar:' X ↦ e' ]]" := (free_svar_subst e e' X) (at level 2, e' at level 200, left associativity,
   format "e .[[ 'svar:' X ↦ e' ]]" ).
  Notation "e . [ e' ]" := (instantiate e e') (at level 2, e' at level 200, left associativity).

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


Section with_signature.
  Context {Σ : Signature}.

  

End with_signature.


#[export]
 Hint Resolve wf_imp_wfc : core.

#[export]
 Hint Resolve wfc_ex_implies_not_bevar_occur : core.



Definition evar_quantify_ctx {Σ : Signature} (x : evar) (n : db_index) (C : PatternCtx) : PatternCtx :=
  match decide (x = pcEvar C)  with
  | left _ => C
  | right pf => @Build_PatternCtx Σ (pcEvar C) (evar_quantify x n (pcPattern C))
  end.

Lemma is_linear_context_evar_quantify {Σ : Signature} (x : evar) (n : db_index) (C : PatternCtx) :
  is_linear_context C ->
  is_linear_context (evar_quantify_ctx x n C).
Proof.
  intros Hlin. unfold evar_quantify_ctx.
  unfold is_linear_context in *.
  destruct (decide (x = pcEvar C)); simpl.
  - assumption.
  - destruct C. simpl in *.
    rename pcEvar into pcEvar0. rename pcPattern into pcPattern0.
    assert (count_evar_occurrences pcEvar0 (evar_quantify x n pcPattern0)
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

Definition svar_quantify_ctx {Σ : Signature} (X : svar) (n : db_index) (C : PatternCtx) : PatternCtx :=
  @Build_PatternCtx Σ (pcEvar C) (svar_quantify X n (pcPattern C)).

Lemma is_linear_context_svar_quantify {Σ : Signature} (X : svar) (n : db_index) (C : PatternCtx) :
  is_linear_context C ->
  is_linear_context (svar_quantify_ctx X n C).
Proof.
  intros Hlin. unfold svar_quantify_ctx. unfold is_linear_context in *.
  destruct C. simpl in *.
  rename pcEvar into pcEvar0. rename pcPattern into pcPattern0.
  assert (count_evar_occurrences pcEvar0 (svar_quantify X n pcPattern0)
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

Lemma svar_quantify_free_evar_subst {Σ : Signature} ψ ϕ x X n:
  svar_quantify X n (free_evar_subst ψ ϕ x) =
  free_evar_subst (svar_quantify X n ψ) (svar_quantify X n ϕ) x.
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


Lemma svar_quantify_emplace {Σ : Signature} X n C ϕ:
  svar_quantify X n (emplace C ϕ) = emplace (svar_quantify_ctx X n C) (svar_quantify X n ϕ).
Proof.
  destruct C.
  unfold svar_quantify_ctx,emplace. simpl.
Abort.

Lemma evar_quantify_subst_ctx {Σ : Signature} x n AC ϕ:
  x ∉ AC_free_evars AC ->
  evar_quantify x n (subst_ctx AC ϕ) = subst_ctx AC (evar_quantify x n ϕ).
Proof.
  intros Hx.
  induction AC.
  - reflexivity.
  - simpl. simpl in Hx.
    rewrite IHAC.
    { set_solver. }
    rewrite [evar_quantify x n p]evar_quantify_fresh.
    unfold evar_is_fresh_in. set_solver.
    reflexivity.
  - simpl. simpl in Hx.
    rewrite IHAC.
    { set_solver. }
    rewrite [evar_quantify x n p]evar_quantify_fresh.
    unfold evar_is_fresh_in. set_solver.
    reflexivity.
Qed.


Lemma Private_no_negative_occurrence_svar_quantify {Σ : Signature} ϕ level X:
  (
    no_negative_occurrence_db_b level ϕ = true ->
    svar_has_negative_occurrence X ϕ = false ->
    no_negative_occurrence_db_b level (svar_quantify X level ϕ) = true
  )
  /\
  (
    no_positive_occurrence_db_b level ϕ = true ->
    svar_has_positive_occurrence X ϕ = false ->
    no_positive_occurrence_db_b level (svar_quantify X level ϕ) = true
  ).
Proof.
  move: level.
  induction ϕ; intros level; split; intros HnoX Hnolevel; cbn in *; auto.
  - case_match; reflexivity.
  - case_match; cbn. 2: reflexivity. congruence.
  - apply orb_false_iff in Hnolevel. destruct_and!.
    pose proof (IH1 := IHϕ1 level).
    destruct IH1 as [IH11 _].
    specialize (IH11 ltac:(assumption) ltac:(assumption)).
    pose proof (IH2 := IHϕ2 level).
    destruct IH2 as [IH21 _].
    specialize (IH21 ltac:(assumption) ltac:(assumption)).
    split_and!; assumption.
  - apply orb_false_iff in Hnolevel. destruct_and!.
    pose proof (IH1 := IHϕ1 level).
    destruct IH1 as [_ IH12].
    specialize (IH12 ltac:(assumption) ltac:(assumption)).
    pose proof (IH2 := IHϕ2 level).
    destruct IH2 as [_ IH22].
    specialize (IH22 ltac:(assumption) ltac:(assumption)).
    split_and!; assumption.
  - apply orb_false_iff in Hnolevel. destruct_and!.
    pose proof (IH1 := IHϕ1 level).
    destruct IH1 as [_ IH12].
    specialize (IH12 ltac:(assumption) ltac:(assumption)).
    pose proof (IH2 := IHϕ2 level).
    destruct IH2 as [IH21 _].
    specialize (IH21 ltac:(assumption) ltac:(assumption)).
    split_and!; assumption.
  - apply orb_false_iff in Hnolevel. destruct_and!.
    pose proof (IH1 := IHϕ1 level).
    destruct IH1 as [IH11 _].
    specialize (IH11 ltac:(assumption) ltac:(assumption)).
    pose proof (IH2 := IHϕ2 level).
    destruct IH2 as [_ IH22].
    specialize (IH22 ltac:(assumption) ltac:(assumption)).
    split_and!; assumption.
  - firstorder.
  - firstorder.
  - firstorder.
  - firstorder.
Qed.

Lemma no_negative_occurrence_svar_quantify {Σ : Signature} ϕ level X:
  no_negative_occurrence_db_b level ϕ = true ->
  svar_has_negative_occurrence X ϕ = false ->
  no_negative_occurrence_db_b level (svar_quantify X level ϕ) = true.
Proof.
  intros H1 H2.
  pose proof (Htmp :=Private_no_negative_occurrence_svar_quantify ϕ level X).
  destruct Htmp as [Htmp1 Htmp2].
  auto.
Qed.

Lemma no_positive_occurrence_svar_quantify {Σ : Signature} ϕ level X:
    no_positive_occurrence_db_b level ϕ = true ->
    svar_has_positive_occurrence X ϕ = false ->
    no_positive_occurrence_db_b level (svar_quantify X level ϕ) = true.
Proof.
  intros H1 H2.
  pose proof (Htmp :=Private_no_negative_occurrence_svar_quantify ϕ level X).
  destruct Htmp as [Htmp1 Htmp2].
  auto.
Qed.

#[export]
 Hint Resolve no_positive_occurrence_svar_quantify : core.

#[export]
 Hint Resolve no_negative_occurrence_svar_quantify : core.

#[export]
 Hint Resolve wfc_impl_no_neg_occ : core.


Lemma no_negative_occurrence_svar_quantify_2 {Σ : Signature} X dbi1 dbi2 ϕ:
  dbi1 <> dbi2 ->
  no_negative_occurrence_db_b dbi1 (svar_quantify X dbi2 ϕ) = no_negative_occurrence_db_b dbi1 ϕ
with no_positive_occurrence_svar_quantify_2  {Σ : Signature} X dbi1 dbi2 ϕ:
  dbi1 <> dbi2 ->
  no_positive_occurrence_db_b dbi1 (svar_quantify X dbi2 ϕ) = no_positive_occurrence_db_b dbi1 ϕ.
Proof.
  - move: dbi1 dbi2.
    induction ϕ; intros dbi1 dbi2 Hdbi; simpl; auto.
    + case_match; reflexivity.
    + cbn. rewrite IHϕ1. lia. rewrite IHϕ2. lia. reflexivity.
    + unfold no_negative_occurrence_db_b at 1.
      fold (no_positive_occurrence_db_b dbi1 (svar_quantify X dbi2 ϕ1)).
      fold (no_negative_occurrence_db_b dbi1 (svar_quantify X dbi2 ϕ2)).
      rewrite no_positive_occurrence_svar_quantify_2. lia. rewrite IHϕ2. lia. reflexivity.
    + cbn. rewrite IHϕ. lia. reflexivity.
    + cbn. rewrite IHϕ. lia. reflexivity.
  - move: dbi1 dbi2.
    induction ϕ; intros dbi1 dbi2 Hdbi; simpl; auto.
    + case_match; cbn. 2: reflexivity. case_match; congruence.
    + cbn. rewrite IHϕ1. lia. rewrite IHϕ2. lia. reflexivity.
    + unfold no_positive_occurrence_db_b at 1.
      fold (no_negative_occurrence_db_b dbi1 (svar_quantify X dbi2 ϕ1)).
      fold (no_positive_occurrence_db_b dbi1 (svar_quantify X dbi2 ϕ2)).
      rewrite no_negative_occurrence_svar_quantify_2. lia. rewrite IHϕ2. lia. reflexivity.
    + cbn. rewrite IHϕ. lia. reflexivity.
    + cbn. rewrite IHϕ. lia. reflexivity.
Qed.

Lemma well_formed_positive_svar_quantify {Σ : Signature} X dbi ϕ:
  well_formed_positive ϕ ->
  well_formed_positive (svar_quantify X dbi ϕ) = true.
Proof.
  intros Hϕ.
  move: dbi.
  induction ϕ; intros dbi; simpl; auto.
  - case_match; reflexivity.
  - simpl in Hϕ.
    destruct_and!.
    specialize (IHϕ1 ltac:(assumption)).
    specialize (IHϕ2 ltac:(assumption)).
    rewrite IHϕ1. rewrite IHϕ2.
    reflexivity.
  - simpl in Hϕ.
    destruct_and!.
    specialize (IHϕ1 ltac:(assumption)).
    specialize (IHϕ2 ltac:(assumption)).
    rewrite IHϕ1. rewrite IHϕ2.
    reflexivity.
  - simpl in Hϕ.
    destruct_and!.
    specialize (IHϕ ltac:(assumption)).
    rewrite IHϕ.
    rewrite no_negative_occurrence_svar_quantify_2. lia.
    split_and!; auto.
Qed.

#[export]
 Hint Resolve well_formed_positive_svar_quantify : core.

(* Lemma bevar_occur_positivity {Σ : Signature} ψ dbi :
  bsvar_occur ψ dbi = false ->
  no_negative_occurrence_db_b dbi ψ = true /\ no_positive_occurrence_db_b dbi ψ.
Proof.
  induction ψ; intros H; cbn; auto.
  * simpl in H. case_match; auto.
  * Search bsvar_occur. *)

Lemma nno_free_svar_subst {Σ : Signature} dbi ϕ ψ X:
  well_formed_closed_mu_aux ψ dbi ->
  no_negative_occurrence_db_b dbi (free_svar_subst ϕ ψ X)
  = no_negative_occurrence_db_b dbi ϕ
with npo_free_svar_subst {Σ : Signature} dbi ϕ ψ X:
  well_formed_closed_mu_aux ψ dbi ->
  no_positive_occurrence_db_b dbi (free_svar_subst ϕ ψ X)
  = no_positive_occurrence_db_b dbi ϕ.
Proof.
  - move: dbi.
    induction ϕ; intros dbi Hwf; simpl; auto.
    + case_match; cbn; [|reflexivity].
      eapply Private_wfc_impl_no_neg_pos_occ. exact Hwf. lia.
    + cbn. rewrite IHϕ1; auto. rewrite IHϕ2; auto.
    + cbn.
      fold (no_positive_occurrence_db_b).
      rewrite nno_free_svar_subst; auto.
      rewrite npo_free_svar_subst; auto.
    + cbn.
      rewrite IHϕ; auto.
    + cbn.
      rewrite IHϕ; auto. eapply well_formed_closed_mu_aux_ind. 2: exact Hwf. lia.
  - move: dbi.
    induction ϕ; intros dbi Hwf; simpl; auto.
    + case_match; cbn; [|reflexivity].
      eapply Private_wfc_impl_no_neg_pos_occ. exact Hwf. lia.
    + cbn. rewrite IHϕ1; auto. rewrite IHϕ2; auto.
    + cbn.
      fold (no_negative_occurrence_db_b).
      rewrite nno_free_svar_subst; auto.
      rewrite IHϕ2; auto.
    + cbn.
      rewrite IHϕ; auto.
    + cbn.
      rewrite IHϕ; auto. eapply well_formed_closed_mu_aux_ind. 2: exact Hwf. lia.
Qed.

Lemma wfp_free_svar_subst_1 {Σ : Signature} ϕ ψ X:
  well_formed_closed ψ = true ->
  well_formed_positive ψ = true ->
  well_formed_positive ϕ = true ->
  well_formed_positive (free_svar_subst ϕ ψ X) = true.
Proof.
  intros wfcψ wfpψ wfpϕ.
  induction ϕ; simpl; auto.
  - case_match; auto.
  - simpl in wfpϕ. destruct_and!.
    rewrite -> IHϕ1 by assumption.
    rewrite -> IHϕ2 by assumption.
    reflexivity.
  - simpl in wfpϕ. destruct_and!.
    rewrite -> IHϕ1 by assumption.
    rewrite -> IHϕ2 by assumption.
    reflexivity.
  - simpl in wfpϕ. destruct_and!.
    specialize (IHϕ H0).
    rewrite -> IHϕ.
    rewrite nno_free_svar_subst.
    { apply andb_true_iff in wfcψ. apply wfcψ. }
    rewrite H.
    reflexivity.
Qed.

Lemma wfp_free_svar_subst {Σ : Signature} ϕ ψ X:
  well_formed_closed_mu_aux ψ 0 ->
  well_formed_positive ψ = true ->
  well_formed_positive ϕ = true ->
  svar_has_negative_occurrence X ϕ = false ->
  well_formed_positive (free_svar_subst ϕ ψ X) = true
with wfp_neg_free_svar_subst {Σ : Signature} ϕ ψ X:
  well_formed_closed_mu_aux ψ 0 ->
  well_formed_positive ψ = true ->
  well_formed_positive ϕ = true ->
  svar_has_positive_occurrence X ϕ = false ->
  well_formed_positive (free_svar_subst ϕ ψ X) = true.
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
      pose proof (IH1 := wfp_neg_free_svar_subst Σ ϕ1 ψ X ltac:(assumption)).
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
      pose proof (IH1 := wfp_free_svar_subst Σ ϕ1 ψ X ltac:(assumption)).
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

#[export]
 Hint Resolve wfp_free_svar_subst : core.

#[export]
 Hint Resolve wfp_neg_free_svar_subst : core.

Lemma wfc_mu_free_svar_subst {Σ : Signature} level ϕ ψ X:
  well_formed_closed_mu_aux ϕ level ->
  well_formed_closed_mu_aux ψ level ->
  well_formed_closed_mu_aux (free_svar_subst ϕ ψ X) level = true.
Proof.
  intros Hϕ Hψ.
  move: level Hϕ Hψ.
  induction ϕ; intros level Hϕ Hψ; simpl in *; auto.
  - case_match; [|reflexivity].
    assumption.
  - destruct_and!.
    rewrite IHϕ1; auto.
    rewrite IHϕ2; auto.
  - destruct_and!.
    rewrite IHϕ1; auto.
    rewrite IHϕ2; auto.
  - rewrite IHϕ; auto. eapply well_formed_closed_mu_aux_ind. 2: exact Hψ. lia.
Qed.

#[export]
 Hint Resolve wfc_mu_free_svar_subst : core.

Lemma wfc_ex_free_svar_subst {Σ : Signature} level ϕ ψ X:
  well_formed_closed_ex_aux ϕ level ->
  well_formed_closed_ex_aux ψ level ->
  well_formed_closed_ex_aux (free_svar_subst ϕ ψ X) level = true.
Proof.
  intros Hϕ Hψ.
  move: level Hϕ Hψ.
  induction ϕ; intros level Hϕ Hψ; simpl in *; auto.
  - case_match; [|reflexivity].
    assumption.
  - destruct_and!.
    rewrite IHϕ1; auto.
    rewrite IHϕ2; auto.
  - destruct_and!.
    rewrite IHϕ1; auto.
    rewrite IHϕ2; auto.
  - rewrite IHϕ; auto. eapply well_formed_closed_ex_aux_ind. 2: exact Hψ. lia.
Qed.

#[export]
 Hint Resolve wfc_mu_free_svar_subst : core.

Lemma wfc_ex_free_evar_subst_2 {Σ : Signature} level ϕ ψ X:
  well_formed_closed_ex_aux ϕ level ->
  well_formed_closed_ex_aux ψ level ->
  well_formed_closed_ex_aux (free_evar_subst ϕ ψ X) level = true.
Proof.
  intros Hϕ Hψ.
  move: level Hϕ Hψ.
  induction ϕ; intros level Hϕ Hψ; simpl in *; auto.
  - case_match; [|reflexivity].
    repeat case_match; auto.
  - destruct_and!.
    rewrite IHϕ1; auto.
    rewrite IHϕ2; auto.
  - destruct_and!.
    rewrite IHϕ1; auto.
    rewrite IHϕ2; auto.
  - rewrite IHϕ; auto. eapply well_formed_closed_ex_aux_ind. 2: exact Hψ. lia.
Qed.

#[export]
 Hint Resolve wfc_ex_free_evar_subst_2 : core.

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

Lemma count_evar_occurrences_bevar_subst {Σ : Signature} pcEvar ϕ ψ k:
  count_evar_occurrences pcEvar ψ = 0 ->
  count_evar_occurrences pcEvar (bevar_subst ϕ ψ k) = count_evar_occurrences pcEvar ϕ.
Proof.
  intros H.
  move: k.
  induction ϕ; intros k; simpl; auto.
  - case_match; auto.
Qed.

Lemma count_evar_occurrences_evar_open {Σ : Signature} pcEvar ϕ x:
  pcEvar <> x ->
  count_evar_occurrences pcEvar (evar_open 0 x ϕ) = count_evar_occurrences pcEvar ϕ.
Proof.
  intros H. apply count_evar_occurrences_bevar_subst. simpl. case_match; congruence.
Qed.


      
#[export]
 Hint Resolve wfp_evar_open : core.

#[export]
 Hint Resolve wfc_mu_aux_body_ex_imp1 : core.

#[export]
 Hint Resolve wfc_ex_aux_body_ex_imp1 : core.


Lemma evar_open_size' {Σ : Signature} :
  forall (k : db_index) (n : evar) (p : Pattern),
    size' (evar_open k n p) = size' p.
Proof.
  intros k n p. generalize dependent k.
  induction p; intros k; cbn; try reflexivity.
  break_match_goal; reflexivity.
  rewrite (IHp1 k); rewrite (IHp2 k); reflexivity.
  rewrite (IHp1 k); rewrite (IHp2 k); reflexivity.
  rewrite (IHp (S k)); reflexivity.
  rewrite (IHp k); reflexivity.
Qed.

Lemma svar_open_size' {Σ : Signature} :
  forall (k : db_index) (n : svar) (p : Pattern),
    size' (svar_open k n p) = size' p.
Proof.
  intros k n p. generalize dependent k.
  induction p; intros k; cbn; try reflexivity.
  break_match_goal; reflexivity.
  rewrite (IHp1 k); rewrite (IHp2 k); reflexivity.
  rewrite (IHp1 k); rewrite (IHp2 k); reflexivity.
  rewrite (IHp k); reflexivity.
  rewrite (IHp (S k)); reflexivity.
Qed.

(* TODO remove the no-negative-ocurrence assumption from the svar version *)
Lemma wfp_free_evar_subst {Σ : Signature} ϕ ψ x:
  well_formed_closed_mu_aux ψ 0 ->
  well_formed_positive ψ = true ->
  well_formed_positive ϕ = true ->
  well_formed_positive (free_evar_subst ϕ ψ x) = true
with wfp_neg_free_evar_subst {Σ : Signature} ϕ ψ x:
  well_formed_closed_mu_aux ψ 0 ->
  well_formed_positive ψ = true ->
  well_formed_positive ϕ = true ->
  well_formed_positive (free_evar_subst ϕ ψ x) = true.
Proof.
  -
    intros Hwfcψ Hwfpψ Hwfpϕ. (* Hnoneg.*)
    induction ϕ; simpl; auto.
    + case_match; [|reflexivity].
      assumption.
    + cbn in Hwfpϕ.
      destruct_and!.
      specialize (IHϕ1 ltac:(assumption)).
      specialize (IHϕ2 ltac:(assumption)).
      split_and!; auto.
    + cbn in Hwfpϕ.
      destruct_and!.
      pose proof (IH1 := wfp_neg_free_evar_subst Σ ϕ1 ψ x ltac:(assumption)).
      feed specialize IH1.
      { assumption. }
      { assumption. }
      specialize (IHϕ2 ltac:(assumption)).
      split_and!; auto.
    + cbn in Hwfpϕ. destruct_and!.
      rewrite IHϕ. assumption. split_and!; auto.
      rewrite free_evar_subst_preserves_no_negative_occurrence; auto.
  -
    intros Hwfcψ Hwfpψ Hwfpϕ.
    induction ϕ; simpl; auto.
    + case_match; [|reflexivity].
      assumption.
    + cbn in Hwfpϕ.
      destruct_and!.
      specialize (IHϕ1 ltac:(assumption)).
      specialize (IHϕ2 ltac:(assumption)).
      split_and!; auto.
    + cbn in Hwfpϕ.
      destruct_and!.
      pose proof (IH1 := wfp_free_evar_subst Σ ϕ1 ψ x ltac:(assumption)).
      feed specialize IH1.
      { assumption. }
      { assumption. }
      specialize (IHϕ2 ltac:(assumption)).
      split_and!; auto.
    + cbn in Hwfpϕ. destruct_and!.
      rewrite IHϕ. assumption. split_and!; auto.
      rewrite free_evar_subst_preserves_no_negative_occurrence; auto.
Qed.

#[export]
 Hint Resolve wfp_free_evar_subst : core.

#[export]
Hint Resolve bevar_subst_positive_2 : core.

#[export]
Hint Resolve wfc_mu_aux_bevar_subst : core.

#[export]
Hint Resolve wfc_ex_aux_bevar_subst : core.

Lemma count_evar_occurrences_svar_open {Σ : Signature} x dbi ϕ ψ:
  count_evar_occurrences x ψ = 0 ->
  count_evar_occurrences x (bsvar_subst ϕ ψ dbi) = count_evar_occurrences x ϕ.
Proof.
  move: dbi.
  induction ϕ; intros dbi H; simpl; auto.
  case_match; auto.
Qed.

#[export]
Hint Resolve wfp_svar_open : core.

Lemma free_evar_subst_bsvar_subst {Σ : Signature} ϕ ψ ξ x dbi:
  well_formed_closed_mu_aux ξ 0 ->
  evar_is_fresh_in x ψ ->
  free_evar_subst (bsvar_subst ϕ ψ dbi) ξ x
  = bsvar_subst (free_evar_subst ϕ ξ x) ψ dbi.
Proof.
  move: dbi.
  induction ϕ; intros dbi H1 H2; simpl; auto.
  - repeat case_match; auto.
    erewrite well_formed_bsvar_subst. reflexivity.
    2: eassumption.
    lia.
  - repeat case_match; auto.
    apply free_evar_subst_no_occurrence.
    apply count_evar_occurrences_0. assumption.
  - rewrite IHϕ1; auto. rewrite IHϕ2; auto.
  - rewrite IHϕ1; auto. rewrite IHϕ2; auto.
  - rewrite IHϕ; auto.
  - rewrite IHϕ; auto.
Qed.

Lemma svar_hno_bsvar_subst {Σ : Signature} X ϕ ψ dbi:
  (svar_has_negative_occurrence X ψ = true -> no_positive_occurrence_db_b dbi ϕ = true) ->
  (svar_has_positive_occurrence X ψ = true -> no_negative_occurrence_db_b dbi ϕ = true) ->
  svar_has_negative_occurrence X ϕ = false ->
  svar_has_negative_occurrence X (bsvar_subst ϕ ψ dbi) = false
with svar_hpo_bsvar_subst {Σ : Signature} X ϕ ψ dbi:
       (svar_has_negative_occurrence X ψ = true -> no_negative_occurrence_db_b dbi ϕ = true) ->
       (svar_has_positive_occurrence X ψ = true -> no_positive_occurrence_db_b dbi ϕ = true) ->
       svar_has_positive_occurrence X ϕ = false ->
       svar_has_positive_occurrence X (bsvar_subst ϕ ψ dbi) = false.
Proof.
  -
    move: dbi.
    induction ϕ; intros dbi H1 H2 H3; cbn in *; auto.
    + case_match; auto. case_match; try lia.
      destruct (decide (svar_has_negative_occurrence X ψ = false)); auto.
      apply not_false_is_true in n0. specialize (H1 n0). congruence. case_match; auto. congruence.
    + apply orb_false_iff in H3.
      destruct_and!.
      rewrite IHϕ1; auto.
      { naive_bsolver. }
      { naive_bsolver. }
      rewrite IHϕ2; auto.
      { naive_bsolver. }
      { naive_bsolver. }
    + fold svar_has_positive_occurrence in *.
      fold no_positive_occurrence_db_b in *.
      fold no_negative_occurrence_db_b in *.
      apply orb_false_iff in H3.
      destruct_and!.
      rewrite svar_hpo_bsvar_subst; auto.
      { naive_bsolver. }
      { naive_bsolver. }
      rewrite IHϕ2; auto.
      { naive_bsolver. }
      { naive_bsolver. }
  -
    move: dbi.
    induction ϕ; intros dbi H1 H2 H3; cbn in *; auto.
    + case_match; auto. case_match; try lia.
      destruct (decide (svar_has_positive_occurrence X ψ = false)); auto.
      apply not_false_is_true in n0. specialize (H2 n0). congruence. case_match; auto. congruence.
    + apply orb_false_iff in H3.
      destruct_and!.
      rewrite IHϕ1; auto.
      { naive_bsolver. }
      { naive_bsolver. }
      rewrite IHϕ2; auto.
      { naive_bsolver. }
      { naive_bsolver. }
    + fold svar_has_positive_occurrence in *.
      fold svar_has_negative_occurrence in *.
      fold no_positive_occurrence_db_b in *.
      fold no_negative_occurrence_db_b in *.
      apply orb_false_iff in H3.
      destruct_and!.
      rewrite svar_hno_bsvar_subst; auto.
      { naive_bsolver. }
      { naive_bsolver. }
      rewrite IHϕ2; auto.
      { naive_bsolver. }
      { naive_bsolver. }
Qed.

Lemma svar_hno_false_if_fresh {Σ : Signature} X ϕ:
  svar_is_fresh_in X ϕ ->
  svar_has_negative_occurrence X ϕ = false
with svar_hpo_false_if_fresh {Σ : Signature} X ϕ:
       svar_is_fresh_in X ϕ ->
       svar_has_positive_occurrence X ϕ = false.
Proof.
  - unfold svar_is_fresh_in.
    induction ϕ; intros H; cbn in *; auto.
    + rewrite -> IHϕ1, -> IHϕ2; try reflexivity; set_solver.
    + fold svar_has_positive_occurrence.
      rewrite -> svar_hpo_false_if_fresh, -> IHϕ2; try reflexivity.
      * set_solver.
      * unfold svar_is_fresh_in. set_solver.
  - unfold svar_is_fresh_in.
    induction ϕ; intros H; cbn in *; auto.
    + case_match; auto. set_solver.
    + rewrite -> IHϕ1, -> IHϕ2; try reflexivity; set_solver.
    + fold svar_has_negative_occurrence.
      rewrite -> svar_hno_false_if_fresh, -> IHϕ2; try reflexivity.
      * set_solver.
      * unfold svar_is_fresh_in. set_solver.
Qed.

Lemma wfc_mu_free_evar_subst {Σ : Signature} level ϕ ψ x:
  well_formed_closed_mu_aux ϕ level ->
  well_formed_closed_mu_aux ψ level ->
  well_formed_closed_mu_aux (free_evar_subst ϕ ψ x) level = true.
Proof.
  intros Hϕ Hψ.
  move: level Hϕ Hψ.
  induction ϕ; intros level Hϕ Hψ; simpl in *; auto.
  - case_match; [|reflexivity].
    assumption.
  - destruct_and!.
    rewrite IHϕ1; auto.
    rewrite IHϕ2; auto.
  - destruct_and!.
    rewrite IHϕ1; auto.
    rewrite IHϕ2; auto.
  - apply IHϕ; auto.
    eapply well_formed_closed_mu_aux_ind.
    2: eassumption. lia.
Qed.


Lemma well_formed_app_proj1 {Σ : Signature} p q:
  well_formed (patt_app p q) ->
  well_formed p.
Proof.
  intros H.
  unfold well_formed,well_formed_closed in *. simpl in *.
  destruct_and!.
  unfold well_formed,well_formed_closed. split_and!; assumption.
Qed.

Lemma well_formed_app_proj2 {Σ : Signature} p q:
  well_formed (patt_app p q) ->
  well_formed q.
Proof.
  intros H.
  unfold well_formed,well_formed_closed in *. simpl in *.
  destruct_and!.
  unfold well_formed,well_formed_closed. split_and!; assumption.
Qed.

Lemma well_formed_imp_proj1 {Σ : Signature} p q:
  well_formed (patt_imp p q) ->
  well_formed p.
Proof.
  intros H.
  unfold well_formed,well_formed_closed in *. simpl in *.
  destruct_and!.
  unfold well_formed,well_formed_closed. split_and!; assumption.
Qed.

Lemma well_formed_imp_proj2 {Σ : Signature} p q:
  well_formed (patt_imp p q) ->
  well_formed q.
Proof.
  intros H.
  unfold well_formed,well_formed_closed in *. simpl in *.
  destruct_and!.
  unfold well_formed,well_formed_closed. split_and!; assumption.
Qed.


Tactic Notation "wf_auto" int_or_var(n)
  := auto n; unfold well_formed, well_formed_closed in *; destruct_and?; simpl in *; split_and?; auto n.
Tactic Notation "wf_auto" := wf_auto 5.

Import Notations.

  Lemma wf_evar_open_from_wf_ex {Σ : Signature} x ϕ:
    well_formed (patt_exists ϕ) ->
    well_formed (evar_open 0 x ϕ).
  Proof.
    intros H. wf_auto.
  Qed.

  Lemma wf_svar_open_from_wf_mu {Σ : Signature} X ϕ:
    well_formed (patt_mu ϕ) ->
    well_formed (svar_open 0 X ϕ).
  Proof.
    intros H. wf_auto;
    destruct_and!;
        [ (apply wfp_svar_open; auto)
        | (apply wfc_mu_aux_body_mu_imp1; assumption)
        | (apply wfc_ex_aux_body_mu_imp1; assumption)
        ].
  Qed.


Lemma wfcex_after_subst_impl_wfcex_before {Σ : Signature} ϕ ψ x dbi:
  well_formed_closed_ex_aux (free_evar_subst ϕ ψ x) dbi = true ->
  well_formed_closed_ex_aux ϕ dbi = true.
Proof.
  intros Hsubst.
  move: dbi Hsubst.
  induction ϕ; intros dbi Hsubst; simpl in *; auto.
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

Lemma wfcmu_after_subst_impl_wfcmu_before {Σ : Signature} ϕ ψ x dbi:
  well_formed_closed_mu_aux (free_evar_subst ϕ ψ x) dbi = true ->
  well_formed_closed_mu_aux ϕ dbi = true.
Proof.
  intros Hsubst.
  move: dbi Hsubst.
  induction ϕ; intros dbi Hsubst; simpl in *; auto.
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

Lemma nno_after_subst_impl_nno_before {Σ : Signature} ϕ ψ x dbi:
  no_negative_occurrence_db_b dbi (free_evar_subst ϕ ψ x) = true ->
  no_negative_occurrence_db_b dbi ϕ = true
with npo_after_subst_impl_npo_before {Σ : Signature} ϕ ψ x dbi:
  no_positive_occurrence_db_b dbi (free_evar_subst ϕ ψ x) = true ->
  no_positive_occurrence_db_b dbi ϕ = true.
Proof.
  - move: dbi.
    induction ϕ; intros dbi Hsubst; cbn in *; auto.
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
    induction ϕ; intros dbi Hsubst; cbn in *; auto.
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

#[export]
 Hint Resolve wfc_mu_free_evar_subst : core.

Lemma wfp_after_subst_impl_wfp_before {Σ : Signature} ϕ ψ x:
  well_formed_positive (free_evar_subst ϕ ψ x) = true ->
  well_formed_positive ϕ = true.
Proof.
  intros Hsubst.
  move: Hsubst.
  induction ϕ; intros Hsubst; simpl in *; auto.
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

Lemma wf_after_subst_impl_wf_before {Σ : Signature} ϕ ψ x:
  well_formed (free_evar_subst ϕ ψ x) = true ->
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

Lemma wf_emplaced_impl_wf_context {Σ : Signature} (C : PatternCtx) (ψ : Pattern) :
  well_formed (emplace C ψ) = true ->
  PC_wf C.
Proof.
  intros H.
  unfold emplace in H. unfold PC_wf.
  eapply wf_after_subst_impl_wf_before.
  eassumption.
Qed.

Global Instance evar_is_fresh_in_dec {Σ : Signature} (x : evar) (p : Pattern) :
  Decision (evar_is_fresh_in x p).
Proof.
  unfold evar_is_fresh_in.
  apply not_dec. apply gset_elem_of_dec.
Defined.

Definition evar_is_fresh_in_list {Σ : Signature} (x : evar) (l : list Pattern) :=
  Forall (evar_is_fresh_in x) l.

Global Instance evar_is_fresh_in_list_dec {Σ : Signature} (x : evar) (l : list Pattern) :
  Decision (evar_is_fresh_in_list x l).
Proof.
  unfold Decision. unfold evar_is_fresh_in_list.
  apply Forall_dec.
  intros p.
  apply evar_is_fresh_in_dec.
Defined.

Global Instance svar_is_fresh_in_dec {Σ : Signature} (X : svar) (p : Pattern) :
  Decision (svar_is_fresh_in X p).
Proof.
  unfold svar_is_fresh_in.
  apply not_dec. apply gset_elem_of_dec.
Defined.

Definition svar_is_fresh_in_list {Σ : Signature} (X : svar) (l : list Pattern) :=
  Forall (svar_is_fresh_in X) l.

Global Instance svar_is_fresh_in_list_dec {Σ : Signature} (X : svar) (l : list Pattern) :
  Decision (svar_is_fresh_in_list X l).
Proof.
  unfold Decision. unfold svar_is_fresh_in_list.
  apply Forall_dec.
  intros p.
  apply svar_is_fresh_in_dec.
Defined.

Lemma no_neg_occ_quan_impl_no_neg_occ {Σ : Signature} x n1 n2 ϕ:
 no_negative_occurrence_db_b n1 (evar_quantify x n2 ϕ) = true ->
 no_negative_occurrence_db_b n1 ϕ = true
with no_pos_occ_quan_impl_no_pos_occ {Σ : Signature} x n1 n2 ϕ:
 no_positive_occurrence_db_b n1 (evar_quantify x n2 ϕ) = true ->
 no_positive_occurrence_db_b n1 ϕ = true.
Proof.
 - intros H.
   move: n1 n2 H.
   induction ϕ; intros n1 n2 H; simpl in *; auto.
   + unfold no_negative_occurrence_db_b in *. simpl in *. fold no_negative_occurrence_db_b in *.
     destruct_and!.
     erewrite -> IHϕ1 by eassumption.
     erewrite -> IHϕ2 by eassumption.
     reflexivity.
   + unfold no_negative_occurrence_db_b in *. simpl in *.
     fold no_negative_occurrence_db_b no_positive_occurrence_db_b in *.
     destruct_and!.
     erewrite -> no_pos_occ_quan_impl_no_pos_occ by eassumption.
     erewrite -> IHϕ2 by eassumption.
     reflexivity.
   + unfold no_negative_occurrence_db_b in *. simpl in *. fold no_negative_occurrence_db_b in *.
     erewrite -> IHϕ by eassumption.
     reflexivity.
   + unfold no_negative_occurrence_db_b in *. simpl in *. fold no_negative_occurrence_db_b in *.
     erewrite -> IHϕ by eassumption.
     reflexivity.
 - intros H.
   move: n1 n2 H.
   induction ϕ; intros n1 n2 H; simpl in *; auto.
   + unfold no_positive_occurrence_db_b in *. simpl in *. fold no_positive_occurrence_db_b in *.
     destruct_and!.
     erewrite -> IHϕ1 by eassumption.
     erewrite -> IHϕ2 by eassumption.
     reflexivity.
   + unfold no_positive_occurrence_db_b in *. simpl in *.
     fold no_positive_occurrence_db_b no_negative_occurrence_db_b in *.
     destruct_and!.
     erewrite -> no_neg_occ_quan_impl_no_neg_occ by eassumption.
     erewrite -> IHϕ2 by eassumption.
     reflexivity.
   + unfold no_positive_occurrence_db_b in *. simpl in *. fold no_positive_occurrence_db_b in *.
     erewrite -> IHϕ by eassumption.
     reflexivity.
   + unfold no_positive_occurrence_db_b in *. simpl in *. fold no_positive_occurrence_db_b in *.
     erewrite -> IHϕ by eassumption.
     reflexivity.
Qed.

Lemma wfp_evar_quan_impl_wfp {Σ : Signature} x n ϕ:
  well_formed_positive (evar_quantify x n ϕ) = true ->
  well_formed_positive ϕ.
Proof.
  intros H.
  move: n H.
  induction ϕ; intros n' H; simpl in *; auto.
  - destruct_and!.
    erewrite -> IHϕ1 by eassumption.
    erewrite -> IHϕ2 by eassumption.
    reflexivity.
  - destruct_and!.
    erewrite -> IHϕ1 by eassumption.
    erewrite -> IHϕ2 by eassumption.
    reflexivity.
  - erewrite IHϕ by eassumption.
    reflexivity.
  - simpl.
    destruct_and!.
    erewrite -> IHϕ by eassumption.
    erewrite -> no_neg_occ_quan_impl_no_neg_occ by eassumption.
    reflexivity.
Qed.

Lemma wfcex_evar_quan_impl_wfcex {Σ : Signature} x n dbi ϕ:
  well_formed_closed_ex_aux (evar_quantify x n ϕ) dbi = true ->
  well_formed_closed_ex_aux ϕ dbi.
Proof.
  intros H.
  move: n dbi H.
  induction ϕ; intros n' dbi H; simpl in *; auto.
  - destruct_and!.
    erewrite -> IHϕ1 by eassumption.
    erewrite -> IHϕ2 by eassumption.
    reflexivity.
  - destruct_and!.
    erewrite -> IHϕ1 by eassumption.
    erewrite -> IHϕ2 by eassumption.
    reflexivity.
  - erewrite IHϕ by eassumption.
    reflexivity.
  - simpl.
    erewrite -> IHϕ by eassumption.
    reflexivity.
Qed.

Lemma wfcmu_evar_quan_impl_wfcmu {Σ : Signature} x n dbi ϕ:
  well_formed_closed_mu_aux (evar_quantify x n ϕ) dbi = true ->
  well_formed_closed_mu_aux ϕ dbi.
Proof.
  intros H.
  move: n dbi H.
  induction ϕ; intros n' dbi H; simpl in *; auto.
  - destruct_and!.
    erewrite -> IHϕ1 by eassumption.
    erewrite -> IHϕ2 by eassumption.
    reflexivity.
  - destruct_and!.
    erewrite -> IHϕ1 by eassumption.
    erewrite -> IHϕ2 by eassumption.
    reflexivity.
  - erewrite IHϕ by eassumption.
    reflexivity.
  - simpl.
    erewrite -> IHϕ by eassumption.
    reflexivity.
Qed.

Lemma wfc_ex_lower (Σ : Signature) ϕ n:
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

Lemma wfc_mu_lower (Σ : Signature) ϕ n:
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

Lemma wf_ex_quan_impl_wf {Σ : Signature} (x : evar) (ϕ : Pattern):
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

Lemma bevar_occur_evar_open_2 {Σ : Signature} dbi x ϕ:
  well_formed_closed_ex_aux ϕ dbi ->
  bevar_occur (evar_open dbi x ϕ) dbi = false.
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

Lemma bsvar_occur_svar_open_2 {Σ : Signature} dbi X ϕ:
  well_formed_closed_mu_aux ϕ dbi ->
  bsvar_occur (svar_open dbi X ϕ) dbi = false.
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

