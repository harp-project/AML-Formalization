From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Coq.Logic Require Import FunctionalExtensionality PropExtensionality Classical_Pred_Type Classical_Prop.
From Coq.micromega Require Import Lia.
From Coq.Program Require Import Wf.

From stdpp Require Import base fin_sets.
From stdpp Require Import pmap gmap mapset fin_sets sets propset.

From MatchingLogic.Utils Require Import Lattice stdpp_ext extralibrary.
From MatchingLogic Require Import Syntax NamedAxioms.

Import MatchingLogic.Syntax.Notations.

Section index_manipulation.
  Context {Σ : Signature}.

  Fixpoint nest_ex_aux level more ϕ {struct ϕ} : Pattern :=
    match ϕ with
    | patt_free_evar _ => ϕ
    | patt_free_svar _ => ϕ
    | patt_bound_evar n => patt_bound_evar (if decide (n < level) is left _ then n else n + more)
    | patt_bound_svar _ => ϕ
    | patt_sym _ => ϕ
    | patt_bott => ϕ
    | patt_app ϕ₁ ϕ₂ => patt_app (nest_ex_aux level more ϕ₁) (nest_ex_aux level more ϕ₂)
    | patt_imp ϕ₁ ϕ₂ => patt_imp (nest_ex_aux level more ϕ₁) (nest_ex_aux level more ϕ₂)
    | patt_exists ϕ' => patt_exists (nest_ex_aux (S level) more ϕ')
    | patt_mu ϕ' => patt_mu (nest_ex_aux level more ϕ')
    end.

  Fixpoint nest_mu_aux level more ϕ {struct ϕ} : Pattern :=
    match ϕ with
    | patt_free_evar _ => ϕ
    | patt_free_svar _ => ϕ
    | patt_bound_evar _ => ϕ
    | patt_bound_svar n => patt_bound_svar (if decide (n < level) is left _ then n else n + more)
    | patt_sym _ => ϕ
    | patt_bott => ϕ
    | patt_app ϕ₁ ϕ₂ => patt_app (nest_mu_aux level more ϕ₁) (nest_mu_aux level more ϕ₂)
    | patt_imp ϕ₁ ϕ₂ => patt_imp (nest_mu_aux level more ϕ₁) (nest_mu_aux level more ϕ₂)
    | patt_exists ϕ' => patt_exists (nest_mu_aux level more ϕ')
    | patt_mu ϕ' => patt_mu (nest_mu_aux (S level) more ϕ')
    end.
  
  Definition nest_ex ϕ := nest_ex_aux 0 1 ϕ.
  Definition nest_mu ϕ := nest_mu_aux 0 1 ϕ.

  Lemma not_bevar_occur_level_nest_ex_aux level more ϕ :
    more > 0 ->
    bevar_occur (nest_ex_aux level more ϕ) level = false.
  Proof.
    intros Hmore.
    move: ϕ level.
    induction ϕ; move=> level; simpl; auto.
    - repeat case_match; simpl; auto; lia.
    - rewrite IHϕ1. rewrite IHϕ2. simpl. reflexivity.
    - rewrite IHϕ1. rewrite IHϕ2. simpl. reflexivity.
  Qed.

  Corollary not_bevar_occur_0_nest_ex ϕ :
    bevar_occur (nest_ex ϕ) 0 = false.
  Proof.
    apply not_bevar_occur_level_nest_ex_aux. lia.
  Qed.

  Lemma nest_ex_same : forall φ dbi ψ,
     bevar_subst (nest_ex_aux dbi 1 φ) ψ dbi = φ.
  Proof.
    induction φ; intros; cbn; auto.
    * do 2 case_match; auto; try lia. rewrite Nat.add_comm. now simpl.
    * now rewrite -> IHφ1, -> IHφ2.
    * now rewrite -> IHφ1, -> IHφ2.
    * simpl. now rewrite IHφ.
    * now rewrite IHφ.
  Qed.

  Lemma not_bsvar_occur_level_nest_mu_aux level more ϕ :
    more > 0 ->
    bsvar_occur (nest_mu_aux level more ϕ) level = false.
  Proof.
    intros Hmore.
    move: ϕ level.
    induction ϕ; move=> level; simpl; auto.
    - repeat case_match; simpl; auto; lia.
    - rewrite IHϕ1. rewrite IHϕ2. simpl. reflexivity.
    - rewrite IHϕ1. rewrite IHϕ2. simpl. reflexivity.
  Qed.

  Corollary not_bsvar_occur_0_nest_mu ϕ :
    bsvar_occur (nest_mu ϕ) 0 = false.
  Proof.
    apply not_bsvar_occur_level_nest_mu_aux. lia.
  Qed.

  Lemma nest_mu_same : forall φ dbi ψ,
     bsvar_subst (nest_mu_aux dbi 1 φ) ψ dbi = φ.
  Proof.
    induction φ; intros; cbn; auto.
    * do 2 case_match; auto; try lia. rewrite Nat.add_comm. now simpl.
    * now rewrite -> IHφ1, -> IHφ2.
    * now rewrite -> IHφ1, -> IHφ2.
    * simpl. now rewrite IHφ.
    * now rewrite IHφ.
  Qed.

  Lemma nest_ex_aux_comm n more more' p:
    nest_ex_aux (n + more) more' (nest_ex_aux n more p) = nest_ex_aux n (more + more') p.
  Proof.
    move: n more more'.
    induction p; intros n' more more'; simpl; auto.
    - f_equal.
      repeat case_match; auto; try lia.
    - by rewrite IHp1 IHp2.
    - by rewrite IHp1 IHp2.
    - replace (S (n' + more)) with ((S n') + more) by lia.
        by rewrite IHp.
    - by rewrite IHp.
  Qed.

  Lemma nest_mu_aux_comm n more more' p:
    nest_mu_aux (n + more) more' (nest_mu_aux n more p) = nest_mu_aux n (more + more') p.
  Proof.
    move: n more more'.
    induction p; intros n' more more'; simpl; auto.
    - f_equal.
      repeat case_match; auto; try lia.
    - by rewrite IHp1 IHp2.
    - by rewrite IHp1 IHp2.
    - by rewrite IHp.
    - replace (S (n' + more)) with ((S n') + more) by lia.
        by rewrite IHp.
  Qed.

  Lemma nest_ex_aux_wfcex level more ϕ:
    well_formed_closed_ex_aux ϕ level ->
    nest_ex_aux level more ϕ = ϕ.
  Proof.
    move: level.
    induction ϕ; simpl; intros level H; auto.
    - case_match;[reflexivity|congruence].
    - destruct_and!. by rewrite -> IHϕ1, -> IHϕ2.
    - destruct_and!. by rewrite -> IHϕ1, -> IHϕ2.
    - by rewrite IHϕ.
    - by rewrite IHϕ.
  Qed.

  Lemma nest_mu_aux_wfcmu level more ϕ:
    well_formed_closed_mu_aux ϕ level ->
    nest_mu_aux level more ϕ = ϕ.
  Proof.
    move: level.
    induction ϕ; simpl; intros level H; auto.
    - case_match;[reflexivity|congruence].
    - destruct_and!. by rewrite -> IHϕ1, -> IHϕ2.
    - destruct_and!. by rewrite -> IHϕ1, -> IHϕ2.
    - by rewrite IHϕ.
    - by rewrite IHϕ.
  Qed.

 Lemma bsvar_subst_nest_ex_aux_comm level more ϕ dbi ψ:
    well_formed_closed_ex_aux ψ level ->
    bsvar_subst (nest_ex_aux level more ϕ) ψ dbi = nest_ex_aux level more (bsvar_subst ϕ ψ dbi).
  Proof.
    move: level dbi. unfold svar_open.
    induction ϕ; move=> level dbi H; simpl; auto.
    - case_match; try reflexivity. by rewrite nest_ex_aux_wfcex.
    - rewrite IHϕ1;[assumption|]. rewrite IHϕ2;[assumption|]. reflexivity.
    - rewrite IHϕ1;[assumption|]. rewrite IHϕ2;[assumption|]. reflexivity.
    - rewrite IHϕ.
      { eapply well_formed_closed_ex_aux_ind;[|eassumption]. lia. }
      reflexivity.
    - rewrite IHϕ;[assumption|]. reflexivity.
  Qed.

  Lemma svar_open_nest_ex_aux_comm level more ϕ dbi X:
    svar_open dbi X (nest_ex_aux level more ϕ) = nest_ex_aux level more (svar_open dbi X ϕ).
  Proof.
    apply bsvar_subst_nest_ex_aux_comm.
    reflexivity.
  Qed.

  Lemma bevar_subst_nest_mu_aux_comm level more ϕ dbi ψ:
    well_formed_closed_mu_aux ψ level ->
    bevar_subst (nest_mu_aux level more ϕ) ψ dbi = nest_mu_aux level more (bevar_subst ϕ ψ dbi).
  Proof.
    move: level dbi. unfold svar_open.
    induction ϕ; move=> level dbi H; simpl; auto.
    - case_match; try reflexivity. by rewrite nest_mu_aux_wfcmu.
    - rewrite IHϕ1;[assumption|]. rewrite IHϕ2;[assumption|]. reflexivity.
    - rewrite IHϕ1;[assumption|]. rewrite IHϕ2;[assumption|]. reflexivity.
    - rewrite IHϕ;[assumption|]. reflexivity.
    - rewrite IHϕ.
      { eapply well_formed_closed_mu_aux_ind;[|eassumption]. lia. }
      reflexivity.
  Qed.

  Lemma evar_open_nest_mu_aux_comm level more ϕ dbi X:
    evar_open dbi X (nest_mu_aux level more ϕ) = nest_mu_aux level more (evar_open dbi X ϕ).
  Proof.
    move: level dbi. unfold evar_open.
    induction ϕ; move=> level dbi; simpl; auto; try congruence.
    - case_match; reflexivity.
  Qed.

  Lemma free_svars_nest_ex_aux dbi more ϕ:
    free_svars (nest_ex_aux dbi more ϕ) = free_svars ϕ.
  Proof.
    move: dbi. induction ϕ; move=> dbi; simpl; try reflexivity.
    - rewrite IHϕ1. rewrite IHϕ2. reflexivity.
    - rewrite IHϕ1. rewrite IHϕ2. reflexivity.
    - rewrite IHϕ. reflexivity.
    - rewrite IHϕ. reflexivity.
  Qed.

  Lemma free_evars_nest_mu_aux dbi more ϕ:
    free_evars (nest_mu_aux dbi more ϕ) = free_evars ϕ.
  Proof.
    move: dbi. induction ϕ; move=> dbi; simpl; try reflexivity.
    - rewrite IHϕ1. rewrite IHϕ2. reflexivity.
    - rewrite IHϕ1. rewrite IHϕ2. reflexivity.
    - rewrite IHϕ. reflexivity.
    - rewrite IHϕ. reflexivity.
  Qed.

  Lemma free_evars_nest_ex_aux dbi more ϕ:
    free_evars (nest_ex_aux dbi more ϕ) = free_evars ϕ.
  Proof.
    move: dbi. induction ϕ; move=> dbi; simpl; try reflexivity.
    - rewrite IHϕ1. rewrite IHϕ2. reflexivity.
    - rewrite IHϕ1. rewrite IHϕ2. reflexivity.
    - rewrite IHϕ. reflexivity.
    - rewrite IHϕ. reflexivity.
  Qed.

  Corollary free_evars_nest_ex ϕ:
    free_evars (nest_ex ϕ) = free_evars ϕ.
  Proof.
    apply free_evars_nest_ex_aux.
  Qed.

  Lemma free_svars_nest_mu_aux dbi more ϕ:
    free_svars (nest_mu_aux dbi more ϕ) = free_svars ϕ.
  Proof.
    move: dbi. induction ϕ; move=> dbi; simpl; try reflexivity.
    - rewrite IHϕ1. rewrite IHϕ2. reflexivity.
    - rewrite IHϕ1. rewrite IHϕ2. reflexivity.
    - rewrite IHϕ. reflexivity.
    - rewrite IHϕ. reflexivity.
  Qed.

  Corollary free_svars_nest_mu ϕ:
    free_svars (nest_mu ϕ) = free_svars ϕ.
  Proof.
    apply free_svars_nest_mu_aux.
  Qed.

  Corollary fresh_svar_nest_ex_aux dbi more ϕ:
    fresh_svar (nest_ex_aux dbi more ϕ) = fresh_svar ϕ.
  Proof.
    unfold fresh_svar.
      by rewrite free_svars_nest_ex_aux.
  Qed.

  Corollary fresh_evar_nest_mu_aux dbi more ϕ:
    fresh_evar (nest_mu_aux dbi more ϕ) = fresh_evar ϕ.
  Proof.
    unfold fresh_evar.
      by rewrite free_evars_nest_mu_aux.
  Qed.

  Corollary fresh_evar_nest_ex_aux dbi more ϕ:
    fresh_evar (nest_ex_aux dbi more ϕ) = fresh_evar ϕ.
  Proof.
    unfold fresh_evar.
      by rewrite free_evars_nest_ex_aux.
  Qed.

  Corollary fresh_svar_nest_mu_aux dbi more ϕ:
    fresh_svar (nest_mu_aux dbi more ϕ) = fresh_svar ϕ.
  Proof.
    unfold fresh_svar.
      by rewrite free_svars_nest_mu_aux.
  Qed.

  Corollary svar_open_nest_ex_comm ϕ dbi X:
    svar_open dbi X (nest_ex ϕ) = nest_ex (svar_open dbi X ϕ).
  Proof.
    exact (svar_open_nest_ex_aux_comm 0 1 ϕ dbi X).
  Qed.

  Corollary evar_open_nest_mu_comm ϕ dbi X:
    evar_open dbi X (nest_mu ϕ) = nest_mu (evar_open dbi X ϕ).
  Proof.
    exact (evar_open_nest_mu_aux_comm 0 1 ϕ dbi X).
  Qed.

  Lemma nest_mu_aux_0 level p:
    nest_mu_aux level 0 p = p.
  Proof.
    move: level.
    induction p; intros level; simpl; auto.
    - case_match; auto.
    - by rewrite IHp1 IHp2.
    - by rewrite IHp1 IHp2.
    - by rewrite IHp.
    - by rewrite IHp.
  Defined.

  Lemma nest_ex_aux_0 level p:
    nest_ex_aux level 0 p = p.
  Proof.
    move: level.
    induction p; intros level; simpl; auto.
    - case_match; auto.
    - by rewrite IHp1 IHp2.
    - by rewrite IHp1 IHp2.
    - by rewrite IHp.
    - by rewrite IHp.
  Defined.

  Lemma wfc_mu_nest_mu psi level level' more:
    well_formed_closed_mu_aux psi level ->
    well_formed_closed_mu_aux (nest_mu_aux level' more psi) (level+more).
  Proof.
    intros H.
    move: level level' H.
    induction psi; intros level level' H; simpl in *; auto.
    - repeat case_match; auto; lia.
    - destruct_and!.
      specialize (IHpsi1 level level' ltac:(assumption)).
      specialize (IHpsi2 level level' ltac:(assumption)).
      split_and!; auto.
    - destruct_and!.
      specialize (IHpsi1 level level' ltac:(assumption)).
      specialize (IHpsi2 level level' ltac:(assumption)).
      split_and!; auto.
    - specialize (IHpsi (S level) (S level') ltac:(assumption)).
      simpl in IHpsi. auto.
  Qed.

  Lemma Private_positive_negative_occurrence_db_nest_mu_aux dbi level more ϕ:
    (no_negative_occurrence_db_b dbi (nest_mu_aux level more ϕ)
     = if decide (dbi < level) is left _ then no_negative_occurrence_db_b dbi ϕ
       else if decide (dbi < level + more) is left _ then true
            else no_negative_occurrence_db_b (dbi-more) ϕ
    ) /\ (
      no_positive_occurrence_db_b dbi (nest_mu_aux level more ϕ)
     = if decide (dbi < level) is left _ then no_positive_occurrence_db_b dbi ϕ
       else if decide (dbi < level + more) is left _ then true
            else no_positive_occurrence_db_b (dbi-more) ϕ
    ).
  Proof.
    move: dbi level more.
    induction ϕ; intros dbi level more; simpl;
      destruct (compare_nat dbi level); auto;cbn;
        repeat case_match; simpl; try lia; auto;
          try rewrite (proj1 (IHϕ1 _ _ _));
          try rewrite (proj2 (IHϕ1 _ _ _));
          try rewrite (proj1 (IHϕ2 _ _ _));
          try rewrite (proj2 (IHϕ2 _ _ _));
          try rewrite (proj1 (IHϕ _ _ _));
          try rewrite (proj2 (IHϕ _ _ _));
          simpl;
          repeat case_match; cbn; try lia; auto.
    all: fold no_negative_occurrence_db_b; fold no_positive_occurrence_db_b.
    all:           try rewrite (proj1 (IHϕ1 _ _ _));
          try rewrite (proj2 (IHϕ1 _ _ _));
          try rewrite (proj1 (IHϕ2 _ _ _));
          try rewrite (proj2 (IHϕ2 _ _ _));repeat case_match; cbn; try lia; auto.
    replace (S dbi - more) with (S (dbi - more)) by lia. split; reflexivity.
    replace (S dbi - more) with (S (dbi - more)) by lia. split; reflexivity.
  Qed.

  Lemma no_negative_occurrence_db_nest_mu_aux dbi level more ϕ:
    no_negative_occurrence_db_b dbi (nest_mu_aux level more ϕ)
     = if decide (dbi < level) is left _ then no_negative_occurrence_db_b dbi ϕ
       else if decide (dbi < level + more) is left _ then true
            else no_negative_occurrence_db_b (dbi-more) ϕ.
  Proof.
    apply Private_positive_negative_occurrence_db_nest_mu_aux.
  Qed.

  Lemma no_positive_occurrence_db_nest_mu_aux dbi level more ϕ:
    no_positive_occurrence_db_b dbi (nest_mu_aux level more ϕ)
     = if decide (dbi < level) is left _ then no_positive_occurrence_db_b dbi ϕ
       else if decide (dbi < level + more) is left _ then true
            else no_positive_occurrence_db_b (dbi-more) ϕ.
  Proof.
    apply Private_positive_negative_occurrence_db_nest_mu_aux.
  Qed.

  Lemma well_formed_positive_nest_mu_aux level more ϕ:
    well_formed_positive (nest_mu_aux level more ϕ) = well_formed_positive ϕ.
  Proof.
    move: level.
    induction ϕ; intros level; simpl; auto.
    - rewrite IHϕ1. rewrite IHϕ2. auto.
    - rewrite IHϕ1. rewrite IHϕ2. auto.
    - rewrite IHϕ.
      rewrite no_negative_occurrence_db_nest_mu_aux. simpl.
      reflexivity.
  Qed.

  Definition simpl_free_evars :=
    (
      (@left_id_L EVarSet  ∅ (@union _ _)),
      (@right_id_L EVarSet ∅ (@union _ _)),
      @free_evars_nest_ex_aux,
      @nest_ex_same,
      @free_evars_nest_ex
    ).
  Definition simpl_free_svars :=
    (
      (@left_id_L SVarSet  ∅ (@union _ _)),
      (@right_id_L SVarSet ∅ (@union _ _)),
      @free_svars_nest_mu_aux,
      @nest_mu_same,
      @free_svars_nest_mu
    ).

End index_manipulation.

Ltac simpl_bevar_subst := repeat (rewrite simpl_bevar_subst';[reflexivity|]).
Ltac simpl_bsvar_subst := repeat (rewrite simpl_bsvar_subst';[reflexivity|]).

Tactic Notation "solve_free_evars_inclusion" int_or_var(depth) :=
  simpl;
  (do ? [rewrite simpl_free_evars/=]) ;
  auto;
  clear;
  set_solver.

Tactic Notation "solve_free_svars_inclusion" int_or_var(depth) :=
  simpl;
  (do ? [rewrite simpl_free_svars/=]) ;
  auto;
  clear;
  set_solver.