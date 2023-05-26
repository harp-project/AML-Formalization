From Coq Require Import ssreflect ssrfun ssrbool.

From Coq.Logic Require Import FunctionalExtensionality PropExtensionality Classical_Pred_Type Classical_Prop.
From Coq.micromega Require Import Lia.
From Coq.Program Require Import Wf.

From stdpp Require Import base fin_sets.
From stdpp Require Import pmap gmap mapset fin_sets sets propset.

From MatchingLogic.Utils Require Import stdpp_ext extralibrary.
From MatchingLogic Require Import Pattern Substitution Freshness.

Import MatchingLogic.Substitution.Notations.

Section index_manipulation.
  Context {Σ : Signature}.
  Open Scope ml_scope.

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

  Lemma bevar_occur_nest_ex dbi more φ:
    forall x, x >= dbi -> x < dbi + more -> bevar_occur (nest_ex_aux dbi more φ) x = false.
  Proof.
    move: φ dbi.
    induction φ; move=> dbi x' Hlt Hgt; simpl; auto.
    - repeat case_match; simpl; auto; lia.
    - rewrite -> IHφ1, -> IHφ2; auto.
    - rewrite -> IHφ1, -> IHφ2; auto.
    - rewrite -> IHφ; auto. all: lia.
  Qed.

  Lemma bsvar_occur_nest_mu dbi more φ:
    forall x, x >= dbi -> x < dbi + more -> bsvar_occur (nest_mu_aux dbi more φ) x = false.
  Proof.
    move: φ dbi.
    induction φ; move=> dbi x' Hlt Hgt; simpl; auto.
    - repeat case_match; simpl; auto; lia.
    - rewrite -> IHφ1, -> IHφ2; auto.
    - rewrite -> IHφ1, -> IHφ2; auto.
    - rewrite -> IHφ; auto. all: lia.
  Qed.

  Corollary not_bevar_occur_level_nest_ex_aux level more ϕ :
    more > 0 ->
    bevar_occur (nest_ex_aux level more ϕ) level = false.
  Proof.
    intro Hmore. apply bevar_occur_nest_ex; lia.
  Qed.

  Corollary not_bsvar_occur_level_nest_mu_aux level more ϕ :
    more > 0 ->
    bsvar_occur (nest_mu_aux level more ϕ) level = false.
  Proof.
    intro Hmore. apply bsvar_occur_nest_mu; lia.
  Qed.

  Corollary not_bevar_occur_0_nest_ex ϕ :
    bevar_occur (nest_ex ϕ) 0 = false.
  Proof.
    apply not_bevar_occur_level_nest_ex_aux. lia.
  Qed.

  Corollary not_bsvar_occur_0_nest_mu ϕ :
    bsvar_occur (nest_mu ϕ) 0 = false.
  Proof.
    apply not_bsvar_occur_level_nest_mu_aux. lia.
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

  Lemma nest_ex_gt : forall φ dbi dbi2 ψ more, dbi2 >= dbi -> well_formed_closed ψ ->
     (nest_ex_aux dbi more φ)^[evar: (dbi2 + more) ↦ ψ] = nest_ex_aux dbi more (φ^[evar: dbi2 ↦ ψ]).
  Proof.
    induction φ; intros dbi dbi2 ψ more Hgt Hwf; cbn; auto.
    * do 3 case_match; auto; simpl; try case_match; subst; try lia; auto.

      rewrite nest_ex_aux_wfcex; auto. eapply well_formed_closed_ex_aux_ind.
      2: apply andb_true_iff in Hwf; apply Hwf. lia.
      now replace (pred n + more) with (pred (n + more)) by lia.
    * rewrite -> IHφ1, -> IHφ2; auto.
    * rewrite -> IHφ1, -> IHφ2; auto.
    * specialize (IHφ (S dbi) (S dbi2) ψ more ltac:(lia) Hwf). simpl in IHφ.
      rewrite -> IHφ; auto.
    * rewrite -> IHφ; auto.
  Qed.

  Lemma nest_mu_gt : forall φ dbi dbi2 ψ more, dbi2 >= dbi -> well_formed_closed ψ ->
     (nest_mu_aux dbi more φ)^[svar: (dbi2 + more) ↦ ψ] = nest_mu_aux dbi more (φ^[svar: dbi2 ↦ ψ]).
  Proof.
    induction φ; intros dbi dbi2 ψ more Hgt Hwf; cbn; auto.
    * do 3 case_match; auto; simpl; try case_match; subst; try lia; auto.
      rewrite nest_mu_aux_wfcmu; auto. eapply well_formed_closed_mu_aux_ind.
      2: apply andb_true_iff in Hwf; apply Hwf. lia.
      now replace (pred n + more) with (pred (n + more)) by lia.
    * rewrite -> IHφ1, -> IHφ2; auto.
    * rewrite -> IHφ1, -> IHφ2; auto.
    * rewrite -> IHφ; auto.
    * specialize (IHφ (S dbi) (S dbi2) ψ more ltac:(lia) Hwf). simpl in IHφ.
      rewrite -> IHφ; auto.
  Qed.


(** NESTING AND QUANTIFICATION **)

  Lemma nest_ex_gt_evar_quantify : forall φ dbi dbi2 x more, dbi >= dbi2 ->
     (nest_ex_aux dbi2 more φ)^{{evar: x ↦ dbi + more}} = 
     nest_ex_aux dbi2 more (φ^{{evar: x ↦ dbi}}).
  Proof.
    induction φ; intros dbi dbi2 x' more Hgt; cbn; auto.
    * case_match; auto; simpl; try case_match; subst; try lia; auto.
    * rewrite -> IHφ1, -> IHφ2; auto.
    * rewrite -> IHφ1, -> IHφ2; auto.
    * specialize (IHφ (S dbi) (S dbi2) x' more ltac:(lia)). simpl in IHφ.
      rewrite -> IHφ; auto.
    * rewrite -> IHφ; auto.
  Qed.

  Lemma nest_mu_gt_svar_quantify : forall φ dbi dbi2 x more, dbi >= dbi2 ->
     (nest_mu_aux dbi2 more φ)^{{svar: x ↦ dbi + more}} = 
     nest_mu_aux dbi2 more (φ^{{svar: x ↦ dbi}}).
  Proof.
    induction φ; intros dbi dbi2 x' more Hgt; cbn; auto.
    * case_match; auto; simpl; try case_match; subst; try lia; auto.
    * rewrite -> IHφ1, -> IHφ2; auto.
    * rewrite -> IHφ1, -> IHφ2; auto.
    * rewrite -> IHφ; auto.
    * specialize (IHφ (S dbi) (S dbi2) x' more ltac:(lia)). simpl in IHφ.
      rewrite -> IHφ; auto.
  Qed.

  Lemma nest_mu_evar_quantify : forall φ dbi dbi2 x more,
     (nest_mu_aux dbi2 more φ)^{{evar: x ↦ dbi}} = nest_mu_aux dbi2 more (φ^{{evar: x ↦ dbi}}).
  Proof.
    induction φ; intros dbi dbi2 x' more; cbn; auto.
    * case_match; auto; simpl; try case_match; subst; try lia; auto.
    * rewrite -> IHφ1, -> IHφ2; auto.
    * rewrite -> IHφ1, -> IHφ2; auto.
    * rewrite -> IHφ; auto.
    * rewrite -> IHφ; auto.
  Qed.

  Lemma nest_ex_svar_quantify : forall φ dbi dbi2 x more,
     (nest_ex_aux dbi2 more φ)^{{svar: x ↦ dbi}} = nest_ex_aux dbi2 more (φ^{{svar: x ↦ dbi}}).
  Proof.
    induction φ; intros dbi dbi2 x' more; cbn; auto.
    * case_match; auto; simpl; try case_match; subst; try lia; auto.
    * rewrite -> IHφ1, -> IHφ2; auto.
    * rewrite -> IHφ1, -> IHφ2; auto.
    * rewrite -> IHφ; auto.
    * rewrite -> IHφ; auto.
  Qed.

(** NESTING AND FREE VARIABLE SUBSTITUTION **)

  Lemma nest_ex_free_evar_subst : forall φ dbi x more ψ,
     well_formed_closed_ex_aux ψ dbi ->
     (nest_ex_aux dbi more φ)^[[evar: x ↦ ψ]] = 
     nest_ex_aux dbi more (φ^[[evar: x ↦ ψ]]).
  Proof.
    induction φ; intros dbi x' more ψ Hwf; cbn; auto.
    * case_match; auto; simpl; try case_match; subst; try lia; auto.
      now rewrite nest_ex_aux_wfcex.
    * rewrite -> IHφ1, -> IHφ2; auto.
    * rewrite -> IHφ1, -> IHφ2; auto.
    * rewrite -> IHφ; auto. eapply well_formed_closed_ex_aux_ind. 2: eassumption. lia.
    * rewrite -> IHφ; auto.
  Qed.

  Lemma nest_mu_free_evar_subst : forall φ dbi x more ψ,
     well_formed_closed_mu_aux ψ dbi ->
     (nest_mu_aux dbi more φ)^[[evar: x ↦ ψ]] = 
     nest_mu_aux dbi more (φ^[[evar: x ↦ ψ]]).
  Proof.
    induction φ; intros dbi x' more ψ Hwf; cbn; auto.
    * case_match; auto; simpl; try case_match; subst; try lia; auto.
      now rewrite nest_mu_aux_wfcmu.
    * rewrite -> IHφ1, -> IHφ2; auto.
    * rewrite -> IHφ1, -> IHφ2; auto.
    * rewrite -> IHφ; auto.
    * rewrite -> IHφ; auto. eapply well_formed_closed_mu_aux_ind. 2: eassumption. lia.
  Qed.

  Lemma nest_ex_free_svar_subst : forall φ dbi X more ψ,
     well_formed_closed_ex_aux ψ dbi ->
     (nest_ex_aux dbi more φ)^[[svar: X ↦ ψ]] = 
     nest_ex_aux dbi more (φ^[[svar: X ↦ ψ]]).
  Proof.
    induction φ; intros dbi x' more ψ Hwf; cbn; auto.
    * case_match; auto; simpl; try case_match; subst; try lia; auto.
      now rewrite nest_ex_aux_wfcex.
    * rewrite -> IHφ1, -> IHφ2; auto.
    * rewrite -> IHφ1, -> IHφ2; auto.
    * rewrite -> IHφ; auto. eapply well_formed_closed_ex_aux_ind. 2: eassumption. lia.
    * rewrite -> IHφ; auto.
  Qed.

  Lemma nest_mu_free_svar_subst : forall φ dbi X more ψ,
     well_formed_closed_mu_aux ψ dbi ->
     (nest_mu_aux dbi more φ)^[[svar: X ↦ ψ]] = 
     nest_mu_aux dbi more (φ^[[svar: X ↦ ψ]]).
  Proof.
    induction φ; intros dbi x' more ψ Hwf; cbn; auto.
    * case_match; auto; simpl; try case_match; subst; try lia; auto.
      now rewrite nest_mu_aux_wfcmu.
    * rewrite -> IHφ1, -> IHφ2; auto.
    * rewrite -> IHφ1, -> IHφ2; auto.
    * rewrite -> IHφ; auto.
    * rewrite -> IHφ; auto. eapply well_formed_closed_mu_aux_ind. 2: eassumption. lia.
  Qed.

(** ******* **)

  Lemma nest_ex_same_general : forall φ dbi ψ more,
     forall x,  x >= dbi -> x < dbi + more -> 
     (nest_ex_aux dbi more φ)^[evar: x ↦ ψ] = nest_ex_aux dbi (pred more) φ.
  Proof.
    induction φ; intros dbi ψ more x' Hx1 Hx2; cbn; auto.
    * do 2 case_match; auto; try lia.
      now replace (n + pred more) with (pred (n + more)) by lia.
    * rewrite -> IHφ1, -> IHφ2; auto.
    * rewrite -> IHφ1, -> IHφ2; auto.
    * rewrite -> IHφ; auto. all: lia.
    * rewrite -> IHφ; auto. all: lia.
  Qed.

  Lemma nest_mu_same_general : forall φ dbi ψ more,
     forall x,  x >= dbi -> x < dbi + more -> 
     (nest_mu_aux dbi more φ)^[svar: x ↦ ψ] = nest_mu_aux dbi (pred more) φ.
  Proof.
    induction φ; intros dbi ψ more x' Hx1 Hx2; cbn; auto.
    * do 2 case_match; auto; try lia.
      now replace (n + pred more) with (pred (n + more)) by lia.
    * rewrite -> IHφ1, -> IHφ2; auto.
    * rewrite -> IHφ1, -> IHφ2; auto.
    * rewrite -> IHφ; auto. all: lia.
    * rewrite -> IHφ; auto. all: lia.
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

  Corollary nest_ex_same : forall φ dbi ψ,
     (nest_ex_aux dbi 1 φ)^[evar: dbi ↦ ψ] = φ.
  Proof.
    intros φ dbi ψ. rewrite nest_ex_same_general; try lia.
    simpl. now rewrite nest_ex_aux_0.
  Qed.

  Corollary nest_mu_same : forall φ dbi ψ,
     (nest_mu_aux dbi 1 φ)^[svar: dbi ↦ ψ] = φ.
  Proof.
    intros φ dbi ψ. rewrite nest_mu_same_general; try lia.
    simpl. now rewrite nest_mu_aux_0.
  Qed.

  Lemma fuse_nest_ex n more more' p:
    forall x, x <= more -> nest_ex_aux (n + x) more' (nest_ex_aux n more p) = nest_ex_aux n (more + more') p.
  Proof.
    move: n more more'.
    induction p; intros n' more more' x' Hx'; simpl; auto.
    - f_equal.
      repeat case_match; auto; try lia.
    - rewrite -> IHp1, -> IHp2; auto.
    - rewrite -> IHp1, -> IHp2; auto.
    - replace (S (n' + x')) with ((S n') + x') by lia.
        by rewrite IHp.
    - by rewrite IHp.
  Qed.

  Lemma fuse_nest_mu n more more' p:
    forall x, x <= more -> nest_mu_aux (n + x) more' (nest_mu_aux n more p) = nest_mu_aux n (more + more') p.
  Proof.
    move: n more more'.
    induction p; intros n' more more' x' Hx'; simpl; auto.
    - f_equal.
      repeat case_match; auto; try lia.
    - rewrite -> IHp1, -> IHp2; auto.
    - rewrite -> IHp1, -> IHp2; auto.
    - by rewrite IHp.
    - replace (S (n' + x')) with ((S n') + x') by lia.
        by rewrite IHp.
  Qed.

  Corollary fuse_nest_ex_same n more more' p:
    nest_ex_aux n more' (nest_ex_aux n more p) = nest_ex_aux n (more + more') p.
  Proof.
    pose proof (@fuse_nest_ex n more more' p 0 ltac:(lia)). now rewrite Nat.add_0_r in H.
  Qed.

  Corollary fuse_nest_mu_same n more more' p:
    nest_mu_aux n more' (nest_mu_aux n more p) = nest_mu_aux n (more + more') p.
  Proof.
    pose proof (@fuse_nest_mu n more more' p 0 ltac:(lia)). now rewrite Nat.add_0_r in H.
  Qed.

 Lemma bsvar_subst_nest_ex_aux_comm level more ϕ dbi ψ:
    well_formed_closed_ex_aux ψ level ->
    (nest_ex_aux level more ϕ)^[svar: dbi ↦ ψ] = nest_ex_aux level more (ϕ^[svar: dbi ↦ ψ]).
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
    (nest_ex_aux level more ϕ)^{svar: dbi ↦ X} = 
    nest_ex_aux level more (ϕ^{svar: dbi ↦ X}).
  Proof.
    apply bsvar_subst_nest_ex_aux_comm.
    reflexivity.
  Qed.

  Lemma bevar_subst_nest_mu_aux_comm level more ϕ dbi ψ:
    well_formed_closed_mu_aux ψ level ->
    (nest_mu_aux level more ϕ)^[evar: dbi ↦ ψ] = nest_mu_aux level more (ϕ^[evar: dbi ↦ ψ]).
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
    (nest_mu_aux level more ϕ)^{evar: dbi ↦ X} =
    nest_mu_aux level more (ϕ^{evar: dbi ↦ X}).
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
    (nest_ex ϕ)^{svar: dbi ↦ X} = nest_ex (ϕ^{svar: dbi ↦ X}).
  Proof.
    exact (svar_open_nest_ex_aux_comm 0 1 ϕ dbi X).
  Qed.

  Corollary evar_open_nest_mu_comm ϕ dbi X:
    (nest_mu ϕ)^{evar: dbi ↦ X} = nest_mu (ϕ^{evar: dbi ↦ X}).
  Proof.
    exact (evar_open_nest_mu_aux_comm 0 1 ϕ dbi X).
  Qed.

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

  Lemma no_negative_occurrence_db_nest_ex_aux level more dbi ϕ:
    no_negative_occurrence_db_b dbi (nest_ex_aux level more ϕ)
    = no_negative_occurrence_db_b dbi ϕ
  with no_positive_occurrence_db_nest_ex_aux level more dbi ϕ:
    no_positive_occurrence_db_b dbi (nest_ex_aux level more ϕ)
    = no_positive_occurrence_db_b dbi ϕ
  .
  Proof.
    {
      move: level more dbi.
      induction ϕ; intros level more dbi; cbn; try reflexivity.
      {
        rewrite IHϕ1. rewrite IHϕ2. reflexivity.
      }
      {
        fold no_negative_occurrence_db_b no_positive_occurrence_db_b.
        rewrite IHϕ2.
        rewrite no_positive_occurrence_db_nest_ex_aux.
        reflexivity.
      }
      {
        rewrite IHϕ. reflexivity.
      }
      {
        rewrite IHϕ. reflexivity.
      }
    }
    {
      move: level more dbi.
      induction ϕ; intros level more dbi; cbn; try reflexivity.
      {
        rewrite IHϕ1. rewrite IHϕ2. reflexivity.
      }
      {
        fold no_negative_occurrence_db_b no_positive_occurrence_db_b.
        rewrite IHϕ2.
        rewrite no_negative_occurrence_db_nest_ex_aux.
        reflexivity.
      }
      {
        rewrite IHϕ. reflexivity.
      }
      {
        rewrite IHϕ. reflexivity.
      }
    }
  Qed.

  Lemma well_formed_positive_nest_ex_aux level more ϕ:
    well_formed_positive (nest_ex_aux level more ϕ) = well_formed_positive ϕ.
  Proof.
    move: level.
    induction ϕ; intros level; simpl; try reflexivity.
    - rewrite IHϕ1. rewrite IHϕ2. reflexivity.
    - rewrite IHϕ1. rewrite IHϕ2. reflexivity.
    - rewrite IHϕ. reflexivity.
    - rewrite IHϕ.
      rewrite no_negative_occurrence_db_nest_ex_aux. simpl.
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

Tactic Notation "solve_free_evars_inclusion" int_or_var(depth) :=
  simpl;
  (do ? [rewrite simpl_free_evars/=]);
  auto;
  clear;
  set_solver.


Ltac unify_free_evar_conditions :=
  match goal with
  | |- context C [free_evars (foldr _ _ _)] =>
      rewrite free_evars_of_list_foldr
  | |- context C [free_evars_of_list _] => unfold free_evars_of_list
  | [H : context C [free_evars (foldr _ _ _)] |- _] =>
      rewrite free_evars_of_list_foldr in H
  | [H: context C [free_evars_of_list _] |- _] => unfold free_evars_of_list in H
  end.
Ltac simplify_map_app_union :=
  match goal with
  | |- context C [map _ (_ ++ _)] => rewrite map_app
  | [H : context C [map _ (_ ++ _)] |- _] => rewrite map_app in H
  | |- context C [union_list (_ ++ _)] => rewrite union_list_app
  | [H : context C [union_list (_ ++ _)] |- _] => rewrite union_list_app in H
  end.
(* same as the previous "solve_free_evars_inclusion", but without clearing,
   and support for list of free evars *)
Tactic Notation "solve_free_evars" int_or_var(depth) :=
  unfold evar_is_fresh_in in *;  
  repeat unify_free_evar_conditions;
  repeat simplify_map_app_union;
  simpl in *;
  repeat rewrite free_evars_evar_quantify;
  (do ? [rewrite simpl_free_evars/=]);
  auto;
  set_solver. 

Tactic Notation "solve_free_svars_inclusion" int_or_var(depth) :=
  simpl;
  (do ? [rewrite simpl_free_svars/=]) ;
  auto;
  clear;
  set_solver.
