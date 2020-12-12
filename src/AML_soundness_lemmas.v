Require Import Arith.
Require Import ZArith.
Require Import List.
Require Import Coq.micromega.Lia.
Require Export String.
Require Export Coq.Program.Wf.
From Coq Require Import Bool.Bool.
From Coq Require Import Logic.FunctionalExtensionality.

From stdpp Require Import fin_sets.
Require Import extralibrary.
Require Import MatchingLogic.Syntax.
Require Export locally_nameless.
Require Import Lattice.
Require Import stdpp_ext.

Require Export Ensembles_Ext.


Import MLNotations.
Open Scope ml_scope.

Section soundness_lemmas.

  Context {sig : Signature}.
  Existing Instance variables. 


Lemma update_val_fresh12 {m : Model}:
  forall sz  phi n,
  le (size phi) sz ->
  forall fresh1 fresh2,
   fresh1 ∉ (free_evars phi) -> fresh2 ∉ (free_evars phi) ->
  well_formed_closed (evar_open n fresh1 phi) -> well_formed_closed (evar_open n fresh2 phi)
  ->
  forall evar_val svar_val c,
  pattern_interpretation (update_evar_val fresh1 c evar_val) svar_val (evar_open n fresh1 phi) =
  @pattern_interpretation sig m (update_evar_val fresh2 c evar_val) svar_val (evar_open n fresh2 phi).
Proof. 

  (* Induction on size *)
  induction sz; destruct phi; intros n0 Hsz fresh1 fresh2 HLs1 HLs2 Hwfb1 Hwfb2 eval sval c; auto; try inversion Hsz; subst.
  - repeat rewrite evar_open_fresh. 
    2, 3: unfold well_formed_closed; simpl; trivial.
    repeat rewrite pattern_interpretation_free_evar_simpl.
    unfold update_evar_val.
    destruct (evar_eq fresh1 x) eqn:P; destruct (evar_eq fresh2 x) eqn:P1.
    + rewrite e in HLs1. simpl in HLs1.
      eapply not_elem_of_singleton_1 in HLs1. contradiction.
    + rewrite e in HLs1. simpl in HLs1.
      eapply not_elem_of_singleton_1 in HLs1. contradiction.
    + rewrite e in HLs2. simpl in HLs2. 
      eapply not_elem_of_singleton_1 in HLs2. contradiction.
    + auto.
  - unfold well_formed_closed in Hwfb1. simpl in Hwfb1.
    assert (n = n0).
    destruct (n =? n0) eqn:P.
      + apply beq_nat_true in P. assumption.
      + inversion Hwfb1.
      + simpl. apply Nat.eqb_eq in H. rewrite H. repeat rewrite pattern_interpretation_free_evar_simpl. unfold update_evar_val.
        destruct (evar_eq fresh1 fresh1) eqn:P. destruct (evar_eq fresh2 fresh2) eqn:P1.
        auto. contradiction. contradiction.
  - erewrite IHsz. reflexivity. assumption. assumption. assumption. assumption. assumption.
  - erewrite IHsz. reflexivity. assumption. assumption. assumption. assumption. assumption.
  - simpl. simpl in Hsz. repeat rewrite pattern_interpretation_app_simpl.
    simpl in HLs1, HLs2.
    rewrite elem_of_union in HLs1, HLs2. apply not_or_and in HLs1. apply not_or_and in HLs2.
    destruct HLs1, HLs2. 
    apply wfc_wfc_ind in Hwfb1. inversion Hwfb1.
    apply wfc_wfc_ind in Hwfb2. inversion Hwfb2.
    erewrite IHsz. erewrite (IHsz phi2). reflexivity. lia. assumption. assumption. 
    + apply (wfc_ind_wfc). assumption.
    + apply (wfc_ind_wfc). assumption.
    + lia.
    + assumption.
    + assumption.
    + apply (wfc_ind_wfc). assumption.
    + apply (wfc_ind_wfc). assumption.
      (*
    + erewrite <- evar_open_size. erewrite <- evar_open_size. lia. exact sig. exact sig.
    + rewrite <- (evar_open_size sig n0 fresh1 (phi1 $ phi2)). rewrite <- (evar_open_size sig 0 fresh2 (phi1 $ phi2)). lia.*)
  - simpl. simpl in Hsz. repeat rewrite pattern_interpretation_app_simpl.
    simpl in HLs1, HLs2.
    rewrite elem_of_union in HLs1, HLs2. apply not_or_and in HLs1. apply not_or_and in HLs2.
    destruct HLs1, HLs2. 
    apply wfc_wfc_ind in Hwfb1. inversion Hwfb1.
    apply wfc_wfc_ind in Hwfb2. inversion Hwfb2.
    erewrite IHsz. erewrite (IHsz phi2). reflexivity. lia. assumption. assumption. 
    + apply (wfc_ind_wfc). assumption.
    + apply (wfc_ind_wfc). assumption.
    + lia.
    + assumption.
    + assumption.
    + apply (wfc_ind_wfc). assumption.
    + apply (wfc_ind_wfc). assumption.
      (*
    + erewrite <- evar_open_size. erewrite <- evar_open_size. lia. exact sig. exact sig.
    + erewrite <- evar_open_size. erewrite <- evar_open_size. lia. exact sig. exact sig.*)
  - simpl. simpl in Hsz. repeat rewrite pattern_interpretation_imp_simpl.
    simpl in HLs1, HLs2. rewrite elem_of_union in HLs1, HLs2. apply not_or_and in HLs1. apply not_or_and in HLs2.
    destruct HLs1, HLs2. 
    apply wfc_wfc_ind in Hwfb1. inversion Hwfb1.
    apply wfc_wfc_ind in Hwfb2. inversion Hwfb2.
    erewrite IHsz. erewrite (IHsz phi2). reflexivity. lia. assumption. assumption. 
    + apply (wfc_ind_wfc). assumption.
    + apply (wfc_ind_wfc). assumption.
    + lia.
    + assumption.
    + assumption.
    + apply (wfc_ind_wfc). assumption.
    + apply (wfc_ind_wfc). assumption.
      (*
    + erewrite <- evar_open_size. erewrite <- evar_open_size. simpl. lia. exact sig. exact sig.
    + rewrite <- (evar_open_size sig n0 fresh1 (phi1 ---> phi2)). rewrite <- (evar_open_size sig 0 fresh2 (phi1 $ phi2)). simpl. lia.*)
  - simpl. simpl in Hsz. repeat rewrite pattern_interpretation_imp_simpl.
    simpl in HLs1, HLs2. rewrite elem_of_union in HLs1, HLs2. apply not_or_and in HLs1. apply not_or_and in HLs2.
    destruct HLs1, HLs2. 
    apply wfc_wfc_ind in Hwfb1. inversion Hwfb1.
    apply wfc_wfc_ind in Hwfb2. inversion Hwfb2.
    erewrite IHsz. erewrite (IHsz phi2). reflexivity. lia. assumption. assumption. 
    + apply (wfc_ind_wfc). assumption.
    + apply (wfc_ind_wfc). assumption.
    + lia.
    + assumption.
    + assumption.
    + apply (wfc_ind_wfc). assumption.
    + apply (wfc_ind_wfc). assumption.
      (*
    + rewrite <- (evar_open_size sig n0 fresh2 (phi1 ---> phi2)). rewrite <- (evar_open_size sig 0 fresh2 (phi1 $ phi2)). simpl. lia.
    + rewrite <- (evar_open_size sig n0 fresh1 (phi1 ---> phi2)). rewrite <- (evar_open_size sig 0 fresh2 (phi1 $ phi2)). simpl. lia.*)
  - simpl. repeat rewrite pattern_interpretation_ex_simpl. simpl.
    remember (fresh_evar (evar_open (n0 + 1) fresh2 phi)) as fresh22.
    remember (fresh_evar (evar_open (n0 + 1) fresh1 phi)) as fresh11.
    apply Extensionality_Ensembles. apply FA_Union_same. intros. unfold Same_set, Included, In. split.
    + intros. simpl in Hwfb1. apply wfc_ex_to_wfc_body in Hwfb1.
      destruct (evar_eq fresh1 fresh2). 
        * subst. auto.
        * epose (IHsz (evar_open (n0 + 1) fresh1 phi) 0 _ fresh11 fresh22 _ _ _ _   
          (update_evar_val fresh1 c eval) sval c0).
          rewrite e in H. clear e.
          rewrite update_evar_val_comm.
          rewrite evar_open_comm. 2: lia.
          
          epose (IHsz (evar_open 0 fresh22 phi) (n0+1) _ fresh1 fresh2 _ _ _ _ 
          (update_evar_val fresh22 c0 eval) sval c).
          rewrite <- e. rewrite evar_open_comm. 2: lia.
          rewrite update_evar_val_comm. assumption.
          destruct (evar_eq fresh1 fresh22).
          -- admit. (*TODO: Counterexample. *)
          -- assumption.
          -- admit. (* From Heqfresh22 *)

Admitted. (* update_evar_val_shadow *)

Lemma update_valuation_fresh {m : Model}  :
  forall phi,
  well_formed_closed phi ->
  forall v,
  v ∉ (free_evars phi) ->
  forall evar_val svar_val c,
  pattern_interpretation (update_evar_val v c evar_val) svar_val phi =
  @pattern_interpretation sig m evar_val svar_val phi.
Proof.
  
  intros phi Hwfc. apply wfc_wfc_ind in Hwfc.
  induction Hwfc.
  - intros. simpl in H. apply not_elem_of_singleton_1 in H.
    repeat rewrite pattern_interpretation_free_evar_simpl. unfold update_evar_val.
    destruct (evar_eq v x) eqn:P.
      + contradiction.
      + auto.
  - auto.
  - auto.
  - intros. repeat rewrite pattern_interpretation_app_simpl. 
    simpl in H. rewrite elem_of_union in H. apply not_or_and in H. destruct H.
    rewrite IHHwfc1. rewrite IHHwfc2. reflexivity. assumption. assumption.
  - intros. repeat rewrite pattern_interpretation_bott_simpl. reflexivity.
  - intros. repeat rewrite pattern_interpretation_imp_simpl.
    simpl in H. rewrite elem_of_union in H. apply not_or_and in H. destruct H.
    rewrite IHHwfc1. rewrite IHHwfc2. reflexivity. assumption. assumption.
  - intros. repeat rewrite pattern_interpretation_ex_simpl. simpl. apply Extensionality_Ensembles.
    apply FA_Union_same. intros.
    unfold Same_set, Included, In. split.
    + intros. remember (fresh_evar phi) as fresh1.
      destruct (evar_eq fresh1 v).
        * rewrite <- e in H2. rewrite update_evar_val_shadow in H2. assumption.
        * simpl in H1. rewrite update_evar_val_comm in H2. rewrite H0 in H2.
          -- assumption.
          -- rewrite Heqfresh1. apply set_evar_fresh_is_fresh.
          -- apply (fresh_notin (size (evar_open 0 fresh1 phi))).
             ++ rewrite (evar_open_size sig 0 fresh1). lia.
             ++ assumption.
             ++ rewrite Heqfresh1. apply set_evar_fresh_is_fresh.
             ++ unfold not. intro. rewrite H3 in n. contradiction.
          -- assumption.
    + intros. remember (fresh_evar phi) as fresh1.
      destruct (evar_eq fresh1 v).
        * rewrite e. rewrite update_evar_val_shadow. rewrite e in H2. assumption.
        * simpl in H1. rewrite update_evar_val_comm. rewrite H0.
          -- assumption.
          -- rewrite Heqfresh1. apply set_evar_fresh_is_fresh.
          -- apply (fresh_notin (size (evar_open 0 fresh1 phi))).
             ++ rewrite (evar_open_size sig 0 fresh1). lia.
             ++ assumption.
             ++ rewrite Heqfresh1. apply set_evar_fresh_is_fresh.
             ++ unfold not. intro. rewrite H3 in n. contradiction.
          -- assumption.
  - intros. repeat rewrite pattern_interpretation_mu_simpl. simpl.
    remember (fresh_svar phi) as fresh1.
    assert ((fun S : Ensemble (Domain m) =>
      pattern_interpretation 
      (update_evar_val v c evar_val) (
      update_svar_val fresh1 S svar_val)
      (svar_open 0 fresh1 phi)) =
      (fun S : Ensemble (Domain m) =>
      pattern_interpretation evar_val (update_svar_val fresh1 S svar_val)
        (svar_open 0 fresh1 phi))).
    + apply functional_extensionality. intros. apply H0.
      * rewrite Heqfresh1. apply set_svar_fresh_is_fresh.
      * rewrite free_evars_svar_open. assumption.
    + rewrite H2. reflexivity.
Qed.


(* Definitions and lemmas inside this section are useful for proving `is_monotonic`,
   but they are probably not usefull for any other purpose. *)
Section respects_blacklist.
  (* Bp - Blacklist of Positive Occurrence - these variables can occur only negatively.
     Bn - Blacklist of Negative Occurrence - these variables can occur only positively *)
  Definition respects_blacklist (phi : Pattern) (Bp Bn : Ensemble svar) : Prop :=
    forall (var : svar),
      (Bp var -> negative_occurrence_named var phi) /\ (Bn var -> @positive_occurrence_named sig var phi).

  Lemma respects_blacklist_app : forall (phi1 phi2 : Pattern) (Bp Bn : Ensemble svar),
      respects_blacklist phi1 Bp Bn -> respects_blacklist phi2 Bp Bn ->
      respects_blacklist (phi1 $ phi2) Bp Bn.
  Proof.
    intros. unfold respects_blacklist in *.
    intros. split; intros; constructor; firstorder; firstorder.
  Qed.

  Lemma respects_blacklist_app_1 : forall (phi1 phi2 : Pattern) (Bp Bn : Ensemble svar),
      respects_blacklist (phi1 $ phi2) Bp Bn -> respects_blacklist phi1 Bp Bn.
  Proof.
    unfold respects_blacklist.
    intros.
    specialize (H var).
    destruct H as [Hneg Hpos].
    split; intros.
    * specialize (Hneg H).
      inversion Hneg. subst. assumption.
    * specialize (Hpos H).
      inversion Hpos. subst. assumption.
  Qed.

  (* This proof is the same as for app_1 *)
  Lemma respects_blacklist_app_2 : forall (phi1 phi2 : Pattern) (Bp Bn : Ensemble svar),
      respects_blacklist (phi1 $ phi2) Bp Bn -> respects_blacklist phi2 Bp Bn.
  Proof.
    unfold respects_blacklist.
    intros.
    specialize (H var).
    destruct H as [Hneg Hpos].
    split; intros.
    * specialize (Hneg H).
      inversion Hneg. subst. assumption.
    * specialize (Hpos H).
      inversion Hpos. subst. assumption.
  Qed.

  Lemma respects_blacklist_impl : forall (phi1 phi2 : Pattern) (Bp Bn : Ensemble svar),
      respects_blacklist phi1 Bn Bp -> respects_blacklist phi2 Bp Bn ->
      respects_blacklist (phi1 ---> phi2) Bp Bn.
  Proof.
    unfold respects_blacklist.
    intros.
    specialize (H var).
    specialize (H0 var).
    destruct H as [H1neg H1pos].
    destruct H0 as [H2neg H2pos].
    split; intros; constructor; firstorder.
  Qed.

  Lemma respects_blacklist_impl_1 : forall (phi1 phi2 : Pattern) (Bp Bn : Ensemble svar),
      respects_blacklist (phi1 ---> phi2) Bp Bn -> respects_blacklist phi1 Bn Bp.
  Proof.
    unfold respects_blacklist.
    intros.
    specialize (H var).
    destruct H as [Hneg Hpos].
    split; intros.
    * specialize (Hpos H).
      inversion Hpos. subst. assumption.
    * specialize (Hneg H).
      inversion Hneg. subst. assumption.
  Qed.

  Lemma respects_blacklist_impl_2 : forall (phi1 phi2 : Pattern) (Bp Bn : Ensemble svar),
      respects_blacklist (phi1 ---> phi2) Bp Bn -> respects_blacklist phi2 Bp Bn.
  Proof.
    unfold respects_blacklist.
    intros.
    specialize (H var).
    destruct H as [Hneg Hpos].
    split; intros.
    * specialize (Hneg H).
      inversion Hneg. subst. assumption.
    * specialize (Hpos H).
      inversion Hpos. subst. assumption.
  Qed.

  Lemma respects_blacklist_ex : forall (phi : Pattern) (Bp Bn : Ensemble svar),
      respects_blacklist (patt_exists phi) Bp Bn -> respects_blacklist phi Bp Bn.
  Proof.
    intros. unfold respects_blacklist in *.
    intros. specialize (H var). destruct H as [Hneg Hpos].
    split; intros.
    * specialize (Hneg H). inversion Hneg. assumption.
    * specialize (Hpos H). inversion Hpos. assumption.
  Qed.

  Lemma respects_blacklist_ex' : forall (phi : Pattern) (Bp Bn : Ensemble svar),
      respects_blacklist phi Bp Bn -> respects_blacklist (patt_exists phi) Bp Bn.
  Proof.
    unfold respects_blacklist. intros.
    specialize (H var).
    destruct H as [Hneg Hpos].
    split; intros; constructor; firstorder.
  Qed.

  Lemma respects_blacklist_mu : forall (phi : Pattern) (Bp Bn : Ensemble svar),
      respects_blacklist (patt_mu phi) Bp Bn -> respects_blacklist phi Bp Bn.
  Proof.
    unfold respects_blacklist. intros.
    specialize (H var).
    destruct H as [Hneg Hpos].
    split; intros.
    - specialize (Hneg H).
      inversion Hneg. assumption.
    - specialize (Hpos H).
      inversion Hpos. assumption.
  Qed.

  Lemma respects_blacklist_mu' : forall (phi : Pattern) (Bp Bn : Ensemble svar),
      respects_blacklist phi Bp Bn -> respects_blacklist (patt_mu phi) Bp Bn.
  Proof.
    unfold respects_blacklist. intros.
    specialize (H var).
    destruct H as [Hneg Hpos].
    split; intros; constructor; firstorder.
  Qed.

  Lemma respects_blacklist_union : forall (phi : Pattern) (Bp1 Bn1 Bp2 Bn2 : Ensemble svar),
      respects_blacklist phi Bp1 Bn1 ->
      respects_blacklist phi Bp2 Bn2 ->
      respects_blacklist phi (Union svar Bp1 Bp2) (Union svar Bn1 Bn2).
  Proof.
    unfold respects_blacklist.
    induction phi; intros; split; intros;
      destruct H1; unfold In in *;
        try specialize (H x0); try specialize (H x);
          try specialize (H0 x0); try specialize (H0 x); firstorder; try constructor.
  Qed.

  Lemma positive_occurrence_respects_blacklist_svar_open :
    forall (phi : Pattern) (dbi : db_index) (X : svar),
      positive_occurrence_db dbi phi ->
      X ∉ (free_svars phi) ->
      respects_blacklist (svar_open dbi X phi) (Empty_set svar) (Singleton svar X).
  Proof.
    intros phi dbi X Hpodb Hni.
    pose proof (Hpno := not_free_implies_positive_negative_occurrence phi X Hni).
    unfold respects_blacklist. intros.
    split; intros.
    * firstorder using positive_negative_occurrence_db_named.
    * inversion H. subst.
      pose (Hpd := positive_negative_occurrence_db_named phi dbi var).
      destruct Hpd as [Hpd1 Hpd2].
      destruct Hpno as [Hpno1 Hpno2].
      auto.
  Qed.
  
  Lemma mu_wellformed_respects_blacklist : forall (phi : Pattern),
      well_formed_positive (patt_mu phi) ->
      let X := fresh_svar phi in
      respects_blacklist (svar_open 0 X phi) (Empty_set svar) (Singleton svar X).
  Proof.
    intros. destruct H as [Hpo Hwfp].
    pose proof (Hfr := set_svar_fresh_is_fresh phi).
    auto using positive_occurrence_respects_blacklist_svar_open.
  Qed.


  (*
Lemma respects_blacklist_ex' : forall (phi : Pattern) (Bp Bn : Ensemble svar),
    respects_blacklist ()
respects_blacklist (evar_open 0 (evar_fresh variables (free_evars phi)) phi) Bp B
   *)

  Lemma evar_open_respects_blacklist :
    forall (phi : Pattern) (Bp Bn : Ensemble svar) (x : evar) (n : nat),
      respects_blacklist phi Bp Bn ->
      respects_blacklist (evar_open n x phi) Bp Bn.
  Proof.
    induction phi; try auto.
    - (* EVar bound *)
      intros. simpl.
      destruct (n =? n0).
      * unfold respects_blacklist. intros.
        split; intros; constructor.
      * assumption.  
    -  (* App *) 
      intros.
      simpl.
      remember (respects_blacklist_app_1 phi1 phi2 Bp Bn H) as Hrb1. clear HeqHrb1.
      remember (respects_blacklist_app_2 phi1 phi2 Bp Bn H) as Hrb2. clear HeqHrb2.
      specialize (IHphi1 Bp Bn x n Hrb1).
      specialize (IHphi2 Bp Bn x n Hrb2).
      clear H Hrb1 Hrb2.
      apply respects_blacklist_app. assumption. assumption.
    - (* Impl *)
      intros.
      simpl.
      remember (respects_blacklist_impl_1 phi1 phi2 Bp Bn H) as Hrb1. clear HeqHrb1.
      remember (respects_blacklist_impl_2 phi1 phi2 Bp Bn H) as Hrb2. clear HeqHrb2.
      specialize (IHphi1 Bn Bp x n Hrb1).
      specialize (IHphi2 Bp Bn x n Hrb2).
      apply respects_blacklist_impl; assumption.
    - (* Ex *)
      intros.
      simpl.
      apply respects_blacklist_ex'.
      apply respects_blacklist_ex in H.
      auto.
    - (* Mu *)
      intros.
      simpl.
      apply respects_blacklist_mu in H.
      specialize (IHphi Bp Bn x n H).
      auto using respects_blacklist_mu'.
  Qed.
End respects_blacklist.

(* From the following section, `update_svar_val_comm`, `update_svar_shadow`
   and `is_monotonic` may be generally useful.
   The lemma `respects_blacklist_implies_monotonic` is only a technical lemma for proving `is_monotonic`,
   which is the main lemma of the section.
*)
Section with_model.

  Context {M : @Model sig}.
  Let A := Ensemble (@Domain sig M).
  Let OS := EnsembleOrderedSet (@Domain sig M).
  Let L := PowersetLattice (@Domain sig M).

  Lemma respects_blacklist_implies_monotonic :
    forall (n : nat) (phi : Pattern),
      le (size phi) n -> well_formed_positive phi ->
      forall (Bp Bn : Ensemble svar),
        respects_blacklist phi Bp Bn ->
        forall (evar_val : evar -> Domain M)
               (svar_val : svar -> Power (Domain M))
               (X : svar),
          (Bp X ->
           @AntiMonotonicFunction A OS (fun S : Ensemble (Domain M) =>
                                          (@pattern_interpretation sig M evar_val (update_svar_val X S svar_val) phi)
                                       )
          ) /\
          (Bn X ->
           @MonotonicFunction A OS (fun S : Ensemble (Domain M) =>
                                      (@pattern_interpretation sig M evar_val (update_svar_val X S svar_val) phi))
          )
  .
  Proof.
    induction n.
    - (* n = 0 *)
      intros. destruct phi; simpl in H; try inversion H.
      + (* EVar free *)
        unfold MonotonicFunction. unfold AntiMonotonicFunction. unfold leq. simpl. unfold Included.
        unfold In. split; intros; rewrite -> pattern_interpretation_free_evar_simpl in *; assumption.
      + (* SVar free *)
        unfold MonotonicFunction. unfold AntiMonotonicFunction. unfold leq. simpl. unfold Included.
        unfold In.
        split; intros; rewrite -> pattern_interpretation_free_svar_simpl in *;
          unfold update_svar_val in *; destruct (svar_eq X x); subst.
        * unfold respects_blacklist in H1.
          specialize (H1 x).
          destruct H1 as [Hneg Hpos].
          specialize (Hneg H2).
          inversion Hneg. subst. contradiction.
        * assumption.
        * simpl. simpl in H4. auto.
        * assumption.
          
      + (* EVar bound *)
        unfold AntiMonotonicFunction. unfold MonotonicFunction. unfold leq. simpl.
        split; intros; repeat rewrite -> pattern_interpretation_bound_evar_simpl; unfold Included;
          unfold In; intros; assumption.
      + (* SVar bound *)
        unfold AntiMonotonicFunction. unfold MonotonicFunction. unfold leq. simpl.
        split; intros; repeat rewrite -> pattern_interpretation_bound_svar_simpl; unfold Included;
          unfold In; intros; assumption.
      + (* Sym *)
        unfold AntiMonotonicFunction. unfold MonotonicFunction. unfold leq. simpl.
        split; intros; repeat rewrite -> pattern_interpretation_sym_simpl; unfold Included;
          unfold In; intros; assumption.
      + (* Bot *)
        unfold AntiMonotonicFunction. unfold MonotonicFunction. unfold leq. simpl.
        split; intros; rewrite -> pattern_interpretation_bott_simpl; unfold Included; intros; inversion H4.
    - (* S n *)
      intros phi Hsz Hwfp Bp Bn Hrb evar_val svar_val V.
      destruct phi.
      * apply IHn. simpl. lia. assumption. assumption.
      * apply IHn. simpl. lia. assumption. assumption.
      * apply IHn. simpl. lia. assumption. assumption.
      * apply IHn. simpl. lia. assumption. assumption.
      * apply IHn. simpl. lia. assumption. assumption.
      * (* App *)
        remember (respects_blacklist_app_1 phi1 phi2 Bp Bn Hrb) as Hrb1. clear HeqHrb1.
        remember (respects_blacklist_app_2 phi1 phi2 Bp Bn Hrb) as Hrb2. clear HeqHrb2.
        inversion Hwfp.
        rename H into Hwfp1. rename H0 into Hwfp2.

        (* phi1 and phi2 are smaller then the whole implication *)
        simpl in Hsz.
        assert (Hsz1: size phi1 <= n).
        { lia. }
        assert (Hsz2: size phi2 <= n).
        { lia. }

        split.
        {
          intros HBp. unfold AntiMonotonicFunction in *.
          intros.
          repeat rewrite -> pattern_interpretation_app_simpl.
          unfold app_ext. unfold leq in *. simpl in *.
          unfold Included in *. intros. unfold In in *.
          destruct H0. destruct H0. destruct H0. destruct H1.
          
          exists x1. exists x2.
          split.
          - specialize (IHn phi1 Hsz1 Hwfp1 Bp Bn Hrb1 evar_val svar_val V).
            destruct IHn as [IHam IHmo].
            apply (IHam HBp x y H x1). assumption.
          - split.
            + specialize (IHn phi2 Hsz2 Hwfp2 Bp Bn Hrb2 evar_val svar_val V).
              destruct IHn as [IHam IHmo].
              apply (IHam HBp x y H x2). assumption.
            + assumption.
        }
        {
          intros HBp. unfold MonotonicFunction in *.
          intros.
          repeat rewrite -> pattern_interpretation_app_simpl.
          unfold app_ext. unfold leq in *. simpl in *.
          unfold Included in *. intros. unfold In in *.
          destruct H0. destruct H0. destruct H0. destruct H1.
          
          exists x1. exists x2.
          split.
          - specialize (IHn phi1 Hsz1 Hwfp1 Bp Bn Hrb1 evar_val svar_val V).
            destruct IHn as [IHam IHmo].
            apply (IHmo HBp x y H x1). assumption.
          - split.
            + specialize (IHn phi2 Hsz2 Hwfp2 Bp Bn Hrb2 evar_val svar_val V).
              destruct IHn as [IHam IHmo].
              apply (IHmo HBp x y H x2). assumption.
            + assumption.
        }
        
      * (* Bot *)
        apply IHn. simpl. lia. assumption. assumption.
      * (* Impl *)
        (* phi1 and phi2 are well-formed-positive *)
        inversion Hwfp. rename H into Hwfp1. rename H0 into Hwfp2.

        (* phi1 and phi2 are smaller then the whole implication *)
        simpl in Hsz.
        assert (Hsz1: size phi1 <= n).
        { lia. }
        assert (Hsz2: size phi2 <= n).
        { lia. }
        
        
        remember (respects_blacklist_impl_1 phi1 phi2 Bp Bn Hrb) as Hrb1. clear HeqHrb1.
        remember (respects_blacklist_impl_2 phi1 phi2 Bp Bn Hrb) as Hrb2. clear HeqHrb2.
        remember IHn as IHn1. clear HeqIHn1.
        rename IHn into IHn2.
        specialize (IHn1 phi1 Hsz1 Hwfp1 Bn Bp Hrb1 evar_val svar_val V).
        specialize (IHn2 phi2 Hsz2 Hwfp2 Bp Bn Hrb2 evar_val svar_val V).
        unfold AntiMonotonicFunction in *.
        unfold MonotonicFunction in *.
        
        split.
        {
          intros HBp.
          intros.
          repeat rewrite -> pattern_interpretation_imp_simpl.
          unfold leq in *. simpl in *. unfold Included in *. intros.
          destruct H0.
          + left. unfold Complement in *.
            unfold not in *. unfold In in *. intros.
            apply H0.
            
            destruct IHn1 as [IHn11 IHn12].
            apply (IHn12 HBp x y H x0).
            apply H1.
          + right. unfold In in *.
            destruct IHn2 as [IHn21 IHn22].
            apply (IHn21 HBp x y H x0 H0).
        }
        {
          intros HBn.
          intros. repeat rewrite -> pattern_interpretation_imp_simpl.
          unfold leq in *. simpl in *. unfold Included in *. intros.
          destruct H0.
          + left. unfold Complement in *.
            unfold not in *. unfold In in *. intros.
            apply H0.

            destruct IHn1 as [IHn11 IHn12].
            apply (IHn11 HBn x y H x0).
            apply H1.
          + right. unfold In in *.
            destruct IHn2 as [IHn21 IHn22].
            apply (IHn22 HBn x y H x0 H0).
        }
      * (* Ex *)
        simpl. remember (respects_blacklist_ex phi Bp Bn Hrb) as Hrb'. clear HeqHrb'.
        specialize (IHn (evar_open 0 (evar_fresh (elements (free_evars phi))) phi)).
        rewrite <- evar_open_size in IHn.
        assert (Hsz': size phi <= n). simpl in *. lia.
        remember (evar_fresh (elements (free_evars phi))) as fresh.
        pose proof (Hwfp' := evar_open_wfp n phi Hsz' 0 fresh Hwfp).
        specialize (IHn Hsz' Hwfp' Bp Bn).
        pose proof (Hrb'' := evar_open_respects_blacklist phi Bp Bn fresh 0 Hrb').
        unfold MonotonicFunction in *. unfold AntiMonotonicFunction in *.
        unfold leq. simpl.
        unfold Included in *. unfold In in *.
        (*rewrite -> pattern_interpretation_ex_simpl in *.*)
        split; intros HBp S1 S2 Hincl; rewrite -> pattern_interpretation_ex_simpl; simpl;
          intros m [x [c Hc]]; rewrite -> pattern_interpretation_ex_simpl; simpl; constructor; exists c;
            remember (update_evar_val fresh c evar_val) as evar_val';
            specialize (IHn Hrb'' evar_val' svar_val V);
            destruct IHn as [IHn1 IHn2].        
        {
          specialize (IHn1 HBp S1 S2 Hincl).
          remember (evar_open 0 fresh phi) as phi'.
          remember (update_svar_val V S1 svar_val) as svar_val1.
          unfold leq in IHn1. simpl in *. unfold Included in *. unfold In in *.
          subst.
          apply IHn1. apply Hc.
        }
        {
          specialize (IHn2 HBp S1 S2 Hincl).
          remember (evar_open 0 fresh phi) as phi'.
          remember (update_svar_val V S1 svar_val) as svar_val1.
          unfold leq in IHn1. simpl in *. unfold Included in *. unfold In in *.
          subst.
          apply IHn2. apply Hc.
        }
        auto.
      * (* Mu *)
        remember Hwfp as Hwfpmu. clear HeqHwfpmu.
        simpl in Hsz.
        assert (Hsz': size phi <= n).
        { lia. }
        split.
        {
          unfold AntiMonotonicFunction. intros.
          repeat rewrite -> pattern_interpretation_mu_simpl.
          Arguments LeastFixpointOf : simpl never.
          Arguments leq : simpl never.
          simpl.

          remember (fresh_svar phi) as X'.
          remember (svar_open 0 X' phi) as phi'.
          pose proof (Hszeq := svar_open_size sig 0 X' phi).
          assert (Hsz'': size phi' <= n).
          { rewrite -> Heqphi'. rewrite <- Hszeq. assumption. }
          specialize (IHn phi' Hsz'').
          simpl in Hwfp. destruct Hwfp as [Hpo Hwfp].
          
          assert (Hrb': respects_blacklist phi' (Empty_set svar) (Singleton svar X')).
          { subst. apply mu_wellformed_respects_blacklist. assumption. }

          assert (Hwfp' : well_formed_positive phi').
          { subst. apply wfp_svar_open. assumption. }

          remember IHn as IHn'. clear HeqIHn'.
          specialize (IHn' Hwfp' (Empty_set svar) (Singleton svar X') Hrb' evar_val).
          remember IHn' as Hy. clear HeqHy.
          rename IHn' into Hx.
          specialize (Hx (update_svar_val V x svar_val) X').
          specialize (Hy (update_svar_val V y svar_val) X').

          apply lfp_preserves_order.
          - apply Hy. constructor.
          - apply Hx. constructor.
          - clear Hx. clear Hy.
            intros.
            destruct (svar_eq X' V).
            + (* X' = V *)
              rewrite <- e.
              repeat rewrite -> update_svar_val_shadow.
              unfold leq. simpl. unfold Included. unfold In. auto.
            + (* X' <> V*)
              pose proof (Uhsvcx := update_svar_val_comm M X' V x0 x svar_val n0).
              rewrite -> Uhsvcx.
              pose proof (Uhsvcy := update_svar_val_comm M X' V x0 y svar_val n0).
              rewrite -> Uhsvcy.

              assert (HrbV: respects_blacklist phi' (Singleton svar V) (Empty_set svar)).
              {
                unfold respects_blacklist. intros. split.
                - intros. inversion H1. rewrite <- H2.
                  unfold respects_blacklist in Hrb.
                  specialize (Hrb V).
                  destruct Hrb as [Hrbn Hrbp].
                  specialize (Hrbn H).
                  rewrite <- H2 in *. clear H2.                  
                  subst.
                  apply positive_negative_occurrence_named_svar_open.
                  *
                    unfold not. intros. assert (fresh_svar phi = V).
                    {
                      symmetry. assumption.
                    }
                    unfold not in n0. destruct (n0 H3).
                  * inversion Hrbn. assumption.
                - intros. destruct H1.
              }

              specialize (IHn Hwfp' (Singleton svar V) (Empty_set svar) HrbV).
              specialize (IHn evar_val (update_svar_val X' x0 svar_val) V).
              destruct IHn as [IHam IHmo].
              apply IHam. constructor. assumption.
        }
        (* This is the same as the previous, with minor changes *)
        {
          unfold MonotonicFunction. intros.
          repeat rewrite -> pattern_interpretation_mu_simpl.
          Arguments LeastFixpointOf : simpl never.
          Arguments leq : simpl never.
          simpl.

          remember (fresh_svar phi) as X'.
          remember (svar_open 0 X' phi) as phi'.
          pose proof (Hszeq := svar_open_size sig 0 X' phi).
          assert (Hsz'': size phi' <= n).
          { rewrite -> Heqphi'. rewrite <- Hszeq. assumption. }
          specialize (IHn phi' Hsz'').
          simpl in Hwfp. destruct Hwfp as [Hpo Hwfp].
          
          assert (Hrb': respects_blacklist phi' (Empty_set svar) (Singleton svar X')).
          { subst. apply mu_wellformed_respects_blacklist. assumption. }

          assert (Hwfp' : well_formed_positive phi').
          { subst. apply wfp_svar_open. assumption. }

          remember IHn as IHn'. clear HeqIHn'.
          specialize (IHn' Hwfp' (Empty_set svar) (Singleton svar X') Hrb' evar_val).
          remember IHn' as Hy. clear HeqHy.
          rename IHn' into Hx.
          specialize (Hx (update_svar_val V x svar_val) X').
          specialize (Hy (update_svar_val V y svar_val) X').

          apply lfp_preserves_order.
          - apply Hx. constructor.
          - apply Hy. constructor.
          - clear Hy. clear Hx.
            intros.
            destruct (svar_eq X' V).
            + (* X' = V *)
              rewrite <- e.
              repeat rewrite -> update_svar_val_shadow.
              unfold leq. simpl. unfold Included. unfold In. auto.
            + (* X' <> V*)
              pose proof (Uhsvcx := update_svar_val_comm M X' V x0 x svar_val n0).
              rewrite -> Uhsvcx.
              pose proof (Uhsvcy := update_svar_val_comm M X' V x0 y svar_val n0).
              rewrite -> Uhsvcy.

              assert (HrbV: respects_blacklist phi' (Empty_set svar) (Singleton svar V)).
              {
                unfold respects_blacklist. intros. split.
                - intros. inversion H1.
                - intros. inversion H1. rewrite <- H2.
                  unfold respects_blacklist in Hrb.
                  specialize (Hrb V).
                  destruct Hrb as [Hrbn Hrbp].
                  specialize (Hrbp H).
                  rewrite <- H2 in *. clear H2.                  
                  subst.
                  apply positive_negative_occurrence_named_svar_open.
                  *
                    unfold not. intros. assert (fresh_svar phi = V).
                    {
                      symmetry. assumption.
                    }
                    unfold not in n0. destruct (n0 H3).
                  * inversion Hrbp. assumption.
              }

              specialize (IHn Hwfp' (Empty_set svar) (Singleton svar V) HrbV).
              specialize (IHn evar_val (update_svar_val X' x0 svar_val) V).
              destruct IHn as [IHam IHmo].
              apply IHmo. constructor. assumption.
        }
  Qed.

  Lemma is_monotonic : forall (phi : @Pattern sig)
                              (evar_val : @EVarVal sig M)
                              (svar_val : @SVarVal sig M),
      well_formed (mu, phi) ->
      let X := fresh_svar phi in
      @MonotonicFunction A OS
                         (fun S : Ensemble (Domain M) =>
                            (@pattern_interpretation sig M evar_val (update_svar_val X S svar_val)
                                            (svar_open 0 X phi))).
  Proof.
    simpl. intros. unfold well_formed in H. destruct H as [Hwfp Hwfc].
    pose proof (Hrb := mu_wellformed_respects_blacklist phi Hwfp).
    simpl in Hrb.
    inversion Hwfp.
    remember (svar_open 0 (fresh_svar phi) phi) as phi'.
    assert (Hsz : size phi' <= size phi').
    { lia. }
    pose proof (Hmono := respects_blacklist_implies_monotonic (size phi') phi').
    assert (Hwfp' : well_formed_positive phi').
    { subst. apply wfp_svar_open. assumption. }
    specialize (Hmono Hsz Hwfp').
    specialize (Hmono (Empty_set svar) (Singleton svar (fresh_svar phi))).
    specialize (Hmono Hrb evar_val svar_val (fresh_svar phi)).
    destruct Hmono.
    apply H2.
    constructor.
  Qed.
End with_model.


(* if pattern_interpretation (phi1 ---> phi2) = Full_set 
   then pattern_interpretation phi1 subset pattern_interpretation phi2
*)
Theorem pattern_interpretation_iff_subset {m : Model}
        (evar_val : evar -> Domain m) (svar_val : svar -> Power (Domain m))
        (phi1 : Pattern) (phi2 : Pattern) :
  Same_set (Domain m) (pattern_interpretation evar_val svar_val (phi1 ---> phi2)) (Full_set (Domain m)) <->
  Included (Domain m) (pattern_interpretation evar_val svar_val phi1)
           (@pattern_interpretation sig m evar_val svar_val phi2).
Proof.
  intros; split; unfold Included; intros.
  * rewrite pattern_interpretation_imp_simpl in H.
    remember (pattern_interpretation evar_val svar_val phi1) as Xphi1.
    remember (pattern_interpretation evar_val svar_val phi2) as Xphi2.
    assert (In (Domain m) (Union (Domain m) (Complement (Domain m) Xphi1) Xphi2) x).
    apply Same_set_to_eq in H. rewrite H. constructor.
    inversion H1. contradiction. assumption.
  * rewrite pattern_interpretation_imp_simpl.
    remember (pattern_interpretation evar_val svar_val phi1) as Xphi1.
    remember (pattern_interpretation evar_val svar_val phi2) as Xphi2.
    constructor. constructor.
    assert (Union (Domain m) (Complement (Domain m) Xphi1) Xphi1 = Full_set (Domain m)).
    apply Same_set_to_eq; apply Union_Compl_Fullset. rewrite <- H0; clear H0.
    unfold Included; intros.
    inversion H0.
    left; assumption.
    right; apply H in H1; assumption.
Qed.

(* pattern_interpretation with free_svar_subst does not change *)
Lemma update_valuation_free_svar_subst {m : Model}
      (evar_val : evar -> Domain m) (svar_val : svar -> Power (Domain m))
      (phi : Pattern) (psi : Pattern) (X : svar) :
  pattern_interpretation evar_val svar_val phi
  = pattern_interpretation evar_val svar_val (@free_svar_subst sig phi psi X) .
Proof.
Admitted.

Lemma proof_rule_prop_ex_right_sound {m : Model} (theory : Theory) (phi psi : Pattern)  
      (evar_val : evar -> Domain m) (svar_val : svar -> Power (Domain m)):
  (well_formed (patt_imp (patt_app (patt_exists phi) psi) (patt_exists (patt_app phi psi)))) ->
  (well_formed phi) -> (@well_formed sig psi) ->
  (forall axiom : Pattern,
     In Pattern theory axiom ->
     forall (evar_val : evar -> Domain m)
       (svar_val : svar -> Power (Domain m)),
     Same_set (Domain m) (pattern_interpretation evar_val svar_val axiom)
       (Full_set (@Domain sig m))) ->
  Same_set (Domain m)
  (pattern_interpretation evar_val svar_val
     (patt_imp (patt_app (patt_exists phi) psi)
        (patt_exists (patt_app phi psi)))) (Full_set (Domain m)).
Proof.
  intros Hwf H H0 Hv.
  rewrite pattern_interpretation_imp_simpl.
    constructor. constructor.
    remember (pattern_interpretation evar_val svar_val (patt_app (patt_exists phi) psi)) as Xex.
    assert (Union (Domain m) (Complement (Domain m) Xex) Xex = Full_set (Domain m)).
    apply Same_set_to_eq; apply Union_Compl_Fullset. rewrite <- H1; clear H1.
    unfold Included; intros. inversion H1; subst.
    left. assumption.
    right. rewrite pattern_interpretation_ex_simpl. simpl. constructor.
    rewrite pattern_interpretation_app_simpl, pattern_interpretation_ex_simpl in H2.
    destruct H2 as [le [re [Hunion [Hext_le Happ]]]]. inversion Hunion; subst.
    destruct H2 as [c Hext_re].
    exists c. rewrite pattern_interpretation_app_simpl. unfold app_ext.
    exists le, re.
    assert ((evar_fresh (elements (union (free_evars phi) (free_evars psi)))) ∉ (free_evars psi)).
    admit.
    assert ((evar_fresh (elements (union (free_evars phi) (free_evars psi)))) ∉ (free_evars phi)).
    admit.
    rewrite evar_open_fresh in Hext_re; try assumption.
    rewrite update_valuation_fresh in Hext_re; try assumption.
    repeat rewrite evar_open_fresh; try assumption.
    repeat rewrite update_valuation_fresh; try assumption.
    repeat split; assumption.
    admit. admit.
Admitted.

Lemma proof_rule_prop_ex_left_sound {m : Model} (theory : Theory) (phi psi : Pattern)  
      (evar_val : evar -> Domain m) (svar_val : svar -> Power (Domain m)):
  (well_formed (patt_imp (patt_app psi (patt_exists phi)) (patt_exists (patt_app psi phi)))) ->
  (well_formed phi) -> (well_formed psi) ->
  (forall axiom : Pattern,
     In Pattern theory axiom ->
     forall (evar_val : evar -> Domain m)
       (svar_val : svar ->
                   Power (Domain m)),
     Same_set (Domain m)
       (pattern_interpretation evar_val svar_val axiom)
       (Full_set (Domain m))) ->
  (Same_set (Domain m)
  (pattern_interpretation evar_val svar_val
     (patt_imp (patt_app psi (patt_exists phi))
        (patt_exists (patt_app psi phi))))
  (Full_set (Domain m))).
Proof.
  intros Hwf H H0 Hv.
  rewrite pattern_interpretation_imp_simpl.
    constructor. constructor.
    remember (pattern_interpretation evar_val svar_val (patt_app psi (patt_exists phi))) as Xex.
    assert (Union (Domain m) (Complement (Domain m) Xex) Xex = Full_set (Domain m)).
    apply Same_set_to_eq; apply Union_Compl_Fullset. rewrite <- H1; clear H1.
    unfold Included; intros. inversion H1; subst.
    left. assumption.
    right. rewrite pattern_interpretation_ex_simpl. simpl. constructor.
    rewrite pattern_interpretation_app_simpl, pattern_interpretation_ex_simpl in H2.
    destruct H2 as [le [re [Hext_le [Hunion Happ]]]]. inversion Hunion; subst.
    destruct H2 as [c Hext_re].
    exists c. rewrite pattern_interpretation_app_simpl. unfold app_ext.
    exists le, re.
    assert ((evar_fresh (elements (union (free_evars psi) (free_evars phi)))) ∉ (free_evars psi)).
    admit.
    assert ((evar_fresh (elements (union (free_evars psi) (free_evars phi)))) ∉ (free_evars phi)).
    admit.
    rewrite evar_open_fresh in Hext_re; try assumption.
    rewrite update_valuation_fresh in Hext_re; try assumption.
    repeat rewrite evar_open_fresh; try assumption.
    repeat rewrite update_valuation_fresh; try assumption.
    repeat split; assumption.
    admit. admit.
Admitted.


(* There are two ways how to plug a pattern phi2 into a pattern phi1:
   either substitute it for some variable,
   or evaluate phi2 first and then evaluate phi1 with valuation updated to the result of phi2 *)
Lemma plugging_patterns_helper : forall (sz : nat) (dbi : db_index) (M : @Model sig) (phi1 phi2 : @Pattern sig),
    size phi1 <= sz -> forall    (evar_val1 evar_val2 : @EVarVal sig M)
                                 (svar_val : @SVarVal sig M) (X : svar), (* TODO X not free in ?? *)
    well_formed_closed (patt_mu phi1) ->
    well_formed_closed phi2 ->
    (forall x : evar, x ∈ free_evars phi1 -> evar_val1 x = evar_val2 x) ->
    ~ elem_of X (free_svars phi1) ->
    @pattern_interpretation sig M evar_val1 svar_val (bsvar_subst phi1 phi2 dbi (*0?*)) (*~ open_svar dbi phi2 ph1*)
    = @pattern_interpretation sig M evar_val2
                     (update_svar_val X (@pattern_interpretation sig M evar_val1 svar_val phi2) svar_val)
                     (svar_open dbi X phi1).
Proof.
  induction sz; intros dbi M phi1 phi2 Hsz evar_val1 evar_val2 svar_val X Hwfc1 Hwfc2 He1e2eq H.
  - (* sz == 0 *)
    destruct phi1; simpl in Hsz; simpl.
    + (* free_evar *)
      repeat rewrite pattern_interpretation_free_evar_simpl. rewrite He1e2eq. reflexivity.
      apply elem_of_singleton_2. auto.
    + (* free_svar *)
      repeat rewrite pattern_interpretation_free_svar_simpl.
      unfold update_svar_val. destruct (svar_eq X x).
      * simpl in H. simpl. unfold not in H. exfalso. apply H.
        apply elem_of_singleton_2. auto.
      * auto.
    + (* bound_evar *)
      apply wfc_body_wfc_mu_iff in Hwfc1. unfold wfc_body_mu in Hwfc1.
      specialize (Hwfc1 X H). unfold well_formed_closed in Hwfc1; simpl in Hwfc1.
      lia. assumption.
    + (* bound_svar *)
      simpl. destruct (n =? dbi) eqn:Heq, (compare_nat n dbi).
      * symmetry in Heq; apply beq_nat_eq in Heq. lia.
      * rewrite pattern_interpretation_free_svar_simpl. unfold update_svar_val.
        destruct (svar_eq X X). auto. contradiction.
      * symmetry in Heq; apply beq_nat_eq in Heq. lia.
      * repeat rewrite pattern_interpretation_bound_svar_simpl; auto.
      * apply beq_nat_false in Heq. lia.
      * repeat rewrite pattern_interpretation_bound_svar_simpl; auto.
    + (* sym *)
      simpl. repeat rewrite pattern_interpretation_sym_simpl; auto.
    + (* app *)
      lia.
    + (* bot *)
      simpl. repeat rewrite pattern_interpretation_bott_simpl; auto.
    + (* impl *)
      lia.
    + (* ex *)
      lia.
    + (* mu *)
      lia.
  - (* sz = S sz' *)
    destruct phi1; simpl.
    (* HERE we duplicate some of the effort. I do not like it. *)
    + (* free_evar *)
      repeat rewrite pattern_interpretation_free_evar_simpl. rewrite He1e2eq. reflexivity.
      apply elem_of_singleton_2. auto.
    + (* free_svar *)
      repeat rewrite pattern_interpretation_free_svar_simpl.
      unfold update_svar_val. destruct (svar_eq X x).
      * simpl in H. simpl. unfold not in H. exfalso. apply H.
        apply elem_of_singleton_2. auto.
      * auto.
    + (* bound_evar *)
      apply wfc_body_wfc_mu_iff in Hwfc1. unfold wfc_body_mu in Hwfc1.
      specialize (Hwfc1 X H). unfold well_formed_closed in Hwfc1; simpl in Hwfc1.
      lia. assumption.
    + (* bound_svar *)
      simpl. destruct (n =? dbi) eqn:Heq, (compare_nat n dbi).
      * symmetry in Heq; apply beq_nat_eq in Heq. lia.
      * rewrite pattern_interpretation_free_svar_simpl. unfold update_svar_val.
        destruct (svar_eq X X). simpl. auto. contradiction.
      * symmetry in Heq; apply beq_nat_eq in Heq. lia.
      * repeat rewrite pattern_interpretation_bound_svar_simpl; auto.
      * apply beq_nat_false in Heq. lia.
      * repeat rewrite pattern_interpretation_bound_svar_simpl; auto.
    + (* sym *)
      simpl. repeat rewrite pattern_interpretation_sym_simpl; auto.
      (* HERE the duplication ends *)
    + (* app *)
      simpl.
      simpl in H. apply not_elem_of_union in H. destruct H.
      repeat rewrite pattern_interpretation_app_simpl.
      simpl in Hsz.
      repeat rewrite <- IHsz.
       * reflexivity.
       * lia.
       * admit.
       * assumption.
       * intros. apply He1e2eq. simpl. apply elem_of_union_r. assumption.
       * assumption.
       * lia.
       * admit.
       * assumption.
       * intros. apply He1e2eq. simpl. apply elem_of_union_l. assumption.
       * assumption.
    + (* Bot. Again, a duplication of the sz=0 case *)
      simpl. repeat rewrite pattern_interpretation_bott_simpl; auto.
    + (* imp *)
      simpl in Hsz. simpl in H.
      apply not_elem_of_union in H. destruct H.
      repeat rewrite pattern_interpretation_imp_simpl.
      repeat rewrite <- IHsz.
      * reflexivity.
      * lia.
      * admit.
      * assumption.
      * intros. apply He1e2eq. simpl. apply elem_of_union_r. assumption.
      * assumption.
      * lia.
      * admit.
      * assumption.
      * intros. apply He1e2eq. simpl. apply elem_of_union_l. assumption.
      * assumption.
    (* TODO *)
    + simpl in Hsz. simpl in H.
      repeat rewrite pattern_interpretation_ex_simpl. simpl.
      apply Same_set_to_eq. apply FA_Union_same. intros c.
      remember (update_evar_val (fresh_evar (bsvar_subst phi1 phi2 dbi)) c evar_val1) as evar_val1'.
      remember (update_evar_val (fresh_evar (svar_open dbi X phi1)) c evar_val2) as evar_val2'.
      rewrite -> svar_open_evar_open_comm.
      rewrite -> evar_open_bsvar_subst. 2: auto.
      rewrite -> fresh_evar_svar_open in *.
      remember (fresh_evar (bsvar_subst phi1 phi2 dbi)) as Xfr1.
      remember (fresh_evar phi1) as Xfr2.
      
      assert (He1e1':
         (update_svar_val X (pattern_interpretation evar_val1 svar_val phi2) svar_val) =
         (update_svar_val X (pattern_interpretation evar_val1' svar_val phi2) svar_val)
        ). admit.
      (* TODO: I'm not sure if this is true, but if it is then we can apply the IH
         in a way where we have the same evar_val on both sides *)
      rewrite He1e1'.
      rewrite <- IHsz.
      2: { rewrite <- evar_open_size. lia. auto. }
      2: { admit. }
      2: { auto. }
      2: { intros. subst. unfold update_evar_val. unfold ssrbool.is_left.
           assert (Hfree: fresh_evar (bsvar_subst phi1 phi2 (S dbi)) =
                          fresh_evar (svar_open dbi X phi1)). admit.
           destruct (evar_eq (fresh_evar (bsvar_subst phi1 phi2 (S dbi))) x),
           (evar_eq (fresh_evar (svar_open dbi X phi1)) x). auto.
           rewrite Hfree in e. admit.
           (*rewrite Hfree in n.*) admit.
           (*apply He1e2eq. simpl. auto. admit.*)admit. admit. }
      2: { admit. }

Admitted.

End soundness_lemmas.
