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

From MatchingLogic Require Import Syntax Semantics.
Require Export locally_nameless.
Require Import Lattice.
Require Import stdpp_ext.

Require Export Ensembles_Ext.


Import MatchingLogic.Syntax.Notations.
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
