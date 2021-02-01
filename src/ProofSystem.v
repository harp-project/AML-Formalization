From Coq Require Import Ensembles.

From MatchingLogic.Utils Require Import Ensembles_Ext.
From MatchingLogic Require Import Syntax Semantics DerivedOperators Helpers.monotonic.
From Coq.Logic Require Import FunctionalExtensionality Classical_Pred_Type.
From stdpp Require Import fin_sets.

Import MatchingLogic.Syntax.Notations.
Import MatchingLogic.Semantics.Notations.
Import MatchingLogic.DerivedOperators.Notations.

Section ml_proof_system.
  Open Scope ml_scope.

  Context {signature : Signature}.

Lemma proof_rule_prop_ex_right_sound {m : Model} (theory : Theory) (phi psi : Pattern)
      (evar_val : evar -> Domain m) (svar_val : svar -> Power (Domain m)):
  (well_formed (patt_imp (patt_app (patt_exists phi) psi) (patt_exists (patt_app phi psi)))) ->
  (well_formed (ex, phi)) -> (@well_formed signature psi) ->
  (∀ axiom : Pattern,
       Ensembles.In Pattern theory axiom
       → ∀ (evar_val : evar → Domain m) (svar_val : svar → Power (Domain m)),
           pattern_interpretation evar_val svar_val axiom = Full) ->
  pattern_interpretation evar_val svar_val ((ex , phi) $ psi ---> ex , phi $ psi) = Full.
Proof.
  intros Hwf H H0 Hv.
  rewrite -> pattern_interpretation_imp_simpl. apply Extensionality_Ensembles.
    constructor. constructor.
    remember (pattern_interpretation evar_val svar_val (patt_app (patt_exists phi) psi)) as Xex.
    assert (Ensembles.Union (Domain m) (Complement (Domain m) Xex) Xex = Full_set (Domain m)).
    apply Same_set_to_eq; apply Union_Compl_Fullset. unfold Full. rewrite <- H1; clear H1.
    unfold Included; intros. inversion H1; subst.
    left. assumption.
    right. rewrite -> pattern_interpretation_ex_simpl. simpl. constructor.
    rewrite -> pattern_interpretation_app_simpl, pattern_interpretation_ex_simpl in H2.
    destruct H2 as [le [re [Hunion [Hext_le Happ]]]]. inversion Hunion; subst.
    destruct H2 as [c Hext_re].
    exists c. rewrite -> pattern_interpretation_app_simpl. unfold app_ext.
    exists le, re.
    split. erewrite -> (@interpretation_fresh_evar_open signature m) in Hext_re. exact Hext_re. 
    apply set_evar_fresh_is_fresh.
    {
      unfold fresh_evar. simpl. 
      pose(@set_evar_fresh_is_fresh' signature (free_evars phi ∪ free_evars psi)).
      apply not_elem_of_union in n. destruct n. assumption.
    }
    split.
      * erewrite -> (update_valuation_fresh). erewrite -> (evar_open_fresh). exact Hext_le.
        unfold well_formed in H0. destruct H0. assumption.
        rewrite -> (evar_open_fresh). unfold well_formed in H0. destruct H0. assumption.
        unfold well_formed in H0. destruct H0. assumption.
        {
          rewrite -> evar_open_fresh. unfold fresh_evar. simpl. 
          pose(@set_evar_fresh_is_fresh' signature (free_evars phi ∪ free_evars psi)).
          apply not_elem_of_union in n. destruct n. assumption.
          unfold well_formed in H0. destruct H0. assumption.
        }
      * assumption.
Qed.

Lemma proof_rule_prop_ex_left_sound {m : Model} (theory : Theory) (phi psi : Pattern)  
      (evar_val : evar -> Domain m) (svar_val : svar -> Power (Domain m)):
  (well_formed (patt_imp (patt_app psi (patt_exists phi)) (patt_exists (patt_app psi phi)))) ->
  (well_formed (ex, phi)) -> (well_formed psi) ->
  (∀ axiom : Pattern,
       Ensembles.In Pattern theory axiom
       → ∀ (evar_val : evar → Domain m) (svar_val : svar → Power (Domain m)),
           pattern_interpretation evar_val svar_val axiom = Full) ->
  pattern_interpretation evar_val svar_val (psi $ (ex , phi) ---> ex , psi $ phi) = Full.
Proof.
  intros Hwf H H0 Hv.
  rewrite -> pattern_interpretation_imp_simpl. apply Extensionality_Ensembles.
    constructor. constructor.
    remember (pattern_interpretation evar_val svar_val (patt_app psi (patt_exists phi))) as Xex.
    assert (Ensembles.Union (Domain m) (Complement (Domain m) Xex) Xex = Full_set (Domain m)).
    apply Same_set_to_eq; apply Union_Compl_Fullset. unfold Full. rewrite <- H1; clear H1.
    unfold Included; intros. inversion H1; subst.
    left. assumption.
    right. rewrite -> pattern_interpretation_ex_simpl. simpl. constructor.
    rewrite -> pattern_interpretation_app_simpl, pattern_interpretation_ex_simpl in H2.
    destruct H2 as [le [re [Hext_le [Hunion Happ]]]]. inversion Hunion; subst.
    destruct H2 as [c Hext_re].
    exists c. rewrite -> pattern_interpretation_app_simpl. unfold app_ext.
    exists le, re.
    split.
    - rewrite -> evar_open_fresh. rewrite -> update_valuation_fresh. assumption.
      unfold well_formed in H0. destruct H0. assumption.
      {
        unfold fresh_evar. simpl. unfold evar_is_fresh_in.
        pose(@set_evar_fresh_is_fresh' signature (free_evars psi ∪ free_evars phi)).
          apply not_elem_of_union in n. destruct n. assumption.
      }
      unfold well_formed in H0. destruct H0. assumption.
    - split.
      + erewrite -> (@interpretation_fresh_evar_open signature m) in Hext_re. exact Hext_re.
        apply set_evar_fresh_is_fresh.
        {
          pose(@set_evar_fresh_is_fresh' signature (free_evars psi ∪ free_evars phi)).
          apply not_elem_of_union in n. destruct n. assumption.
        }
      + assumption.
Qed.

Lemma evar_open_inj : ∀ phi psi x n,
  evar_is_fresh_in x phi → evar_is_fresh_in x psi →
  evar_open n x phi =
    evar_open n x psi
    → phi = psi.
Proof.
  induction phi; destruct psi; intros; try (simpl in H1; congruence); try (simpl in H1; destruct (n =? n0) eqn:P; congruence); auto.
  - simpl in H1. destruct (n =? n0) eqn:P.
    + inversion H1. subst. unfold evar_is_fresh_in in H. simpl in H. apply not_elem_of_singleton_1 in H.
      congruence.
    + congruence.
  - simpl in H1. destruct (n =? n0) eqn:P.
    + inversion H1. subst. unfold evar_is_fresh_in in H0. simpl in H0. apply not_elem_of_singleton_1 in H0.
      congruence.
    + congruence.
  - simpl in H1. destruct (n =? n1) eqn:P; destruct (n0 =? n1) eqn:P2.
    + apply Nat.eqb_eq in P. apply Nat.eqb_eq in P2. subst. reflexivity.
    + congruence.
    + congruence.
    + inversion H1. reflexivity.
  - simpl in H1. destruct (n =? n1) eqn:P.
    + inversion H1.
    + congruence.
  - inversion H1. destruct (n0 =? n1) eqn:P.
    + inversion H3.
    + assumption.
  - inversion H1. apply IHphi1 in H3. apply IHphi2 in H4. subst. reflexivity.
    apply evar_is_fresh_in_app_r in H. assumption.
    apply evar_is_fresh_in_app_r in H0. assumption.
    apply evar_is_fresh_in_app_l in H. assumption.
    apply evar_is_fresh_in_app_l in H0. assumption.
  - inversion H1. apply IHphi1 in H3. apply IHphi2 in H4. subst. reflexivity.
    apply evar_is_fresh_in_imp_r in H. assumption.
    apply evar_is_fresh_in_imp_r in H0. assumption.
    apply evar_is_fresh_in_imp_l in H. assumption.
    apply evar_is_fresh_in_imp_l in H0. assumption.
  - inversion H1. apply IHphi in H3. subst. reflexivity.
    apply evar_is_fresh_in_exists in H. assumption.
    apply evar_is_fresh_in_exists in H0. assumption.
  - inversion H1. apply IHphi in H3. subst. reflexivity.
    apply evar_is_fresh_in_mu in H. assumption.
    apply evar_is_fresh_in_mu in H0. assumption.
Qed.

Lemma svar_open_inj : ∀ phi psi X n,
  svar_is_fresh_in X phi → svar_is_fresh_in X psi →
  svar_open n X phi =
    svar_open n X psi
    → phi = psi.
Proof.
  induction phi; destruct psi; intros; try (simpl in H1; congruence); try (simpl in H1; destruct (n =? n0) eqn:P; congruence); auto.
  - simpl in H1. destruct (n =? n0) eqn:P.
    + inversion H1. subst. unfold svar_is_fresh_in in H. simpl in H. apply not_elem_of_singleton_1 in H.
      congruence.
    + congruence.
  - inversion H1. destruct (n0 =? n1) eqn:P.
    + inversion H3.
    + assumption.
  - simpl in H1. destruct (n =? n0) eqn:P.
    + inversion H1. subst. unfold svar_is_fresh_in in H0. simpl in H0. apply not_elem_of_singleton_1 in H0.
      congruence.
    + congruence.
  - simpl in H1. destruct (n =? n1) eqn:P; destruct (n0 =? n1) eqn:P2.
    + inversion H1. 
    + congruence.
    + congruence.
    + inversion H1.
  - simpl in H1. destruct (n =? n1) eqn:P; destruct (n0 =? n1) eqn:P2.
    + apply Nat.eqb_eq in P. apply Nat.eqb_eq in P2. subst. reflexivity.
    + congruence.
    + congruence.
    + inversion H1. reflexivity.
  - inversion H1. apply IHphi1 in H3. apply IHphi2 in H4. subst. reflexivity.
    apply svar_is_fresh_in_app_r in H. assumption.
    apply svar_is_fresh_in_app_r in H0. assumption.
    apply svar_is_fresh_in_app_l in H. assumption.
    apply svar_is_fresh_in_app_l in H0. assumption.
  - inversion H1. apply IHphi1 in H3. apply IHphi2 in H4. subst. reflexivity.
    apply svar_is_fresh_in_imp_r in H. assumption.
    apply svar_is_fresh_in_imp_r in H0. assumption.
    apply svar_is_fresh_in_imp_l in H. assumption.
    apply svar_is_fresh_in_imp_l in H0. assumption.
  - inversion H1. apply IHphi in H3. subst. reflexivity.
    apply svar_is_fresh_in_exists in H. assumption.
    apply svar_is_fresh_in_exists in H0. assumption.
  - inversion H1. apply IHphi in H3. subst. reflexivity.
    apply svar_is_fresh_in_mu in H. assumption.
    apply svar_is_fresh_in_mu in H0. assumption.
Qed.

Lemma evar_open_free_svar_subst_comm: ∀ sz phi psi fresh n X,
  (le (Syntax.size phi) sz) → (well_formed_closed psi) → evar_is_fresh_in fresh phi →
  evar_is_fresh_in fresh (free_svar_subst phi psi X)
  →
  (evar_open n fresh (free_svar_subst phi psi X)) = (free_svar_subst (evar_open n fresh phi) psi X).
Proof.
  induction sz; destruct phi; intros psi fresh n0 X Hsz Hwf Hfresh1 Hfresh2; try inversion Hsz; auto.
  - simpl. destruct (ssrbool.is_left (svar_eqdec X x)) eqn:P.
    + rewrite -> evar_open_fresh. reflexivity. assumption.
    + simpl. reflexivity.
  - simpl. destruct (n =? n0) eqn:P.
    + reflexivity.
    + reflexivity.
  - simpl. rewrite -> IHsz; try lia; try assumption. rewrite -> IHsz; try lia; try assumption.
    reflexivity. apply (evar_is_fresh_in_app_r Hfresh1). simpl in Hfresh2.
    apply (evar_is_fresh_in_app_r Hfresh2). apply (evar_is_fresh_in_app_l Hfresh1).
    apply (evar_is_fresh_in_app_l Hfresh2).
  - simpl. rewrite -> IHsz; try lia; try assumption. rewrite -> IHsz; try lia; try assumption.
    reflexivity. apply (evar_is_fresh_in_imp_r Hfresh1).
    apply (evar_is_fresh_in_imp_r Hfresh2). apply (evar_is_fresh_in_imp_l Hfresh1).
    apply (evar_is_fresh_in_imp_l Hfresh2).
  - simpl. rewrite -> IHsz. reflexivity. lia. assumption.
    apply evar_is_fresh_in_exists in Hfresh1. assumption.
    simpl in Hfresh2. apply evar_is_fresh_in_exists in Hfresh1. assumption.
  - simpl. rewrite -> IHsz. reflexivity.
    lia. assumption. apply evar_is_fresh_in_mu in Hfresh1. assumption.
    simpl in Hfresh2. apply evar_is_fresh_in_mu in Hfresh2. assumption.
Qed.

Lemma svar_open_free_svar_subst_comm {m : Model}: ∀ sz phi psi fresh n X,
  (le (Syntax.size phi) sz) → (well_formed_closed psi) (* → well_formed_closed (svar_open n fresh phi)  *)→  
  svar_is_fresh_in fresh phi → svar_is_fresh_in fresh (free_svar_subst phi psi X) → (fresh ≠ X) 
  →
  (svar_open n fresh (free_svar_subst phi psi X)) = 
  (free_svar_subst (svar_open n fresh phi) psi X).
Proof.
  induction sz; destruct phi; intros psi fresh n0 X Hsz Hwf (* Hwfc *) Hfresh1 Hfresh2 Hneq; try inversion Hsz; auto.
  - simpl. destruct (ssrbool.is_left (svar_eqdec X x)) eqn:P.
    + rewrite -> svar_open_fresh. reflexivity. assumption.
    + simpl. reflexivity.
  - (* simpl in Hwfc. *) simpl. destruct (n =? n0) eqn:P.
    + simpl. destruct (svar_eqdec X fresh) eqn:D.
      * rewrite -> e in Hneq. assert (fresh = fresh). reflexivity. contradiction.
      * reflexivity.
    + simpl. reflexivity.
  - simpl. (* simpl in Hwfc. apply wfc_wfc_ind in Hwfc. inversion Hwfc. *)
    rewrite -> IHsz; try lia; try assumption. rewrite -> IHsz; try lia; try assumption.
    reflexivity. (* apply wfc_ind_wfc. assumption. *)
    simpl in Hfresh1. apply svar_is_fresh_in_app_r in Hfresh1. assumption.
    simpl in Hfresh2. apply svar_is_fresh_in_app_r in Hfresh2. assumption.
    (*apply wfc_ind_wfc. assumption. *)
    simpl in Hfresh1. apply svar_is_fresh_in_app_l in Hfresh1. assumption.
    simpl in Hfresh2. apply svar_is_fresh_in_app_l in Hfresh2. assumption.
  - simpl. (*  simpl in Hwfc. apply wfc_wfc_ind in Hwfc. inversion Hwfc. *)
    rewrite -> IHsz; try lia; try assumption. rewrite -> IHsz; try lia; try assumption.
    reflexivity. 
    (* apply wfc_ind_wfc. assumption. *)
    simpl in Hfresh1. apply svar_is_fresh_in_app_r in Hfresh1. assumption.
    simpl in Hfresh2. apply svar_is_fresh_in_app_r in Hfresh2. assumption.
    (* apply wfc_ind_wfc. assumption. *)
    simpl in Hfresh1. apply svar_is_fresh_in_app_l in Hfresh1. assumption.
    simpl in Hfresh2. apply svar_is_fresh_in_app_l in Hfresh2. assumption.
  - remember ((free_evars (svar_open n0 fresh (free_svar_subst phi psi X))) ∪
      (free_evars (free_svar_subst (svar_open n0 fresh phi) psi X))) as B.
    simpl. remember (@evar_fresh (@variables signature) (elements B)) as x.
    assert(x ∉ B).
      {
        subst. apply set_evar_fresh_is_fresh'.
      }
      subst B.  apply not_elem_of_union in H. destruct H.
    (*magic happens*)
    erewrite (evar_open_inj (svar_open n0 fresh (free_svar_subst phi psi X)) (free_svar_subst (svar_open n0 fresh phi) psi X) x 0 _ _ ).
    reflexivity.
    (*x needs to be fresh in ...*)
     rewrite -> IHsz. reflexivity. lia. assumption. simpl in Hfresh2. apply svar_is_fresh_in_exists in Hfresh1. assumption.
     apply svar_is_fresh_in_exists in Hfresh2. assumption. assumption.
  - remember ((free_svars (svar_open (n0 + 1) fresh (free_svar_subst phi psi X)) ∪
      (free_svars (free_svar_subst (svar_open (n0 + 1) fresh phi) psi X)))) as B.
    simpl. remember (@svar_fresh (@variables signature) (elements B)) as X'.
    assert(X' ∉ B).
      {
        subst. apply set_svar_fresh_is_fresh'.
      }
      subst B.  apply not_elem_of_union in H. destruct H.
    simpl.
    (*magic happens*)
    erewrite (svar_open_inj (svar_open (n0+1) fresh (free_svar_subst phi psi X)) (free_svar_subst (svar_open (n0+1) fresh phi) psi X) X' 0 _ _ ).
    reflexivity.
    (*x needs to be fresh in ...*)
     rewrite -> IHsz. reflexivity. lia. assumption. simpl in Hfresh2. assumption. assumption. assumption.
     Unshelve.
     {
      unfold evar_is_fresh_in. assumption.
     }
     {
      unfold evar_is_fresh_in. assumption.
     }
     {
      unfold evar_is_fresh_in. assumption.
     }
     {
      unfold evar_is_fresh_in. assumption.
     }
Qed.

Lemma free_svar_subst_update_exchange {m : Model}: ∀ sz phi psi X svar_val evar_val,
  le (Syntax.size phi) sz → well_formed psi → well_formed_closed phi → 
  pattern_interpretation evar_val svar_val (free_svar_subst phi psi X) =
  pattern_interpretation evar_val (@update_svar_val signature m X 
                                  (pattern_interpretation evar_val svar_val psi) svar_val) 
                                  phi.
Proof. 
  induction sz; destruct phi; intros psi X svar_val evar_val Hsz Hwf Hwfc ; simpl in *; try inversion Hsz;
  apply wfc_wfc_ind in Hwfc; auto.
  - rewrite -> pattern_interpretation_free_svar_simpl. unfold update_svar_val.
    destruct (ssrbool.is_left (svar_eqdec X x)) eqn:P.
    + reflexivity.
    + rewrite -> pattern_interpretation_free_svar_simpl. reflexivity.
  - rewrite -> pattern_interpretation_free_svar_simpl. unfold update_svar_val.
    destruct (ssrbool.is_left (svar_eqdec X x)) eqn:P.
    + reflexivity.
    + rewrite -> pattern_interpretation_free_svar_simpl. reflexivity.
  - repeat rewrite -> pattern_interpretation_app_simpl.
    erewrite -> IHsz. erewrite -> IHsz. reflexivity. lia. assumption.
    apply wfc_ind_wfc. inversion Hwfc. assumption. lia. assumption.
    apply wfc_ind_wfc. inversion Hwfc. assumption.
  - repeat rewrite -> pattern_interpretation_app_simpl.
    erewrite -> IHsz. erewrite -> IHsz. reflexivity. lia. assumption.
    apply wfc_ind_wfc. inversion Hwfc. assumption. lia. assumption.
    apply wfc_ind_wfc. inversion Hwfc. assumption.
  - repeat rewrite -> pattern_interpretation_imp_simpl.
    erewrite -> IHsz. erewrite -> IHsz. reflexivity. lia. assumption.
    apply wfc_ind_wfc. inversion Hwfc. assumption. lia. assumption.
    apply wfc_ind_wfc. inversion Hwfc. assumption.
  - repeat rewrite -> pattern_interpretation_imp_simpl.
    erewrite -> IHsz. erewrite -> IHsz. reflexivity. lia. assumption.
    apply wfc_ind_wfc. inversion Hwfc. assumption. lia. assumption.
    apply wfc_ind_wfc. inversion Hwfc. assumption.
  - repeat rewrite -> pattern_interpretation_ex_simpl. simpl.
    apply Extensionality_Ensembles. apply FA_Union_same. intros.
    unfold Same_set, Included, In. split.
    + intros.
      remember ((free_evars (free_svar_subst phi psi X)) ∪ (free_evars phi) ∪ (free_evars psi)) as B.
      remember (@evar_fresh (@variables signature) (elements B)) as fresh.
      assert(evar_is_fresh_in (fresh_evar (free_svar_subst phi psi X)) (free_svar_subst phi psi X)).
      {
        apply set_evar_fresh_is_fresh.
      }
      assert(fresh ∉ B).
      {
        subst. apply set_evar_fresh_is_fresh'.
      }
      subst fresh. subst B. apply not_elem_of_union in H2. destruct H2.
      apply not_elem_of_union in H2. destruct H2.
      remember ((free_evars (free_svar_subst phi psi X)) ∪ (free_evars phi) ∪ (free_evars psi)) as B.
      remember (@evar_fresh (@variables signature) (elements B)) as fresh.
      assert(evar_is_fresh_in fresh (free_svar_subst phi psi X)).
      {
        unfold evar_is_fresh_in. assumption.
      }
      epose (interpretation_fresh_evar_open c 0 evar_val svar_val
             H1 H2) as HFresh.
      rewrite -> HFresh in H.
      clear HFresh.
      assert(evar_is_fresh_in fresh phi).
      {
        unfold evar_is_fresh_in. assumption.
      }
      assert(evar_is_fresh_in (fresh_evar phi) phi).
      {
        apply set_evar_fresh_is_fresh.
      }
      epose (interpretation_fresh_evar_open c 0 evar_val (update_svar_val X (pattern_interpretation evar_val svar_val psi) svar_val)
             _ _) as HFresh.
      rewrite -> HFresh.
      clear HFresh.
      epose (IHsz (evar_open 0 fresh phi) 
                           psi X svar_val 
                          (update_evar_val fresh c evar_val) _ _ ).
      pose (@pattern_interpretation_free_evar_independent signature m evar_val svar_val fresh c psi).
      rewrite -> e0 in e. clear e0.
      rewrite -> (evar_open_free_svar_subst_comm (Syntax.size phi)) in H.
      rewrite -> e in H.
      exact H. inversion Hwfc. apply wfc_ind_wfc. eapply (H9 fresh). 
      unfold evar_is_fresh_in in H6. assumption. lia. destruct Hwf. assumption. assumption.
      assumption. assumption.
    + intros.
      remember ((free_evars (free_svar_subst phi psi X)) ∪ (free_evars phi) ∪ (free_evars psi)) as B.
      remember (@evar_fresh (@variables signature) (elements B)) as fresh.
      assert(evar_is_fresh_in (fresh_evar (free_svar_subst phi psi X)) (free_svar_subst phi psi X)).
      {
        apply set_evar_fresh_is_fresh.
      }
      assert(fresh ∉ B).
      {
        subst. apply set_evar_fresh_is_fresh'.
      }
      subst fresh. subst B. apply not_elem_of_union in H2. destruct H2.
      apply not_elem_of_union in H2. destruct H2.
      remember ((free_evars (free_svar_subst phi psi X)) ∪ (free_evars phi) ∪ (free_evars psi)) as B.
      remember (@evar_fresh (@variables signature) (elements B)) as fresh.
      assert(evar_is_fresh_in fresh (free_svar_subst phi psi X)).
      {
        unfold evar_is_fresh_in. assumption.
      }
      epose (interpretation_fresh_evar_open c 0 evar_val svar_val
             H1 H2) as HFresh.
      rewrite -> HFresh.
      clear HFresh.
      assert(evar_is_fresh_in fresh phi).
      {
        unfold evar_is_fresh_in. assumption.
      }
      assert(evar_is_fresh_in (fresh_evar phi) phi).
      {
        apply set_evar_fresh_is_fresh.
      }
      epose (interpretation_fresh_evar_open c 0 evar_val (update_svar_val X (pattern_interpretation evar_val svar_val psi) svar_val)
             _ _) as HFresh.
      rewrite -> HFresh in H.
      clear HFresh.
      epose (IHsz (evar_open 0 fresh phi) 
                           psi X svar_val 
                          (update_evar_val fresh c evar_val) _ _ ).
      pose (@pattern_interpretation_free_evar_independent signature m evar_val svar_val fresh c psi).
      rewrite -> e0 in e. clear e0.
      rewrite -> (evar_open_free_svar_subst_comm (Syntax.size phi)).
      rewrite -> e.
      exact H. inversion Hwfc. apply wfc_ind_wfc. eapply (H9 fresh). 
      unfold evar_is_fresh_in in H6. assumption.
      lia. destruct Hwf. assumption. assumption. assumption. assumption.
  - repeat rewrite -> pattern_interpretation_ex_simpl. simpl.
    apply Extensionality_Ensembles. apply FA_Union_same. intros.
    unfold Same_set, Included, In. split.
    + intros.
      remember ((free_evars (free_svar_subst phi psi X)) ∪ (free_evars phi) ∪ (free_evars psi)) as B.
      remember (@evar_fresh (@variables signature) (elements B)) as fresh.
      assert(evar_is_fresh_in (fresh_evar (free_svar_subst phi psi X)) (free_svar_subst phi psi X)).
      {
        apply set_evar_fresh_is_fresh.
      }
      assert(fresh ∉ B).
      {
        subst. apply set_evar_fresh_is_fresh'.
      }
      subst fresh. subst B. apply not_elem_of_union in H3. destruct H3.
      apply not_elem_of_union in H3. destruct H3.
      remember ((free_evars (free_svar_subst phi psi X)) ∪ (free_evars phi) ∪ (free_evars psi)) as B.
      remember (@evar_fresh (@variables signature) (elements B)) as fresh.
      assert(evar_is_fresh_in fresh (free_svar_subst phi psi X)).
      {
        unfold evar_is_fresh_in. assumption.
      }
      epose (interpretation_fresh_evar_open c 0 evar_val svar_val
             H2 H3) as HFresh.
      rewrite -> HFresh in H1.
      clear HFresh.
      assert(evar_is_fresh_in fresh phi).
      {
        unfold evar_is_fresh_in. assumption.
      }
      assert(evar_is_fresh_in (fresh_evar phi) phi).
      {
        apply set_evar_fresh_is_fresh.
      }
      epose (interpretation_fresh_evar_open c 0 evar_val (update_svar_val X (pattern_interpretation evar_val svar_val psi) svar_val)
             _ _) as HFresh.
      rewrite -> HFresh.
      clear HFresh.
      epose (IHsz (evar_open 0 fresh phi) 
                           psi X svar_val 
                          (update_evar_val fresh c evar_val) _ _ ).
      pose (@pattern_interpretation_free_evar_independent signature m evar_val svar_val fresh c psi).
      rewrite -> e0 in e. clear e0.
      rewrite -> (evar_open_free_svar_subst_comm (Syntax.size phi)) in H1.
      rewrite -> e in H1.
      exact H1. inversion Hwfc. apply wfc_ind_wfc. eapply (H10 fresh). 
      unfold evar_is_fresh_in in H6. assumption.
      lia. destruct Hwf. assumption. assumption. assumption. assumption.
    + intros.
      remember ((free_evars (free_svar_subst phi psi X)) ∪ (free_evars phi) ∪ (free_evars psi)) as B.
      remember (@evar_fresh (@variables signature) (elements B)) as fresh.
      assert(evar_is_fresh_in (fresh_evar (free_svar_subst phi psi X)) (free_svar_subst phi psi X)).
      {
        apply set_evar_fresh_is_fresh.
      }
      assert(fresh ∉ B).
      {
        subst. apply set_evar_fresh_is_fresh'.
      }
      subst fresh. subst B. apply not_elem_of_union in H3. destruct H3.
      apply not_elem_of_union in H3. destruct H3.
      remember ((free_evars (free_svar_subst phi psi X)) ∪ (free_evars phi) ∪ (free_evars psi)) as B.
      remember (@evar_fresh (@variables signature) (elements B)) as fresh.
      assert(evar_is_fresh_in fresh (free_svar_subst phi psi X)).
      {
        unfold evar_is_fresh_in. assumption.
      }
      epose (interpretation_fresh_evar_open c 0 evar_val svar_val
             H2 H3) as HFresh.
      rewrite -> HFresh.
      clear HFresh.
      assert(evar_is_fresh_in fresh phi).
      {
        unfold evar_is_fresh_in. assumption.
      }
      assert(evar_is_fresh_in (fresh_evar phi) phi).
      {
        apply set_evar_fresh_is_fresh.
      }
      epose (interpretation_fresh_evar_open c 0 evar_val (update_svar_val X (pattern_interpretation evar_val svar_val psi) svar_val)
             _ _) as HFresh.
      rewrite -> HFresh in H1.
      clear HFresh.
      epose (IHsz (evar_open 0 fresh phi) 
                           psi X svar_val 
                          (update_evar_val fresh c evar_val) _ _ ).
      pose (@pattern_interpretation_free_evar_independent signature m evar_val svar_val fresh c psi).
      rewrite -> e0 in e. clear e0.
      rewrite -> (evar_open_free_svar_subst_comm (Syntax.size phi)).
      rewrite -> e.
      exact H1. inversion Hwfc. apply wfc_ind_wfc. eapply (H10 fresh). 
      unfold evar_is_fresh_in in H6. assumption.
      lia. destruct Hwf. assumption. assumption. assumption. assumption.
  - repeat rewrite -> pattern_interpretation_mu_simpl. simpl.
    assert ((λ S : Ensemble (Domain m),
     pattern_interpretation evar_val
       (update_svar_val (fresh_svar (free_svar_subst phi psi X)) S svar_val)
       (svar_open 0 (fresh_svar (free_svar_subst phi psi X)) (free_svar_subst phi psi X))) =
       (λ S : Ensemble (Domain m),
     pattern_interpretation evar_val
       (update_svar_val (fresh_svar phi) S
          (update_svar_val X (pattern_interpretation evar_val svar_val psi) svar_val))
       (svar_open 0 (fresh_svar phi) phi))).
       apply functional_extensionality. intros.
    + (*Create a common fresh var.*)
      remember ((free_svars phi) ∪ (free_svars psi) ∪ (free_svars (free_svar_subst phi psi X)) ∪ 
      (free_svars (patt_free_svar X))) as B.
      remember (@svar_fresh (@variables signature) (elements B)) as MuZ.
      remember (fresh_svar phi) as MuX.
      remember (fresh_svar (free_svar_subst phi psi X)) as MuY.
      assert(MuZ ∉ B).
      {
        subst. apply set_svar_fresh_is_fresh'.
      }
      subst B. apply not_elem_of_union in H. destruct H.
      apply not_elem_of_union in H. destruct H.
      apply not_elem_of_union in H. destruct H.
      
      erewrite (@interpretation_fresh_svar_open _ _ _ MuX MuZ); try assumption.
      erewrite (@interpretation_fresh_svar_open _ _ _ MuY MuZ); try assumption.
      erewrite -> svar_open_free_svar_subst_comm; try assumption.
      rewrite update_svar_val_comm; try assumption. 
      epose (IHsz (svar_open 0 MuZ phi) psi X 
      (update_svar_val MuZ x svar_val) evar_val _ _ ).
      rewrite e. 
      erewrite (@pattern_interpretation_free_svar_independent _ _ _ _ MuZ x psi); 
      try assumption.
      reflexivity.
      {
        inversion Hwfc. pose (H5 MuZ H). apply wfc_ind_wfc in w. assumption.
      }
      {
        simpl in H1. apply not_elem_of_singleton_1 in H1. assumption.
      }
      reflexivity. destruct Hwf. assumption.
      {
        simpl in H1. apply not_elem_of_singleton_1 in H1. assumption.
      }
      {
        subst MuY. apply set_svar_fresh_is_fresh.
      }
      {
        subst MuX. apply set_svar_fresh_is_fresh.
      }
    + rewrite H. reflexivity.
  - repeat rewrite -> pattern_interpretation_mu_simpl. simpl.
    assert ((λ S : Ensemble (Domain m),
     pattern_interpretation evar_val
       (update_svar_val (fresh_svar (free_svar_subst phi psi X)) S svar_val)
       (svar_open 0 (fresh_svar (free_svar_subst phi psi X)) (free_svar_subst phi psi X))) =
       (λ S : Ensemble (Domain m),
     pattern_interpretation evar_val
       (update_svar_val (fresh_svar phi) S
          (update_svar_val X (pattern_interpretation evar_val svar_val psi) svar_val))
       (svar_open 0 (fresh_svar phi) phi))).
       apply functional_extensionality. intros.
    + (*Create a common fresh var.*)
      remember ((free_svars phi) ∪ (free_svars psi) ∪ (free_svars (free_svar_subst phi psi X)) ∪ 
      (free_svars (patt_free_svar X))) as B.
      remember (@svar_fresh (@variables signature) (elements B)) as MuZ.
      remember (fresh_svar phi) as MuX.
      remember (fresh_svar (free_svar_subst phi psi X)) as MuY.
      assert(MuZ ∉ B).
      {
        subst. apply set_svar_fresh_is_fresh'.
      }
      subst B. apply not_elem_of_union in H1. destruct H1.
      apply not_elem_of_union in H1. destruct H1.
      apply not_elem_of_union in H1. destruct H1.
      
      erewrite (@interpretation_fresh_svar_open _ _ _ MuX MuZ); try assumption.
      erewrite (@interpretation_fresh_svar_open _ _ _ MuY MuZ); try assumption.
      erewrite -> svar_open_free_svar_subst_comm; try assumption.
      rewrite update_svar_val_comm; try assumption. 
      epose (IHsz (svar_open 0 MuZ phi) psi X 
      (update_svar_val MuZ x svar_val) evar_val _ _ ).
      rewrite e. 
      erewrite (@pattern_interpretation_free_svar_independent _ _ _ _ MuZ x psi); 
      try assumption.
      reflexivity.
      {
        inversion Hwfc. pose (H6 MuZ H1). apply wfc_ind_wfc in w. assumption.
      }
      {
        simpl in H2. apply not_elem_of_singleton_1 in H2. assumption.
      }
      reflexivity. destruct Hwf. assumption.
      {
        simpl in H2. apply not_elem_of_singleton_1 in H2. assumption.
      }
      {
        subst MuY. apply set_svar_fresh_is_fresh.
      }
      {
        subst MuX. apply set_svar_fresh_is_fresh.
      }
    + rewrite H1. reflexivity.
    Unshelve. 
    apply set_evar_fresh_is_fresh.
    assumption.
    {
      subst sz. erewrite <- evar_open_size. reflexivity.
    }
    assumption. apply set_evar_fresh_is_fresh. assumption.
    {
      subst sz. erewrite <- evar_open_size. reflexivity.
    }
    assumption. apply set_evar_fresh_is_fresh. assumption.
    {
      erewrite <- evar_open_size. lia.
    }
    assumption. apply set_evar_fresh_is_fresh. assumption.
    {
      erewrite <- evar_open_size. lia.
    }
    assumption. exact m.
    {
      subst sz. erewrite <- svar_open_size. reflexivity.
    }
    assumption. exact m. 
    {
      erewrite <- svar_open_size. lia.
    }
    assumption.
Qed.

Lemma proof_rule_set_var_subst_sound {m : Model}:
  ∀ phi psi,
  well_formed_closed phi  → well_formed psi →
        (∀ (evar_val : evar → Domain m) (svar_val : svar → Power (Domain m)),
         pattern_interpretation evar_val svar_val phi = Full)
  →
  ∀ X evar_val svar_val,
  @pattern_interpretation signature m evar_val svar_val (free_svar_subst phi psi X) = Full.
Proof.
  intros. pose (H1 evar_val (update_svar_val X 
                                  (pattern_interpretation evar_val svar_val psi) svar_val)).
  erewrite <- free_svar_subst_update_exchange in e. exact e. reflexivity. assumption. unfold well_formed in H. assumption.
Qed.

  
  (* Proof system for AML ref. snapshot: Section 3 *)
  (* TODO: all propagation rules, framing, use left and right rules (no contexts) like in bott *)
  (* TODO: add well-formedness of theory *)
  (* TODO: use well-formedness as parameter in proof system *)

  Reserved Notation "theory ⊢ pattern" (at level 1).
  Inductive ML_proof_system (theory : Theory) :
    Pattern -> Prop :=

  (* Hypothesis *)
  | hypothesis (axiom : Pattern) :
      well_formed axiom ->
      (Ensembles.In _ theory axiom) -> theory ⊢ axiom
                                              
  (* FOL reasoning *)
  (* Propositional tautology *)
  | P1 (phi psi : Pattern) :
      well_formed phi -> well_formed psi ->
      theory ⊢ (phi ---> (psi ---> phi))
  | P2 (phi psi xi : Pattern) :
      well_formed phi -> well_formed psi -> well_formed xi ->
      theory ⊢ ((phi ---> (psi ---> xi)) ---> ((phi ---> psi) ---> (phi ---> xi)))
  | P3 (phi : Pattern) :
      well_formed phi ->
      theory ⊢ (((phi ---> Bot) ---> Bot) ---> phi)

  (* Modus ponens *)
  | Modus_ponens (phi1 phi2 : Pattern) :
      well_formed phi1 -> well_formed (phi1 ---> phi2) ->
      theory ⊢ phi1 ->
      theory ⊢ (phi1 ---> phi2) ->
      theory ⊢ phi2

  (* Existential quantifier *)
  | Ex_quan (phi : Pattern) (y : evar) :
      well_formed phi ->
      theory ⊢ (instantiate (patt_exists phi) (patt_free_evar y) ---> (patt_exists phi))

  (* Existential generalization *)
  | Ex_gen (phi1 phi2 : Pattern) (x : evar) :
      well_formed phi1 -> well_formed phi2 ->
      theory ⊢ (phi1 ---> phi2) ->
      x ∉ (free_evars phi2) ->
      theory ⊢ (exists_quantify x phi1 ---> phi2)

  (* Frame reasoning *)
  (* Propagation bottom *)
  | Prop_bott_left (phi : Pattern) :
      well_formed phi ->
      theory ⊢ (patt_bott $ phi ---> patt_bott)

  | Prop_bott_right (phi : Pattern) :
      well_formed phi ->
      theory ⊢ (phi $ patt_bott ---> patt_bott)

  (* Propagation disjunction *)
  | Prop_disj_left (phi1 phi2 psi : Pattern) :
      well_formed phi1 -> well_formed phi2 -> well_formed psi ->
      theory ⊢ (((phi1 or phi2) $ psi) ---> ((phi1 $ psi) or (phi2 $ psi)))

  | Prop_disj_right (phi1 phi2 psi : Pattern) :
      well_formed phi1 -> well_formed phi2 -> well_formed psi ->
      theory ⊢ ((psi $ (phi1 or phi2)) ---> ((psi $ phi1) or (psi $ phi2)))

  (* Propagation exist *)
  | Prop_ex_left (phi psi : Pattern) :
      well_formed (ex , phi) -> well_formed psi ->
      theory ⊢ (((ex , phi) $ psi) ---> (ex , phi $ psi))

  | Prop_ex_right (phi psi : Pattern) :
      well_formed (ex , phi) -> well_formed psi ->
      theory ⊢ ((psi $ (ex , phi)) ---> (ex , psi $ phi))

  (* Framing *)
  | Framing_left (phi1 phi2 psi : Pattern) :
      theory ⊢ (phi1 ---> phi2) ->
      theory ⊢ ((phi1 $ psi) ---> (phi2 $ psi))

  | Framing_right (phi1 phi2 psi : Pattern) :
      theory ⊢ (phi1 ---> phi2) ->
      theory ⊢ ((psi $ phi1) ---> (psi $ phi2))

  (* Fixpoint reasoning *)
  (* Set Variable Substitution *)
  | Svar_subst (phi psi : Pattern) (X : svar) :
      well_formed phi -> well_formed psi ->
      theory ⊢ phi -> theory ⊢ (free_svar_subst phi psi X)

  (* Pre-Fixpoint *)
  (* TODO: is this correct? *)
  | Pre_fixp (phi : Pattern) :
      theory ⊢ (instantiate (patt_mu phi) (patt_mu phi) ---> (patt_mu phi))

  (* Knaster-Tarski *)
  | Knaster_tarski (phi psi : Pattern) :
      theory ⊢ ((instantiate (patt_mu phi) psi) ---> psi) ->
      theory ⊢ ((@patt_mu signature phi) ---> psi)

  (* Technical rules *)
  (* Existence *)
  | Existence : theory ⊢ (ex , patt_bound_evar 0)

  (* Singleton *)
  | Singleton_ctx (C1 C2 : Application_context) (phi : Pattern) (x : evar) : 
      theory ⊢ (¬ ((subst_ctx C1 (patt_free_evar x and phi)) and
                                                             (subst_ctx C2 (patt_free_evar x and (¬ phi)))))

  where "theory ⊢ pattern" := (ML_proof_system theory pattern).

  Notation "G |= phi" := (@satisfies signature G phi) (left associativity, at level 50).
  (* Soundness theorem *)
Theorem Soundness :
  forall phi : Pattern, forall theory : Theory,
  well_formed phi -> (theory ⊢ phi) -> (theory |= phi).
Proof.
  intros phi theory Hwf Hp. unfold satisfies, satisfies_theory, satisfies_model.
  intros m Hv evar_val svar_val. 
  generalize dependent svar_val. generalize dependent evar_val. generalize dependent Hv.
  induction Hp.

  * intros Hv evar_val svar_val. apply Hv. assumption.

  * intros Hv evar_val svar_val.
    repeat rewrite -> pattern_interpretation_imp_simpl.
    remember (pattern_interpretation evar_val svar_val phi) as Xphi.
    remember (pattern_interpretation evar_val svar_val psi) as Xpsi.
    apply Extensionality_Ensembles.
    constructor. constructor.
    assert (Ensembles.Union (Domain m) (Complement (Domain m) Xphi) Xphi = Full_set (Domain m)).
    apply Same_set_to_eq. apply Union_Compl_Fullset. unfold Full. rewrite <- H1; clear H1.
    unfold Included; intros; apply Union_is_or.
    inversion H1. left. assumption. right. apply Union_intror. assumption.

  * intros Hv evar_val svar_val.
    repeat rewrite -> pattern_interpretation_imp_simpl.
    remember (pattern_interpretation evar_val svar_val phi) as Xphi.
    remember (pattern_interpretation evar_val svar_val psi) as Xpsi.
    remember (pattern_interpretation evar_val svar_val xi) as Xxi.
    pose proof Compl_Union_Intes_Compl_Ensembles; eapply Same_set_to_eq in H2; rewrite -> H2; clear H2.
    pose proof Compl_Union_Intes_Compl_Ensembles; eapply Same_set_to_eq in H2; rewrite -> H2; clear H2.
    pose proof Compl_Compl_Ensembles; eapply Same_set_to_eq in H2; rewrite -> H2; clear H2.
    pose proof Compl_Compl_Ensembles; eapply Same_set_to_eq in H2; rewrite -> H2; clear H2.
    pose proof Compl_Union_Intes_Compl_Ensembles; eapply Same_set_to_eq in H2; rewrite -> H2; clear H2.
    pose proof Compl_Compl_Ensembles; eapply Same_set_to_eq in H2; rewrite -> H2; clear H2.
    epose proof Union_Transitive (Ensembles.Intersection (Domain m) Xphi (Complement (Domain m) Xpsi))
          (Complement (Domain m) Xphi) Xxi.
    apply Same_set_to_eq in H2; rewrite <- H2; clear H2.
    pose proof Intes_Union_Compl_Ensembles; eapply Same_set_to_eq in H2; rewrite -> H2; clear H2.
    pose proof Union_Symmetric (Complement (Domain m) Xpsi) (Complement (Domain m) Xphi).
    apply Same_set_to_eq in H2; rewrite -> H2; clear H2.
    epose proof Union_Transitive; eapply Same_set_to_eq in H2; rewrite <- H2; clear H2.
    epose proof Union_Transitive; eapply Same_set_to_eq in H2; rewrite <- H2; clear H2.
    pose proof Intes_Union_Compl_Ensembles; eapply Same_set_to_eq in H2; rewrite -> H2; clear H2.
    epose proof Union_Transitive; eapply Same_set_to_eq in H2; erewrite -> H2; clear H2.
    epose proof Union_Transitive; eapply Same_set_to_eq in H2; erewrite -> H2; clear H2.
    pose proof Union_Symmetric (Complement (Domain m) Xpsi) Xxi.
    apply Same_set_to_eq in H2; erewrite -> H2; clear H2.
    pose proof Union_Transitive (Complement (Domain m) Xphi) Xxi (Complement (Domain m) Xpsi).
    apply Same_set_to_eq in H2; rewrite <- H2; clear H2.
    pose proof Union_Symmetric (Complement (Domain m) Xphi) Xxi.
    apply Same_set_to_eq in H2; erewrite -> H2; clear H2.
    pose proof Compl_Compl_Ensembles (Domain m) Xxi.
    apply Same_set_to_eq in H2; rewrite <- H2 at 2; clear H2.
    pose proof Intersection_Symmetric Xpsi (Complement (Domain m) Xxi).
    apply Same_set_to_eq in H2; erewrite -> H2; clear H2.
    epose proof Union_Transitive; eapply Same_set_to_eq in H2; erewrite <- H2; clear H2.    
    epose proof Union_Transitive; eapply Same_set_to_eq in H2; erewrite <- H2; clear H2.
    pose proof Intes_Union_Compl_Ensembles; eapply Same_set_to_eq in H2; rewrite -> H2; clear H2.
    pose proof Compl_Compl_Ensembles; eapply Same_set_to_eq in H2; rewrite -> H2; clear H2.

    apply Extensionality_Ensembles.
    constructor. constructor.
    assert (Ensembles.Union (Domain m) (Complement (Domain m) Xpsi) Xpsi = Full_set (Domain m)).
    apply Same_set_to_eq. apply Union_Compl_Fullset. unfold Full. rewrite <- H2; clear H2.
    unfold Included; intros; unfold In. inversion H2.
    apply Union_intror; assumption.
    apply Union_introl; apply Union_introl; apply Union_introl; assumption.

  * intros Hv evar_val svar_val. 
    repeat rewrite -> pattern_interpretation_imp_simpl; rewrite -> pattern_interpretation_bott_simpl.
    epose proof Union_Empty_l; eapply Same_set_to_eq in H0; unfold Semantics.Empty; rewrite -> H0; clear H0.
    epose proof Union_Empty_l; eapply Same_set_to_eq in H0; rewrite -> H0; clear H0.
    pose proof Compl_Compl_Ensembles; eapply Same_set_to_eq in H0; rewrite -> H0; clear H0.
    apply Extensionality_Ensembles.
    apply Union_Compl_Fullset.

  * intros Hv evar_val svar_val.
    pose (IHHp2 H0 Hv evar_val svar_val) as e.
    rewrite -> pattern_interpretation_iff_subset in e.
    apply Extensionality_Ensembles.
    constructor. constructor. rewrite <- (IHHp1 H Hv evar_val svar_val). apply e; assumption.

  * intros Hv evar_val svar_val. 
    rewrite -> pattern_interpretation_imp_simpl. rewrite -> pattern_interpretation_ex_simpl.
    unfold instantiate. apply Extensionality_Ensembles.
    constructor. constructor.
    unfold Included; intros. admit.

  * admit.

  * intros Hv evar_val svar_val. 
    rewrite -> pattern_interpretation_imp_simpl, pattern_interpretation_app_simpl, pattern_interpretation_bott_simpl.
    epose proof Union_Empty_l; eapply Same_set_to_eq in H0; unfold Semantics.Empty; rewrite -> H0; clear H0.
    apply Extensionality_Ensembles.
    constructor. constructor.
    unfold Included; intros.
    epose proof app_ext_bot_l; unfold Semantics.Empty in H1; rewrite -> H1; clear H1.
    unfold Ensembles.In; unfold Complement; unfold not; contradiction.

  * intros Hv evar_val svar_val. 
    rewrite -> pattern_interpretation_imp_simpl, pattern_interpretation_app_simpl, pattern_interpretation_bott_simpl.
    epose proof Union_Empty_l; eapply Same_set_to_eq in H0; unfold Semantics.Empty; rewrite -> H0; clear H0.
    apply Extensionality_Ensembles.
    constructor. constructor.
    unfold Included; intros.
    epose proof app_ext_bot_r; unfold Semantics.Empty in H1; rewrite -> H1; clear H1.
    unfold Ensembles.In; unfold Complement; unfold not; contradiction.

  * intros Hv evar_val svar_val. 
    unfold patt_or, patt_not. repeat rewrite -> pattern_interpretation_imp_simpl.
    repeat rewrite -> pattern_interpretation_app_simpl, pattern_interpretation_imp_simpl.
    rewrite -> pattern_interpretation_app_simpl, pattern_interpretation_bott_simpl.
    epose proof Union_Empty_l; eapply Same_set_to_eq in H2; unfold Semantics.Empty; rewrite -> H2; clear H2.
    epose proof Union_Empty_l; eapply Same_set_to_eq in H2; rewrite -> H2; clear H2.
    pose proof Compl_Compl_Ensembles; eapply Same_set_to_eq in H2; rewrite -> H2; clear H2.
    pose proof Compl_Compl_Ensembles; eapply Same_set_to_eq in H2; rewrite -> H2; clear H2.
    remember (pattern_interpretation evar_val svar_val phi1) as Xphi1.
    remember (pattern_interpretation evar_val svar_val phi2) as Xphi2.
    remember (pattern_interpretation evar_val svar_val psi) as Xpsi.
    remember (app_ext (Ensembles.Union (Domain m) Xphi1 Xphi2) Xpsi) as Xext_union.
    apply Extensionality_Ensembles.
    constructor. constructor.
    assert (Ensembles.Union (Domain m) (Complement (Domain m) Xext_union) Xext_union =
            Full_set (Domain m)).
    apply Same_set_to_eq; apply Union_Compl_Fullset. unfold Full. rewrite <- H2; clear H2.
    unfold Included; unfold In; intros. inversion H2.
    - left; assumption.
    - right; subst Xext_union; unfold In; unfold app_ext.
      destruct H3 as [le [re [Hunion [Hre Happ]]]].
      inversion Hunion.
      left. unfold In; exists le; exists re; repeat split; assumption.
      right. unfold In; exists le; exists re; repeat split; assumption.

  * intros Hv evar_val svar_val. 
    unfold patt_or, patt_not. repeat rewrite -> pattern_interpretation_imp_simpl.
    repeat rewrite -> pattern_interpretation_app_simpl, pattern_interpretation_imp_simpl.
    rewrite -> pattern_interpretation_app_simpl, pattern_interpretation_bott_simpl.
    simpl.
    epose proof Union_Empty_l; eapply Same_set_to_eq in H2; unfold Semantics.Empty; rewrite -> H2; clear H2.
    epose proof Union_Empty_l; eapply Same_set_to_eq in H2; rewrite -> H2; clear H2.
    pose proof Compl_Compl_Ensembles; eapply Same_set_to_eq in H2; rewrite -> H2; clear H2.
    pose proof Compl_Compl_Ensembles; eapply Same_set_to_eq in H2; rewrite -> H2; clear H2.
    remember (pattern_interpretation evar_val svar_val phi1) as Xphi1.
    remember (pattern_interpretation evar_val svar_val phi2) as Xphi2.
    remember (pattern_interpretation evar_val svar_val psi) as Xpsi.
    remember (app_ext Xpsi (Ensembles.Union (Domain m) Xphi1 Xphi2)) as Xext_union.
    apply Extensionality_Ensembles.
    constructor. constructor.
    assert (Ensembles.Union (Domain m) (Complement (Domain m) Xext_union) Xext_union =
            Full_set (Domain m)).
    apply Same_set_to_eq; apply Union_Compl_Fullset. unfold Full. rewrite <- H2; clear H2.
    unfold Included; unfold In; intros. inversion H2.
    - left; assumption.
    - right; subst Xext_union; unfold In; unfold app_ext.
      destruct H3 as [le [re [Hle [Hunion Happ]]]].
      inversion Hunion.
      left. unfold In; exists le; exists re; repeat split; assumption.
      right. unfold In; exists le; exists re; repeat split; assumption.

  * intros Hv evar_val svar_val. 
    apply (proof_rule_prop_ex_right_sound theory phi psi (evar_val)
          (svar_val) Hwf H H0 Hv ).

  * intros Hv evar_val svar_val. 
    apply (proof_rule_prop_ex_left_sound theory phi psi (evar_val)
          (svar_val) Hwf H H0 Hv).

  * intros Hv evar_val svar_val. 
    rewrite -> pattern_interpretation_iff_subset.
    epose (IHHp _ Hv evar_val svar_val) as e.
    rewrite -> pattern_interpretation_iff_subset in e.
    repeat rewrite -> pattern_interpretation_app_simpl.
    unfold Included in *; intros; unfold In in *.
    destruct H as [le [re [Hphi1 [Hpsi Happ]]]].
    unfold app_ext.
    exists le, re.
    split. apply e. assumption.
    Unshelve.
    split; assumption.
    {
      inversion Hwf.
      unfold well_formed. split.
      - inversion H. inversion H1. inversion H2. simpl. split; assumption.
      - unfold well_formed_closed. simpl. 
        inversion H0. inversion H1. inversion H2. split; assumption.
    }

  * intros Hv evar_val svar_val.
    rewrite -> pattern_interpretation_iff_subset.
    epose (IHHp _ Hv evar_val svar_val) as e.
    rewrite -> pattern_interpretation_iff_subset in e.
    repeat rewrite -> pattern_interpretation_app_simpl.
    unfold Included in *; intros; unfold In in *.
    destruct H as [le [re [Hphi1 [Hpsi Happ]]]].
    unfold app_ext.
    exists le, re.
    split. assumption.
    Unshelve.
    split. apply e. assumption.
    assumption.
    {
      inversion Hwf.
      unfold well_formed. split.
      - inversion H. inversion H1. inversion H2. simpl. split; assumption.
      - unfold well_formed_closed. simpl. 
        inversion H0. inversion H1. inversion H2. split; assumption.
    }

  * intros. epose (IHHp H Hv ) as IH.
    unfold well_formed in H. destruct H.
    eapply (proof_rule_set_var_subst_sound phi psi w0 H0 ) in IH.
    exact IH.
    
  * intros Hv evar_val svar_val.
    apply pattern_interpretation_iff_subset. simpl.
    rewrite -> pattern_interpretation_mu_simpl.
    simpl.
    remember (fun S : Ensemble (Domain m) =>
                pattern_interpretation evar_val
                                       (update_svar_val (fresh_svar phi) S svar_val)
                                       (svar_open 0 (fresh_svar phi) phi)) as F.
    pose (OS := Lattice.EnsembleOrderedSet (@Domain signature m)).
    pose (L := Lattice.PowersetLattice (@Domain signature m)).
    assert (Ffix : Lattice.isFixpoint F (Lattice.LeastFixpointOf F)).
    { apply Lattice.LeastFixpoint_fixpoint. subst. apply is_monotonic. 
      inversion Hwf. unfold well_formed.
      inversion H. inversion H0. assumption.
      apply set_svar_fresh_is_fresh.
    }
    unfold Lattice.isFixpoint in Ffix.
    assert (Ffix_set : Same_set (Domain m) (F (Lattice.LeastFixpointOf F)) (Lattice.LeastFixpointOf F)).
    { rewrite -> Ffix. apply Same_set_refl. }
    destruct Ffix_set. clear H0.
    eapply Included_transitive.
    2: { apply H. }
    rewrite -> HeqF.
    epose proof (Hsimpl := pattern_interpretation_mu_simpl).
    specialize (Hsimpl evar_val svar_val phi).
    simpl in Hsimpl. subst OS. subst L.
    rewrite <- Hsimpl.
    
    (*Check plugging_patterns.*)
    (*
    simpl. rewrite -> ext_valuation_imp_simpl. rewrite -> ext_valuation_mu_simpl.
    constructor. constructor.
    unfold Included. intros. unfold In.*)
    admit.

  * intros Hv evar_val svar_val.
    rewrite -> pattern_interpretation_imp_simpl. rewrite -> pattern_interpretation_mu_simpl.
    epose (IHHp _ Hv evar_val svar_val) as e.
    simpl in e. rewrite -> pattern_interpretation_imp_simpl in e.
    apply Extensionality_Ensembles.
    constructor. constructor.
    unfold Included. intros.
    destruct e.
    left. unfold In. unfold Complement. unfold not. unfold In. unfold Ensembles_Ext.mu.
    unfold FA_Inters_cond. intros.
    (*
    inversion H0; subst.
    edestruct H1 with x. assumption.
    unfold In, Complement, not in H3. apply H3.
    apply H2. unfold Included. intros.
    unfold In. admit.*)
    admit.

Admitted.

End ml_proof_system.

