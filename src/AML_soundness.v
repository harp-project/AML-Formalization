Require Import Arith.
Require Import ZArith.
Require Import List.
Require Import extralibrary.
Require Import DefaultVariables.
Require Import Signature.
Require Export AML_soundness_lemmas.

Require Import Coq.micromega.Lia.

Require Export String.
Require Export Coq.Lists.ListSet.
Require Export Ensembles_Ext.

Require Export Coq.Program.Wf.

Section soundness.

Context {signature : Signature}.
Notation "G |= phi" := (@satisfies signature G phi) (left associativity, at level 50).
Notation "theory ⊢ pattern" := (@ML_proof_system signature theory pattern) (at level 1, no associativity).

(* Soundness theorem *)
Theorem Soundness :
  forall phi : Pattern, forall theory : Theory,
  well_formed phi -> (theory ⊢ phi) -> (theory |= phi).
Proof.
  intros phi theory Hwf Hp. unfold satisfies, satisfies_theory, satisfies_model.
  intros m Hv evar_val svar_val.
  induction Hp.

  * apply Hv. assumption.

  * repeat rewrite pattern_interpretation_imp_simpl.
    remember (pattern_interpretation evar_val svar_val phi) as Xphi.
    remember (pattern_interpretation evar_val svar_val psi) as Xpsi.
    constructor. constructor.
    assert (Union (Domain m) (Complement (Domain m) Xphi) Xphi = Full_set (Domain m)).
    apply Same_set_to_eq. apply Union_Compl_Fullset. rewrite <- H1; clear H1.
    unfold Included; intros; apply Union_is_or.
    inversion H1. left. assumption. right. apply Union_intror. assumption.

  * repeat rewrite pattern_interpretation_imp_simpl.
    remember (pattern_interpretation evar_val svar_val phi) as Xphi.
    remember (pattern_interpretation evar_val svar_val psi) as Xpsi.
    remember (pattern_interpretation evar_val svar_val xi) as Xxi.
    pose proof Compl_Union_Intes_Compl_Ensembles; eapply Same_set_to_eq in H2; rewrite H2; clear H2.
    pose proof Compl_Union_Intes_Compl_Ensembles; eapply Same_set_to_eq in H2; rewrite H2; clear H2.
    pose proof Compl_Compl_Ensembles; eapply Same_set_to_eq in H2; rewrite H2; clear H2.
    pose proof Compl_Compl_Ensembles; eapply Same_set_to_eq in H2; rewrite H2; clear H2.
    pose proof Compl_Union_Intes_Compl_Ensembles; eapply Same_set_to_eq in H2; rewrite H2; clear H2.
    pose proof Compl_Compl_Ensembles; eapply Same_set_to_eq in H2; rewrite H2; clear H2.
    epose proof Union_Transitive (Intersection (Domain m) Xphi (Complement (Domain m) Xpsi))
          (Complement (Domain m) Xphi) Xxi.
    apply Same_set_to_eq in H2; rewrite <- H2; clear H2.
    pose proof Intes_Union_Compl_Ensembles; eapply Same_set_to_eq in H2; rewrite H2; clear H2.
    pose proof Union_Symmetric (Complement (Domain m) Xpsi) (Complement (Domain m) Xphi).
    apply Same_set_to_eq in H2; rewrite H2; clear H2.
    epose proof Union_Transitive; eapply Same_set_to_eq in H2; rewrite <- H2; clear H2.
    epose proof Union_Transitive; eapply Same_set_to_eq in H2; rewrite <- H2; clear H2.
    pose proof Intes_Union_Compl_Ensembles; eapply Same_set_to_eq in H2; rewrite H2; clear H2.
    epose proof Union_Transitive; eapply Same_set_to_eq in H2; erewrite H2; clear H2.
    epose proof Union_Transitive; eapply Same_set_to_eq in H2; erewrite H2; clear H2.
    pose proof Union_Symmetric (Complement (Domain m) Xpsi) Xxi.
    apply Same_set_to_eq in H2; erewrite H2; clear H2.
    pose proof Union_Transitive (Complement (Domain m) Xphi) Xxi (Complement (Domain m) Xpsi).
    apply Same_set_to_eq in H2; rewrite <- H2; clear H2.
    pose proof Union_Symmetric (Complement (Domain m) Xphi) Xxi.
    apply Same_set_to_eq in H2; erewrite H2; clear H2.
    pose proof Compl_Compl_Ensembles (Domain m) Xxi.
    apply Same_set_to_eq in H2; rewrite <- H2 at 2; clear H2.
    pose proof Intersection_Symmetric Xpsi (Complement (Domain m) Xxi).
    apply Same_set_to_eq in H2; erewrite H2; clear H2.
    epose proof Union_Transitive; eapply Same_set_to_eq in H2; erewrite <- H2; clear H2.    
    epose proof Union_Transitive; eapply Same_set_to_eq in H2; erewrite <- H2; clear H2.
    pose proof Intes_Union_Compl_Ensembles; eapply Same_set_to_eq in H2; rewrite H2; clear H2.
    pose proof Compl_Compl_Ensembles; eapply Same_set_to_eq in H2; rewrite H2; clear H2.

    constructor. constructor.
    assert (Union (Domain m) (Complement (Domain m) Xpsi) Xpsi = Full_set (Domain m)).
    apply Same_set_to_eq. apply Union_Compl_Fullset. rewrite <- H2; clear H2.
    unfold Included; intros; unfold In. inversion H2.
    apply Union_intror; assumption.
    apply Union_introl; apply Union_introl; apply Union_introl; assumption.

  * repeat rewrite pattern_interpretation_imp_simpl; rewrite pattern_interpretation_bott_simpl.
    epose proof Union_Empty_l; eapply Same_set_to_eq in H0; rewrite H0; clear H0.
    epose proof Union_Empty_l; eapply Same_set_to_eq in H0; rewrite H0; clear H0.
    pose proof Compl_Compl_Ensembles; eapply Same_set_to_eq in H0; rewrite H0; clear H0.
    apply Union_Compl_Fullset.

  * rewrite pattern_interpretation_iff_subset in IHHp2.
    apply Same_set_to_eq in IHHp1; try assumption.
    constructor. constructor. rewrite <- IHHp1. apply IHHp2; assumption.

  * rewrite pattern_interpretation_imp_simpl. rewrite pattern_interpretation_ex_simpl.
    unfold instantiate.
    constructor. constructor.
    unfold Included; intros. admit.

  * admit.

  * rewrite pattern_interpretation_imp_simpl, pattern_interpretation_app_simpl, pattern_interpretation_bott_simpl.
    epose proof Union_Empty_l; eapply Same_set_to_eq in H0; rewrite H0; clear H0.
    constructor. constructor.
    unfold Included; intros.
    epose proof app_ext_bot_l; eapply Same_set_to_eq in H1; rewrite H1; clear H1.
    unfold In; unfold Complement; unfold not; contradiction.

  * rewrite pattern_interpretation_imp_simpl, pattern_interpretation_app_simpl, pattern_interpretation_bott_simpl.
    epose proof Union_Empty_l; eapply Same_set_to_eq in H0; rewrite H0; clear H0.
    constructor. constructor.
    unfold Included; intros.
    epose proof app_ext_bot_r; eapply Same_set_to_eq in H1; rewrite H1; clear H1.
    unfold In; unfold Complement; unfold not; contradiction.

  * unfold patt_or, patt_not. repeat rewrite pattern_interpretation_imp_simpl.
    repeat rewrite pattern_interpretation_app_simpl, pattern_interpretation_imp_simpl.
    rewrite pattern_interpretation_app_simpl, pattern_interpretation_bott_simpl.
    epose proof Union_Empty_l; eapply Same_set_to_eq in H2; rewrite H2; clear H2.
    epose proof Union_Empty_l; eapply Same_set_to_eq in H2; rewrite H2; clear H2.
    pose proof Compl_Compl_Ensembles; eapply Same_set_to_eq in H2; rewrite H2; clear H2.
    pose proof Compl_Compl_Ensembles; eapply Same_set_to_eq in H2; rewrite H2; clear H2.
    remember (pattern_interpretation evar_val svar_val phi1) as Xphi1.
    remember (pattern_interpretation evar_val svar_val phi2) as Xphi2.
    remember (pattern_interpretation evar_val svar_val psi) as Xpsi.
    remember (app_ext (Union (Domain m) Xphi1 Xphi2) Xpsi) as Xext_union.
    constructor. constructor.
    assert (Union (Domain m) (Complement (Domain m) Xext_union) Xext_union =
            Full_set (Domain m)).
    apply Same_set_to_eq; apply Union_Compl_Fullset. rewrite <- H2; clear H2.
    unfold Included; unfold In; intros. inversion H2.
    - left; assumption.
    - right; subst Xext_union; unfold In; unfold app_ext.
      destruct H3 as [le [re [Hunion [Hre Happ]]]].
      inversion Hunion.
      left. unfold In; exists le; exists re; repeat split; assumption.
      right. unfold In; exists le; exists re; repeat split; assumption.

  * unfold patt_or, patt_not. repeat rewrite pattern_interpretation_imp_simpl.
    repeat rewrite pattern_interpretation_app_simpl, pattern_interpretation_imp_simpl.
    rewrite pattern_interpretation_app_simpl, pattern_interpretation_bott_simpl.
    simpl.
    epose proof Union_Empty_l; eapply Same_set_to_eq in H2; rewrite H2; clear H2.
    epose proof Union_Empty_l; eapply Same_set_to_eq in H2; rewrite H2; clear H2.
    pose proof Compl_Compl_Ensembles; eapply Same_set_to_eq in H2; rewrite H2; clear H2.
    pose proof Compl_Compl_Ensembles; eapply Same_set_to_eq in H2; rewrite H2; clear H2.
    remember (pattern_interpretation evar_val svar_val phi1) as Xphi1.
    remember (pattern_interpretation evar_val svar_val phi2) as Xphi2.
    remember (pattern_interpretation evar_val svar_val psi) as Xpsi.
    remember (app_ext Xpsi (Union (Domain m) Xphi1 Xphi2)) as Xext_union.
    constructor. constructor.
    assert (Union (Domain m) (Complement (Domain m) Xext_union) Xext_union =
            Full_set (Domain m)).
    apply Same_set_to_eq; apply Union_Compl_Fullset. rewrite <- H2; clear H2.
    unfold Included; unfold In; intros. inversion H2.
    - left; assumption.
    - right; subst Xext_union; unfold In; unfold app_ext.
      destruct H3 as [le [re [Hle [Hunion Happ]]]].
      inversion Hunion.
      left. unfold In; exists le; exists re; repeat split; assumption.
      right. unfold In; exists le; exists re; repeat split; assumption.

  * apply (proof_rule_prop_ex_right_sound theory phi psi (evar_val)
          (svar_val) Hwf H H0 Hv ).

  * apply (proof_rule_prop_ex_left_sound theory phi psi (evar_val)
          (svar_val) Hwf H H0 Hv).

  * rewrite pattern_interpretation_iff_subset.
    rewrite pattern_interpretation_iff_subset in IHHp.
    repeat rewrite pattern_interpretation_app_simpl.
    unfold Included in *; intros; unfold In in *.
    destruct H as [le [re [Hphi1 [Hpsi Happ]]]].
    unfold app_ext.
    exists le, re.
    split. apply IHHp. admit. assumption.
    split; assumption.

  * rewrite pattern_interpretation_iff_subset.
    rewrite pattern_interpretation_iff_subset in IHHp.
    repeat rewrite pattern_interpretation_app_simpl.
    unfold Included in *; intros; unfold In in *.
    destruct H as [le [re [Hphi1 [Hpsi Happ]]]].
    unfold app_ext.
    exists le, re.
    split. assumption.
    split. apply IHHp. admit. assumption.
    assumption.

  * constructor. constructor.
    destruct IHHp. admit.
    clear H. unfold Included in *.
    intros. apply H0 in H. clear H0.
    admit.
    
  * apply pattern_interpretation_iff_subset. simpl.
    rewrite -> pattern_interpretation_mu_simpl.
    Arguments Lattice.LeastFixpointOf : simpl never.
    simpl.
    remember (fun S : Ensemble (Domain m) =>
                pattern_interpretation evar_val
                                       (update_svar_val (fresh_svar phi) S svar_val)
                                       (svar_open 0 (fresh_svar phi) phi)) as F.
    pose (OS := Lattice.EnsembleOrderedSet (@Domain signature m)).
    pose (L := Lattice.PowersetLattice (@Domain signature m)).
    assert (Ffix : Lattice.isFixpoint F (Lattice.LeastFixpointOf F)).
    { apply Lattice.LeastFixpoint_fixpoint. subst. apply is_monotonic.
      inversion Hwf. unfold well_formed. split.
      inversion H. assumption.
      inversion H0. assumption.
    }
    unfold Lattice.isFixpoint in Ffix.
    assert (Ffix_set : Same_set (Domain m) (F (Lattice.LeastFixpointOf F)) (Lattice.LeastFixpointOf F)).
    { rewrite Ffix. apply Same_set_refl. }
    destruct Ffix_set. clear H0.
    eapply Included_transitive.
    2: { apply H. }
    rewrite -> HeqF.
    epose proof (Hsimpl := pattern_interpretation_mu_simpl).
    specialize (Hsimpl evar_val svar_val phi).
    simpl in Hsimpl. subst OS. subst L.
    rewrite <- Hsimpl.
    Check plugging_patterns.
    subst. unfold Included; unfold In; intros.
    unfold update_svar_val. 
    rewrite F- HeqF at 1. 
    
    Print Same_set_to_eq.
    Search Same_set Included.
    Search eq Included.
    assert (Fsub : Included (Domain m) F (Lattice.LeastFixpointOf F)).
    Print Lattice.isFixpoint.
    Search Lattice.Meet.
    Search bvar_subst.
    (*
    simpl. rewrite ext_valuation_imp_simpl. rewrite ext_valuation_mu_simpl.
    constructor. constructor.
    unfold Included. intros. unfold In.*)
    admit.

  * rewrite pattern_interpretation_imp_simpl. rewrite pattern_interpretation_mu_simpl.
    simpl in IHHp. rewrite pattern_interpretation_imp_simpl in IHHp.
    constructor. constructor.
    unfold Included. intros.
    destruct IHHp. admit. clear H0.
    unfold Included in H1.
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

End soundness.
