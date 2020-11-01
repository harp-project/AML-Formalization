Require Import Arith.
Require Import ZArith.
Require Import List.
Require Import extralibrary.
Require Import ML.DefaultVariables.
Require Import ML.Signature.
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

  * repeat rewrite ext_valuation_imp_simpl.
    remember (ext_valuation evar_val svar_val phi) as Xphi.
    remember (ext_valuation evar_val svar_val psi) as Xpsi.
    constructor. constructor.
    assert (Union (Domain m) (Complement (Domain m) Xphi) Xphi = Full_set (Domain m)).
    apply Same_set_to_eq. apply Union_Compl_Fullset. rewrite <- H1; clear H1.
    unfold Included; intros; apply Union_is_or.
    inversion H1. left. assumption. right. apply Union_intror. assumption.

  * repeat rewrite ext_valuation_imp_simpl.
    remember (ext_valuation evar_val svar_val phi) as Xphi.
    remember (ext_valuation evar_val svar_val psi) as Xpsi.
    remember (ext_valuation evar_val svar_val xi) as Xxi.
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

  * repeat rewrite ext_valuation_imp_simpl; rewrite ext_valuation_bott_simpl.
    epose proof Union_Empty_l; eapply Same_set_to_eq in H0; rewrite H0; clear H0.
    epose proof Union_Empty_l; eapply Same_set_to_eq in H0; rewrite H0; clear H0.
    pose proof Compl_Compl_Ensembles; eapply Same_set_to_eq in H0; rewrite H0; clear H0.
    apply Union_Compl_Fullset.

  * rewrite ext_valuation_iff_subset in IHHp2.
    apply Same_set_to_eq in IHHp1; try assumption.
    constructor. constructor. rewrite <- IHHp1. apply IHHp2; assumption.

  * rewrite ext_valuation_imp_simpl. rewrite ext_valuation_ex_simpl.
    unfold instantiate.
    constructor. constructor.
    unfold Included; intros. admit.

  * admit.

  * rewrite ext_valuation_imp_simpl, ext_valuation_app_simpl, ext_valuation_bott_simpl.
    epose proof Union_Empty_l; eapply Same_set_to_eq in H0; rewrite H0; clear H0.
    constructor. constructor.
    unfold Included; intros.
    epose proof pointwise_ext_bot_l; eapply Same_set_to_eq in H1; rewrite H1; clear H1.
    unfold In; unfold Complement; unfold not; contradiction.

  * rewrite ext_valuation_imp_simpl, ext_valuation_app_simpl, ext_valuation_bott_simpl.
    epose proof Union_Empty_l; eapply Same_set_to_eq in H0; rewrite H0; clear H0.
    constructor. constructor.
    unfold Included; intros.
    epose proof pointwise_ext_bot_r; eapply Same_set_to_eq in H1; rewrite H1; clear H1.
    unfold In; unfold Complement; unfold not; contradiction.

  * unfold patt_or, patt_not. repeat rewrite ext_valuation_imp_simpl.
    repeat rewrite ext_valuation_app_simpl, ext_valuation_imp_simpl.
    rewrite ext_valuation_app_simpl, ext_valuation_bott_simpl.
    epose proof Union_Empty_l; eapply Same_set_to_eq in H2; rewrite H2; clear H2.
    epose proof Union_Empty_l; eapply Same_set_to_eq in H2; rewrite H2; clear H2.
    pose proof Compl_Compl_Ensembles; eapply Same_set_to_eq in H2; rewrite H2; clear H2.
    pose proof Compl_Compl_Ensembles; eapply Same_set_to_eq in H2; rewrite H2; clear H2.
    remember (ext_valuation evar_val svar_val phi1) as Xphi1.
    remember (ext_valuation evar_val svar_val phi2) as Xphi2.
    remember (ext_valuation evar_val svar_val psi) as Xpsi.
    remember (pointwise_ext (Union (Domain m) Xphi1 Xphi2) Xpsi) as Xext_union.
    constructor. constructor.
    assert (Union (Domain m) (Complement (Domain m) Xext_union) Xext_union =
            Full_set (Domain m)).
    apply Same_set_to_eq; apply Union_Compl_Fullset. rewrite <- H2; clear H2.
    unfold Included; unfold In; intros. inversion H2.
    - left; assumption.
    - right; subst Xext_union; unfold In; unfold pointwise_ext.
      destruct H3 as [le [re [Hunion [Hre Happ]]]].
      inversion Hunion.
      left. unfold In; exists le; exists re; repeat split; assumption.
      right. unfold In; exists le; exists re; repeat split; assumption.

  * unfold patt_or, patt_not. repeat rewrite ext_valuation_imp_simpl.
    repeat rewrite ext_valuation_app_simpl, ext_valuation_imp_simpl.
    rewrite ext_valuation_app_simpl, ext_valuation_bott_simpl.
    simpl.
    epose proof Union_Empty_l; eapply Same_set_to_eq in H2; rewrite H2; clear H2.
    epose proof Union_Empty_l; eapply Same_set_to_eq in H2; rewrite H2; clear H2.
    pose proof Compl_Compl_Ensembles; eapply Same_set_to_eq in H2; rewrite H2; clear H2.
    pose proof Compl_Compl_Ensembles; eapply Same_set_to_eq in H2; rewrite H2; clear H2.
    remember (ext_valuation evar_val svar_val phi1) as Xphi1.
    remember (ext_valuation evar_val svar_val phi2) as Xphi2.
    remember (ext_valuation evar_val svar_val psi) as Xpsi.
    remember (pointwise_ext Xpsi (Union (Domain m) Xphi1 Xphi2)) as Xext_union.
    constructor. constructor.
    assert (Union (Domain m) (Complement (Domain m) Xext_union) Xext_union =
            Full_set (Domain m)).
    apply Same_set_to_eq; apply Union_Compl_Fullset. rewrite <- H2; clear H2.
    unfold Included; unfold In; intros. inversion H2.
    - left; assumption.
    - right; subst Xext_union; unfold In; unfold pointwise_ext.
      destruct H3 as [le [re [Hle [Hunion Happ]]]].
      inversion Hunion.
      left. unfold In; exists le; exists re; repeat split; assumption.
      right. unfold In; exists le; exists re; repeat split; assumption.

  * rewrite ext_valuation_imp_simpl.
    constructor. constructor.
    remember (ext_valuation evar_val svar_val (patt_app (patt_exists phi) psi)) as Xex.
    assert (Union (Domain m) (Complement (Domain m) Xex) Xex = Full_set (Domain m)).
    apply Same_set_to_eq; apply Union_Compl_Fullset. rewrite <- H1; clear H1.
    unfold Included; intros. inversion H1; subst.
    left. assumption.
    right. rewrite ext_valuation_ex_simpl. simpl. constructor.
    rewrite ext_valuation_app_simpl, ext_valuation_ex_simpl in H2.
    destruct H2 as [le [re [Hunion [Hext_le Happ]]]]. inversion Hunion; subst.
    destruct H2 as [c Hext_re].
    exists c. rewrite ext_valuation_app_simpl. unfold pointwise_ext.
    exists le, re.
    split. admit. admit.
    (* assumption.
    erewrite evar_open_fresh. rewrite update_valuation_fresh.
    split; assumption.
    assumption. *)

  * rewrite ext_valuation_imp_simpl.
    constructor. constructor.
    remember (ext_valuation evar_val svar_val (patt_app psi (patt_exists phi))) as Xex.
    assert (Union (Domain m) (Complement (Domain m) Xex) Xex = Full_set (Domain m)).
    apply Same_set_to_eq; apply Union_Compl_Fullset. rewrite <- H1; clear H1.
    unfold Included; intros. inversion H1; subst.
    left. assumption.
    right. rewrite ext_valuation_ex_simpl. simpl. constructor.
    rewrite ext_valuation_app_simpl, ext_valuation_ex_simpl in H2.
    destruct H2 as [le [re [Hext_le [Hunion Happ]]]]. inversion Hunion; subst.
    destruct H2 as [c Hext_re].
    exists c. rewrite ext_valuation_app_simpl. unfold pointwise_ext.
    exists le, re.
    split. admit. admit.
    (* erewrite evar_open_fresh. rewrite update_valuation_fresh. assumption.
    assumption.
    split; assumption. *)

  * rewrite ext_valuation_iff_subset.
    rewrite ext_valuation_iff_subset in IHHp.
    repeat rewrite ext_valuation_app_simpl.
    unfold Included in *; intros; unfold In in *.
    destruct H as [le [re [Hphi1 [Hpsi Happ]]]].
    unfold pointwise_ext.
    exists le, re.
    split. apply IHHp. admit. assumption.
    split; assumption.

  * rewrite ext_valuation_iff_subset.
    rewrite ext_valuation_iff_subset in IHHp.
    repeat rewrite ext_valuation_app_simpl.
    unfold Included in *; intros; unfold In in *.
    destruct H as [le [re [Hphi1 [Hpsi Happ]]]].
    unfold pointwise_ext.
    exists le, re.
    split. assumption.
    split. apply IHHp. admit. assumption.
    assumption.

  * constructor. constructor.
    destruct IHHp. admit.
    clear H. unfold Included in *.
    intros. apply H0 in H. clear H0.
    admit.
    
  * simpl. rewrite ext_valuation_imp_simpl. rewrite ext_valuation_mu_simpl.
    constructor. constructor.
    unfold Included. intros. unfold In.
    admit.

  * rewrite ext_valuation_imp_simpl. rewrite ext_valuation_mu_simpl.
    simpl in IHHp. rewrite ext_valuation_imp_simpl in IHHp.
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
