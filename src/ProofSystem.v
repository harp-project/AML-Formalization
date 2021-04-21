From Coq Require Import ssreflect ssrfun ssrbool.
From Coq Require Import Ensembles.

From MatchingLogic.Utils Require Import Ensembles_Ext.
From MatchingLogic Require Import Syntax Semantics DerivedOperators Helpers.monotonic.
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
        unfold well_formed in H0.
        apply andb_true_iff in H0.
        destruct H0. assumption.
        rewrite -> (evar_open_fresh). unfold well_formed in H0.
        apply andb_true_iff in H0.
        destruct H0. assumption.
        unfold well_formed in H0.
        apply andb_true_iff in H0.
        destruct H0. assumption.
        {
          rewrite -> evar_open_fresh. unfold fresh_evar. simpl. 
          pose(@set_evar_fresh_is_fresh' signature (free_evars phi ∪ free_evars psi)).
          apply not_elem_of_union in n. destruct n. assumption.
          unfold well_formed in H0.
          apply andb_true_iff in H0.
          destruct H0. assumption.
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
      unfold well_formed in H0.
      apply andb_true_iff in H0.
      destruct H0. assumption.
      {
        unfold fresh_evar. simpl. unfold evar_is_fresh_in.
        pose(@set_evar_fresh_is_fresh' signature (free_evars psi ∪ free_evars phi)).
          apply not_elem_of_union in n. destruct n. assumption.
      }
      unfold well_formed in H0.
      apply andb_true_iff in H0.
      destruct H0. assumption.
    - split.
      + erewrite -> (@interpretation_fresh_evar_open signature m) in Hext_re. exact Hext_re.
        apply set_evar_fresh_is_fresh.
        {
          pose(@set_evar_fresh_is_fresh' signature (free_evars psi ∪ free_evars phi)).
          apply not_elem_of_union in n. destruct n. assumption.
        }
      + assumption.
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
  erewrite <- free_svar_subst_update_exchange in e. exact e. assumption. unfold well_formed in H. assumption.
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
    simpl.
    rewrite -> pattern_interpretation_imp_simpl.
    rewrite -> pattern_interpretation_ex_simpl.
    simpl.
    
    unfold instantiate. apply Extensionality_Ensembles.
    constructor. constructor.
    unfold Included; unfold Ensembles.In; intros x _.
    rewrite -> element_substitution_lemma with (x0 := fresh_evar phi).
    2: apply set_evar_fresh_is_fresh.
    destruct (classic (  Complement (Domain m)
    (pattern_interpretation (update_evar_val (fresh_evar phi) (evar_val y) evar_val) svar_val
                            (evar_open 0 (fresh_evar phi) phi)) x)).
    -- left. apply H.
    -- right. unfold Complement in H. apply NNPP in H.
       constructor. exists (evar_val y). apply H.

  * intros Hv evar_val svar_val.
    rewrite pattern_interpretation_iff_subset.
    assert (Hwf_imp: well_formed (phi1 ---> phi2)).
    { unfold well_formed. simpl. unfold well_formed in H, H0.
      unfold well_formed_closed. unfold well_formed_closed in H, H0.
      simpl. apply andb_true_iff in H. apply andb_true_iff in H0.
      destruct H as [Hwfp_phi1 Hwfc_phi1].
      destruct H0 as [Hwfp_phi2 Hwfc_phi2].
      apply andb_true_iff; split; apply andb_true_iff; split; assumption.
    }
    specialize (IHHp Hwf_imp Hv). clear Hv. clear Hwf_imp.
    assert (forall evar_val svar_val,
               Included (Domain m)
                        (pattern_interpretation evar_val svar_val phi1)
                        (pattern_interpretation evar_val svar_val phi2)
           ).
    { intros. apply pattern_interpretation_iff_subset. apply IHHp. }
    apply pattern_interpretation_subset_union
      with (evar_val0 := evar_val) (svar_val0 := svar_val) (x0 := x) in H2.
    unfold Included, Ensembles.In. intros x0 Hphi1.
    unfold Included, Ensembles.In in IHHp.
    destruct H2 with (x0 := x0).
    -- assert (Included (Domain m)
                        (pattern_interpretation evar_val svar_val (exists_quantify x phi1))
                        (FA_Union
                           (λ e : Domain m, pattern_interpretation
                                              (update_evar_val x e evar_val) svar_val phi1))).
       { unfold exists_quantify. rewrite pattern_interpretation_ex_simpl. simpl.
         apply FA_Union_included. unfold Included, Ensembles.In. intros.
         remember (fresh_evar (evar_quantify x 0 phi1)) as x2.
         erewrite interpretation_fresh_evar_open with (y := x) in H3.
         3: { apply evar_is_fresh_in_evar_quantify. }
         2: { subst x2. apply set_evar_fresh_is_fresh. }
         admit.
       }
       unfold Included, Ensembles.In in H2. apply H2. apply Hphi1.

    -- destruct H2 as [c Hphi2].
       rewrite pattern_interpretation_free_evar_independent in Hphi2. apply H1.
       apply Hphi2.

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
      unfold well_formed in Hwf.
      apply andb_true_iff in Hwf.
      inversion Hwf.
      simpl in H.
      unfold well_formed.
      apply andb_true_iff in H. destruct H as [H1 H2].
      apply andb_true_iff in H1. destruct H1 as [H3 H4].
      apply andb_true_iff in H2. destruct H2 as [H5 H6].
      simpl. rewrite H3. rewrite H5. simpl.
      unfold well_formed_closed.
      unfold well_formed_closed in H0. simpl in H0.
      apply andb_true_iff in H0. destruct H0 as [H01 H02].
      apply andb_true_iff in H01. destruct H01 as [H011 H012].
      apply andb_true_iff in H02. destruct H02 as [H021 H022].
      simpl.
      rewrite H011. rewrite H021.
      reflexivity.
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
      unfold well_formed in Hwf.
      apply andb_true_iff in Hwf.
      destruct Hwf as [Hwf1 Hwf2].
      simpl in Hwf1. apply andb_true_iff in Hwf1. destruct Hwf1 as [Hwf11 Hwf12].
      apply andb_true_iff in Hwf11. destruct Hwf11 as [Hwf111 Hwf112].
      apply andb_true_iff in Hwf12. destruct Hwf12 as [Hwf121 Hwf122].
      unfold well_formed. simpl.
      rewrite Hwf112. rewrite Hwf122. simpl.
      unfold well_formed_closed in Hwf2. simpl in Hwf2.
      apply andb_true_iff in Hwf2. destruct Hwf2 as [Hwfc1 Hwfc2].
      apply andb_true_iff in Hwfc1. destruct Hwfc1 as [Hwfc3 Hwfc4].
      apply andb_true_iff in Hwfc2. destruct Hwfc2 as [H2fc5 Hwfc6].
      unfold well_formed_closed. simpl.
      rewrite Hwfc4. rewrite Hwfc6.
      reflexivity.
    }

  * intros. epose proof (IHHp H Hv ) as IH.
    unfold well_formed in H.
    apply andb_true_iff in H. destruct H as [H1 H2].
    eapply (proof_rule_set_var_subst_sound phi psi _ H0 ) in IH.
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
      unfold well_formed in Hwf.
      apply andb_true_iff in Hwf.
      destruct Hwf as [Hwfp Hwfc].
      simpl in Hwfp. unfold well_formed_closed in Hwfc. simpl in Hwfc.
      apply andb_true_iff in Hwfp. destruct Hwfp as [Hwfp1 Hwfp2].
      apply andb_true_iff in Hwfp2. destruct Hwfp2 as [Hwfp2 Hwfp3].
      simpl. rewrite Hwfp3. rewrite Hwfp2.
      reflexivity.
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
    
    rewrite <- set_substitution_lemma.
    2: { simpl in Hwf. unfold well_formed in Hwf.
         apply andb_true_iff in Hwf.
         destruct Hwf as [_ Hwfc].
         apply wfc_wfc_ind in Hwfc. inversion Hwfc. subst.
         apply wfc_ind_wfc. assumption.
    }
    2: { apply set_svar_fresh_is_fresh. }
    unfold Included. intros. auto.

  * intros Hv evar_val svar_val.
    rewrite -> pattern_interpretation_imp_simpl. rewrite -> pattern_interpretation_mu_simpl.


   simpl.
    remember (fun S : Ensemble (Domain m) =>
                pattern_interpretation evar_val
                                       (update_svar_val (fresh_svar phi) S svar_val)
                                       (svar_open 0 (fresh_svar phi) phi)) as F.

    pose (OS := Lattice.EnsembleOrderedSet (@Domain signature m)).
    pose (L := Lattice.PowersetLattice (@Domain signature m)).

    assert (Ffix : Lattice.isFixpoint F (Lattice.LeastFixpointOf F)).
    { apply Lattice.LeastFixpoint_fixpoint. subst. apply is_monotonic.
      unfold well_formed in Hwf.
      apply andb_true_iff in Hwf.
      destruct Hwf as [Hwfp Hwfc].
      simpl in Hwfp. unfold well_formed_closed in Hwfc. simpl in Hwfc.
      apply andb_true_iff in Hwfp. destruct Hwfp as [Hwfp1 Hwfp2].
      apply andb_true_iff in Hwfp1. destruct Hwfp1 as [Hwfp1 Hwfp3].
      simpl. rewrite Hwfp1. rewrite Hwfp3.
      reflexivity.
      apply set_svar_fresh_is_fresh.
    }
    
    unfold Lattice.isFixpoint in Ffix.
    assert (Ffix_set : Same_set (Domain m) (F (Lattice.LeastFixpointOf F)) (Lattice.LeastFixpointOf F)).
    { rewrite -> Ffix. apply Same_set_refl. }
    destruct Ffix_set. clear H0.
    unfold Full.
    symmetry.
    apply Same_set_to_eq.
    apply Same_set_Full_set.
    apply Full_subset_union_iff_subset.
    pose proof (Htmp := Lattice.LeastFixpoint_LesserThanPrefixpoint).
    specialize (Htmp (Ensemble (Domain m)) OS L F). simpl in Htmp. apply Htmp.

    assert (Hwf': well_formed (instantiate (mu , phi) psi ---> psi)).
    { unfold well_formed in Hwf. apply andb_true_iff in Hwf.
      destruct Hwf as [Hwfp Hwfc].
      simpl in Hwfp. apply andb_true_iff in Hwfp. 
      destruct Hwfp as [Hwfp1 Hwfp2].
      simpl in Hwfp1.
      apply wfc_wfc_ind in Hwfc.
      inversion Hwfc. rename H3 into Hwfcpsi. apply wfc_ind_wfc in Hwfcpsi.
      simpl. unfold well_formed. simpl.
      rewrite Hwfp2.
      apply wfc_ind_wfc in H2.

      rewrite wfp_bsvar_subst; auto.
      simpl.

      unfold well_formed_closed. simpl.
      apply andb_true_iff. split.
      2: { assumption. }
      unfold well_formed_closed in H2.
      simpl in H2.
      apply wfc_aux_body_mu_imp_bsvar_subst; assumption.
    }
    specialize (IHHp Hwf').

    simpl in IHHp.
    unfold well_formed in Hwf.
    apply andb_true_iff in Hwf.
    destruct Hwf as [_ Hwfc]. apply wfc_wfc_ind in Hwfc. inversion Hwfc.
    subst psi0. subst phi0.

    unfold instantiate in Hp.
    apply IHHp with (evar_val:=evar_val) (svar_val:=svar_val) in Hv.
    apply pattern_interpretation_iff_subset in Hv.

    subst F.
    rewrite <- set_substitution_lemma.
    apply Hv. apply wfc_ind_wfc in H3. apply H3. apply set_svar_fresh_is_fresh.

  * intros Hv evar_val svar_val.
    assert (pattern_interpretation evar_val svar_val (ex , BoundVarSugar.b0)
            = pattern_interpretation evar_val svar_val (ex , (BoundVarSugar.b0 and Top))).
    { repeat rewrite pattern_interpretation_ex_simpl. simpl.
      rewrite eq_iff_Same_set. apply FA_Union_same. intros.
      repeat rewrite pattern_interpretation_imp_simpl.
      repeat rewrite pattern_interpretation_bott_simpl.
      repeat rewrite Union_Empty_l_eq.
      repeat rewrite Compl_Compl_Ensembles_eq.
      rewrite Union_Empty_l_eq.
      rewrite Compl_Compl_Ensembles_eq.
      apply Same_set_refl.
    }
    rewrite H.
    rewrite pattern_interpretation_set_builder.
    { unfold M_predicate. left. simpl. rewrite pattern_interpretation_imp_simpl.
      rewrite pattern_interpretation_bott_simpl.
      rewrite Union_Empty_l_eq.
      apply Complement_Empty_is_Full_eq.
    }
    simpl.
    rewrite eq_iff_Same_set. constructor. constructor.
    unfold Included. intros. unfold Ensembles.In.
    rewrite pattern_interpretation_imp_simpl.
    rewrite eq_iff_Same_set. apply Union_Compl_Fullset.

  * assert (Hemp: forall (evar_val : evar -> Domain m) svar_val,
               pattern_interpretation
                 evar_val svar_val
                 (subst_ctx C1 (patt_free_evar x and phi)
                            and subst_ctx C2 (patt_free_evar x and (phi ---> Bot)))
               = Semantics.Empty).
    { intros evar_val svar_val.
      rewrite -> pattern_interpretation_and_simpl.
      destruct (Ensembles_Ext.In_dec (pattern_interpretation evar_val svar_val phi) (evar_val x)).
      - rewrite [(pattern_interpretation
                    evar_val svar_val
                    (subst_ctx C2 (patt_free_evar x and (phi ---> Bot))))]
                propagate_context_empty.
        2: { rewrite eq_iff_Same_set. apply Intersection_Empty_l. }
        rewrite pattern_interpretation_and_simpl.
        rewrite pattern_interpretation_free_evar_simpl.
        rewrite pattern_interpretation_imp_simpl.
        rewrite pattern_interpretation_bott_simpl.
        rewrite Union_Empty_l_eq.
        rewrite eq_iff_Same_set.
        rewrite Intersection_singleton_empty.
        unfold not. intros. contradiction.
      - rewrite propagate_context_empty.
        2: { rewrite eq_iff_Same_set. apply Intersection_Empty_r. }
        rewrite pattern_interpretation_and_simpl.
        rewrite pattern_interpretation_free_evar_simpl.
        rewrite eq_iff_Same_set.
        rewrite <- Intersection_singleton in H.
        apply NNPP. exact H.
    }
    intros Hv evar_val svar_val.
    rewrite pattern_interpretation_predicate_not.
    - apply empty_impl_not_full. rewrite Hemp. reflexivity.
    - unfold M_predicate. right. apply Hemp.

    Unshelve. rewrite H2; reflexivity.
Admitted.


End ml_proof_system.

