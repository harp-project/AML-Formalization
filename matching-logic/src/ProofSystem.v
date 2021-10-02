From Coq Require Import ssreflect ssrfun ssrbool.

From Coq Require Import Logic.Classical_Prop.
From MatchingLogic.Utils Require Import stdpp_ext Lattice.
From MatchingLogic Require Import Syntax Semantics DerivedOperators Helpers.monotonic.
From stdpp Require Import base fin_sets sets propset.

From MatchingLogic.Utils Require Import extralibrary.

Import MatchingLogic.Syntax.Notations.
Import MatchingLogic.Semantics.Notations.
Import MatchingLogic.DerivedOperators.Notations.

Section ml_proof_system.
  Open Scope ml_scope.

  Context {signature : Signature}.

  (* soundness for prop_ex_right *)
  Lemma proof_rule_prop_ex_right_sound {m : Model} (theory : Theory) (phi psi : Pattern)
        (evar_val : evar -> Domain m) (svar_val : svar -> Power (Domain m)):
    (well_formed (patt_imp (patt_app (patt_exists phi) psi) (patt_exists (patt_app phi psi)))) ->
    (well_formed (ex, phi)) -> (@well_formed signature psi) ->
    (∀ axiom : Pattern,
        axiom ∈ theory
        → ∀ (evar_val : evar → Domain m) (svar_val : svar → Power (Domain m)),
          pattern_interpretation evar_val svar_val axiom = ⊤) ->
    pattern_interpretation evar_val svar_val ((ex , phi) $ psi ---> ex , phi $ psi) = ⊤.
  Proof.
    intros Hwf H H0 Hv.
    rewrite -> pattern_interpretation_imp_simpl.

    remember (pattern_interpretation evar_val svar_val (patt_app (patt_exists phi) psi)) as Xex.
    assert (Huxex: (⊤ ∖ Xex) ∪ Xex = ⊤).
    { clear.
      set_unfold. intros x. split; intros H. exact I.
      destruct (classic (x ∈ Xex)). right. assumption. left. auto.
    }
    rewrite -> set_eq_subseteq.
    split.
    - rewrite <- Huxex.
      rewrite -> elem_of_subseteq. intros x H1.
      inversion H1.
      + left. rewrite -> Huxex in H2. exact H2.
      + rewrite Huxex. apply elem_of_top'.
    - rewrite -> pattern_interpretation_ex_simpl. simpl.
      rewrite -> elem_of_subseteq.
      intros x _.
      destruct (classic (x ∈ Xex)).
      2: { left. clear -H1. set_solver. }
      right. unfold stdpp_ext.propset_fa_union.
      rewrite -> elem_of_PropSet.
      rewrite -> HeqXex in H1.
      rewrite -> pattern_interpretation_app_simpl, pattern_interpretation_ex_simpl in H1.
      simpl in H1.
      unfold stdpp_ext.propset_fa_union in H1.
      unfold app_ext in H1.
      rewrite -> elem_of_PropSet in H1.
      destruct H1 as [le [re [Hunion [Hext_le Happ]]]].
      rewrite -> elem_of_PropSet in Hunion.
      destruct Hunion as [c Hext_re].
      exists c. rewrite -> evar_open_app, -> pattern_interpretation_app_simpl. unfold app_ext.
      rewrite -> elem_of_PropSet.
      exists le, re.
      split.
      + erewrite -> (@interpretation_fresh_evar_open signature m) in Hext_re. exact Hext_re.
        apply set_evar_fresh_is_fresh.
        {
          unfold fresh_evar. simpl. 
          pose(@set_evar_fresh_is_fresh' signature (free_evars phi ∪ free_evars psi)).
          apply not_elem_of_union in n. destruct n. assumption.
        }
      + unfold well_formed,well_formed_closed in *. simpl in *.
        destruct_and!.
        erewrite -> pattern_interpretation_free_evar_independent.
        erewrite -> evar_open_closed.
        split.
        2: { exact Happ. }
        exact Hext_le.
        assumption.
        rewrite -> evar_open_closed.
        {
          unfold fresh_evar. simpl. 
          pose(@set_evar_fresh_is_fresh' signature (free_evars phi ∪ free_evars psi)).
          apply not_elem_of_union in n. destruct n. assumption.
        }
        assumption.
  Qed.

(* soundness for prop_ex_left *)
  Lemma proof_rule_prop_ex_left_sound {m : Model} (theory : Theory) (phi psi : Pattern)
        (evar_val : evar -> Domain m) (svar_val : svar -> Power (Domain m)):
    (well_formed (patt_imp (patt_app psi (patt_exists phi)) (patt_exists (patt_app psi phi)))) ->
    (well_formed (ex, phi)) -> (@well_formed signature psi) ->
    (∀ axiom : Pattern,
        axiom ∈ theory
        → ∀ (evar_val : evar → Domain m) (svar_val : svar → Power (Domain m)),
          pattern_interpretation evar_val svar_val axiom = ⊤) ->
    pattern_interpretation evar_val svar_val (psi $ (ex , phi) ---> ex , psi $ phi) = ⊤.
  Proof.
    intros Hwf H H0 Hv.
    rewrite -> pattern_interpretation_imp_simpl.

    remember (pattern_interpretation evar_val svar_val (patt_app psi (patt_exists phi))) as Xex.
    assert (Huxex: (⊤ ∖ Xex) ∪ Xex = ⊤).
    { clear.
      set_unfold. intros x. split; intros H. exact I.
      destruct (classic (x ∈ Xex)). right. assumption. left. auto.
    }
    rewrite -> set_eq_subseteq.
    split.
    - rewrite <- Huxex.
      rewrite -> elem_of_subseteq. intros x H1.
      rewrite Huxex. apply elem_of_top'.
    - rewrite -> pattern_interpretation_ex_simpl. simpl.
      rewrite -> elem_of_subseteq.
      intros x _.
      destruct (classic (x ∈ Xex)).
      2: { left. clear -H1. set_solver. }
      right. unfold stdpp_ext.propset_fa_union.
      rewrite -> elem_of_PropSet.
      rewrite -> HeqXex in H1.
      rewrite -> pattern_interpretation_app_simpl, pattern_interpretation_ex_simpl in H1.
      simpl in H1.
      unfold stdpp_ext.propset_fa_union in H1.
      unfold app_ext in H1.
      rewrite -> elem_of_PropSet in H1.
      destruct H1 as [le [re [Hext_le [Hunion Happ]]]].
      rewrite -> elem_of_PropSet in Hunion.
      destruct Hunion as [c Hext_re].

      exists c. rewrite -> evar_open_app, -> pattern_interpretation_app_simpl. unfold app_ext.
      exists le, re.
      split.
      + erewrite -> evar_open_closed.
        erewrite -> pattern_interpretation_free_evar_independent. exact Hext_le.
        unfold well_formed in H0.
        apply andb_true_iff in H0.
        destruct H0. 
        {
          unfold fresh_evar. simpl. unfold evar_is_fresh_in.
          pose(@set_evar_fresh_is_fresh' signature (free_evars psi ∪ free_evars phi)).
          apply not_elem_of_union in n. destruct n. assumption.
        }
        unfold well_formed,well_formed_closed in *. simpl in *.
        destruct_and!.
        assumption.
      + split; try assumption.
        erewrite -> (@interpretation_fresh_evar_open signature m) in Hext_re. exact Hext_re.
        apply set_evar_fresh_is_fresh.
        {
          pose(@set_evar_fresh_is_fresh' signature (free_evars psi ∪ free_evars phi)).
          apply not_elem_of_union in n. destruct n. assumption.
        }
  Qed.

(* free_svar_subst maintains soundness *)
Lemma proof_rule_set_var_subst_sound {m : Model}: ∀ phi psi,
  well_formed_closed phi → well_formed psi →
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

  Reserved Notation "theory ⊢ pattern" (at level 76).
  Inductive ML_proof_system (theory : Theory) :
    Pattern -> Set :=

  (* Hypothesis *)
  | hypothesis (axiom : Pattern) :
      well_formed axiom ->
      (axiom ∈ theory) -> theory ⊢ axiom
                                              
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
      theory ⊢ (! ((subst_ctx C1 (patt_free_evar x and phi)) and
                   (subst_ctx C2 (patt_free_evar x and (! phi)))))

  where "theory ⊢ pattern" := (ML_proof_system theory pattern).

  Notation "G |= phi" := (@satisfies signature G phi) (no associativity, at level 50).

  Instance ML_proof_system_eqdec: forall gamma phi, EqDecision (ML_proof_system gamma phi).
  Proof. intros. intros x y. 
         unfold Decision. Fail decide equality.
  Abort.

(* Soundness theorem *)
Theorem Soundness :
  forall phi : Pattern, forall theory : Theory,
  well_formed phi -> (theory ⊢ phi) -> (theory |= phi).
Proof.
  intros phi theory Hwf Hp. unfold satisfies, satisfies_theory, satisfies_model.
  intros m Hv evar_val svar_val. 
  generalize dependent svar_val. generalize dependent evar_val. generalize dependent Hv.
  induction Hp.

  (* hypothesis *)
  - intros Hv evar_val svar_val. apply Hv. assumption.

  (* FOL reasoning - P1 *)
  - intros Hv evar_val svar_val.
    repeat rewrite -> pattern_interpretation_imp_simpl.
    remember (pattern_interpretation evar_val svar_val phi) as Xphi.
    remember (pattern_interpretation evar_val svar_val psi) as Xpsi.
    rewrite -> set_eq_subseteq.
    split.
    { apply top_subseteq. }

    assert (Huxphi: (⊤ ∖ Xphi) ∪ Xphi = ⊤).
    { clear.
      set_unfold. intros x. split; intros H. exact I.
      destruct (classic (x ∈ Xphi)). right. assumption. left. auto.
    }

    rewrite <- Huxphi.
    rewrite -> elem_of_subseteq. intros x H.
    rewrite -> elem_of_union.
    destruct (classic (x ∈ Xphi)).
    + right. right. assumption.
    + left. clear -H0. set_solver.

  (* FOL reasoning - P2 *)
  - intros Hv evar_val svar_val.
    repeat rewrite -> pattern_interpretation_imp_simpl.
    remember (pattern_interpretation evar_val svar_val phi) as Xphi.
    remember (pattern_interpretation evar_val svar_val psi) as Xpsi.
    remember (pattern_interpretation evar_val svar_val xi) as Xxi.
    clear.
    apply set_eq_subseteq. split.
    { apply top_subseteq. }
    rewrite -> elem_of_subseteq. intros x _.
    destruct (classic (x ∈ Xphi)), (classic (x ∈ Xpsi)), (classic (x ∈ Xxi));
      set_solver.

  (* FOL reasoning - P3 *)
  - intros Hv evar_val svar_val. 
    repeat rewrite -> pattern_interpretation_imp_simpl; rewrite -> pattern_interpretation_bott_simpl.
    remember (pattern_interpretation evar_val svar_val phi) as Xphi.
    clear.
    apply set_eq_subseteq. split.
    { apply top_subseteq. }
    rewrite -> elem_of_subseteq. intros x _.
    destruct (classic (x ∈ Xphi)); set_solver.

  (* Modus ponens *)
  - intros Hv evar_val svar_val.
    rename i into wfphi1. rename i0 into wfphi1impphi2.
    pose (IHHp2 wfphi1impphi2 Hv evar_val svar_val) as e.
    rewrite -> pattern_interpretation_iff_subset in e.
    unfold Full.
    pose proof (H1 := (IHHp1 wfphi1 Hv evar_val svar_val)).
    unfold Full in H1.
    clear -e H1.
    set_solver.

  (* Existential quantifier *)
  - intros Hv evar_val svar_val.
    simpl.
    rewrite -> pattern_interpretation_imp_simpl.
    rewrite -> pattern_interpretation_ex_simpl.
    simpl.

    rewrite -> element_substitution_lemma with (x := fresh_evar phi).
    2: { apply set_evar_fresh_is_fresh. }
    apply set_eq_subseteq. split.
    { apply top_subseteq. }
    rewrite -> elem_of_subseteq. intros x _.
    destruct (classic (x ∈ (⊤ ∖
                              (pattern_interpretation
                                 (update_evar_val (fresh_evar phi) (evar_val y) evar_val)
                                 svar_val
                                 (evar_open 0 (fresh_evar phi) phi))))).
    -- left. apply H.
    -- right. unfold not in H.
       rewrite -> elem_of_difference in H.
       unfold stdpp_ext.propset_fa_union.
       rewrite -> elem_of_PropSet.
       exists (evar_val y).
       assert (x
                 ∉ pattern_interpretation (update_evar_val (fresh_evar phi) (evar_val y) evar_val) svar_val
                 (evar_open 0 (fresh_evar phi) phi) → False).
       { intros Hcontra. apply H. split. apply elem_of_top'. apply Hcontra. }
       apply NNPP in H0. exact H0.
       
  (* Existential generalization *)
  - intros Hv evar_val svar_val.
    rename i into H. rename i0 into H0.
    rewrite pattern_interpretation_iff_subset.
    assert (Hwf_imp: well_formed (phi1 ---> phi2)).
    { unfold well_formed. simpl. unfold well_formed in H, H0.
      unfold well_formed_closed. unfold well_formed_closed in H, H0.
      simpl. apply andb_true_iff in H. apply andb_true_iff in H0.
      destruct H as [Hwfp_phi1 Hwfc_phi1].
      destruct H0 as [Hwfp_phi2 Hwfc_phi2].
      unfold well_formed,well_formed_closed in *. simpl in *.
      destruct_and!.
      split_and!; assumption.
    }
    specialize (IHHp Hwf_imp Hv). clear Hv. clear Hwf_imp.
    assert (H2: forall evar_val svar_val,
               (@pattern_interpretation _ m evar_val svar_val phi1)
                 ⊆
                 (pattern_interpretation evar_val svar_val phi2)
           ).
    { intros. apply pattern_interpretation_iff_subset. apply IHHp. }
    apply pattern_interpretation_subset_union
      with (evar_val0 := evar_val) (svar_val0 := svar_val) (x0 := x) in H2.
    rewrite -> elem_of_subseteq. intros x0 Hphi1.
    rewrite -> elem_of_subseteq in H2.
    destruct H2 with (x0 := x0).
    -- assert (Hinc:
                              (pattern_interpretation evar_val svar_val (exists_quantify x phi1))
                              ⊆
                              (propset_fa_union
                                 (λ e : Domain m, pattern_interpretation
                                                    (update_evar_val x e evar_val) svar_val phi1))).
       { unfold exists_quantify. rewrite pattern_interpretation_ex_simpl. simpl.
         apply propset_fa_union_included.
         setoid_rewrite -> elem_of_subseteq.
         intros c x1 H3.
         remember (fresh_evar (evar_quantify x 0 phi1)) as x2.
         erewrite interpretation_fresh_evar_open with (y := x) in H3.
         3: { apply evar_is_fresh_in_evar_quantify. }
         2: { subst x2. apply set_evar_fresh_is_fresh. }
         unfold well_formed in H.
         apply andb_true_iff in H.
         destruct H as [Hwfp Hwfc].
         unfold well_formed_closed in Hwfc.
         rewrite -> evar_open_evar_quantify in H3.
         assumption.
         unfold well_formed,well_formed_closed in *. simpl in *.
         destruct_and!.
         assumption.
       }
       rewrite -> elem_of_subseteq in Hinc.
       apply Hinc. apply Hphi1.

    -- simpl.
       rewrite pattern_interpretation_free_evar_independent in H1.
       { auto. }
       apply H1.

  (* Propagation bottom - left *)
  - intros Hv evar_val svar_val. 
    rewrite -> pattern_interpretation_imp_simpl, pattern_interpretation_app_simpl, pattern_interpretation_bott_simpl.
    unfold Full.
    rewrite right_id_L.
    rewrite -> complement_full_iff_empty.
    apply app_ext_bot_l.
    
  (* Propagation bottom - right *)
  - intros Hv evar_val svar_val. 
    rewrite -> pattern_interpretation_imp_simpl, pattern_interpretation_app_simpl, pattern_interpretation_bott_simpl.
    rewrite right_id_L.
    rewrite -> complement_full_iff_empty.
    apply app_ext_bot_r.

  (* Propagation disjunction - left *)
  - intros Hv evar_val svar_val. 
    unfold patt_or, patt_not. repeat rewrite -> pattern_interpretation_imp_simpl.
    repeat rewrite -> pattern_interpretation_app_simpl, pattern_interpretation_imp_simpl.
    rewrite -> pattern_interpretation_app_simpl, pattern_interpretation_bott_simpl.
    remember (pattern_interpretation evar_val svar_val phi1) as Xphi1.
    remember (pattern_interpretation evar_val svar_val phi2) as Xphi2.
    remember (pattern_interpretation evar_val svar_val psi) as Xpsi.
    unfold Full.
    rewrite [_ ∪ ∅]right_id_L.
    rewrite [_ ∪ ∅]right_id_L.
    repeat rewrite Compl_Compl_propset.

    remember (app_ext (Xphi1 ∪ Xphi2) Xpsi) as Xext_union.
    rewrite -> set_eq_subseteq.
    split.
    1: { apply top_subseteq. }
    
    rewrite -> elem_of_subseteq.
    intros x _.
    destruct (classic (x ∈ Xext_union)).
    + right. subst Xext_union.
      destruct H as [le [re [Hunion [Hre Happ] ] ] ].
      destruct Hunion.
      * left. exists le, re. repeat split; assumption.
      * right. exists le, re. repeat split; assumption.
    + left. rewrite -> elem_of_compl. apply H.

  (* Propagation disjunction - right *)
  - intros Hv evar_val svar_val. 
    unfold patt_or, patt_not. repeat rewrite -> pattern_interpretation_imp_simpl.
    repeat rewrite -> pattern_interpretation_app_simpl, pattern_interpretation_imp_simpl.
    rewrite -> pattern_interpretation_app_simpl, pattern_interpretation_bott_simpl.
    remember (pattern_interpretation evar_val svar_val phi1) as Xphi1.
    remember (pattern_interpretation evar_val svar_val phi2) as Xphi2.
    remember (pattern_interpretation evar_val svar_val psi) as Xpsi.
    unfold Full.
    rewrite [_ ∪ ∅]right_id_L.
    rewrite [_ ∪ ∅]right_id_L.
    repeat rewrite Compl_Compl_propset.

    remember (app_ext Xpsi (Xphi1 ∪ Xphi2)) as Xext_union.
    rewrite -> set_eq_subseteq.
    split.
    1: { apply top_subseteq. }
    
    rewrite -> elem_of_subseteq.
    intros x _.
    destruct (classic (x ∈ Xext_union)).
    + right. subst Xext_union.
      destruct H as [le [re [Hle [Hunion Happ] ] ] ].
      destruct Hunion.
      * left. exists le, re. repeat split; assumption.
      * right. exists le, re. repeat split; assumption.
    + left. rewrite -> elem_of_compl. apply H.

  (* Propagation exists - left *)
  - intros Hv evar_val svar_val.
    eauto using proof_rule_prop_ex_right_sound.

  (* Propagation exists - right *)
  - intros Hv evar_val svar_val.
    eauto using proof_rule_prop_ex_left_sound.

  (* Framing - left *)
  - intros Hv evar_val svar_val. 
    rewrite -> pattern_interpretation_iff_subset.
    epose (IHHp _ Hv evar_val svar_val) as e.
    rewrite -> pattern_interpretation_iff_subset in e.
    repeat rewrite -> pattern_interpretation_app_simpl.
    rewrite -> elem_of_subseteq. intros.
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
      destruct_and!.
      split_and!; assumption.
    }

  (* Framing - right *)
  - intros Hv evar_val svar_val.
    rewrite -> pattern_interpretation_iff_subset.
    epose (IHHp _ Hv evar_val svar_val) as e.
    rewrite -> pattern_interpretation_iff_subset in e.
    repeat rewrite -> pattern_interpretation_app_simpl.
    rewrite -> elem_of_subseteq. intros.
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
      destruct_and!. split_and!; assumption.
    }

  (* Set Variable Substitution *)
  - intros. epose proof (IHHp ltac:(auto) Hv ) as IH.
    unfold well_formed in i.
    apply andb_true_iff in i. destruct i as [H1 H2].
    eauto using proof_rule_set_var_subst_sound.

  (* Pre-Fixpoint *)
  - intros Hv evar_val svar_val.
    apply pattern_interpretation_iff_subset. simpl.
    rewrite -> pattern_interpretation_mu_simpl.
    simpl.
    remember (fun S : propset (Domain m) =>
                pattern_interpretation evar_val
                                       (update_svar_val (fresh_svar phi) S svar_val)
                                       (svar_open 0 (fresh_svar phi) phi)) as F.
    pose (OS := Lattice.PropsetOrderedSet (@Domain signature m)).
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
    assert (Ffix_set : (F (Lattice.LeastFixpointOf F)) = (Lattice.LeastFixpointOf F)).
    { rewrite -> Ffix. reflexivity. }
    rewrite -> set_eq_subseteq in Ffix_set.
    destruct Ffix_set. clear H0.
    eapply transitivity.
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
    apply reflexivity.

  (* Knaster-Tarski *)
  - intros Hv evar_val svar_val.
    rewrite -> pattern_interpretation_imp_simpl. rewrite -> pattern_interpretation_mu_simpl.
    simpl.
    remember (fun S : propset (Domain m) =>
                pattern_interpretation evar_val
                                       (update_svar_val (fresh_svar phi) S svar_val)
                                       (svar_open 0 (fresh_svar phi) phi)) as F.

    pose (OS := Lattice.PropsetOrderedSet (@Domain signature m)).
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
    assert (Ffix_set : (F (Lattice.LeastFixpointOf F)) = (Lattice.LeastFixpointOf F)).
    { rewrite -> Ffix. reflexivity. }
    rewrite -> set_eq_subseteq in Ffix_set.
    destruct Ffix_set. clear H0.
    unfold Full.
    rewrite -> set_eq_subseteq.
    split.
    { apply top_subseteq. }

    (* TODO make it a lemma *)
    assert (Hwannabe_lemma: forall (L R : propset (Domain m)),
               (⊤ ⊆ ((⊤ ∖ L) ∪ R)) ↔ (L ⊆ R)).
    { intros L0 R0. clear. split; intros H. set_solver. rewrite -> elem_of_subseteq. intros x _.
      set_unfold in H.
      destruct (classic (x ∈ R0)); set_solver.
    }
    rewrite -> Hwannabe_lemma. clear Hwannabe_lemma.

    pose proof (Htmp := Lattice.LeastFixpoint_LesserThanPrefixpoint).
    specialize (Htmp (propset (Domain m)) OS L F). simpl in Htmp.
    apply Htmp.

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

      unfold well_formed,well_formed_closed in *. simpl in *.
      destruct_and!. assumption.
      split_and!; auto.
      unfold well_formed_closed in *. simpl in *.
      destruct_and!.
      split_and!; auto.
      + apply wfc_mu_aux_bsvar_subst; auto.
      + apply wfc_ex_aux_bsvar_subst; auto.
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


  (* Existence *)
  - intros Hv evar_val svar_val.
    assert (pattern_interpretation evar_val svar_val (ex , BoundVarSugar.b0)
            = pattern_interpretation evar_val svar_val (ex , (BoundVarSugar.b0 and Top))).
    { repeat rewrite pattern_interpretation_ex_simpl. simpl.
      apply propset_fa_union_same. intros.
      repeat rewrite pattern_interpretation_imp_simpl.
      repeat rewrite pattern_interpretation_bott_simpl.
      rewrite [_ ∪ ∅]right_id_L.
      rewrite [_ ∪ ∅]right_id_L.
      rewrite [_ ∪ ∅]right_id_L.
      rewrite [_ ∪ ∅]right_id_L.
      rewrite [_ ∪ ∅]right_id_L.
      rewrite difference_empty_L.
      rewrite difference_diag_L.
      rewrite [_ ∪ ∅]right_id_L.
      repeat rewrite Compl_Compl_propset.
      simpl.
      reflexivity.
    }
    unfold Full.
    rewrite H.
    rewrite pattern_interpretation_set_builder.
    { unfold M_predicate. left. simpl. rewrite pattern_interpretation_imp_simpl.
      rewrite pattern_interpretation_bott_simpl.
      clear. set_solver.
    }
    simpl.
    rewrite -> set_eq_subseteq.
    split.
    { apply top_subseteq. }
    rewrite -> elem_of_subseteq. intros x _.
    rewrite -> elem_of_PropSet.
    rewrite pattern_interpretation_imp_simpl.
    clear. set_solver.
    
  (* Singleton *)
  - assert (Hemp: forall (evar_val : evar -> Domain m) svar_val,
               pattern_interpretation
                 evar_val svar_val
                 (subst_ctx C1 (patt_free_evar x and phi)
                            and subst_ctx C2 (patt_free_evar x and (phi ---> Bot)))
               = ∅).
    { intros evar_val svar_val.
      rewrite -> pattern_interpretation_and_simpl.
      destruct (classic (evar_val x ∈ pattern_interpretation evar_val svar_val phi)).
      - rewrite [(pattern_interpretation
                    evar_val svar_val
                    (subst_ctx C2 (patt_free_evar x and (phi ---> Bot))))]
                propagate_context_empty.
        2: { unfold Semantics.Empty. rewrite intersection_empty_r_L. reflexivity. }
        rewrite pattern_interpretation_and_simpl.
        rewrite pattern_interpretation_free_evar_simpl.
        rewrite pattern_interpretation_imp_simpl.
        rewrite pattern_interpretation_bott_simpl.
        unfold Semantics.Empty.
        rewrite right_id_L.
        clear -H. set_solver.
      - rewrite propagate_context_empty.
        2: { unfold Semantics.Empty. rewrite intersection_empty_l_L. reflexivity. }
        rewrite pattern_interpretation_and_simpl.
        rewrite pattern_interpretation_free_evar_simpl.
        clear -H. set_solver.
    }
    intros Hv evar_val svar_val.
    rewrite pattern_interpretation_predicate_not.
    + rewrite Hemp. clear. apply empty_impl_not_full. reflexivity.
    + unfold M_predicate. right. apply Hemp.
Qed.

End ml_proof_system.


Module Notations.

  Notation "theory ⊢ pattern" := (ML_proof_system theory pattern) (at level 95, no associativity).

End Notations.

