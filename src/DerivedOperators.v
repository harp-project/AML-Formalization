From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From stdpp Require Import base sets.

From MatchingLogic.Utils Require Import Lattice Ensembles_Ext stdpp_ext extralibrary.
From MatchingLogic Require Import Syntax Semantics.

Import MatchingLogic.Syntax.Notations.

Section with_signature.
    Context {Σ : Signature}.
    Existing Instance variables.

    Section with_model.
      Context {M : Model}.
      
      Lemma pattern_interpretation_not_simpl : forall (evar_val : EVarVal) (svar_val : SVarVal) (phi : Pattern),
          @pattern_interpretation Σ M evar_val svar_val (patt_not phi) = Complement (Domain M) (pattern_interpretation evar_val svar_val phi).
      Proof.
        intros. unfold patt_not.
        rewrite -> pattern_interpretation_imp_simpl.
        rewrite -> pattern_interpretation_bott_simpl.
        apply Extensionality_Ensembles.
        apply Union_Empty_l.
      Qed.

      Lemma pattern_interpretation_or_simpl : forall (evar_val : EVarVal) (svar_val : SVarVal)
                                                     (phi1 phi2 : Pattern),
          pattern_interpretation evar_val svar_val (patt_or phi1 phi2)
          = Ensembles.Union (Domain M) (pattern_interpretation evar_val svar_val phi1) (pattern_interpretation evar_val svar_val phi2).
      Proof.
        intros. unfold patt_or.
        rewrite -> pattern_interpretation_imp_simpl.
        rewrite -> pattern_interpretation_not_simpl.
        assert (H: Complement (Domain M) (Complement (Domain M) (pattern_interpretation evar_val svar_val phi1)) = pattern_interpretation evar_val svar_val phi1).
        { apply Extensionality_Ensembles. apply Compl_Compl_Ensembles. }
        rewrite -> H. reflexivity.
      Qed.

      Lemma pattern_interpretation_or_comm : forall (evar_val : EVarVal) (svar_val : SVarVal)
                                                    (phi1 phi2 : Pattern),
          @pattern_interpretation Σ M evar_val svar_val (patt_or phi1 phi2)
          = pattern_interpretation evar_val svar_val (patt_or phi2 phi1).
      Proof.
        intros.
        repeat rewrite -> pattern_interpretation_or_simpl.
        apply Extensionality_Ensembles.
        apply Union_Symmetric.
      Qed.

      Lemma pattern_interpretation_and_simpl : forall (evar_val : EVarVal) (svar_val : SVarVal)
                                                      (phi1 phi2 : Pattern),
          pattern_interpretation evar_val svar_val (patt_and phi1 phi2)
          = Ensembles.Intersection (Domain M) (pattern_interpretation evar_val svar_val phi1) (pattern_interpretation evar_val svar_val phi2).
      Proof.
        intros. unfold patt_and.
        rewrite -> pattern_interpretation_not_simpl.
        rewrite -> pattern_interpretation_or_simpl.
        repeat rewrite -> pattern_interpretation_not_simpl.
        apply Extensionality_Ensembles.
        apply Compl_Union_Compl_Intes_Ensembles_alt.
      Qed.

      Lemma pattern_interpretation_and_comm : forall (evar_val : EVarVal) (svar_val : SVarVal)
                                                     (phi1 phi2 : Pattern),
          @pattern_interpretation Σ M evar_val svar_val (patt_and phi1 phi2)
          = pattern_interpretation evar_val svar_val (patt_and phi2 phi1).
      Proof.
        intros.
        repeat rewrite -> pattern_interpretation_and_simpl.
        apply Extensionality_Ensembles.
        apply Intersection_Symmetric.
      Qed.

      Lemma pattern_interpretation_top_simpl : forall (evar_val : EVarVal) (svar_val : SVarVal),
          @pattern_interpretation Σ M evar_val svar_val patt_top = Full.
      Proof.
        intros. unfold patt_top.
        rewrite -> pattern_interpretation_not_simpl.
        rewrite -> pattern_interpretation_bott_simpl.
        apply Extensionality_Ensembles.
        apply Complement_Empty_is_Full.
      Qed.

      (* TODO prove. Maybe some de-morgan laws could be helpful in proving this? *)
      Lemma pattern_interpretation_iff_or : forall (evar_val : EVarVal) (svar_val : SVarVal)
                                                   (phi1 phi2 : Pattern),
          @pattern_interpretation Σ M evar_val svar_val (patt_iff phi1 phi2)
          = pattern_interpretation evar_val svar_val (patt_or (patt_and phi1 phi2) (patt_and (patt_not phi1) (patt_not phi2))).
      Proof.

      Abort.

      Lemma pattern_interpretation_iff_comm : forall (evar_val : EVarVal) (svar_val : SVarVal)
                                                     (phi1 phi2 : Pattern),
          @pattern_interpretation Σ M evar_val svar_val (patt_iff phi1 phi2)
          = pattern_interpretation evar_val svar_val (patt_iff phi2 phi1).
      Proof.
        intros.
        unfold patt_iff.
        rewrite -> pattern_interpretation_and_comm.
        reflexivity.
      Qed.

      (* TODO: forall, nu *)



          (* if pattern_interpretation (phi1 ---> phi2) = Full_set,
             then pattern_interpretation phi1 subset pattern_interpretation phi2
          *)
      Lemma pattern_interpretation_iff_subset (evar_val : EVarVal) (svar_val : SVarVal)
            (phi1 : Pattern) (phi2 : Pattern) :
        pattern_interpretation evar_val svar_val (phi1 ---> phi2)%ml = Full <->
        Included (Domain M) (pattern_interpretation evar_val svar_val phi1)
                 (pattern_interpretation evar_val svar_val phi2).
      Proof.
        intros; split; unfold Included; intros.
        * rewrite pattern_interpretation_imp_simpl in H.
          remember (pattern_interpretation evar_val svar_val phi1) as Xphi1.
          remember (pattern_interpretation evar_val svar_val phi2) as Xphi2.
          assert (In (Domain M) (Union (Domain M) (Complement (Domain M) Xphi1) Xphi2) x).
          rewrite H. constructor.
          inversion H1. contradiction. assumption.
        * apply Extensionality_Ensembles.
          rewrite pattern_interpretation_imp_simpl.
          remember (pattern_interpretation evar_val svar_val phi1) as Xphi1.
          remember (pattern_interpretation evar_val svar_val phi2) as Xphi2.
          constructor. constructor.
          assert (Union (Domain M) (Complement (Domain M) Xphi1) Xphi1 = Full_set (Domain M)).
          apply Same_set_to_eq; apply Union_Compl_Fullset. unfold Full. rewrite <- H0; clear H0.
          unfold Included; intros.
          inversion H0.
          left; assumption.
          right; apply H in H1; assumption.
      Qed.


      Hint Resolve M_predicate_not : core.

      Lemma M_predicate_or ϕ₁ ϕ₂ : M_predicate M ϕ₁ -> M_predicate M ϕ₂ -> M_predicate M (patt_or ϕ₁ ϕ₂).
      Proof.
        intros. unfold patt_or. auto using M_predicate_not, M_predicate_impl.
      Qed.

      Hint Resolve M_predicate_or : core.

      Lemma M_predicate_and ϕ₁ ϕ₂ : M_predicate M ϕ₁ -> M_predicate M ϕ₂ -> M_predicate M (patt_and ϕ₁ ϕ₂).
      Proof.
        intros. unfold patt_and. auto using M_predicate_or, M_predicate_not.
      Qed.

      Hint Resolve M_predicate_and : core.


      Lemma M_predicate_top : M_predicate M patt_top.
      Proof.
        unfold patt_top. apply M_predicate_not. apply M_predicate_bott.
      Qed.

      Hint Resolve M_predicate_top : core.

      Lemma M_predicate_forall ϕ :
        let x := fresh_evar ϕ in
        M_predicate M (evar_open 0 x ϕ) -> M_predicate M (patt_forall ϕ).
      Proof.
        intros x Hpred.
        unfold patt_forall.
        apply M_predicate_not.
        apply M_predicate_exists.
        rewrite !simpl_evar_open.
        apply M_predicate_not.
        subst x.
        simpl.        
        rewrite -> sets.union_empty_r_L.
        apply Hpred.
      Qed.

      Hint Resolve M_predicate_forall : core.

      Lemma M_predicate_iff ϕ₁ ϕ₂ :
        M_predicate M ϕ₁ ->
        M_predicate M ϕ₂ ->
        M_predicate M (patt_iff ϕ₁ ϕ₂).
      Proof.
        intros H1 H2.
        unfold patt_iff.
        apply M_predicate_and; apply M_predicate_impl; auto.
      Qed.

      Hint Resolve M_predicate_iff : core.

      (* TODO forall *)

      (* ML's 'set comprehension'/'set building' scheme.
   Pattern `∃ x. x ∧ P(x)` gets interpreted as {m ∈ M | P(m) holds}
       *)
      (* ϕ is expected to have dangling evar indices *)

      Lemma pattern_interpretation_set_builder ϕ ρₑ ρₛ :
        let x := fresh_evar ϕ in
        M_predicate M (evar_open 0 x ϕ) ->
        (pattern_interpretation ρₑ ρₛ (patt_exists (patt_and (patt_bound_evar 0) ϕ)))
        = (fun m : (Domain M) => pattern_interpretation (update_evar_val x m ρₑ) ρₛ (evar_open 0 x ϕ) = Full).
      
      Proof.
        simpl. intros Hmp.
        rewrite -> pattern_interpretation_ex_simpl.
        unfold fresh_evar. simpl free_evars.
        repeat rewrite -> union_empty_r_L.
        rewrite -> union_empty_l_L.
        rewrite -> evar_open_and.
        remember (evar_fresh (elements (free_evars ϕ))) as x.
        apply Extensionality_Ensembles.
        unfold Included. unfold Ensembles.In. split; intros m H.
        - destruct H as [m [m' H]].
          rewrite -> pattern_interpretation_and_simpl in H.
          unfold Ensembles.In in H.
          destruct H as [m Hbound Hϕ].
          assert (Heqmm' : m = m').
          { unfold Ensembles.In in Hbound.
            simpl in Hbound.
            rewrite -> pattern_interpretation_free_evar_simpl in Hbound. destruct Hbound. 
            unfold update_evar_val.
            destruct (evar_eqdec x x).
            + simpl. reflexivity.
            + contradiction.
          }
          rewrite <- Heqmm' in Hϕ.
          apply predicate_not_empty_iff_full.
          + rewrite -> Heqx. unfold fresh_evar in Hmp. assumption.
          + intros Contra. apply eq_to_Same_set in Contra.
            apply Contains_Elements_Not_Empty in Contra.
            apply Contra. exists m. unfold In in Hϕ. apply Hϕ.
        - constructor. exists m.
          rewrite -> pattern_interpretation_and_simpl. constructor.
          + simpl. rewrite -> pattern_interpretation_free_evar_simpl.
            unfold Ensembles.In. rewrite -> update_evar_val_same. constructor.
          + apply eq_to_Same_set in H. destruct H as [H1 H2]. unfold Included in H2.
            specialize (H2 m). apply H2. unfold Ensembles.In. constructor.
      Qed.

      Lemma pattern_interpretation_forall_predicate ϕ ρₑ ρₛ :
        let x := fresh_evar ϕ in
      M_predicate M (evar_open 0 x ϕ) ->
      pattern_interpretation ρₑ ρₛ (patt_forall ϕ) = Full <->
      ∀ (m : Domain M), pattern_interpretation (update_evar_val x m ρₑ) ρₛ (evar_open 0 x ϕ) = Full.
    Proof.
      intros x H.
      unfold patt_forall.
      rewrite -> pattern_interpretation_not_simpl.
      
      rewrite eq_iff_Same_set.
      unfold Full.
      pose proof (Hcompl := @Compl_Compl_Ensembles (Domain M) (Full_set _)).
      rewrite <- eq_iff_Same_set in Hcompl.
      rewrite <- Hcompl at 1.
      rewrite <- Same_set_Compl.
      pose proof (Hscfie := @Complement_Full_is_Empty (Domain M)).
      apply eq_iff_Same_set in Hscfie.
      rewrite -> Hscfie at 1.
      rewrite <- eq_iff_Same_set.
      rewrite -> pattern_interpretation_exists_empty.

      assert (Hfr: fresh_evar (¬ϕ)%ml = fresh_evar ϕ).
      { unfold fresh_evar. apply f_equal. apply f_equal. simpl.
        rewrite -> union_empty_r_L. reflexivity.
      }

      rewrite -> Hfr. subst x.
      rewrite !simpl_evar_open.
      pose proof (Hcfe := @Complement_Full_is_Empty (Domain M)).
      apply eq_iff_Same_set in Hcfe.
      split; intros H'.
      - intros m.
        specialize (H' m).
        rewrite -> pattern_interpretation_not_simpl in H'.
        unfold Empty in H'. rewrite <- Hcfe in H'.
        apply eq_iff_Same_set in H'.
        apply Same_set_Compl in H'.
        apply eq_iff_Same_set. assumption.
      - intros m.
        specialize (H' m).
        rewrite -> pattern_interpretation_not_simpl.
        unfold Empty.
        rewrite <- Hcfe.
        apply eq_iff_Same_set.
        apply eq_iff_Same_set in H'.
        rewrite <- Same_set_Compl.
        assumption.
    Qed.

    Lemma pattern_interpretation_and_full ρₑ ρₛ ϕ₁ ϕ₂:
      @pattern_interpretation Σ M ρₑ ρₛ (patt_and ϕ₁ ϕ₂) = Full
      <-> (@pattern_interpretation Σ M ρₑ ρₛ ϕ₁ = Full
           /\ @pattern_interpretation Σ M ρₑ ρₛ ϕ₂ = Full).
    Proof.
      unfold Full.
      rewrite -> pattern_interpretation_and_simpl.
      split.
      - intros H.
        apply Intersection_eq_Full_eq in H.
        auto.
      - intros [H1 H2].
        rewrite -> H1. rewrite -> H2.
        apply Same_set_to_eq.
        apply Intersection_same.
    Qed.

    Lemma pattern_interpretation_predicate_not ρₑ ρₛ ϕ :
      M_predicate M ϕ ->
      pattern_interpretation ρₑ ρₛ (patt_not ϕ) = Full
      <-> @pattern_interpretation Σ M ρₑ ρₛ ϕ <> Full.
    Proof.
      intros Hpred.
      rewrite pattern_interpretation_not_simpl.
      split; intros H.
      - apply predicate_not_full_iff_empty.
        { apply Hpred. }
        apply eq_iff_Same_set in H.
        rewrite <- Compl_Compl_Ensembles_eq in H.
        apply Same_set_Compl in H.
        rewrite Complement_Full_is_Empty_eq in H.
        apply eq_iff_Same_set in H.
        unfold Empty.
        apply H.
      - apply predicate_not_full_iff_empty in H.
        2: { apply Hpred. }
        rewrite H.
        unfold Empty. unfold Full.
        apply Complement_Empty_is_Full_eq.
    Qed.
    
    End with_model.

    Lemma T_predicate_not Γ ϕ : T_predicate Γ ϕ -> T_predicate Γ (patt_not ϕ).
    Proof.
      unfold T_predicate.
      intros.
      auto using M_predicate_not.
    Qed.

    Hint Resolve T_predicate_not : core.

    Lemma T_predicate_or Γ ϕ₁ ϕ₂ : T_predicate Γ ϕ₁ -> T_predicate Γ ϕ₂ -> T_predicate Γ (patt_or ϕ₁ ϕ₂).
    Proof.
      unfold T_predicate.
      intros.
      auto using M_predicate_or.
    Qed.

    Hint Resolve T_predicate_or : core.

    Lemma T_predicate_and Γ ϕ₁ ϕ₂ : T_predicate Γ ϕ₁ -> T_predicate Γ ϕ₂ -> T_predicate Γ (patt_and ϕ₁ ϕ₂).
    Proof.
      unfold T_predicate.
      intros.
      auto using M_predicate_and.
    Qed.

    Hint Resolve T_predicate_or : core.


End with_signature.

(*Module Hints.*)
#[export]
        Hint Resolve M_predicate_impl : core.
 #[export]
       Hint Resolve M_predicate_or : core.
 #[export]
       Hint Resolve M_predicate_and : core.
 #[export]
       Hint Resolve M_predicate_top : core.
 #[export]
       Hint Resolve M_predicate_forall : core.
 #[export]
       Hint Resolve M_predicate_iff : core.
 #[export]
       Hint Resolve T_predicate_not : core.
 #[export]
       Hint Resolve T_predicate_or : core.
 #[export]
       Hint Resolve T_predicate_or : core.
(*End Hints.*)
