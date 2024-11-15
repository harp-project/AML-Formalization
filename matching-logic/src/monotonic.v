From Coq Require Import Ensembles.
From MatchingLogic Require Export Semantics.

Import MatchingLogic.Syntax.Notations.
Import MatchingLogic.Substitution.Notations.

Section monotonic.
  Open Scope ml_scope.
  Context {Σ : Signature}.


  (* Definitions and lemmas inside this section are useful for proving `is_monotonic`,
   but they are probably not usefull for any other purpose. *)
  Section respects_blacklist.
    (* Bp - Blacklist of Positive Occurrence - these variables can occur only negatively.
     Bn - Blacklist of Negative Occurrence - these variables can occur only positively *)
    Definition respects_blacklist (phi : Pattern) (Bp Bn : Ensemble svar) : Prop :=
      forall (var : svar),
        (Bp var -> svar_has_positive_occurrence var phi = false) /\ (Bn var -> @svar_has_negative_occurrence Σ var phi = false).

    Lemma respects_blacklist_app : forall (phi1 phi2 : Pattern) (Bp Bn : Ensemble svar),
        respects_blacklist phi1 Bp Bn -> respects_blacklist phi2 Bp Bn ->
        respects_blacklist (phi1 ⋅ phi2)%ml Bp Bn.
    Proof.
      intros. unfold respects_blacklist in *.
      intros. split; intros; cbn; apply orb_false_iff; split; try apply H; try apply H0; auto.
    Qed.

    Lemma respects_blacklist_app_1 : forall (phi1 phi2 : Pattern) (Bp Bn : Ensemble svar),
        respects_blacklist (phi1 ⋅ phi2)%ml Bp Bn -> respects_blacklist phi1 Bp Bn.
    Proof.
      unfold respects_blacklist.
      intros.
      specialize (H var).
      destruct H as [Hneg Hpos].
      split; intros.
      * specialize (Hneg H). cbn in Hneg.
        apply orb_false_iff in Hneg as [Hneg _]. assumption.
      * specialize (Hpos H). cbn in Hneg.
        apply orb_false_iff in Hpos as [Hpos _]. assumption.
    Qed.

    (* This proof is the same as for app_1 *)
    Lemma respects_blacklist_app_2 : forall (phi1 phi2 : Pattern) (Bp Bn : Ensemble svar),
        respects_blacklist (phi1 ⋅ phi2) Bp Bn -> respects_blacklist phi2 Bp Bn.
    Proof.
      unfold respects_blacklist.
      intros.
      specialize (H var).
      destruct H as [Hneg Hpos].
      split; intros.
      * specialize (Hneg H). cbn in Hneg.
        apply orb_false_iff in Hneg as [_ Hneg]. assumption.
      * specialize (Hpos H). cbn in Hneg.
        apply orb_false_iff in Hpos as [_ Hpos]. assumption.
    Qed.

    Lemma respects_blacklist_impl : forall (phi1 phi2 : Pattern) (Bp Bn : Ensemble svar),
        respects_blacklist phi1 Bn Bp -> respects_blacklist phi2 Bp Bn ->
        respects_blacklist (phi1 ---> phi2) Bp Bn.
    Proof.
      intros. unfold respects_blacklist in *.
      intros. split; intros; cbn; apply orb_false_iff; split; try apply H; try apply H0; auto.
    Qed.

    Lemma respects_blacklist_impl_1 : forall (phi1 phi2 : Pattern) (Bp Bn : Ensemble svar),
        respects_blacklist (phi1 ---> phi2) Bp Bn -> respects_blacklist phi1 Bn Bp.
    Proof.
      unfold respects_blacklist.
      intros.
      specialize (H var).
      destruct H as [Hpos Hneg].
      split; intros.
      * specialize (Hneg H). cbn in Hneg.
        apply orb_false_iff in Hneg as [Hneg _]. assumption.
      * specialize (Hpos H). cbn in Hneg.
        apply orb_false_iff in Hpos as [Hpos _]. assumption.
    Qed.

    Lemma respects_blacklist_impl_2 : forall (phi1 phi2 : Pattern) (Bp Bn : Ensemble svar),
        respects_blacklist (phi1 ---> phi2) Bp Bn -> respects_blacklist phi2 Bp Bn.
    Proof.
      unfold respects_blacklist.
      intros.
      specialize (H var).
      destruct H as [Hpos Hneg].
      split; intros.
      * specialize (Hpos H). cbn in Hpos.
        apply orb_false_iff in Hpos as [_ Hpos]. assumption.
      * specialize (Hneg H). cbn in Hneg.
        apply orb_false_iff in Hneg as [_ Hneg]. assumption.
    Qed.

    Lemma respects_blacklist_ex : forall (phi : Pattern) (Bp Bn : Ensemble svar),
        respects_blacklist (patt_exists phi) Bp Bn -> respects_blacklist phi Bp Bn.
    Proof.
      intros. unfold respects_blacklist in *.
      intros. specialize (H var). destruct H as [Hneg Hpos].
      split; intros.
      * specialize (Hneg H). assumption.
      * specialize (Hpos H). assumption.
    Qed.

    Lemma respects_blacklist_ex' : forall (phi : Pattern) (Bp Bn : Ensemble svar),
        respects_blacklist phi Bp Bn -> respects_blacklist (patt_exists phi) Bp Bn.
    Proof.
      unfold respects_blacklist. intros.
      specialize (H var).
      destruct H as [Hneg Hpos].
      split; auto.
    Qed.

    Lemma respects_blacklist_mu : forall (phi : Pattern) (Bp Bn : Ensemble svar),
        respects_blacklist (patt_mu phi) Bp Bn -> respects_blacklist phi Bp Bn.
    Proof.
      unfold respects_blacklist. intros.
      specialize (H var).
      destruct H as [Hneg Hpos].
      split; intros; auto.
    Qed.

    Lemma respects_blacklist_mu' : forall (phi : Pattern) (Bp Bn : Ensemble svar),
        respects_blacklist phi Bp Bn -> respects_blacklist (patt_mu phi) Bp Bn.
    Proof.
      unfold respects_blacklist. intros.
      specialize (H var).
      destruct H as [Hneg Hpos].
      split; auto.
    Qed.

    Lemma respects_blacklist_union : forall (phi : Pattern) (Bp1 Bn1 Bp2 Bn2 : Ensemble svar),
        respects_blacklist phi Bp1 Bn1 ->
        respects_blacklist phi Bp2 Bn2 ->
        respects_blacklist phi (Ensembles.Union svar Bp1 Bp2) (Ensembles.Union svar Bn1 Bn2).
    Proof.
      unfold respects_blacklist.
      induction phi; intros; split; intros;
        destruct H1; unfold In in *;
          try specialize (H x0); try specialize (H x);
            try specialize (H0 x0); try specialize (H0 x); firstorder; try constructor.
    Qed.

    Lemma positive_occurrence_respects_blacklist_svar_open :
      forall (phi : Pattern) (dbi : db_index) (X : svar),
        no_negative_occurrence_db_b dbi phi ->
        X ∉ (free_svars phi) ->
        respects_blacklist (phi^{svar: dbi ↦ X}) (Empty_set svar) (Ensembles.Singleton svar X).
    Proof.
      intros phi dbi X Hpodb Hni.
      pose proof (Hpno := @not_free_implies_positive_negative_occurrence Σ phi X Hni).
      unfold respects_blacklist. intros.
      split; intros.
      * firstorder using positive_negative_occurrence_db_named.
      * inversion H. subst.
        pose (Hpd := positive_negative_occurrence_db_named phi dbi var).
        destruct Hpd as [Hpd1 Hpd2].
        destruct Hpno as [Hpno1 Hpno2].
        auto.
    Qed.

    Lemma mu_wellformed_respects_blacklist : forall (phi : Pattern) (X : svar),
        well_formed_positive (patt_mu phi) ->
        svar_is_fresh_in X phi ->
        respects_blacklist (phi^{svar: 0 ↦ X}) (Empty_set svar) (Ensembles.Singleton svar X).
    Proof.
      intros phi X H Hfr. simpl in H.
      apply andb_true_iff in H.
      destruct H as [Hpo Hwfp].
      apply positive_occurrence_respects_blacklist_svar_open; auto.
    Qed.


    (*
Lemma respects_blacklist_ex' : forall (phi : Pattern) (Bp Bn : Ensemble svar),
    respects_blacklist ()
respects_blacklist (evar_open 0 (evar_fresh variables (free_evars phi)) phi) Bp B
     *)

    Lemma evar_open_respects_blacklist :
      forall (phi : Pattern) (Bp Bn : Ensemble svar) (x : evar) (n : nat),
        respects_blacklist phi Bp Bn ->
        respects_blacklist (phi^{evar: n ↦ x}) Bp Bn.
    Proof.
      induction phi; try auto.
      - (* EVar bound *)
        intros. cbn.
        case_match; assumption.
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
        intros. mlSimpl.
        apply respects_blacklist_ex'.
        apply respects_blacklist_ex in H.
        auto.
    Qed.
  End respects_blacklist.

  (* From the following section, `update_svar_val_comm`, `update_svar_shadow`
   and `is_monotonic` may be generally useful.
   The lemma `respects_blacklist_implies_monotonic` is only a technical lemma for proving `is_monotonic`,
   which is the main lemma of the section.
   *)
  Section with_model.

    Context {M : Model}.
    Let A := propset (Domain M).
    Let OS := PropsetOrderedSet (Domain M).
    Let L := PowersetLattice (Domain M).

    Lemma respects_blacklist_implies_monotonic :
      forall (n : nat) (phi : Pattern),
        le (size phi) n -> well_formed_positive phi ->
        forall (Bp Bn : Ensemble svar),
          respects_blacklist phi Bp Bn ->
          forall (ρ : @Valuation _ M)
                 (X : svar),
            (Bp X ->
             @AntiMonotonicFunction A OS (fun (S : propset (Domain M)) =>
                                            (@eval Σ M (update_svar_val X S ρ) phi)
                                         )
            ) /\
            (Bn X ->
             @MonotonicFunction A OS (fun S : propset (Domain M) =>
                                        (@eval Σ M (update_svar_val X S ρ) phi))
            )
    .
    Proof.
      induction n.
      - (* n = 0 *)
        intros. destruct phi; simpl in H; try inversion H.
        + (* EVar free *)
          unfold MonotonicFunction. unfold AntiMonotonicFunction. unfold leq. simpl.
          setoid_rewrite -> elem_of_subseteq.
          unfold In. split; intros; rewrite -> eval_free_evar_simpl in *; assumption.
        + (* SVar free *)
          unfold MonotonicFunction. unfold AntiMonotonicFunction. unfold leq. simpl.
          setoid_rewrite -> elem_of_subseteq.
          split; intros; rewrite -> eval_free_svar_simpl in *;
            unfold update_svar_val in *; destruct (decide (X = x)); subst.
          * unfold respects_blacklist in H1.
            specialize (H1 x).
            destruct H1 as [Hneg Hpos].
            specialize (Hneg H2).
            inversion Hneg. subst. cbn in H5. case_match; congruence.
          * simpl. simpl in H4. destruct (decide (X = x)). contradiction. apply H4.
          * simpl. simpl in H4. rewrite decide_eq_same. rewrite decide_eq_same in H4.
            auto.
          * simpl. simpl in H4. destruct (decide (X = x)). contradiction. apply H4.
            
        + (* EVar bound *)
          unfold AntiMonotonicFunction. unfold MonotonicFunction. unfold leq. simpl.
          split; intros; repeat rewrite -> eval_bound_evar_simpl;
            setoid_rewrite -> elem_of_subseteq;
            unfold In; intros; assumption.
        + (* SVar bound *)
          unfold AntiMonotonicFunction. unfold MonotonicFunction. unfold leq. simpl.
          split; intros; repeat rewrite -> eval_bound_svar_simpl;
            setoid_rewrite -> elem_of_subseteq;
            unfold In; intros; assumption.
        + (* Sym *)
          unfold AntiMonotonicFunction. unfold MonotonicFunction. unfold leq. simpl.
          split; intros; repeat rewrite -> eval_sym_simpl;
            setoid_rewrite -> elem_of_subseteq;
            unfold In; intros; assumption.
        + (* Bot *)
          unfold AntiMonotonicFunction. unfold MonotonicFunction. unfold leq. simpl.
          split; intros; rewrite -> eval_bott_simpl;
            setoid_rewrite -> elem_of_subseteq; intros; inversion H4.
      - (* S n *)
        intros phi Hsz Hwfp Bp Bn Hrb ρ V.
        destruct phi.
        * apply IHn. simpl. lia. assumption. assumption.
        * apply IHn. simpl. lia. assumption. assumption.
        * apply IHn. simpl. lia. assumption. assumption.
        * apply IHn. simpl. lia. assumption. assumption.
        * apply IHn. simpl. lia. assumption. assumption.
        * (* App *)
          remember (respects_blacklist_app_1 phi1 phi2 Bp Bn Hrb) as Hrb1. clear HeqHrb1.
          remember (respects_blacklist_app_2 phi1 phi2 Bp Bn Hrb) as Hrb2. clear HeqHrb2.
          simpl in Hwfp.
          apply andb_true_iff in Hwfp.
          destruct Hwfp as [Hwfp1 Hwfp2].

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
            repeat rewrite -> eval_app_simpl.
            unfold app_ext. unfold leq in *. simpl in *.
            setoid_rewrite -> elem_of_subseteq.
            rewrite -> elem_of_subseteq in H.
            intros.
            destruct H0. destruct H0. destruct H0. destruct H1.
            
            exists x1. exists x2.
            split.
            - specialize (IHn phi1 Hsz1 Hwfp1 Bp Bn Hrb1 ρ V).
              destruct IHn as [IHam IHmo].
              apply (IHam HBp x y H x1). assumption.
            - split.
              + specialize (IHn phi2 Hsz2 Hwfp2 Bp Bn Hrb2 ρ V).
                destruct IHn as [IHam IHmo].
                apply (IHam HBp x y H x2). assumption.
              + assumption.
          }
          {
            intros HBp. unfold MonotonicFunction in *.
            intros.
            repeat rewrite -> eval_app_simpl.
            unfold app_ext. unfold leq in *. simpl in *.
            setoid_rewrite -> elem_of_subseteq.
            rewrite -> elem_of_subseteq in H.
            intros.
            destruct H0. destruct H0. destruct H0. destruct H1.
            
            exists x1. exists x2.
            split.
            - specialize (IHn phi1 Hsz1 Hwfp1 Bp Bn Hrb1 ρ V).
              destruct IHn as [IHam IHmo].
              apply (IHmo HBp x y H x1). assumption.
            - split.
              + specialize (IHn phi2 Hsz2 Hwfp2 Bp Bn Hrb2 ρ V).
                destruct IHn as [IHam IHmo].
                apply (IHmo HBp x y H x2). assumption.
              + assumption.
          }
          
        * (* Bot *)
          apply IHn. simpl. lia. assumption. assumption.
        * (* Impl *)
          (* phi1 and phi2 are well-formed-positive *)
          simpl in Hwfp.
          apply andb_true_iff in Hwfp.
          destruct Hwfp as [Hwfp1 Hwfp2].

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
          specialize (IHn1 phi1 Hsz1 Hwfp1 Bn Bp Hrb1 ρ V).
          specialize (IHn2 phi2 Hsz2 Hwfp2 Bp Bn Hrb2 ρ V).
          unfold AntiMonotonicFunction in *.
          unfold MonotonicFunction in *.
          
          split.
          {
            intros HBp.
            intros.
            repeat rewrite -> eval_imp_simpl.
            unfold leq in *. simpl in *.
            setoid_rewrite -> elem_of_subseteq.
            rewrite -> elem_of_subseteq in H.
            intros.
            destruct H0.
            + left.
              rewrite -> elem_of_difference in H0.
              destruct H0 as [_ H0].
              rewrite -> elem_of_difference.
              split.
              { apply elem_of_top'. }
              
              unfold not in *. intros.
              apply H0.
              
              destruct IHn1 as [IHn11 IHn12].
              apply (IHn12 HBp x y H x0).
              apply H1.
            + right. unfold Ensembles.In in *.
              destruct IHn2 as [IHn21 IHn22].
              apply (IHn21 HBp x y H x0 H0).
          }
          {
            intros HBn.
            intros. repeat rewrite -> eval_imp_simpl.
            unfold leq in *. simpl in *.
            rewrite elem_of_subseteq. rewrite -> elem_of_subseteq in H.
            intros.
            destruct H0.
            + left.

              rewrite -> elem_of_difference in H0.
              destruct H0 as [_ H0].
              rewrite -> elem_of_difference.
              split.
              { apply elem_of_top'. }
           
              unfold not in *. intros.
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
          specialize (IHn (phi^{evar: 0 ↦ (evar_fresh (elements (free_evars phi)))})).
          rewrite <- evar_open_size in IHn.
          assert (Hsz': size phi <= n). simpl in *. lia.
          remember (evar_fresh (elements (free_evars phi))) as fresh.
          pose proof (Hwfp' := @wfp_evar_open Σ phi fresh 0 Hwfp).
          specialize (IHn Hsz' Hwfp' Bp Bn).
          pose proof (Hrb'' := evar_open_respects_blacklist phi Bp Bn fresh 0 Hrb').
          unfold MonotonicFunction in *. unfold AntiMonotonicFunction in *.
          unfold leq. simpl.
          setoid_rewrite elem_of_subseteq.

          split; intros HBp S1 S2 Hincl; rewrite -> eval_ex_simpl; simpl;
          unfold stdpp_ext.propset_fa_union; intros m; rewrite -> elem_of_PropSet;
            intros [c Hc]; rewrite -> eval_ex_simpl; simpl;
              unfold stdpp_ext.propset_fa_union; rewrite -> elem_of_PropSet; exists c;
              remember (update_evar_val fresh c ρ) as ρ';
              specialize (IHn Hrb'' ρ' V);
              destruct IHn as [IHn1 IHn2].
          {
            specialize (IHn1 HBp S1 S2 Hincl).
            remember (phi^{evar: 0 ↦ fresh}) as phi'.
            remember (update_svar_val V S1 ρ') as ρ''.
            unfold leq in IHn1. simpl in *. unfold Included in *. unfold In in *.
            subst.
            apply IHn1. apply Hc.
          }
          {
            specialize (IHn2 HBp S1 S2 Hincl).
            remember (phi^{evar: 0 ↦ fresh}) as phi'.
            remember (update_svar_val V S1 ρ') as ρ''.
            unfold leq in IHn1. simpl in *. unfold Included in *. unfold In in *.
            subst.
            apply IHn2. apply Hc.
          }
        * (* Mu *)
          remember Hwfp as Hwfpmu. clear HeqHwfpmu.
          simpl in Hsz.
          assert (Hsz': size phi <= n).
          { lia. }
          split.
          {
            unfold AntiMonotonicFunction. intros.
            repeat rewrite -> eval_mu_simpl.
            Arguments LeastFixpointOf : simpl never.
            Arguments leq : simpl never.
            simpl.

            remember (fresh_svar phi) as X'.
            remember (phi^{svar: 0 ↦ X'}) as phi'.
            pose proof (Hszeq := svar_open_size 0 X' phi).
            assert (Hsz'': size phi' <= n).
            { rewrite -> Heqphi'. rewrite <- Hszeq. assumption. }
            specialize (IHn phi' Hsz'').
            simpl in Hwfp.

            assert (Hrb': respects_blacklist phi' (Empty_set svar) (Ensembles.Singleton svar X')).
            { subst. apply mu_wellformed_respects_blacklist. apply Hwfpmu. apply set_svar_fresh_is_fresh. }

            simpl in Hwfpmu. apply andb_true_iff in Hwfpmu.
            destruct Hwfpmu as [Hnonegphi Hwfpphi].
            assert (Hwfp' : well_formed_positive phi').
            { subst. apply wfp_svar_open. exact Hwfpphi. }

            remember IHn as IHn'. clear HeqIHn'.
            specialize (IHn' Hwfp' (Empty_set svar) (Ensembles.Singleton svar X') Hrb').
            remember IHn' as Hy. clear HeqHy.
            rename IHn' into Hx.
            specialize (Hx (update_svar_val V x ρ) X').
            specialize (Hy (update_svar_val V y ρ) X').

            apply lfp_preserves_order.
            - apply Hy. constructor.
            - apply Hx. constructor.
            - clear Hx. clear Hy.
              intros.
              destruct (decide (X' = V)).
              + (* X' = V *)
                rewrite <- e.
                repeat rewrite -> update_svar_val_shadow.
                unfold leq. simpl. unfold Included. unfold In. auto.
              + (* X' <> V*)
                pose proof (Uhsvcx := @update_svar_val_comm Σ M X' V x0 x ρ n0).
                rewrite -> Uhsvcx.
                pose proof (Uhsvcy := @update_svar_val_comm Σ M X' V x0 y ρ n0).
                rewrite -> Uhsvcy.

                assert (HrbV: respects_blacklist phi' (Ensembles.Singleton svar V) (Empty_set svar)).
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
                    * assumption.
                  - intros. destruct H1.
                }

                specialize (IHn Hwfp' (Ensembles.Singleton svar V) (Empty_set svar) HrbV).
                specialize (IHn (update_svar_val X' x0 ρ) V).
                destruct IHn as [IHam IHmo].
                apply IHam. constructor. assumption.
          }
          (* This is the same as the previous, with minor changes *)
          {
            unfold MonotonicFunction. intros.
            repeat rewrite -> eval_mu_simpl.
            Arguments LeastFixpointOf : simpl never.
            Arguments leq : simpl never.
            simpl.

            remember (fresh_svar phi) as X'.
            remember (phi^{svar: 0 ↦ X'}) as phi'.
            pose proof (Hszeq := svar_open_size 0 X' phi).
            assert (Hsz'': size phi' <= n).
            { rewrite -> Heqphi'. rewrite <- Hszeq. assumption. }
            specialize (IHn phi' Hsz'').
            simpl in Hwfp.

            assert (Hrb': respects_blacklist phi' (Empty_set svar) (Ensembles.Singleton svar X')).
            { subst. apply mu_wellformed_respects_blacklist. apply Hwfpmu. apply set_svar_fresh_is_fresh. }

            simpl in Hwfpmu. apply andb_true_iff in Hwfpmu.
            destruct Hwfpmu as [Hnonegphi Hwfpphi].
            assert (Hwfp' : well_formed_positive phi').
            { subst. apply wfp_svar_open. exact Hwfpphi. }

            remember IHn as IHn'. clear HeqIHn'.
            specialize (IHn' Hwfp' (Empty_set svar) (Ensembles.Singleton svar X') Hrb').
            remember IHn' as Hy. clear HeqHy.
            rename IHn' into Hx.
            specialize (Hx (update_svar_val V x ρ) X').
            specialize (Hy (update_svar_val V y ρ) X').

            apply lfp_preserves_order.
            - apply Hx. constructor.
            - apply Hy. constructor.
            - clear Hy. clear Hx.
              intros.
              destruct (decide (X' = V)).
              + (* X' = V *)
                rewrite <- e.
                repeat rewrite -> update_svar_val_shadow.
                unfold leq. simpl. unfold Included. unfold Ensembles.In. auto.
              + (* X' <> V*)
                pose proof (Uhsvcx := @update_svar_val_comm Σ M X' V x0 x ρ n0).
                rewrite -> Uhsvcx.
                pose proof (Uhsvcy := @update_svar_val_comm Σ M X' V x0 y ρ n0).
                rewrite -> Uhsvcy.

                assert (HrbV: respects_blacklist phi' (Empty_set svar) (Ensembles.Singleton svar V)).
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
                    * assumption.
                }

                specialize (IHn Hwfp' (Empty_set svar) (Ensembles.Singleton svar V) HrbV).
                specialize (IHn (update_svar_val X' x0 ρ) V).
                destruct IHn as [IHam IHmo].
                apply IHmo. constructor. assumption.
          }
    Qed.

    Lemma is_monotonic : forall (phi : Pattern)
                                (X : svar)
                                (ρ : Valuation),
        well_formed_positive (mu, phi) ->
        svar_is_fresh_in X phi ->
        @MonotonicFunction A OS
                           (fun S : propset (Domain M) =>
                              (@eval Σ M (update_svar_val X S ρ)
                                                       (phi^{svar: 0 ↦ X}))).
    Proof.
      simpl. intros phi X ρ Hwfp Hfr.
      pose proof (Hrb := mu_wellformed_respects_blacklist phi X Hwfp Hfr).
      simpl in Hrb.
      inversion Hwfp.
      remember (phi^{svar: 0 ↦ X}) as phi'.
      assert (Hsz : size phi' <= size phi').
      { lia. }
      pose proof (Hmono := respects_blacklist_implies_monotonic (size phi') phi').
      assert (Hwfp' : well_formed_positive phi').
      { subst. apply wfp_svar_open.
        apply andb_true_iff in Hwfp.
        apply (proj2 Hwfp).
      }
      specialize (Hmono Hsz Hwfp').
      specialize (Hmono (Empty_set svar) (Ensembles.Singleton svar X)).
      specialize (Hmono Hrb ρ X).
      destruct Hmono as [Hantimono Hmono].
      apply Hmono.
      constructor.
    Qed.
  End with_model.

End monotonic.
