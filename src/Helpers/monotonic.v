From Coq Require Import Ensembles.
From stdpp Require Import fin_sets.
From MatchingLogic.Utils Require Import Lattice.
From MatchingLogic Require Import Syntax Semantics.

Import MatchingLogic.Syntax.Notations.
Open Scope ml_scope.

Section monotonic.

  Context {sig : Signature}.
  Existing Instance variables. 


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
        respects_blacklist (phi1 $ phi2)%ml Bp Bn.
    Proof.
      intros. unfold respects_blacklist in *.
      intros. split; intros; constructor; firstorder; firstorder.
    Qed.

    Lemma respects_blacklist_app_1 : forall (phi1 phi2 : Pattern) (Bp Bn : Ensemble svar),
        respects_blacklist (phi1 $ phi2)%ml Bp Bn -> respects_blacklist phi1 Bp Bn.
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
        positive_occurrence_db dbi phi ->
        X ∉ (free_svars phi) ->
        respects_blacklist (svar_open dbi X phi) (Empty_set svar) (Ensembles.Singleton svar X).
    Proof.
      intros phi dbi X Hpodb Hni.
      pose proof (Hpno := @not_free_implies_positive_negative_occurrence sig phi X Hni).
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
        respects_blacklist (svar_open 0 X phi) (Empty_set svar) (Ensembles.Singleton svar X).
    Proof.
      intros. destruct H as [Hpo Hwfp].
      pose proof (Hfr := @set_svar_fresh_is_fresh sig phi).
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
            unfold update_svar_val in *; destruct (svar_eqdec X x); subst.
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
              unfold not in *. unfold Ensembles.In in *. intros.
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
            intros. repeat rewrite -> pattern_interpretation_imp_simpl.
            unfold leq in *. simpl in *. unfold Included in *. intros.
            destruct H0.
            + left. unfold Complement in *.
              unfold not in *. unfold Ensembles.In in *. intros.
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
          pose proof (Hwfp' := @evar_open_wfp sig n phi Hsz' 0 fresh Hwfp).
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
            pose proof (Hszeq := svar_open_size 0 X' phi).
            assert (Hsz'': size phi' <= n).
            { rewrite -> Heqphi'. rewrite <- Hszeq. assumption. }
            specialize (IHn phi' Hsz'').
            simpl in Hwfp. destruct Hwfp as [Hpo Hwfp].
            
            assert (Hrb': respects_blacklist phi' (Empty_set svar) (Ensembles.Singleton svar X')).
            { subst. apply mu_wellformed_respects_blacklist. assumption. }

            assert (Hwfp' : well_formed_positive phi').
            { subst. apply wfp_svar_open. assumption. }

            remember IHn as IHn'. clear HeqIHn'.
            specialize (IHn' Hwfp' (Empty_set svar) (Ensembles.Singleton svar X') Hrb' evar_val).
            remember IHn' as Hy. clear HeqHy.
            rename IHn' into Hx.
            specialize (Hx (update_svar_val V x svar_val) X').
            specialize (Hy (update_svar_val V y svar_val) X').

            apply lfp_preserves_order.
            - apply Hy. constructor.
            - apply Hx. constructor.
            - clear Hx. clear Hy.
              intros.
              destruct (svar_eqdec X' V).
              + (* X' = V *)
                rewrite <- e.
                repeat rewrite -> update_svar_val_shadow.
                unfold leq. simpl. unfold Included. unfold In. auto.
              + (* X' <> V*)
                pose proof (Uhsvcx := @update_svar_val_comm sig M X' V x0 x svar_val n0).
                rewrite -> Uhsvcx.
                pose proof (Uhsvcy := @update_svar_val_comm sig M X' V x0 y svar_val n0).
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
                    * inversion Hrbn. assumption.
                  - intros. destruct H1.
                }

                specialize (IHn Hwfp' (Ensembles.Singleton svar V) (Empty_set svar) HrbV).
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
            pose proof (Hszeq := svar_open_size 0 X' phi).
            assert (Hsz'': size phi' <= n).
            { rewrite -> Heqphi'. rewrite <- Hszeq. assumption. }
            specialize (IHn phi' Hsz'').
            simpl in Hwfp. destruct Hwfp as [Hpo Hwfp].
            
            assert (Hrb': respects_blacklist phi' (Empty_set svar) (Ensembles.Singleton svar X')).
            { subst. apply mu_wellformed_respects_blacklist. assumption. }

            assert (Hwfp' : well_formed_positive phi').
            { subst. apply wfp_svar_open. assumption. }

            remember IHn as IHn'. clear HeqIHn'.
            specialize (IHn' Hwfp' (Empty_set svar) (Ensembles.Singleton svar X') Hrb' evar_val).
            remember IHn' as Hy. clear HeqHy.
            rename IHn' into Hx.
            specialize (Hx (update_svar_val V x svar_val) X').
            specialize (Hy (update_svar_val V y svar_val) X').

            apply lfp_preserves_order.
            - apply Hx. constructor.
            - apply Hy. constructor.
            - clear Hy. clear Hx.
              intros.
              destruct (svar_eqdec X' V).
              + (* X' = V *)
                rewrite <- e.
                repeat rewrite -> update_svar_val_shadow.
                unfold leq. simpl. unfold Included. unfold Ensembles.In. auto.
              + (* X' <> V*)
                pose proof (Uhsvcx := @update_svar_val_comm sig M X' V x0 x svar_val n0).
                rewrite -> Uhsvcx.
                pose proof (Uhsvcy := @update_svar_val_comm sig M X' V x0 y svar_val n0).
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
                    * inversion Hrbp. assumption.
                }

                specialize (IHn Hwfp' (Empty_set svar) (Ensembles.Singleton svar V) HrbV).
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
      specialize (Hmono (Empty_set svar) (Ensembles.Singleton svar (fresh_svar phi))).
      specialize (Hmono Hrb evar_val svar_val (fresh_svar phi)).
      destruct Hmono.
      apply H2.
      constructor.
    Qed.
  End with_model.

End monotonic.
