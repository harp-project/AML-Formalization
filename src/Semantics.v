From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Coq Require Import Ensembles.
From Coq.Logic Require Import FunctionalExtensionality Classical_Pred_Type.
From Coq.micromega Require Import Lia.
From Coq.Program Require Import Wf.

From stdpp Require Import base fin_sets.
From stdpp Require Import pmap gmap mapset fin_sets.

From MatchingLogic.Utils Require Import Lattice Ensembles_Ext stdpp_ext extralibrary.
From MatchingLogic Require Import Syntax.

Import MatchingLogic.Syntax.Notations.
(** ** Matching Logic Semantics *)
Section semantics.
  
    Context {signature : Signature}.
    Existing Instance variables.


    (* Model of AML ref. snapshot: Definition 2 *)

    Record Model := {
      Domain : Type;
      (* TODO think about whether or not to make it an existential formula. Because that would affect the equality,
     due to proof irrelevance. *)
      nonempty_witness : Domain;
      Domain_eq_dec : forall (a b : Domain), {a = b} + {a <> b};
      app_interp : Domain -> Domain -> Power Domain;
      sym_interp (sigma : symbols) : Power Domain;
                   }.

    Definition Empty {M : Model} := Empty_set (Domain M).
    Definition Full {M : Model} := Full_set (Domain M).
    
    Lemma empty_impl_not_full : forall {M : Model} (S : Power (Domain M)),
        S = Empty -> S <> Full.
    Proof.
      intros M S H.
      assert (H1: Same_set (Domain M) S Empty).
      { subst. apply Same_set_refl. }
      intros HContra. rewrite -> HContra in H1.
      unfold Empty in H1. unfold Full in H1.
      unfold Same_set in H1. unfold Included in H1.
      assert (Hexin : Ensembles.In (Domain M) Full (nonempty_witness M)).
      { unfold In. unfold Full. constructor. }
      firstorder.
    Qed.

    Lemma Private_full_impl_not_empty : forall {M : Model} (S : Power (Domain M)),
        Same_set (Domain M) S Full ->
        ~ Same_set (Domain M) S Empty.
    Proof.
      unfold Same_set. unfold Included. unfold not. intros.
      assert (Hexin : Ensembles.In (Domain M) (Full_set (Domain M)) (nonempty_witness M)).
      { unfold In. constructor. }
      firstorder.
    Qed.

    Lemma full_impl_not_empty : forall {M : Model} (S : Power (Domain M)),
        S = Full -> S <> Empty.
    Proof.
      intros M S H Contra.
      epose proof (P := @Private_full_impl_not_empty M S _).
      apply P. rewrite -> Contra. apply Same_set_refl.
      Unshelve. rewrite -> H. apply Same_set_refl.
    Qed.

    Definition EVarVal {m : Model} : Type := evar -> Domain m.
    Definition SVarVal {m : Model} : Type := svar -> Power (Domain m).

    Definition update_evar_val {m : Model} 
               (v : evar) (x : Domain m) (evar_val : @EVarVal m) : EVarVal :=
      fun v' : evar => if evar_eqdec v v' then x else evar_val v'.

    Definition update_svar_val {m : Model}
               (v : svar) (X : Power (Domain m)) (svar_val : @SVarVal m)  : SVarVal :=
      fun v' : svar => if svar_eqdec v v' then X else svar_val v'.

    Lemma update_svar_val_comm M :
      forall (X1 X2 : svar) (S1 S2 : Power (Domain M)) (svar_val : @SVarVal M),
        X1 <> X2 ->
        update_svar_val X1 S1 (update_svar_val X2 S2 svar_val)
        = update_svar_val X2 S2 (update_svar_val X1 S1 svar_val).
    Proof.
      intros.
      unfold update_svar_val.
      apply functional_extensionality.
      intros.
      destruct (svar_eqdec X1 x),(svar_eqdec X2 x); subst.
      * unfold not in H. assert (x = x). reflexivity. apply H in H0. destruct H0.
      * reflexivity.
      * reflexivity.
      * reflexivity.
    Qed.

    Lemma update_svar_val_shadow M : forall (X : svar)
                                            (S1 S2 : Power (Domain M))
                                            (svar_val : @SVarVal M),
        update_svar_val X S1 (update_svar_val X S2 svar_val) = update_svar_val X S1 svar_val.
    Proof.
      intros. unfold update_svar_val. apply functional_extensionality.
      intros. destruct (svar_eqdec X x); reflexivity.
    Qed.

    Lemma update_svar_val_neq M (ρₛ : @SVarVal M) X1 S X2 :
      X1 <> X2 -> update_svar_val X1 S ρₛ X2 = ρₛ X2.
    Proof.
      unfold update_svar_val. intros.
      destruct (svar_eqdec X1 X2); simpl.
      - contradiction.
      - auto.
    Qed.
    
    Lemma update_evar_val_comm M :
      forall (x1 x2 : evar) (m1 m2 : Domain M) (evar_val : @EVarVal M),
        x1 <> x2 ->
        update_evar_val x1 m1 (update_evar_val x2 m2 evar_val)
        = update_evar_val x2 m2 (update_evar_val x1 m1 evar_val).
    Proof.
      intros.
      unfold update_evar_val.
      apply functional_extensionality.
      intros.
      destruct (evar_eqdec x1 x),(evar_eqdec x2 x); subst.
      * unfold not in H. assert (x = x). reflexivity. apply H in H0. destruct H0.
      * reflexivity.
      * reflexivity.
      * reflexivity.
    Qed.

    Lemma update_evar_val_shadow M : forall (x : evar)
                                            (m1 m2 : Domain M)
                                            (evar_val : @EVarVal M),
        update_evar_val x m1 (update_evar_val x m2 evar_val) = update_evar_val x m1 evar_val.
    Proof.
      intros. unfold update_evar_val. apply functional_extensionality.
      intros. destruct (evar_eqdec x x0); reflexivity.
    Qed.

    Lemma update_evar_val_same M x m ρₑ : @update_evar_val M x m ρₑ x = m.
    Proof.
      unfold update_evar_val. destruct (evar_eqdec x x); simpl.
      + reflexivity.
      + contradiction.
    Qed.

    Lemma update_evar_val_neq M (ρₑ : @EVarVal M) x1 e x2 :
      x1 <> x2 -> update_evar_val x1 e ρₑ x2 = ρₑ x2.
    Proof.
      unfold update_evar_val. intros.
      destruct (evar_eqdec x1 x2); simpl.
      - contradiction.
      - auto.
    Qed.

    Lemma update_evar_val_same_2 M x ρₑ : @update_evar_val M x (ρₑ x) ρₑ = ρₑ.
    Proof.
      apply functional_extensionality. intros x0.
      unfold update_evar_val. destruct (evar_eqdec x x0); simpl.
      - subst. reflexivity.
      - reflexivity.
    Qed.

    Definition app_ext {m : Model}
               (l r : Power (Domain m)) :
      Power (Domain m) :=
      fun e:Domain m => exists le re:Domain m, l le /\ r re /\ (@app_interp m) le re e.

    (* TODO move to examples in a different module *)
    (*
Compute @app_ext {| Domain := Pattern |}
        (Singleton _ (evar "a")) (Singleton _ (evar "b")).
     *)
    (* S . empty = empty *)

    Lemma app_ext_bot_r : forall (m : Model),
        forall S : Power (Domain m),
          app_ext S Empty = Empty.
    Proof.
      intros. unfold app_ext. apply Extensionality_Ensembles.  unfold Same_set. unfold Included. unfold In. split; intros.
      * inversion H. inversion H0. inversion H1. inversion H3. contradiction.
      * contradiction.
    Qed.

    Lemma app_ext_bot_l : forall (m : Model),
        forall S : Power (Domain m),
          app_ext Empty S = Empty.
    Proof.
      intros. unfold app_ext. apply Extensionality_Ensembles. unfold Same_set. unfold Included. unfold In. split; intros.
      * inversion H. inversion H0. inversion H1. contradiction.
      * contradiction.
    Qed.

    Lemma app_ext_monotonic_l : forall (m : Model),
        forall (S1 S2 S : Power (Domain m)),
          Included (Domain m) S1 S2 ->
          Included (Domain m) (app_ext S1 S) (app_ext S2 S).
    Proof.
      intros. unfold app_ext. unfold Included. unfold Included in H.
      intros. unfold In in *. destruct H0 as [le [re [H1 [H2 H3]]]].
      apply H in H1. exists le. exists re. firstorder.
    Qed.

    Lemma app_ext_monotonic_r : forall (m : Model),
        forall (S S1 S2 : Power (Domain m)),
          Included (Domain m) S1 S2 ->
          Included (Domain m) (app_ext S S1) (app_ext S S2).
    Proof.
      intros. unfold app_ext. unfold Included. unfold Included in H.
      intros. unfold In in *. destruct H0 as [le [re [H1 [H2 H3]]]].
      apply H in H2. exists le. exists re. firstorder.
    Qed.

    (* Semantics of AML ref. snapshot: Definition 3 *)



    (*
Definition pattern_lt (p1 p2 : Pattern) :=
  size p1 < size p2.
Lemma pattern_lt_well_founded : well_founded (@pattern_lt).
Proof.
  apply well_founded_lt_compat with size; auto.
Qed.

Instance wf_pattern_lt : WellFounded (@pattern_lt).
apply pattern_lt_well_founded.
Defined.

Equations pattern_interpretation_aux {m : Model}
          (evar_val : evar -> Domain m) (svar_val : svar -> Power (Domain m))
          (p : Pattern) : Power (Domain m)
  by wf (size p) :=
  pattern_interpretation_aux evar_val svar_val (patt_free_evar x) := Singleton _ (evar_val x);
  pattern_interpretation_aux evar_val svar_val (patt_free_svar X) := svar_val X;
  pattern_interpretation_aux evar_val svar_val (patt_bound_evar x) := Empty_set _;
  pattern_interpretation_aux evar_val svar_val (patt_bound_svar x) := Empty_set _;
  pattern_interpretation_aux evar_val svar_val (patt_sym s) := (sym_interp m) s;
  pattern_interpretation_aux evar_val svar_val (patt_app ls rs) :=
    app_ext (pattern_interpretation_aux evar_val svar_val ls)
                  (pattern_interpretation_aux evar_val svar_val rs);
  pattern_interpretation_aux evar_val svar_val patt_bott := Empty_set _;
  pattern_interpretation_aux evar_val svar_val (patt_imp ls rs) :=
    Union _ (Complement _ (pattern_interpretation_aux evar_val svar_val ls))
            (pattern_interpretation_aux evar_val svar_val rs);
  pattern_interpretation_aux evar_val svar_val (patt_exists p') :=
    let x := evar_fresh variables (free_evars p') in
    FA_Union
      (fun e => pattern_interpretation_aux (update_evar_val x e evar_val) svar_val
                                  (evar_open 0 x p'));
  pattern_interpretation_aux evar_val svar_val (patt_mu p') :=
    let X := svar_fresh variables (free_svars p') in
    Ensembles_Ext.mu
      (fun S => pattern_interpretation_aux evar_val (update_svar_val X S svar_val)
                                  (svar_open 0 X p')).
Next Obligation. unfold pattern_lt. simpl. lia. Defined.
Next Obligation. unfold pattern_lt. simpl. lia. Defined.
Next Obligation. unfold pattern_lt. simpl. lia. Defined.
Next Obligation. unfold pattern_lt. simpl. lia. Defined.
Next Obligation. unfold pattern_lt. simpl. rewrite <- evar_open_size. lia. apply signature. Defined.
Next Obligation. unfold pattern_lt. simpl. rewrite <- svar_open_size. lia. apply signature. Defined.
     *)

    Section with_model.
      Context {m : Model}.
      Let OS := EnsembleOrderedSet (@Domain m).
      Let  L := PowersetLattice (@Domain m).

      Program Fixpoint pattern_interpretation
              (evar_val : evar -> Domain m) (svar_val : svar -> Power (Domain m))
              (p : Pattern) {measure (size p)} :=
        match p with
        | patt_free_evar x => Ensembles.Singleton _ (evar_val x)
        | patt_free_svar X => svar_val X
        | patt_bound_evar x => Empty
        | patt_bound_svar X => Empty
        | patt_sym s => (@sym_interp m) s
        | patt_app ls rs => app_ext (pattern_interpretation evar_val svar_val ls)
                                    (pattern_interpretation evar_val svar_val rs)
        | patt_bott => Empty
        | patt_imp ls rs => Ensembles.Union _ (Complement _ (pattern_interpretation evar_val svar_val ls))
                                            (pattern_interpretation evar_val svar_val rs)
        | patt_exists p' =>
          let x := fresh_evar p' in
          FA_Union
            (fun e => pattern_interpretation (update_evar_val x e evar_val)
                                             svar_val
                                             (evar_open 0 x p'))
        | patt_mu p' =>
          let X := fresh_svar p' in
          @LeastFixpointOf (Ensemble (@Domain m)) OS L
                           (fun S => pattern_interpretation evar_val
                                                            (update_svar_val X S svar_val)
                                                            (svar_open 0 X p'))
        end.
      Next Obligation. intros. subst. simpl; lia. Defined.
      Next Obligation. intros. subst. simpl; lia. Defined.
      Next Obligation. intros. subst. simpl; lia. Defined.
      Next Obligation. intros. subst. simpl; lia. Defined.
      Next Obligation. intros. subst. simpl; rewrite <- evar_open_size. lia. Defined.
      Next Obligation. intros. subst. simpl; rewrite <- svar_open_size. lia. Defined.
      Next Obligation. Tactics.program_simpl. Defined.

      (* TODO: Need to be able to simplify Program Fixpoint definitions *)

      Lemma pattern_interpretation_free_evar_simpl
            (evar_val : evar -> Domain m) (svar_val : svar -> Power (Domain m))
            (x : evar) :
        pattern_interpretation evar_val svar_val (patt_free_evar x) = Ensembles.Singleton _ (evar_val x).
      Admitted.

      Lemma pattern_interpretation_free_svar_simpl
            (evar_val : evar -> Domain m) (svar_val : svar -> Power (Domain m))
            (X : svar) :
        pattern_interpretation evar_val svar_val (patt_free_svar X) = svar_val X.
      Admitted.

      Lemma pattern_interpretation_bound_evar_simpl
            (evar_val : evar -> Domain m) (svar_val : svar -> Power (Domain m))
            (x : db_index) :
        pattern_interpretation evar_val svar_val (patt_bound_evar x) = Empty.
      Admitted.

      Lemma pattern_interpretation_bound_svar_simpl
            (evar_val : evar -> Domain m) (svar_val : svar -> Power (Domain m))
            (X : db_index) :
        pattern_interpretation evar_val svar_val (patt_bound_svar X) = Empty.
      Admitted.

      Lemma pattern_interpretation_sym_simpl
            (evar_val : @EVarVal m) (svar_val : @SVarVal m)
            (s : symbols) :
        pattern_interpretation evar_val svar_val (patt_sym s) = @sym_interp m s.
      Proof.

      Admitted.


      Lemma pattern_interpretation_app_simpl
            (evar_val : evar -> Domain m) (svar_val : svar -> Power (Domain m))
            (ls rs : Pattern) :
        pattern_interpretation evar_val svar_val (patt_app ls rs) =
        app_ext (pattern_interpretation evar_val svar_val ls)
                (pattern_interpretation evar_val svar_val rs).
      Admitted.

      Lemma pattern_interpretation_bott_simpl
            (evar_val : evar -> Domain m) (svar_val : svar -> Power (Domain m)) :
        pattern_interpretation evar_val svar_val patt_bott = Empty.
      Admitted.

      Lemma pattern_interpretation_imp_simpl
            (evar_val : evar -> Domain m) (svar_val : svar -> Power (Domain m))
            (ls rs : Pattern) :
        pattern_interpretation evar_val svar_val (patt_imp ls rs) =
        Ensembles.Union _ (Complement _ (pattern_interpretation evar_val svar_val ls))
                        (pattern_interpretation evar_val svar_val rs).
      Admitted.

      Lemma pattern_interpretation_ex_simpl
            (evar_val : evar -> Domain m) (svar_val : svar -> Power (Domain m))
            (p : Pattern) :
        pattern_interpretation evar_val svar_val (patt_exists p) =
        let x := fresh_evar p in
        FA_Union 
          (fun e => pattern_interpretation (update_evar_val x e evar_val)
                                           svar_val
                                           (evar_open 0 x p)).
      Admitted.

      Lemma pattern_interpretation_mu_simpl
            (evar_val : evar -> Domain m) (svar_val : svar -> Power (Domain m))
            (p : Pattern) :
        pattern_interpretation evar_val svar_val (patt_mu p) =
        let X := fresh_svar p in
        @LeastFixpointOf (Ensemble (@Domain m)) OS L
                         (fun S => pattern_interpretation evar_val
                                                          (update_svar_val X S svar_val)
                                                          (svar_open 0 X p)).
      Admitted.

      Lemma pattern_interpretation_not_simpl : forall (evar_val : EVarVal) (svar_val : SVarVal) (phi : Pattern),
          pattern_interpretation evar_val svar_val (patt_not phi) = Complement (Domain m) (pattern_interpretation evar_val svar_val phi).
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
          = Ensembles.Union (Domain m) (pattern_interpretation evar_val svar_val phi1) (pattern_interpretation evar_val svar_val phi2).
      Proof.
        intros. unfold patt_or.
        rewrite -> pattern_interpretation_imp_simpl.
        rewrite -> pattern_interpretation_not_simpl.
        assert (H: Complement (Domain m) (Complement (Domain m) (pattern_interpretation evar_val svar_val phi1)) = pattern_interpretation evar_val svar_val phi1).
        { apply Extensionality_Ensembles. apply Compl_Compl_Ensembles. }
        rewrite -> H. reflexivity.
      Qed.

      Lemma pattern_interpretation_or_comm : forall (evar_val : EVarVal) (svar_val : SVarVal)
                                                    (phi1 phi2 : Pattern),
          pattern_interpretation evar_val svar_val (patt_or phi1 phi2)
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
          = Ensembles.Intersection (Domain m) (pattern_interpretation evar_val svar_val phi1) (pattern_interpretation evar_val svar_val phi2).
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
          pattern_interpretation evar_val svar_val (patt_and phi1 phi2)
          = pattern_interpretation evar_val svar_val (patt_and phi2 phi1).
      Proof.
        intros.
        repeat rewrite -> pattern_interpretation_and_simpl.
        apply Extensionality_Ensembles.
        apply Intersection_Symmetric.
      Qed.

      Lemma pattern_interpretation_top_simpl : forall (evar_val : EVarVal) (svar_val : SVarVal),
          pattern_interpretation evar_val svar_val patt_top = Full.
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
          pattern_interpretation evar_val svar_val (patt_iff phi1 phi2)
          = pattern_interpretation evar_val svar_val (patt_or (patt_and phi1 phi2) (patt_and (patt_not phi1) (patt_not phi2))).
      Proof.

      Abort.

      Lemma pattern_interpretation_iff_comm : forall (evar_val : EVarVal) (svar_val : SVarVal)
                                                     (phi1 phi2 : Pattern),
          pattern_interpretation evar_val svar_val (patt_iff phi1 phi2)
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
        Included (Domain m) (pattern_interpretation evar_val svar_val phi1)
                 (pattern_interpretation evar_val svar_val phi2).
      Proof.
        intros; split; unfold Included; intros.
        * rewrite pattern_interpretation_imp_simpl in H.
          remember (pattern_interpretation evar_val svar_val phi1) as Xphi1.
          remember (pattern_interpretation evar_val svar_val phi2) as Xphi2.
          assert (In (Domain m) (Union (Domain m) (Complement (Domain m) Xphi1) Xphi2) x).
          rewrite H. constructor.
          inversion H1. contradiction. assumption.
        * apply Extensionality_Ensembles.
          rewrite pattern_interpretation_imp_simpl.
          remember (pattern_interpretation evar_val svar_val phi1) as Xphi1.
          remember (pattern_interpretation evar_val svar_val phi2) as Xphi2.
          constructor. constructor.
          assert (Union (Domain m) (Complement (Domain m) Xphi1) Xphi1 = Full_set (Domain m)).
          apply Same_set_to_eq; apply Union_Compl_Fullset. unfold Full. rewrite <- H0; clear H0.
          unfold Included; intros.
          inversion H0.
          left; assumption.
          right; apply H in H1; assumption.
      Qed.
      
      (* pattern_interpretation with free_svar_subst does not change *)
      Lemma update_valuation_free_svar_subst
            (evar_val : evar -> Domain m) (svar_val : svar -> Power (Domain m))
            (phi : Pattern) (psi : Pattern) (X : svar) :
        pattern_interpretation evar_val svar_val phi
        = pattern_interpretation evar_val svar_val (free_svar_subst phi psi X) .
      Proof.
      Abort.
      
      (* TODO prove *)
    (*
Lemma pattern_interpretation_fa_simpl : forall {m : Model} (evar_val : @EVarVal m) (svar_val : @SVarVal m) (phi : Pattern),
    pattern_interpretation evar_val svar_val (patt_forall phi) =
    let x := evar_fresh (free_evars phi) in
    FA_Intersection (fun e : @Domain m => pattern_interpretation (update_evar_val x e evar_val) svar_val (evar_open 0 x phi) ).
Proof.
  intros.
  unfold patt_forall.
  rewrite -> pattern_interpretation_not_simpl.
  rewrite -> pattern_interpretation_ex_simpl.
  simpl.
  apply Extensionality_Ensembles.
  unfold Same_set. unfold Complement. unfold Included. unfold In.
  split; intros.
Admitted.
     *)

      
      Lemma Private_interpretation_fresh_svar sz X ϕ ρₑ ρₛ S:
        size ϕ <= sz ->
        svar_is_fresh_in X ϕ ->
        pattern_interpretation ρₑ (update_svar_val X S ρₛ) ϕ
        = pattern_interpretation ρₑ ρₛ ϕ.
      Proof.
        generalize dependent S.
        generalize dependent X.
        generalize dependent ρₛ.
        generalize dependent ρₑ.
        generalize dependent ϕ.
        induction sz.
        - (* sz = 0 *)
          destruct ϕ; simpl; intros ρₑ ρₛ X S Hsz H; try inversion Hsz.
          + repeat rewrite -> pattern_interpretation_free_evar_simpl.    
          reflexivity.
        + repeat rewrite -> pattern_interpretation_free_svar_simpl.
          rewrite -> update_svar_val_neq.
          * auto.
          * unfold svar_is_fresh_in in H. simpl in H.
            apply not_elem_of_singleton_1 in H. auto.
        + repeat rewrite -> pattern_interpretation_bound_evar_simpl.
          auto.
        + repeat rewrite -> pattern_interpretation_bound_svar_simpl.
          auto.
        + repeat rewrite -> pattern_interpretation_sym_simpl.
          auto.
        + repeat rewrite -> pattern_interpretation_bott_simpl.
          auto.
        - (* sz > 0 *)
          destruct ϕ; simpl; intros ρₑ ρₛ X S Hsz H.
          + (* free_evar *)
            rewrite -> IHsz. auto. simpl. lia. auto.
          + (* free_svar *)
            rewrite -> IHsz. auto. simpl. lia. auto.
          + (* bound_evar *)
            rewrite -> IHsz. auto. simpl. lia. auto.
          + (* bound_svar *)
            rewrite -> IHsz. auto. simpl. lia. auto.
          + (* sym *)
            rewrite -> IHsz. auto. simpl. lia. auto.
          + (* app *)
            repeat rewrite -> pattern_interpretation_app_simpl.
            unfold svar_is_fresh_in in *. simpl in H.
            apply not_elem_of_union in H. destruct H.
            repeat rewrite -> IHsz. auto. lia. auto. lia. auto.
          + (* bot *)
            rewrite -> IHsz. auto. simpl. lia. auto.
          + (* imp *)
            repeat rewrite -> pattern_interpretation_imp_simpl.
            unfold svar_is_fresh_in in *. simpl in H.
            apply not_elem_of_union in H. destruct H.
            repeat rewrite -> IHsz. auto. lia. auto. lia. auto.
         + (* exists *)
           repeat rewrite -> pattern_interpretation_ex_simpl.
           simpl. apply f_equal.
           apply functional_extensionality.
           intros. unfold svar_is_fresh_in in *. simpl in H.
           rewrite -> IHsz. auto. rewrite <- evar_open_size. lia. auto.
           rewrite -> free_svars_evar_open. auto.
         + (* mu *)
           repeat rewrite -> pattern_interpretation_mu_simpl.
           simpl. apply f_equal. apply f_equal. apply functional_extensionality.
           intros S'. unfold svar_is_fresh_in in *. simpl in H.
           destruct (svar_eqdec X (fresh_svar ϕ)).
           * subst. rewrite -> update_svar_val_shadow. auto.
           * rewrite -> update_svar_val_comm. 2: auto.
             rewrite -> IHsz. auto.
             rewrite <- svar_open_size. lia. auto.
             pose proof (Fsso := @free_svars_svar_open _ ϕ (fresh_svar ϕ) 0).
             rewrite -> elem_of_subseteq in Fsso.
             unfold not. intros H'.
             specialize (Fsso X H').
             rewrite -> elem_of_union in Fsso.
             destruct Fsso.
             -- apply elem_of_singleton_1 in H0. contradiction.
             -- contradiction.
      Qed.

      Lemma interpretation_fresh_svar X ϕ ρₑ ρₛ S:
        svar_is_fresh_in X ϕ ->
        pattern_interpretation ρₑ (update_svar_val X S ρₛ) ϕ
        = pattern_interpretation ρₑ ρₛ ϕ.
      Proof.
        apply Private_interpretation_fresh_svar with (sz := size ϕ).
        lia.
      Qed.
      
    (*
Ltac proof_ext_val :=
simpl;intros;
repeat
  (* Normalize *)
   rewrite (Same_set_to_eq (Union_Empty_l _))
|| rewrite (Same_set_to_eq (Compl_Compl_Powers _ _))
|| rewrite
   (Same_set_to_eq (Compl_Union_Compl_Intes_Powers_alt _ _ _))
|| rewrite (Same_set_to_eq (FA_rel _ _ _))
  (* Apply *)
|| (eapply (proj1 Same_set_Compl) ; intros)
|| (eapply FA_Inters_same ; intros)
  (* Final step *)
|| exact Complement_Empty_is_Full
|| exact (Symdiff_val _ _)
|| exact (Same_set_refl _).
     *)

    (**
   Proof of correct semantics for the derived operators
   ref. snapshot: Proposition 4
     *)

    End with_model.

    Definition M_predicate (M : Model) (ϕ : Pattern) : Prop := forall ρₑ ρₛ,
        @pattern_interpretation M ρₑ ρₛ ϕ = Full \/ pattern_interpretation ρₑ ρₛ ϕ = Empty.


    Lemma M_predicate_impl M ϕ₁ ϕ₂ : M_predicate M ϕ₁ -> M_predicate M ϕ₂ -> M_predicate M (patt_imp ϕ₁ ϕ₂).
    Proof.
      unfold M_predicate. intros Hp1 Hp2 ρₑ ρₛ.
      specialize (Hp1 ρₑ ρₛ). specialize (Hp2 ρₑ ρₛ).
      rewrite -> pattern_interpretation_imp_simpl.
      destruct Hp1, Hp2; rewrite -> H; rewrite -> H0.
      + left. apply Extensionality_Ensembles. apply Union_Compl_Fullset.
      + right. apply Extensionality_Ensembles. unfold Full. unfold Empty.
        rewrite -> (Same_set_to_eq (Complement_Full_is_Empty)).
        apply Union_Empty_r.
      + left. apply Extensionality_Ensembles. unfold Full. unfold Empty.
        rewrite -> (Same_set_to_eq (Complement_Empty_is_Full)).
        unfold Same_set. unfold Included. unfold In. split; intros; constructor; constructor.
      + left. apply Extensionality_Ensembles. apply Union_Compl_Fullset.
    Qed.

    Lemma M_predicate_bott M : M_predicate M patt_bott.
    Proof.
      unfold M_predicate. intros. right.
      apply pattern_interpretation_bott_simpl.
    Qed.

    Lemma M_predicate_not M ϕ : M_predicate M ϕ -> M_predicate M (patt_not ϕ).
    Proof.
      intros. unfold patt_not. auto using M_predicate_impl, M_predicate_bott.
    Qed.

    Lemma M_predicate_or M ϕ₁ ϕ₂ : M_predicate M ϕ₁ -> M_predicate M ϕ₂ -> M_predicate M (patt_or ϕ₁ ϕ₂).
    Proof.
      intros. unfold patt_or. auto using M_predicate_not, M_predicate_impl.
    Qed.

    Lemma M_predicate_and M ϕ₁ ϕ₂ : M_predicate M ϕ₁ -> M_predicate M ϕ₂ -> M_predicate M (patt_and ϕ₁ ϕ₂).
    Proof.
      intros. unfold patt_and. auto using M_predicate_or, M_predicate_not.
    Qed.


    Lemma M_predicate_exists M ϕ :
      let x := evar_fresh (elements (free_evars ϕ)) in
      M_predicate M (evar_open 0 x ϕ) -> M_predicate M (patt_exists ϕ).
    Proof.
      simpl. unfold M_predicate. intros.
      rewrite -> pattern_interpretation_ex_simpl.
      simpl.
      pose proof (H' := classic (exists e : Domain M, Same_set (Domain M) (pattern_interpretation (update_evar_val (evar_fresh (elements (free_evars ϕ))) e ρₑ) ρₛ (evar_open 0 (evar_fresh (elements (free_evars ϕ))) ϕ)) Full)).
      destruct H'.
      - (* For some member, the subformula evaluates to full set. *)
        left. apply Extensionality_Ensembles. apply Same_set_symmetric. apply Same_set_Full_set.
        unfold Included. intros. constructor.
        destruct H0. unfold Same_set in H0. destruct H0. clear H0.
        unfold Included in H2. specialize (H2 x H1).
        exists x0. unfold In in H2. apply H2.
      - (* The subformula does not evaluate to full set for any member. *)
        right. apply Extensionality_Ensembles.
        unfold Same_set.
        split.
        + unfold Included. intros.
          unfold In in H1. inversion H1. subst. clear H1. destruct H2.
          specialize (H (update_evar_val (evar_fresh (elements (free_evars ϕ))) x0 ρₑ) ρₛ).
          destruct H.
          * exfalso. apply H0. exists x0. rewrite -> H. apply Same_set_refl.
          * apply eq_to_Same_set in H. unfold Same_set in H. destruct H. clear H2.
            unfold Included in H. specialize (H x).
            auto.
        + unfold Included. intros. inversion H1.
    Qed.

    Lemma M_predicate_top M : M_predicate M patt_top.
    Proof.
      unfold patt_top. apply M_predicate_not. apply M_predicate_bott.
    Qed.

    Lemma M_predicate_iff M ϕ₁ ϕ₂ :
      M_predicate M ϕ₁ ->
      M_predicate M ϕ₂ ->
      M_predicate M (patt_iff ϕ₁ ϕ₂).
    Proof.
      intros H1 H2.
      unfold patt_iff.
      apply M_predicate_and; apply M_predicate_impl; auto.
    Qed.

    (* TODO forall *)

    Lemma predicate_not_empty_iff_full M ϕ ρₑ ρₛ :
      M_predicate M ϕ ->
      @pattern_interpretation M ρₑ ρₛ ϕ <> Empty <->
      @pattern_interpretation M ρₑ ρₛ ϕ = Full.
    Proof.
      intros Hmp.
      split.
      - intros Hne. specialize (Hmp ρₑ ρₛ).
        destruct Hmp.
        + assumption.
        + contradiction.
      - intros Hf.
        apply full_impl_not_empty.
        assumption.
    Qed.

    Lemma predicate_not_full_iff_empty M ϕ ρₑ ρₛ :
      M_predicate M ϕ ->
      @pattern_interpretation M ρₑ ρₛ ϕ <> Full <->
      @pattern_interpretation M ρₑ ρₛ ϕ = Empty.
    Proof.
      intros Hmp.
      split.
      - intros Hne. specialize (Hmp ρₑ ρₛ).
        destruct Hmp.
        + contradiction.
        + assumption.
      - intros Hf.
        apply empty_impl_not_full.
        assumption.
    Qed.


    (* ML's 'set comprehension'/'set building' scheme.
   Pattern `∃ x. x ∧ P(x)` gets interpreted as {m ∈ M | P(m) holds}
     *)
    (* ϕ is expected to have dangling evar indices *)

    Lemma pattern_interpretation_set_builder M ϕ ρₑ ρₛ :
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

    Lemma pattern_interpretation_impl_MP M ϕ₁ ϕ₂ ρₑ ρₛ :
      @pattern_interpretation M ρₑ ρₛ (patt_imp ϕ₁ ϕ₂) = Full ->
      @pattern_interpretation M ρₑ ρₛ ϕ₁ = Full ->
      @pattern_interpretation M ρₑ ρₛ ϕ₂ = Full.
    Proof.
      unfold Full.
      rewrite pattern_interpretation_imp_simpl.
      intros H1 H2.
      rewrite -> H2 in H1.
      rewrite -> Complement_Full_is_Empty_eq in H1.
      rewrite -> Union_Empty_r_eq in H1.
      apply H1.
    Qed.

    Lemma pattern_interpretation_predicate_impl M ϕ₁ ϕ₂ ρₑ ρₛ :
      M_predicate M ϕ₁ ->
      pattern_interpretation ρₑ ρₛ (patt_imp ϕ₁ ϕ₂) = Full
      <-> (pattern_interpretation ρₑ ρₛ ϕ₁ = Full
           -> @pattern_interpretation M ρₑ ρₛ ϕ₂ = Full).
    Proof.
      intros Hpred.
      split.
      - intros H H1.
        apply (pattern_interpretation_impl_MP H H1).
      - intros H.
        rewrite -> pattern_interpretation_imp_simpl.
        destruct (classic (pattern_interpretation ρₑ ρₛ ϕ₁ = Full)).
        + specialize (H H0).
          rewrite -> H. rewrite -> H0.
          unfold Full.
          apply Same_set_to_eq.
          apply Union_Compl_Fullset.
        + apply predicate_not_full_iff_empty in H0. 2: apply Hpred.
          rewrite -> H0.
          unfold Empty.
          rewrite -> Complement_Empty_is_Full_eq.
          rewrite -> Union_Full_l_eq. unfold Full.
          reflexivity.
    Qed.
    
    
    (* ϕ is a well-formed body of ex *)
    Lemma pattern_interpretation_exists_predicate_full M ϕ ρₑ ρₛ :
      let x := fresh_evar ϕ in
      M_predicate M (evar_open 0 x ϕ) ->
      pattern_interpretation ρₑ ρₛ (patt_exists ϕ) = Full <->
      ∃ (m : Domain M), pattern_interpretation (update_evar_val x m ρₑ) ρₛ (evar_open 0 x ϕ) = Full.
    Proof.
      intros x Hpred.
      pose proof (Hpredex := M_predicate_exists Hpred).
      rewrite -[pattern_interpretation _ _ _ = Full]predicate_not_empty_iff_full. 2: auto.
      
      (*
        (* I would like to simplify the RHS, but cannot find a way. *)
        under [fun m => _]functional_extensionality => m.
        (* This fails *)
        Fail rewrite <- predicate_not_empty_iff_full.
        Fail rewrite -[_ = Full]predicate_not_empty_iff_full.
        over.
       *)

      rewrite eq_iff_Same_set.
      rewrite -> Not_Empty_iff_Contains_Elements.
      split.
      - intros [x0 Hx0].
        rewrite -> pattern_interpretation_ex_simpl in Hx0.
        simpl in Hx0. inversion Hx0. subst x1.
        destruct H as [c Hc].
        exists c.
        rewrite -predicate_not_empty_iff_full. 2: assumption.
        rewrite eq_iff_Same_set.
        rewrite Not_Empty_iff_Contains_Elements.
        exists x0. apply Hc.
      - intros [m Hm].
        apply full_impl_not_empty in Hm.
        rewrite -> eq_iff_Same_set in Hm.
        unfold Empty in Hm.
        apply Not_Empty_iff_Contains_Elements in Hm.
        destruct Hm as [x0 Hx0].
        exists x0.
        rewrite pattern_interpretation_ex_simpl. simpl.
        constructor. exists m. assumption.
    Qed.

    Lemma pattern_interpretation_exists_empty M ϕ ρₑ ρₛ :
      let x := fresh_evar ϕ in
      pattern_interpretation ρₑ ρₛ (patt_exists ϕ) = Empty <->
      ∀ (m : Domain M), pattern_interpretation (update_evar_val x m ρₑ) ρₛ (evar_open 0 x ϕ) = Empty.
    Proof.
      intros x.
      rewrite -> pattern_interpretation_ex_simpl. simpl.
      rewrite eq_iff_Same_set.
      split.
      - intros [H1 _]. unfold Included in H1. unfold In in H1 at 1.
        intros m.
        rewrite eq_iff_Same_set. unfold Empty.
        apply Same_set_Empty_set. unfold Included.
        intros x0. unfold In in *.
        intros Contra.
        specialize (H1 x0). unfold Empty in H1. apply H1.
        constructor. exists m. subst x. assumption.
      - intros H.
        apply Same_set_Empty_set. unfold Included.
        intros x0. intros [m [m' Contra]]. unfold Empty in H.
        specialize (H m'). subst x.
        rewrite -> H in Contra. inversion Contra.
    Qed.
    
    Lemma pattern_interpretation_forall_predicate M ϕ ρₑ ρₛ :
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
      autorewrite with ml_db.
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

    Lemma pattern_interpretation_and_full M ρₑ ρₛ ϕ₁ ϕ₂:
      @pattern_interpretation M ρₑ ρₛ (patt_and ϕ₁ ϕ₂) = Full
      <-> (@pattern_interpretation M ρₑ ρₛ ϕ₁ = Full
           /\ @pattern_interpretation M ρₑ ρₛ ϕ₂ = Full).
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
      
    
    (* Theory,axiom ref. snapshot: Definition 5 *)

    Definition satisfies_model (m : Model) (phi : Pattern) : Prop :=
      forall (evar_val : evar -> Domain m) (svar_val : svar -> Power (Domain m)),
        pattern_interpretation (m := m) evar_val svar_val phi = Full.

    Definition satisfies_theory (m : Model) (theory : Theory)
      : Prop := forall axiom : Pattern, Ensembles.In _ theory axiom -> (satisfies_model m axiom).

    (* TODO rename *)
    Definition satisfies (theory : Theory) (p: Pattern)
      : Prop := forall m : Model, (satisfies_theory m theory) -> (satisfies_model m p).

    Definition TheoryIncluded (Γ₁ Γ₂ : Theory) := Ensembles.Included _ Γ₁ Γ₂.

    Lemma satisfies_theory_subseteq M Γ₁ Γ₂:
      TheoryIncluded Γ₁ Γ₂ ->
      satisfies_theory M Γ₂ ->
      satisfies_theory M Γ₁.
    Proof.
      unfold TheoryIncluded.
      unfold Included.
      unfold satisfies_theory.
      auto.
    Qed.

    Record NamedAxioms := { NAName : Type; NAAxiom : NAName -> Pattern }.

    Definition theory_of_NamedAxioms (NAs : NamedAxioms) : Theory :=
      fun p => exists (n : NAName NAs), p = NAAxiom n.

    Lemma satisfies_theory_impl_satisfies_named_axiom NAs M:
      satisfies_theory M (theory_of_NamedAxioms NAs) ->
      forall (n : NAName NAs), satisfies_model M (NAAxiom n).
    Proof.
      intros. unfold satisfies_theory in H.
      specialize (H (NAAxiom n)). apply H.
      unfold In. unfold theory_of_NamedAxioms.
      exists n. auto.
    Qed.
    
    (* TODO do we want to make this a type class? *)
    Record NamedAxiomsIncluded (NA₁ NA₂ : NamedAxioms) :=
      { NAIinj : NAName NA₁ -> NAName NA₂;
        NAIax : forall (n : NAName NA₁), NAAxiom n = NAAxiom (NAIinj n);
      }.

    Lemma NamedAxiomsIncluded_impl_TheoryIncluded NA₁ NA₂:
      NamedAxiomsIncluded NA₁ NA₂ ->
      TheoryIncluded (theory_of_NamedAxioms NA₁) (theory_of_NamedAxioms NA₂).
    Proof.
      intros [inj ax].
      unfold TheoryIncluded.
      unfold Included.
      intros ϕ.
      unfold In.
      unfold theory_of_NamedAxioms.
      intros [n Hn].
      exists (inj n).
      specialize (ax n). subst. auto.
    Qed.

    Program Definition NamedAxiomsIncluded_refl NA : NamedAxiomsIncluded NA NA :=
      {| NAIinj := λ n, n; |}.
    Next Obligation. auto. Qed.
    (* TODO make it a stdpp preorder  *)

    Program Definition NamedAxiomsIncluded_compose NA₁ NA₂ NA₃ :
      NamedAxiomsIncluded NA₁ NA₂ ->
      NamedAxiomsIncluded NA₂ NA₃ ->
      NamedAxiomsIncluded NA₁ NA₃ :=
      λ HI₁ HI₂, {| NAIinj := λ n, NAIinj HI₂ (NAIinj HI₁ n);  |}.
    Next Obligation.
      intros NA₁ NA₂ NA₃ [inj₁ ax₁] [inj₂ ax₂] n.
      simpl.
      rewrite -ax₂.
      rewrite -ax₁.
      auto.
    Qed.
       
    
    Definition T_predicate Γ ϕ := forall M, satisfies_theory M Γ -> M_predicate M ϕ.

    Lemma T_predicate_impl Γ ϕ₁ ϕ₂ : T_predicate Γ ϕ₁ -> T_predicate Γ ϕ₂ -> T_predicate Γ (patt_imp ϕ₁ ϕ₂).
    Proof.
      unfold T_predicate.
      intros.
      auto using M_predicate_impl.
    Qed.

    Lemma T_predicate_bot Γ : T_predicate Γ patt_bott.
    Proof.
      unfold T_predicate.
      intros.
      auto using M_predicate_bott.
    Qed.

    Lemma T_predicate_not Γ ϕ : T_predicate Γ ϕ -> T_predicate Γ (patt_not ϕ).
    Proof.
      unfold T_predicate.
      intros.
      auto using M_predicate_not.
    Qed.

    Lemma T_predicate_or Γ ϕ₁ ϕ₂ : T_predicate Γ ϕ₁ -> T_predicate Γ ϕ₂ -> T_predicate Γ (patt_or ϕ₁ ϕ₂).
    Proof.
      unfold T_predicate.
      intros.
      auto using M_predicate_or.
    Qed.

    Lemma T_predicate_and Γ ϕ₁ ϕ₂ : T_predicate Γ ϕ₁ -> T_predicate Γ ϕ₂ -> T_predicate Γ (patt_and ϕ₁ ϕ₂).
    Proof.
      unfold T_predicate.
      intros.
      auto using M_predicate_and.
    Qed.

    (* TODO: top iff exists forall *)

    Lemma update_valuation_fresh {m : Model}  :
      forall phi,
        well_formed_closed phi ->
        forall v,
          evar_is_fresh_in v phi ->
          forall evar_val svar_val c,
            @pattern_interpretation m (update_evar_val v c evar_val) svar_val phi =
            @pattern_interpretation m evar_val svar_val phi.
    Proof.
      unfold evar_is_fresh_in.
      intros phi Hwfc. apply wfc_wfc_ind in Hwfc.
      induction Hwfc.
      - intros. simpl in H. apply not_elem_of_singleton_1 in H.
        repeat rewrite pattern_interpretation_free_evar_simpl. unfold update_evar_val.
        destruct (evar_eqdec v x) eqn:P.
        + contradiction.
        + auto.
      - auto.
      - auto.
      - intros. repeat rewrite pattern_interpretation_app_simpl. 
        simpl in H. rewrite -> elem_of_union in H. apply not_or_and in H. destruct H.
        rewrite -> IHHwfc1. rewrite -> IHHwfc2. reflexivity. assumption. assumption.
      - intros. repeat rewrite -> pattern_interpretation_bott_simpl. reflexivity.
      - intros. repeat rewrite -> pattern_interpretation_imp_simpl.
        simpl in H. rewrite -> elem_of_union in H. apply not_or_and in H. destruct H.
        rewrite -> IHHwfc1. rewrite -> IHHwfc2. reflexivity. assumption. assumption.
      - intros. repeat rewrite -> pattern_interpretation_ex_simpl. simpl. apply Extensionality_Ensembles.
        apply FA_Union_same. intros.
        unfold Same_set, Included, In. split.
        + intros. remember (fresh_evar phi) as fresh1.
          destruct (evar_eqdec fresh1 v).
          * rewrite <- e in H2. rewrite -> update_evar_val_shadow in H2. assumption.
          * simpl in H1. rewrite -> update_evar_val_comm in H2. rewrite -> H0 in H2.
            -- assumption.
            -- rewrite -> Heqfresh1. apply set_evar_fresh_is_fresh.
            -- apply (@fresh_notin signature (size (evar_open 0 fresh1 phi))).
               ++ rewrite -> (evar_open_size 0 fresh1). lia.
               ++ assumption.
               ++ rewrite -> Heqfresh1. apply set_evar_fresh_is_fresh.
               ++ unfold not. intro. rewrite -> H3 in n. contradiction.
            -- assumption.
        + intros. remember (fresh_evar phi) as fresh1.
          destruct (evar_eqdec fresh1 v).
          * rewrite -> e. rewrite -> update_evar_val_shadow. rewrite -> e in H2. assumption.
          * simpl in H1. rewrite -> update_evar_val_comm. rewrite -> H0.
            -- assumption.
            -- rewrite -> Heqfresh1. apply set_evar_fresh_is_fresh.
            -- apply (@fresh_notin signature (size (evar_open 0 fresh1 phi))).
               ++ rewrite -> (evar_open_size 0 fresh1). lia.
               ++ assumption.
               ++ rewrite -> Heqfresh1. apply set_evar_fresh_is_fresh.
               ++ unfold not. intro. rewrite -> H3 in n. contradiction.
            -- assumption.
      - intros. repeat rewrite -> pattern_interpretation_mu_simpl. simpl.
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
          * rewrite -> Heqfresh1. apply set_svar_fresh_is_fresh.
          * rewrite -> free_evars_svar_open. assumption.
        + rewrite -> H2. reflexivity.
    Qed.

    Lemma interpretation_fresh_evar M phi x y c dbi evar_val svar_val:
      evar_is_fresh_in x phi -> evar_is_fresh_in y phi ->
      @pattern_interpretation M (update_evar_val x c evar_val) svar_val (evar_open dbi x phi)
      = @pattern_interpretation M (update_evar_val y c evar_val) svar_val (evar_open dbi y phi).
    Proof.
    Admitted.
    
    
(* There are two ways how to plug a pattern phi2 into a pattern phi1:
   either substitute it for some variable,
   or evaluate phi2 first and then evaluate phi1 with valuation updated to the result of phi2
 TODO prefix with Private_ and creaate a wrapper.
*)
Lemma plugging_patterns_helper : forall (sz : nat) (dbi : db_index) (M : Model) (phi1 phi2 : Pattern),
    size phi1 <= sz -> forall (evar_val : EVarVal)
                              (svar_val : SVarVal) (X : svar), (* TODO X not free in ?? *)
    well_formed_closed (patt_mu phi1) ->
    well_formed_closed phi2 ->
    ~ elem_of X (free_svars phi1) ->
    @pattern_interpretation M evar_val svar_val (bsvar_subst phi1 phi2 dbi (*0?*)) (*~ open_svar dbi phi2 ph1*)
    = @pattern_interpretation M evar_val
                     (update_svar_val X (@pattern_interpretation M evar_val svar_val phi2) svar_val)
                     (svar_open dbi X phi1).
Proof.
  induction sz; intros dbi M phi1 phi2 Hsz evar_val svar_val X Hwfc1 Hwfc2 H.
  - (* sz == 0 *)
    destruct phi1; simpl in Hsz; simpl.
    + (* free_evar *)
      repeat rewrite -> pattern_interpretation_free_evar_simpl. auto.
      (*apply elem_of_singleton_2. auto.*)
    + (* free_svar *)
      repeat rewrite -> pattern_interpretation_free_svar_simpl.
      unfold update_svar_val. destruct (svar_eqdec X x).
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
        destruct (svar_eqdec X X). auto. contradiction.
      * symmetry in Heq; apply beq_nat_eq in Heq. lia.
      * repeat rewrite -> pattern_interpretation_bound_svar_simpl; auto.
      * apply beq_nat_false in Heq. lia.
      * repeat rewrite -> pattern_interpretation_bound_svar_simpl; auto.
    + (* sym *)
      simpl. repeat rewrite -> pattern_interpretation_sym_simpl; auto.
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
      repeat rewrite pattern_interpretation_free_evar_simpl. auto.
    + (* free_svar *)
      repeat rewrite -> pattern_interpretation_free_svar_simpl.
      unfold update_svar_val. destruct (svar_eqdec X x).
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
        destruct (svar_eqdec X X). simpl. auto. contradiction.
      * symmetry in Heq; apply beq_nat_eq in Heq. lia.
      * repeat rewrite -> pattern_interpretation_bound_svar_simpl; auto.
      * apply beq_nat_false in Heq. lia.
      * repeat rewrite -> pattern_interpretation_bound_svar_simpl; auto.
    + (* sym *)
      simpl. repeat rewrite -> pattern_interpretation_sym_simpl; auto.
      (* HERE the duplication ends *)
    + (* app *)
      simpl.
      simpl in H. apply not_elem_of_union in H. destruct H.
      repeat rewrite -> pattern_interpretation_app_simpl.
      simpl in Hsz.
      repeat rewrite <- IHsz.
       * reflexivity.
       * lia.
       * apply wfc_body_to_wfc_mu. unfold wfc_body_mu. intros.
         apply wfc_aux_body_mu_imp1. unfold well_formed_closed in Hwfc1.
         inversion Hwfc1; auto.
       * assumption.
       * auto.
       * lia.
       * apply wfc_body_to_wfc_mu. unfold wfc_body_mu. intros.
         apply wfc_aux_body_mu_imp1. unfold well_formed_closed in Hwfc1.
         inversion Hwfc1; auto.
       * assumption.
       * auto.
    + (* Bot. Again, a duplication of the sz=0 case *)
      simpl. repeat rewrite pattern_interpretation_bott_simpl; auto.
    + (* imp *)
      simpl in Hsz. simpl in H.
      apply not_elem_of_union in H. destruct H.
      repeat rewrite -> pattern_interpretation_imp_simpl.
      repeat rewrite <- IHsz.
      * reflexivity.
      * lia.
      * apply wfc_body_to_wfc_mu. unfold wfc_body_mu. intros.
        apply wfc_aux_body_mu_imp1. unfold well_formed_closed in Hwfc1.
        inversion Hwfc1; auto.
      * assumption.
      * auto.
      * lia.
      * apply wfc_body_to_wfc_mu. unfold wfc_body_mu. intros.
        apply wfc_aux_body_mu_imp1. unfold well_formed_closed in Hwfc1.
        inversion Hwfc1; auto.
      * assumption.
      * auto.
    (* TODO *)
    + simpl in Hsz. simpl in H.
      repeat rewrite -> pattern_interpretation_ex_simpl. simpl.
      apply Same_set_to_eq. apply FA_Union_same. intros c.

      (* x = fresh_evar phi1' *)
      (* y = evar_fresh (elements (free_evars phi1') U (free_evars phi2)) *)
            
      remember (svar_open dbi X phi1) as phi1'.
      remember (fresh_evar phi1') as Xfr2'.
      remember (evar_fresh (elements (union (free_evars phi1') (free_evars phi2)))) as Xu.
      remember (update_svar_val X (pattern_interpretation evar_val svar_val phi2) svar_val) as svar_val2'.
      pose proof (Hfresh_subst := @interpretation_fresh_evar M phi1' Xfr2' Xu c 0 evar_val svar_val2').
      rewrite -> Hfresh_subst.
      3: { admit. }
      2: { subst phi1' Xfr2'. apply set_evar_fresh_is_fresh. }
      
      remember (update_evar_val (fresh_evar (bsvar_subst phi1 phi2 dbi)) c evar_val) as evar_val1'.
      remember (update_evar_val Xu c evar_val) as evar_val2'.
      rewrite -> evar_open_bsvar_subst. 2: auto.
      remember (fresh_evar (bsvar_subst phi1 phi2 dbi)) as Xfr1.
      
      (* dbi may or may not occur in phi1 *)
      remember (bsvar_occur phi1 dbi) as Hoc.
      move: HeqHoc.
      case: Hoc => HeqHoc.
      -- (* dbi ocurs in phi1 *)
        pose proof (HXfr1Fresh := @set_evar_fresh_is_fresh signature (bsvar_subst phi1 phi2 dbi)).
        rewrite <- HeqXfr1 in HXfr1Fresh.
        symmetry in HeqHoc.
        pose proof (Hsub := @bsvar_subst_contains_subformula signature phi1 phi2 dbi HeqHoc).
        pose proof (HXfr1Fresh2 := evar_fresh_in_subformula Hsub HXfr1Fresh).

        assert (Hinterp:
                  (pattern_interpretation evar_val1' svar_val phi2) =
                  (pattern_interpretation evar_val svar_val phi2)
               ).
        { subst. apply update_valuation_fresh. auto. auto. }
        
        assert (He1e1':
                  (update_svar_val X (pattern_interpretation evar_val1' svar_val phi2) svar_val) =
                  (update_svar_val X (pattern_interpretation evar_val svar_val phi2) svar_val)
               ).
        { congruence. }
        subst svar_val2'.
        rewrite <- He1e1'.
        subst phi1'.
        rewrite -> svar_open_evar_open_comm.

        assert (HXu: (Xfr1 = Xu)).
        { subst Xfr1. subst Xu. unfold fresh_evar.
          rewrite -> free_evars_bsvar_subst_eq.
          rewrite -> free_evars_svar_open. auto. auto.
        }
        rewrite -> HXu in *.
        assert (He1e2 : evar_val1' = evar_val2').
        { subst. auto. }
        rewrite <- He1e2.
        rewrite <- IHsz.
        * apply Same_set_refl.
        * rewrite <- evar_open_size. lia. 
        * apply wfc_body_to_wfc_mu. unfold wfc_body_mu. intros.
          apply wfc_aux_body_mu_imp1. unfold well_formed_closed in Hwfc1.
          simpl in Hwfc1. apply wfc_aux_body_ex_imp1. auto.
        * auto.
        * rewrite -> free_svars_evar_open. auto.
      -- (* dbi does not occur in phi1 *)
        rewrite -> bsvar_subst_not_occur_is_noop.
        (* Now svar_open does nothing to phi1, since it does not contain dbi (see HeqHoc).
           We need a lemma for that. *)
        symmetry in HeqHoc. apply svar_open_not_occur_is_noop with (X0:=X) in HeqHoc.
        (* X is not free in phi1, so the fact that in svar_val2' it is updated to some 
           value is irrelevant. *)
        assert (Hpi: pattern_interpretation evar_val2' svar_val2' (evar_open 0 Xu phi1')
                   = pattern_interpretation evar_val2' svar_val (evar_open 0 Xu phi1')).
        { subst svar_val2'. apply interpretation_fresh_svar. unfold svar_is_fresh_in.
          rewrite -> free_svars_evar_open. subst phi1'. rewrite -> HeqHoc. auto.
        }
        rewrite -> Hpi. subst phi1'. rewrite -> HeqHoc.
        subst evar_val1'. subst evar_val2'.
        rewrite -> interpretation_fresh_evar with (y := Xu).
        apply Same_set_refl.
        admit. admit. admit.

    + (* Mu case *)
      admit.
        

Admitted.

Lemma update_val_fresh12{m : Model}:
  forall sz  phi n,
    le (size phi) sz ->
    forall fresh1 fresh2,
      fresh1 ∉ (free_evars phi) -> fresh2 ∉ (free_evars phi) ->
      well_formed_closed (evar_open n fresh1 phi) -> well_formed_closed (evar_open n fresh2 phi)
      ->
      forall evar_val svar_val c,
        pattern_interpretation (update_evar_val fresh1 c evar_val) svar_val (evar_open n fresh1 phi) =
        @pattern_interpretation m (update_evar_val fresh2 c evar_val) svar_val (evar_open n fresh2 phi).
Proof. 

  (* Induction on size *)
  induction sz; destruct phi; intros n0 Hsz fresh1 fresh2 HLs1 HLs2 Hwfb1 Hwfb2 eval sval c; auto; try inversion Hsz; subst.
  - repeat rewrite -> evar_open_fresh. 
    2, 3: unfold well_formed_closed; simpl; trivial.
    repeat rewrite -> pattern_interpretation_free_evar_simpl.
    unfold update_evar_val.
    destruct (evar_eqdec fresh1 x) eqn:P; destruct (evar_eqdec fresh2 x) eqn:P1.
    + rewrite -> e in HLs1. simpl in HLs1.
      eapply not_elem_of_singleton_1 in HLs1. contradiction.
    + rewrite -> e in HLs1. simpl in HLs1.
      eapply not_elem_of_singleton_1 in HLs1. contradiction.
    + rewrite -> e in HLs2. simpl in HLs2. 
      eapply not_elem_of_singleton_1 in HLs2. contradiction.
    + auto.
  - unfold well_formed_closed in Hwfb1. simpl in Hwfb1.
    assert (n = n0).
    destruct (n =? n0) eqn:P.
    + apply beq_nat_true in P. assumption.
    + inversion Hwfb1.
    + simpl. apply Nat.eqb_eq in H. rewrite H. repeat rewrite pattern_interpretation_free_evar_simpl. unfold update_evar_val.
      destruct (evar_eqdec fresh1 fresh1) eqn:P. destruct (evar_eqdec fresh2 fresh2) eqn:P1.
      auto. contradiction. contradiction.
  - erewrite IHsz. reflexivity. assumption. assumption. assumption. assumption. assumption.
  - erewrite IHsz. reflexivity. assumption. assumption. assumption. assumption. assumption.
  - simpl. simpl in Hsz. repeat rewrite pattern_interpretation_app_simpl.
    simpl in HLs1, HLs2.
    rewrite -> elem_of_union in HLs1, HLs2. apply not_or_and in HLs1. apply not_or_and in HLs2.
    destruct HLs1, HLs2. 
    apply wfc_wfc_ind in Hwfb1. inversion Hwfb1.
    apply wfc_wfc_ind in Hwfb2. inversion Hwfb2.
    erewrite -> IHsz. erewrite (IHsz phi2). reflexivity. lia. assumption. assumption. 
    + apply (wfc_ind_wfc). assumption.
    + apply (wfc_ind_wfc). assumption.
    + lia.
    + assumption.
    + assumption.
    + apply (wfc_ind_wfc). assumption.
    + apply (wfc_ind_wfc). assumption.
  - simpl. simpl in Hsz. repeat rewrite pattern_interpretation_app_simpl.
    simpl in HLs1, HLs2.
    rewrite -> elem_of_union in HLs1, HLs2. apply not_or_and in HLs1. apply not_or_and in HLs2.
    destruct HLs1, HLs2. 
    apply wfc_wfc_ind in Hwfb1. inversion Hwfb1.
    apply wfc_wfc_ind in Hwfb2. inversion Hwfb2.
    erewrite -> IHsz. erewrite (IHsz phi2). reflexivity. lia. assumption. assumption. 
    + apply (wfc_ind_wfc). assumption.
    + apply (wfc_ind_wfc). assumption.
    + lia.
    + assumption.
    + assumption.
    + apply (wfc_ind_wfc). assumption.
    + apply (wfc_ind_wfc). assumption.
  - simpl. simpl in Hsz. repeat rewrite pattern_interpretation_imp_simpl.
    simpl in HLs1, HLs2. rewrite -> elem_of_union in HLs1, HLs2. apply not_or_and in HLs1. apply not_or_and in HLs2.
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
  - simpl. simpl in Hsz. repeat rewrite pattern_interpretation_imp_simpl.
    simpl in HLs1, HLs2. rewrite -> elem_of_union in HLs1, HLs2. apply not_or_and in HLs1. apply not_or_and in HLs2.
    destruct HLs1, HLs2. 
    apply wfc_wfc_ind in Hwfb1. inversion Hwfb1.
    apply wfc_wfc_ind in Hwfb2. inversion Hwfb2.
    erewrite -> IHsz. erewrite -> (IHsz phi2). reflexivity. lia. assumption. assumption. 
    + apply (wfc_ind_wfc). assumption.
    + apply (wfc_ind_wfc). assumption.
    + lia.
    + assumption.
    + assumption.
    + apply (wfc_ind_wfc). assumption.
    + apply (wfc_ind_wfc). assumption.
  - simpl. repeat rewrite -> pattern_interpretation_ex_simpl. simpl.
    remember (fresh_evar (evar_open (n0 + 1) fresh2 phi)) as fresh22.
    remember (fresh_evar (evar_open (n0 + 1) fresh1 phi)) as fresh11.
    apply Extensionality_Ensembles. apply FA_Union_same. intros. unfold Same_set, Included, In. split.
    + intros. destruct (evar_eqdec fresh1 fresh2). 
      * subst. auto.
      * remember ((@singleton evar (@EVarSet signature) _ fresh1) ∪ ((singleton fresh2) ∪ ((singleton fresh11)
                 ∪ ((singleton fresh22)
              ∪ ((free_evars (evar_open (n0+1) fresh1 phi)) ∪ (free_evars (evar_open (n0+1) fresh2 phi)
                ∪ (free_evars phi))))))) as B.
        remember (@evar_fresh (@variables signature) (elements B)) as fresh3.
        assert(fresh3 ∉ B).
        {
          subst. apply set_evar_fresh_is_fresh'.
        }
        assert(fresh3 ≠ fresh1).
        {
          subst B. epose (not_elem_of_union fresh3 {[fresh1]} 
                  ((singleton fresh2) 
                  ∪ ((singleton fresh11)
                  ∪ ((singleton fresh22)
                  ∪ ((free_evars (evar_open (n0+1) fresh1 phi)) 
                  ∪ (free_evars (evar_open (n0+1) fresh2 phi)
                  ∪ (free_evars phi))))))).
                  apply i in H0. destruct H0. apply not_elem_of_singleton_1 in H0. assumption.
        }
        assert(fresh3 ≠ fresh2).
        {
          subst B. epose (not_elem_of_union fresh3 {[fresh1]} 
                  ((singleton fresh2) 
                  ∪ ((singleton fresh11)
                  ∪ ((singleton fresh22)
                  ∪ ((free_evars (evar_open (n0+1) fresh1 phi)) 
                  ∪ (free_evars (evar_open (n0+1) fresh2 phi)
                  ∪ (free_evars phi))))))).
                  apply i in H0. destruct H0.
                  epose (not_elem_of_union fresh3 
                  (singleton fresh2) 
                  ((singleton fresh11)
                  ∪ ((singleton fresh22)
                  ∪ ((free_evars (evar_open (n0+1) fresh1 phi)) 
                  ∪ (free_evars (evar_open (n0+1) fresh2 phi)
                  ∪ (free_evars phi)))))).
                  apply i0 in H2. destruct H2.
                  apply not_elem_of_singleton_1 in H2. assumption. 
        }
        assert(fresh3 ≠ fresh11).
        {
          subst B. epose (not_elem_of_union fresh3 {[fresh1]} 
                  ((singleton fresh2) 
                  ∪ ((singleton fresh11)
                  ∪ ((singleton fresh22)
                  ∪ ((free_evars (evar_open (n0+1) fresh1 phi)) 
                  ∪ (free_evars (evar_open (n0+1) fresh2 phi)
                  ∪ (free_evars phi))))))).
                  apply i in H0. destruct H0.
                  epose (not_elem_of_union fresh3 
                  (singleton fresh2) 
                  ((singleton fresh11)
                  ∪ ((singleton fresh22)
                  ∪ ((free_evars (evar_open (n0+1) fresh1 phi)) 
                  ∪ (free_evars (evar_open (n0+1) fresh2 phi)
                  ∪ (free_evars phi)))))).
                  apply i0 in H3. destruct H3.
                  epose (not_elem_of_union fresh3 
                  (singleton fresh11)
                  ((singleton fresh22)
                  ∪ ((free_evars (evar_open (n0+1) fresh1 phi)) 
                  ∪ (free_evars (evar_open (n0+1) fresh2 phi)
                  ∪ (free_evars phi))))).
                  apply i1 in H4. destruct H4.
                  apply not_elem_of_singleton_1 in H4. assumption.
        }
        assert(fresh3 ≠ fresh22).
        {
          subst B. epose (not_elem_of_union fresh3 {[fresh1]} 
                  ((singleton fresh2) 
                  ∪ ((singleton fresh11)
                  ∪ ((singleton fresh22)
                  ∪ ((free_evars (evar_open (n0+1) fresh1 phi)) 
                  ∪ (free_evars (evar_open (n0+1) fresh2 phi)
                  ∪ (free_evars phi))))))).
                  apply i in H0. destruct H0.
                  epose (not_elem_of_union fresh3 
                  (singleton fresh2) 
                  ((singleton fresh11)
                  ∪ ((singleton fresh22)
                  ∪ ((free_evars (evar_open (n0+1) fresh1 phi)) 
                  ∪ (free_evars (evar_open (n0+1) fresh2 phi)
                  ∪ (free_evars phi)))))).
                  apply i0 in H4. destruct H4.
                  epose (not_elem_of_union fresh3 
                  (singleton fresh11)
                  ((singleton fresh22)
                  ∪ ((free_evars (evar_open (n0+1) fresh1 phi)) 
                  ∪ (free_evars (evar_open (n0+1) fresh2 phi)
                  ∪ (free_evars phi))))).
                  apply i1 in H5. destruct H5.
                  epose (not_elem_of_union fresh3 
                  (singleton fresh22)
                  ((free_evars (evar_open (n0+1) fresh1 phi)) 
                  ∪ (free_evars (evar_open (n0+1) fresh2 phi)
                  ∪ (free_evars phi)))).
                  apply i2 in H6. destruct H6.
                  apply not_elem_of_singleton_1 in H6. assumption.
        }
        assert(fresh3 ∉ (free_evars (evar_open (n0 + 1) fresh1 phi))).
        {
          subst B. epose (not_elem_of_union fresh3 {[fresh1]} 
                  ((singleton fresh2) 
                  ∪ ((singleton fresh11)
                  ∪ ((singleton fresh22)
                  ∪ ((free_evars (evar_open (n0+1) fresh1 phi)) 
                  ∪ (free_evars (evar_open (n0+1) fresh2 phi)
                  ∪ (free_evars phi))))))).
                  apply i in H0. destruct H0.
                  epose (not_elem_of_union fresh3 
                  (singleton fresh2) 
                  ((singleton fresh11)
                  ∪ ((singleton fresh22)
                  ∪ ((free_evars (evar_open (n0+1) fresh1 phi)) 
                  ∪ (free_evars (evar_open (n0+1) fresh2 phi)
                  ∪ (free_evars phi)))))).
                  apply i0 in H5. destruct H5.
                  epose (not_elem_of_union fresh3 
                  (singleton fresh11)
                  ((singleton fresh22)
                  ∪ ((free_evars (evar_open (n0+1) fresh1 phi)) 
                  ∪ (free_evars (evar_open (n0+1) fresh2 phi)
                  ∪ (free_evars phi))))).
                  apply i1 in H6. destruct H6.
                  epose (not_elem_of_union fresh3 
                  (singleton fresh22)
                  ((free_evars (evar_open (n0+1) fresh1 phi)) 
                  ∪ (free_evars (evar_open (n0+1) fresh2 phi)
                  ∪ (free_evars phi)))).
                  apply i2 in H7. destruct H7.
                  epose (not_elem_of_union fresh3 
                  (free_evars (evar_open (n0+1) fresh1 phi)) 
                  (free_evars (evar_open (n0+1) fresh2 phi)
                  ∪ (free_evars phi))).
                  apply i3 in H8. destruct H8. assumption.
        }
        assert(fresh3 ∉ (free_evars (evar_open (n0 + 1) fresh2 phi)) ∧ fresh3 ∉ free_evars phi).
        {
          subst B. epose (not_elem_of_union fresh3 {[fresh1]} 
                  ((singleton fresh2) 
                  ∪ ((singleton fresh11)
                  ∪ ((singleton fresh22)
                  ∪ ((free_evars (evar_open (n0+1) fresh1 phi)) 
                  ∪ (free_evars (evar_open (n0+1) fresh2 phi)
                  ∪ (free_evars phi))))))).
                  apply i in H0. destruct H0.
                  epose (not_elem_of_union fresh3 
                  (singleton fresh2) 
                  ((singleton fresh11)
                  ∪ ((singleton fresh22)
                  ∪ ((free_evars (evar_open (n0+1) fresh1 phi)) 
                  ∪ (free_evars (evar_open (n0+1) fresh2 phi)
                  ∪ (free_evars phi)))))).
                  apply i0 in H6. destruct H6.
                  epose (not_elem_of_union fresh3 
                  (singleton fresh11)
                  ((singleton fresh22)
                  ∪ ((free_evars (evar_open (n0+1) fresh1 phi)) 
                  ∪ (free_evars (evar_open (n0+1) fresh2 phi)
                  ∪ (free_evars phi))))).
                  apply i1 in H7. destruct H7.
                  epose (not_elem_of_union fresh3 
                  (singleton fresh22)
                  ((free_evars (evar_open (n0+1) fresh1 phi)) 
                  ∪ (free_evars (evar_open (n0+1) fresh2 phi)
                  ∪ (free_evars phi)))).
                  apply i2 in H8. destruct H8.
                  epose (not_elem_of_union fresh3 
                  (free_evars (evar_open (n0+1) fresh1 phi)) 
                  (free_evars (evar_open (n0+1) fresh2 phi)
                  ∪ (free_evars phi))).
                  apply i3 in H9. destruct H9. 
                  apply not_elem_of_union in H10. assumption.
        }
        destruct H6.
        erewrite -> (IHsz _ _ _ _ fresh3).
        erewrite -> (IHsz _ _ _ _ fresh3) in H.
        rewrite -> update_evar_val_comm. rewrite -> evar_open_comm.
        rewrite -> update_evar_val_comm in H. rewrite -> evar_open_comm in H.
        erewrite -> (IHsz _ _ _ _ fresh1). assumption.
        apply (@fresh_notin signature (size (evar_open 0 fresh3 phi))).
        erewrite <- (evar_open_size). lia.
        simpl in HLs1, HLs2. assumption.
        assumption.
        apply not_eq_sym. assumption.
        apply (@fresh_notin signature (size (evar_open 0 fresh3 phi))).
        erewrite <- (evar_open_size). lia.
        simpl in HLs1. assumption.
        assumption.
        apply not_eq_sym. assumption.
        {
          rewrite -> evar_open_comm. simpl in Hwfb2. apply wfc_ex_to_wfc_body in Hwfb2.
          unfold wfc_body_ex in Hwfb2. exact (Hwfb2 fresh3 H6). lia.
        }
        {
          rewrite -> evar_open_comm. simpl in Hwfb1. apply wfc_ex_to_wfc_body in Hwfb1.
          unfold wfc_body_ex in Hwfb1. exact (Hwfb1 fresh3 H5). lia.
        }
        lia. assumption. lia. assumption. subst fresh11. apply set_evar_fresh_is_fresh.
        assumption.
        {
          simpl in Hwfb1. apply wfc_ex_to_wfc_body in Hwfb1.
          unfold wfc_body_ex in Hwfb1. eapply (Hwfb1 fresh11).
          rewrite -> Heqfresh11. apply set_evar_fresh_is_fresh.
        }
        {
          simpl in Hwfb1. apply wfc_ex_to_wfc_body in Hwfb1.
          unfold wfc_body_ex in Hwfb1. apply (Hwfb1 fresh3 H5).
        }
        rewrite -> Heqfresh22. apply set_evar_fresh_is_fresh.
        assumption.
        {
          simpl in Hwfb2. apply wfc_ex_to_wfc_body in Hwfb2.
          unfold wfc_body_ex in Hwfb2. eapply (Hwfb2 fresh22).
          rewrite -> Heqfresh22. apply set_evar_fresh_is_fresh.
        }
        {
          simpl in Hwfb2. apply wfc_ex_to_wfc_body in Hwfb2.
          unfold wfc_body_ex in Hwfb2. apply (Hwfb2 fresh3 H6).
        }
(*    We need a fresh3 evar such that fresh3 ≠ fresh1,fresh2,fresh11,fresh22 and 
      fresh3 is fresh in (evar_open (n0 + 1) fresh2 phi) 
      and (evar_open (n0 + 1) fresh1 phi).
      Let fresh3 := fresh_evar ({fresh1} U {fresh2} U {fresh11} U {fresh22}
                                 U free_evars (evar_open (n0 + 1) fresh1 phi)
                                 U free_evars (evar_open (n0 + 1) fresh2 phi)).
      We can now rewrite fresh22 to fresh3 in goal (IHsz)
      rewrite fresh11 to fresh3 in H (IHsz)
      do swaps in H and goal (update_evar_val_comm and evar_open_comm)
      rewrite fresh1 to fresh2 in H (IHsz).
      Goal should be exactly the H. *)

    + intros. destruct (evar_eqdec fresh1 fresh2).
      * subst. auto.
      * remember ((@singleton evar (@EVarSet signature) _ fresh1) ∪ ((singleton fresh2) ∪ ((singleton fresh11)
                 ∪ ((singleton fresh22)
              ∪ ((free_evars (evar_open (n0+1) fresh1 phi)) ∪ (free_evars (evar_open (n0+1) fresh2 phi)
                ∪ (free_evars phi))))))) as B.
        remember (@evar_fresh (@variables signature) (elements B)) as fresh3.
        assert(fresh3 ∉ B).
        {
          subst. apply set_evar_fresh_is_fresh'.
        }
        assert(fresh3 ≠ fresh1).
        {
          subst B. epose (not_elem_of_union fresh3 {[fresh1]} 
                  ((singleton fresh2) 
                  ∪ ((singleton fresh11)
                  ∪ ((singleton fresh22)
                  ∪ ((free_evars (evar_open (n0+1) fresh1 phi)) 
                  ∪ (free_evars (evar_open (n0+1) fresh2 phi)
                  ∪ (free_evars phi))))))).
                  apply i in H0. destruct H0. apply not_elem_of_singleton_1 in H0. assumption.
        }
        assert(fresh3 ≠ fresh2).
        {
          subst B. epose (not_elem_of_union fresh3 {[fresh1]} 
                  ((singleton fresh2) 
                  ∪ ((singleton fresh11)
                  ∪ ((singleton fresh22)
                  ∪ ((free_evars (evar_open (n0+1) fresh1 phi)) 
                  ∪ (free_evars (evar_open (n0+1) fresh2 phi)
                  ∪ (free_evars phi))))))).
                  apply i in H0. destruct H0.
                  epose (not_elem_of_union fresh3 
                  (singleton fresh2) 
                  ((singleton fresh11)
                  ∪ ((singleton fresh22)
                  ∪ ((free_evars (evar_open (n0+1) fresh1 phi)) 
                  ∪ (free_evars (evar_open (n0+1) fresh2 phi)
                  ∪ (free_evars phi)))))).
                  apply i0 in H2. destruct H2.
                  apply not_elem_of_singleton_1 in H2. assumption. 
        }
        assert(fresh3 ≠ fresh11).
        {
          subst B. epose (not_elem_of_union fresh3 {[fresh1]} 
                  ((singleton fresh2) 
                  ∪ ((singleton fresh11)
                  ∪ ((singleton fresh22)
                  ∪ ((free_evars (evar_open (n0+1) fresh1 phi)) 
                  ∪ (free_evars (evar_open (n0+1) fresh2 phi)
                  ∪ (free_evars phi))))))).
                  apply i in H0. destruct H0.
                  epose (not_elem_of_union fresh3 
                  (singleton fresh2) 
                  ((singleton fresh11)
                  ∪ ((singleton fresh22)
                  ∪ ((free_evars (evar_open (n0+1) fresh1 phi)) 
                  ∪ (free_evars (evar_open (n0+1) fresh2 phi)
                  ∪ (free_evars phi)))))).
                  apply i0 in H3. destruct H3.
                  epose (not_elem_of_union fresh3 
                  (singleton fresh11)
                  ((singleton fresh22)
                  ∪ ((free_evars (evar_open (n0+1) fresh1 phi)) 
                  ∪ (free_evars (evar_open (n0+1) fresh2 phi)
                  ∪ (free_evars phi))))).
                  apply i1 in H4. destruct H4.
                  apply not_elem_of_singleton_1 in H4. assumption.
        }
        assert(fresh3 ≠ fresh22).
        {
          subst B. epose (not_elem_of_union fresh3 {[fresh1]} 
                  ((singleton fresh2) 
                  ∪ ((singleton fresh11)
                  ∪ ((singleton fresh22)
                  ∪ ((free_evars (evar_open (n0+1) fresh1 phi)) 
                  ∪ (free_evars (evar_open (n0+1) fresh2 phi)
                  ∪ (free_evars phi))))))).
                  apply i in H0. destruct H0.
                  epose (not_elem_of_union fresh3 
                  (singleton fresh2) 
                  ((singleton fresh11)
                  ∪ ((singleton fresh22)
                  ∪ ((free_evars (evar_open (n0+1) fresh1 phi)) 
                  ∪ (free_evars (evar_open (n0+1) fresh2 phi)
                  ∪ (free_evars phi)))))).
                  apply i0 in H4. destruct H4.
                  epose (not_elem_of_union fresh3 
                  (singleton fresh11)
                  ((singleton fresh22)
                  ∪ ((free_evars (evar_open (n0+1) fresh1 phi)) 
                  ∪ (free_evars (evar_open (n0+1) fresh2 phi)
                  ∪ (free_evars phi))))).
                  apply i1 in H5. destruct H5.
                  epose (not_elem_of_union fresh3 
                  (singleton fresh22)
                  ((free_evars (evar_open (n0+1) fresh1 phi)) 
                  ∪ (free_evars (evar_open (n0+1) fresh2 phi)
                  ∪ (free_evars phi)))).
                  apply i2 in H6. destruct H6.
                  apply not_elem_of_singleton_1 in H6. assumption.
        }
        assert(fresh3 ∉ (free_evars (evar_open (n0 + 1) fresh1 phi))).
        {
          subst B. epose (not_elem_of_union fresh3 {[fresh1]} 
                  ((singleton fresh2) 
                  ∪ ((singleton fresh11)
                  ∪ ((singleton fresh22)
                  ∪ ((free_evars (evar_open (n0+1) fresh1 phi)) 
                  ∪ (free_evars (evar_open (n0+1) fresh2 phi)
                  ∪ (free_evars phi))))))).
                  apply i in H0. destruct H0.
                  epose (not_elem_of_union fresh3 
                  (singleton fresh2) 
                  ((singleton fresh11)
                  ∪ ((singleton fresh22)
                  ∪ ((free_evars (evar_open (n0+1) fresh1 phi)) 
                  ∪ (free_evars (evar_open (n0+1) fresh2 phi)
                  ∪ (free_evars phi)))))).
                  apply i0 in H5. destruct H5.
                  epose (not_elem_of_union fresh3 
                  (singleton fresh11)
                  ((singleton fresh22)
                  ∪ ((free_evars (evar_open (n0+1) fresh1 phi)) 
                  ∪ (free_evars (evar_open (n0+1) fresh2 phi)
                  ∪ (free_evars phi))))).
                  apply i1 in H6. destruct H6.
                  epose (not_elem_of_union fresh3 
                  (singleton fresh22)
                  ((free_evars (evar_open (n0+1) fresh1 phi)) 
                  ∪ (free_evars (evar_open (n0+1) fresh2 phi)
                  ∪ (free_evars phi)))).
                  apply i2 in H7. destruct H7.
                  epose (not_elem_of_union fresh3 
                  (free_evars (evar_open (n0+1) fresh1 phi)) 
                  (free_evars (evar_open (n0+1) fresh2 phi)
                  ∪ (free_evars phi))).
                  apply i3 in H8. destruct H8. assumption.
        }
        assert(fresh3 ∉ (free_evars (evar_open (n0 + 1) fresh2 phi)) ∧ fresh3 ∉ free_evars phi).
        {
          subst B. epose (not_elem_of_union fresh3 {[fresh1]} 
                  ((singleton fresh2) 
                  ∪ ((singleton fresh11)
                  ∪ ((singleton fresh22)
                  ∪ ((free_evars (evar_open (n0+1) fresh1 phi)) 
                  ∪ (free_evars (evar_open (n0+1) fresh2 phi)
                  ∪ (free_evars phi))))))).
                  apply i in H0. destruct H0.
                  epose (not_elem_of_union fresh3 
                  (singleton fresh2) 
                  ((singleton fresh11)
                  ∪ ((singleton fresh22)
                  ∪ ((free_evars (evar_open (n0+1) fresh1 phi)) 
                  ∪ (free_evars (evar_open (n0+1) fresh2 phi)
                  ∪ (free_evars phi)))))).
                  apply i0 in H6. destruct H6.
                  epose (not_elem_of_union fresh3 
                  (singleton fresh11)
                  ((singleton fresh22)
                  ∪ ((free_evars (evar_open (n0+1) fresh1 phi)) 
                  ∪ (free_evars (evar_open (n0+1) fresh2 phi)
                  ∪ (free_evars phi))))).
                  apply i1 in H7. destruct H7.
                  epose (not_elem_of_union fresh3 
                  (singleton fresh22)
                  ((free_evars (evar_open (n0+1) fresh1 phi)) 
                  ∪ (free_evars (evar_open (n0+1) fresh2 phi)
                  ∪ (free_evars phi)))).
                  apply i2 in H8. destruct H8.
                  epose (not_elem_of_union fresh3 
                  (free_evars (evar_open (n0+1) fresh1 phi)) 
                  (free_evars (evar_open (n0+1) fresh2 phi)
                  ∪ (free_evars phi))).
                  apply i3 in H9. destruct H9. 
                  apply not_elem_of_union in H10. assumption.
        }
        destruct H6.
        erewrite -> (IHsz _ _ _ _ fresh3) in H.
        erewrite -> (IHsz _ _ _ _ fresh3).
        rewrite -> update_evar_val_comm in H. rewrite -> evar_open_comm in H.
        rewrite -> update_evar_val_comm. rewrite -> evar_open_comm.
        erewrite -> (IHsz _ _ _ _ fresh1) in H. assumption.
        apply (@fresh_notin signature (size (evar_open 0 fresh3 phi))).
        erewrite <- (evar_open_size). lia.
        simpl in HLs1, HLs2. assumption.
        assumption.
        apply not_eq_sym. assumption.
        apply (@fresh_notin signature (size (evar_open 0 fresh3 phi))).
        erewrite <- (evar_open_size). lia.
        simpl in HLs1. assumption.
        assumption.
        apply not_eq_sym. assumption.
        {
          rewrite -> evar_open_comm. simpl in Hwfb2. apply wfc_ex_to_wfc_body in Hwfb2.
          unfold wfc_body_ex in Hwfb2. exact (Hwfb2 fresh3 H6). lia.
        }
        {
          rewrite -> evar_open_comm. simpl in Hwfb1. apply wfc_ex_to_wfc_body in Hwfb1.
          unfold wfc_body_ex in Hwfb1. exact (Hwfb1 fresh3 H5). lia.
        }
        lia. assumption. lia. assumption. subst fresh11. apply set_evar_fresh_is_fresh.
        assumption.
        {
          simpl in Hwfb1. apply wfc_ex_to_wfc_body in Hwfb1.
          unfold wfc_body_ex in Hwfb1. eapply (Hwfb1 fresh11).
          rewrite -> Heqfresh11. apply set_evar_fresh_is_fresh.
        }
        {
          simpl in Hwfb1. apply wfc_ex_to_wfc_body in Hwfb1.
          unfold wfc_body_ex in Hwfb1. apply (Hwfb1 fresh3 H5).
        }
        rewrite -> Heqfresh22. apply set_evar_fresh_is_fresh.
        assumption.
        {
          simpl in Hwfb2. apply wfc_ex_to_wfc_body in Hwfb2.
          unfold wfc_body_ex in Hwfb2. eapply (Hwfb2 fresh22).
          rewrite -> Heqfresh22. apply set_evar_fresh_is_fresh.
        }
        {
          simpl in Hwfb2. apply wfc_ex_to_wfc_body in Hwfb2.
          unfold wfc_body_ex in Hwfb2. apply (Hwfb2 fresh3 H6).
        }
  - erewrite -> IHsz. reflexivity. lia. assumption. assumption. assumption. assumption.
  - simpl. repeat rewrite -> pattern_interpretation_mu_simpl. simpl.
    assert ((λ S : Ensemble (Domain m),
        pattern_interpretation (update_evar_val fresh1 c eval)
          (update_svar_val (fresh_svar (evar_open n0 fresh1 phi)) S sval)
          (svar_open 0 (fresh_svar (evar_open n0 fresh1 phi)) (evar_open n0 fresh1 phi))) = (λ S : Ensemble (Domain m),
        pattern_interpretation (update_evar_val fresh2 c eval)
          (update_svar_val (fresh_svar (evar_open n0 fresh2 phi)) S sval)
          (svar_open 0 (fresh_svar (evar_open n0 fresh2 phi)) (evar_open n0 fresh2 phi)))).
    + apply functional_extensionality. intros. repeat rewrite <- svar_open_evar_open_comm.
      unfold fresh_svar.
      erewrite -> (free_svars_evar_open phi n0 fresh1).
      erewrite -> (free_svars_evar_open phi n0 fresh2).
      erewrite -> IHsz. reflexivity.
      rewrite <- svar_open_size. lia.
      rewrite -> free_evars_svar_open. simpl in HLs1. assumption.
      rewrite -> free_evars_svar_open. simpl in HLs2. assumption.
      {
        simpl in Hwfb1. apply wfc_mu_to_wfc_body in Hwfb1. unfold wfc_body_mu in Hwfb1.
        erewrite -> (svar_open_evar_open_comm). eapply (Hwfb1 (svar_fresh (elements (free_svars phi)))).
        rewrite free_svars_evar_open. apply set_svar_fresh_is_fresh'.
      }
      {
        simpl in Hwfb2. apply wfc_mu_to_wfc_body in Hwfb2. unfold wfc_body_mu in Hwfb2.
        erewrite -> (svar_open_evar_open_comm). eapply (Hwfb2 (svar_fresh (elements (free_svars phi)))).
        rewrite free_svars_evar_open. apply set_svar_fresh_is_fresh'.
      }
    + rewrite -> H. reflexivity.
  - erewrite -> IHsz. reflexivity. lia. assumption. assumption. assumption. assumption.
  Unshelve.
  rewrite <- evar_open_size. lia.
  rewrite <- evar_open_size. lia.
  rewrite <- evar_open_size. lia.
  rewrite <- evar_open_size. lia.
  rewrite <- evar_open_size. lia.
  rewrite <- evar_open_size. lia.
Qed. (* update_val_fresh_12 *)

Lemma Private_pattern_interpretation_free_evar_independent M ρₑ ρₛ x v sz ϕ:
  size ϕ <= sz ->
  well_formed_closed ϕ ->
  x ∉ free_evars ϕ ->
  @pattern_interpretation M (update_evar_val x v ρₑ) ρₛ ϕ
  = @pattern_interpretation M ρₑ ρₛ ϕ.
Proof.
  generalize dependent v. generalize dependent x.
  generalize dependent ρₛ. generalize dependent ρₑ. generalize dependent ϕ.
  induction sz; intros ϕ ρₑ ρₛ x v; destruct ϕ; simpl; intros Hsz Hwfc Hnotin.
  - repeat rewrite -> pattern_interpretation_free_evar_simpl.
    apply f_equal. unfold update_evar_val.
    destruct (evar_eqdec x x0); simpl.
    + subst.
      apply not_elem_of_singleton_1 in Hnotin.
      contradiction.
    + reflexivity.
  - repeat rewrite -> pattern_interpretation_free_svar_simpl.
    reflexivity.
  - repeat rewrite -> pattern_interpretation_bound_evar_simpl.
    reflexivity.
  - repeat rewrite -> pattern_interpretation_bound_svar_simpl.
    reflexivity.
  - repeat rewrite -> pattern_interpretation_sym_simpl.
    reflexivity.
  - lia.
  - repeat rewrite -> pattern_interpretation_bott_simpl.
    reflexivity.
  - lia.
  - lia.
  - lia.
  - apply IHsz. 3: { simpl. apply Hnotin. } 2: apply Hwfc. simpl. lia.
  - apply IHsz. 3: { simpl. apply Hnotin. } 2: apply Hwfc. simpl. lia.
  - apply IHsz. 3: { simpl. apply Hnotin. } 2: apply Hwfc. simpl. lia.
  - apply IHsz. 3: { simpl. apply Hnotin. } 2: apply Hwfc. simpl. lia.
  - apply IHsz. 3: { simpl. apply Hnotin. } 2: apply Hwfc. simpl. lia.
  - repeat rewrite -> pattern_interpretation_app_simpl.
    apply wfc_wfc_ind in Hwfc.
    inversion Hwfc. subst.
    apply wfc_ind_wfc in H1.
    apply wfc_ind_wfc in H2.
    simpl in Hnotin.
    apply not_elem_of_union in Hnotin. destruct Hnotin as [Hnotin1 Hnotin2].
    rewrite -> IHsz. 4: apply Hnotin1. 3: apply H1. 2: lia.
    rewrite -> IHsz. 4: apply Hnotin2. 3: apply H2. 2: lia.
    reflexivity.
  - apply IHsz. 3: { simpl. apply Hnotin. } 2: apply Hwfc. simpl. lia.
  - repeat rewrite -> pattern_interpretation_imp_simpl.
    apply wfc_wfc_ind in Hwfc.
    inversion Hwfc. subst.
    apply wfc_ind_wfc in H1.
    apply wfc_ind_wfc in H2.
    simpl in Hnotin.
    apply not_elem_of_union in Hnotin. destruct Hnotin as [Hnotin1 Hnotin2].
    rewrite -> IHsz. 4: apply Hnotin1. 3: apply H1. 2: lia.
    rewrite -> IHsz. 4: apply Hnotin2. 3: apply H2. 2: lia.
    reflexivity.
  - repeat rewrite -> pattern_interpretation_ex_simpl.
    simpl.
    apply wfc_wfc_ind in Hwfc. inversion Hwfc. subst.
    epose proof (Hϕ := H0 (fresh_evar ϕ) _).
    Unshelve. 2: { fold (evar_is_fresh_in (fresh_evar ϕ) ϕ). apply set_evar_fresh_is_fresh. }
    apply wfc_ind_wfc in Hϕ.
   
    apply f_equal. apply functional_extensionality. intros e.
    destruct (evar_eqdec (fresh_evar ϕ) x).
    + rewrite -> e0. rewrite -> update_evar_val_shadow. reflexivity.
    + rewrite -> update_evar_val_comm. 2: apply n.
      rewrite -> IHsz.
      4: { intros Contra.
           pose proof (Hfeeo := @free_evars_evar_open signature ϕ (fresh_evar ϕ) 0).
           rewrite -> elem_of_subseteq in Hfeeo.
           specialize (Hfeeo x Contra).
           apply elem_of_union in Hfeeo.
           destruct Hfeeo as [H|H].
           * apply elem_of_singleton_1 in H. symmetry in H. contradiction.
           * contradiction.
      }
      3: { apply Hϕ. }
      2: { rewrite <- evar_open_size. lia. }
      reflexivity.
  - repeat rewrite -> pattern_interpretation_mu_simpl. simpl.
    apply wfc_wfc_ind in Hwfc. inversion Hwfc. subst.
    
    apply f_equal. apply f_equal. apply functional_extensionality.
    intros e.
    rewrite -> IHsz.
    4: { intros Contra.
         rewrite -> free_evars_svar_open in Contra.
         contradiction.
    }
    3: {
      apply wfc_ind_wfc.
      apply H0.
      fold (svar_is_fresh_in (fresh_svar ϕ) ϕ).
      apply set_svar_fresh_is_fresh.
    }
    2: {
      rewrite <- svar_open_size. lia.
    }
    reflexivity.
Qed.

Lemma pattern_interpretation_free_evar_independent M ρₑ ρₛ x v ϕ:
  well_formed_closed ϕ ->
  x ∉ free_evars ϕ ->
  @pattern_interpretation M (update_evar_val x v ρₑ) ρₛ ϕ
  = @pattern_interpretation M ρₑ ρₛ ϕ.
Proof.
  intros.
  apply Private_pattern_interpretation_free_evar_independent with (sz := size ϕ).
  * lia.
  * assumption.
  * assumption.
Qed.

End semantics.


Module Notations.
  Declare Scope ml_scope.
  Delimit Scope ml_scope with ml.
  
  Notation "M ⊨ᴹ phi" := (satisfies_model M phi) (left associativity, at level 50) : ml_scope.
  (* FIXME this should not be called `satisfies` *)
Notation "G ⊨ phi" := (satisfies G phi) (left associativity, at level 50) : ml_scope.
Notation "M ⊨ᵀ Gamma" := (satisfies_theory M Gamma)
    (left associativity, at level 50) : ml_scope.
End Notations.
