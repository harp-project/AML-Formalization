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


    Lemma update_svar_val_same M x m ρₑ : @update_svar_val M x m ρₑ x = m.
    Proof.
      unfold update_svar_val. destruct (svar_eqdec x x); simpl.
      + reflexivity.
      + contradiction.
    Qed.

    Lemma update_svar_val_same_2 M x ρₑ : @update_svar_val M x (ρₑ x) ρₑ = ρₑ.
    Proof.
      apply functional_extensionality. intros x0.
      unfold update_svar_val. destruct (svar_eqdec x x0); simpl.
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


      Definition Fassoc ρₑ ρₛ ϕ X :=
        λ S, pattern_interpretation ρₑ (update_svar_val X S ρₛ) ϕ.
      
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

      (* TODO extend with derived constructs using typeclasses *)
      Definition pattern_interpretation_simpl :=
        ( pattern_interpretation_free_evar_simpl,
          pattern_interpretation_free_svar_simpl,
          pattern_interpretation_bound_evar_simpl,
          pattern_interpretation_bound_svar_simpl,
          pattern_interpretation_sym_simpl,  
          pattern_interpretation_app_simpl,
          pattern_interpretation_bott_simpl,
          pattern_interpretation_imp_simpl,
          pattern_interpretation_ex_simpl,
          pattern_interpretation_mu_simpl
        ).
      
      
      
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

      (* TODO for evar *)
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
           simpl. apply f_equal. apply functional_extensionality.
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

    Hint Resolve M_predicate_impl : core.

    Lemma M_predicate_bott M : M_predicate M patt_bott.
    Proof.
      unfold M_predicate. intros. right.
      apply pattern_interpretation_bott_simpl.
    Qed.

    Hint Resolve M_predicate_bott : core.

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

    Hint Resolve M_predicate_exists : core.

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

         Hint Extern 4 (M_predicate _ (evar_open _ _ _)) => rewrite !simpl_evar_open : core.
         Hint Extern 4 (T_predicate _ (evar_open _ _ _)) => rewrite !simpl_evar_open : core.
         Hint Extern 4 (M_predicate _ (svar_open _ _ _)) => rewrite !simpl_svar_open : core.
        Hint Extern 4 (T_predicate _ (svar_open _ _ _)) => rewrite !simpl_svar_open : core.
    
    Lemma T_predicate_impl_M_predicate M Γ ϕ:
      satisfies_theory M Γ -> T_predicate Γ ϕ -> M_predicate M ϕ.
    Proof.
      unfold T_predicate. auto.
    Qed.

        Hint Resolve T_predicate_impl_M_predicate : core.

    Lemma T_predicate_impl Γ ϕ₁ ϕ₂ : T_predicate Γ ϕ₁ -> T_predicate Γ ϕ₂ -> T_predicate Γ (patt_imp ϕ₁ ϕ₂).
    Proof.
      unfold T_predicate.
      intros.
      auto using M_predicate_impl.
    Qed.

        Hint Resolve T_predicate_impl : core.

    Lemma T_predicate_bot Γ : T_predicate Γ patt_bott.
    Proof.
      unfold T_predicate.
      intros.
      auto using M_predicate_bott.
    Qed.

        Hint Resolve T_predicate_bot : core.

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

Lemma Private_interpretation_fresh_var_open M sz ϕ dbi ρₑ ρₛ:
  size ϕ <= sz ->
  (
    forall X Y S,
      svar_is_fresh_in X ϕ ->
      svar_is_fresh_in Y ϕ ->
      @pattern_interpretation M ρₑ (update_svar_val X S ρₛ) (svar_open dbi X ϕ)
      = @pattern_interpretation M ρₑ (update_svar_val Y S ρₛ) (svar_open dbi Y ϕ)
  ) /\
  (
    forall x y c,
      evar_is_fresh_in x ϕ ->
      evar_is_fresh_in y ϕ ->
      @pattern_interpretation M (update_evar_val x c ρₑ) ρₛ (evar_open dbi x ϕ)
      = @pattern_interpretation M (update_evar_val y c ρₑ) ρₛ (evar_open dbi y ϕ)
  )
.
Proof.
  move: ϕ dbi ρₑ ρₛ.
  induction sz.
  - move=> ϕ dbi ρₑ ρₛ Hsz.
    split.
    {
      (* base case - svar *)
      move=> X Y S HfrX HfrY.
      destruct ϕ; simpl in Hsz; try lia.
      + rewrite 2!pattern_interpretation_free_evar_simpl. reflexivity.
      + rewrite 2!pattern_interpretation_free_svar_simpl.
        unfold svar_is_fresh_in in HfrX, HfrY. simpl in HfrX, HfrY.
        apply not_elem_of_singleton_1 in HfrX.
        apply not_elem_of_singleton_1 in HfrY.
        unfold update_svar_val.
        destruct (svar_eqdec X x),(svar_eqdec Y x); simpl; try contradiction.
        reflexivity.
      + rewrite 2!pattern_interpretation_bound_evar_simpl. reflexivity.
      + simpl. case (n =? dbi).
        * rewrite 2!pattern_interpretation_free_svar_simpl.
          rewrite 2!update_svar_val_same. reflexivity.
        * rewrite 2!pattern_interpretation_bound_svar_simpl.
          reflexivity.
      + rewrite 2!pattern_interpretation_sym_simpl.
        reflexivity.
      + rewrite 2!pattern_interpretation_bott_simpl.
        reflexivity.
    }
    {
      (* base case - evar *)
      move=> x y c Hfrx Hfry.
      destruct ϕ; simpl in Hsz; try lia.
      + rewrite 2!pattern_interpretation_free_evar_simpl.
        unfold evar_is_fresh_in in Hfrx, Hfry. simpl in Hfrx, Hfry.
        apply not_elem_of_singleton_1 in Hfrx.
        apply not_elem_of_singleton_1 in Hfry.
        apply f_equal. unfold update_evar_val.
        destruct (evar_eqdec x x0),(evar_eqdec y x0); simpl; try contradiction.
        reflexivity.
      + rewrite 2!pattern_interpretation_free_svar_simpl.
        reflexivity.
      + simpl. case (n =? dbi).
        * rewrite 2!pattern_interpretation_free_evar_simpl.
          rewrite 2!update_evar_val_same. reflexivity.
        * rewrite 2!pattern_interpretation_bound_evar_simpl.
          reflexivity.
      + rewrite 2!pattern_interpretation_bound_svar_simpl. reflexivity.
      + rewrite 2!pattern_interpretation_sym_simpl.
        reflexivity.
      + rewrite 2!pattern_interpretation_bott_simpl.
        reflexivity.
    }
  - move=> ϕ dbi ρₑ ρₛ Hsz.
    split.
    {
      (* inductive case - svar *)
      move=> X Y S HfrX HfrY.
      destruct ϕ; simpl in Hsz.
      + rewrite (proj1 (IHsz _ _ _ _ _) X Y). 4: reflexivity. 3,2: auto. simpl. lia.
      + rewrite (proj1 (IHsz _ _ _ _ _) X Y). 4: reflexivity. 3,2: auto. simpl. lia.
      + rewrite (proj1 (IHsz _ _ _ _ _) X Y). 4: reflexivity. 3,2: auto. simpl. lia.
      + rewrite (proj1 (IHsz _ _ _ _ _) X Y). 4: reflexivity. 3,2: auto. simpl. lia.
      + rewrite (proj1 (IHsz _ _ _ _ _) X Y). 4: reflexivity. 3,2: auto. simpl. lia.
      + rewrite 2!pattern_interpretation_app_simpl. fold svar_open.
        rewrite (proj1 (IHsz _ _ _ _ _) X Y). 4: rewrite (proj1 (IHsz _ _ _ _ _) X Y). lia.
        eapply svar_is_fresh_in_app_l. apply HfrX.
        eapply svar_is_fresh_in_app_l. apply HfrY.
        lia.
        eapply svar_is_fresh_in_app_r. apply HfrX.
        eapply svar_is_fresh_in_app_r. apply HfrY.
        reflexivity.
      + rewrite (proj1 (IHsz _ _ _ _ _) X Y). 4: reflexivity. 3,2: auto. simpl. lia.
      + rewrite 2!pattern_interpretation_imp_simpl. fold svar_open.
        rewrite (proj1 (IHsz _ _ _ _ _) X Y). 4: rewrite (proj1 (IHsz _ _ _ _ _) X Y). lia.
        eapply svar_is_fresh_in_app_l. apply HfrX.
        eapply svar_is_fresh_in_app_l. apply HfrY.
        lia.
        eapply svar_is_fresh_in_app_r. apply HfrX.
        eapply svar_is_fresh_in_app_r. apply HfrY.
        reflexivity.
      + rewrite 2!pattern_interpretation_ex_simpl. fold svar_open. simpl.
        apply f_equal. apply functional_extensionality. intros e.
        rewrite 2!svar_open_evar_open_comm.
        rewrite (proj1 (IHsz _ _ _ _ _) X Y). rewrite -evar_open_size. lia.
        apply svar_is_fresh_in_exists in HfrX.
        apply svar_is_fresh_in_exists in HfrY.
        apply svar_fresh_evar_open. apply HfrX.
        apply svar_fresh_evar_open. apply HfrY.
        rewrite -2!svar_open_evar_open_comm.
        rewrite (proj2 (IHsz _ _ _ _ _) _ (fresh_evar (svar_open dbi Y ϕ))). rewrite -svar_open_size. lia.
        rewrite fresh_evar_svar_open.
        apply evar_fresh_svar_open. apply set_evar_fresh_is_fresh.
        apply set_evar_fresh_is_fresh.
        reflexivity.
      + rewrite 2!pattern_interpretation_mu_simpl. fold svar_open. simpl.
        apply f_equal. apply functional_extensionality.
        intros S'.

        remember (fresh_svar (svar_open (dbi + 1) X ϕ)) as X'.
        remember (fresh_svar (svar_open (dbi + 1) Y ϕ)) as Y'.
        remember ((@singleton svar (@SVarSet signature) _ X) ∪ ((singleton Y) ∪ ((singleton X')
                 ∪ ((singleton Y')
              ∪ ((free_svars (svar_open (dbi+1) X ϕ)) ∪ (free_svars (svar_open (dbi+1) Y ϕ)
                ∪ (free_svars ϕ))))))) as B.
        remember (@svar_fresh (@variables signature) (elements B)) as fresh3.
        assert(HB: fresh3 ∉ B).
        {
          subst. apply set_svar_fresh_is_fresh'.
        }

        remember (free_svars (svar_open (dbi+1) Y ϕ) ∪ (free_svars ϕ)) as B0.
        remember ((free_svars (svar_open (dbi+1) X ϕ)) ∪ B0) as B1.
        remember ({[Y']} ∪ B1) as B2.
        remember ({[X']} ∪ B2) as B3.
        remember ({[Y]} ∪ B3) as B4.
        pose proof (i := not_elem_of_union fresh3 {[X]} B4).
        pose proof (i0 := not_elem_of_union fresh3 {[Y]} B3).
        pose proof (i1 := not_elem_of_union fresh3 {[X']} B2).
        pose proof (i2 := not_elem_of_union fresh3 {[Y']} B1).
        pose proof (i3 := not_elem_of_union fresh3 
                                            (free_svars (svar_open (dbi+1) X ϕ)) 
                                            B0).
        subst B0. subst B1. subst B2. subst B3. subst B4. subst B.
        
        apply i in HB. clear i. destruct HB as [Hneqfr1 HB].        
        apply not_elem_of_singleton_1 in Hneqfr1.

        apply i0 in HB. clear i0. destruct HB as [Hneqfr2 HB].
        apply not_elem_of_singleton_1 in Hneqfr2.

        apply i1 in HB. clear i1. destruct HB as [Hneqfr11 HB].
        apply not_elem_of_singleton_1 in Hneqfr11.

        apply i2 in HB. clear i2. destruct HB as [Hneqfr22 HB].
        apply not_elem_of_singleton_1 in Hneqfr22.

        apply i3 in HB. clear i3. destruct HB as [HnotinFree1 HB].
        apply not_elem_of_union in HB.
        destruct HB as [HnotinFree2 HnotinFree].
        
        rewrite (proj1 (IHsz _ _ _ _ _) X' fresh3). rewrite -svar_open_size. lia.
        rewrite HeqX'. apply set_svar_fresh_is_fresh. unfold svar_is_fresh_in. apply HnotinFree1.
        rewrite (proj1 (IHsz _ _ _ _ _) Y' fresh3). rewrite -svar_open_size. lia.
        rewrite HeqY'. apply set_svar_fresh_is_fresh. unfold svar_is_fresh_in. apply HnotinFree2.
        rewrite (@svar_open_comm signature 0 (dbi+1) _ fresh3 X ϕ). lia.
        rewrite (@svar_open_comm signature 0 (dbi+1) _ fresh3 Y ϕ). lia.
        rewrite (@update_svar_val_comm _ fresh3 X). apply Hneqfr1.
        rewrite (@update_svar_val_comm _ fresh3 Y). apply Hneqfr2.
        apply svar_is_fresh_in_exists in HfrX.
        apply svar_is_fresh_in_exists in HfrY.
        rewrite (proj1 (IHsz _ _ _ _ _) X Y). rewrite -svar_open_size. lia.
        unfold svar_is_fresh_in.
        apply (@svar_fresh_notin _ (size (svar_open 0 fresh3 ϕ))). rewrite -svar_open_size. lia.
        apply HfrX. apply HnotinFree. intros Contra. symmetry in Contra. contradiction.
        apply (@svar_fresh_notin _ (size (svar_open 0 fresh3 ϕ))). rewrite -svar_open_size. lia.
        apply HfrY. apply HnotinFree. intros Contra. symmetry in Contra. contradiction.
        reflexivity.
    }
    {
      (* inductive case - evar *)
      move=> x y c Hfrx Hfry.
      destruct ϕ; simpl in Hsz.
      + rewrite (proj2 (IHsz _ _ _ _ _) x y). 4: reflexivity. 3,2: auto. simpl. lia.
      + rewrite (proj2 (IHsz _ _ _ _ _) x y). 4: reflexivity. 3,2: auto. simpl. lia.
      + rewrite (proj2 (IHsz _ _ _ _ _) x y). 4: reflexivity. 3,2: auto. simpl. lia.
      + rewrite (proj2 (IHsz _ _ _ _ _) x y). 4: reflexivity. 3,2: auto. simpl. lia.
      + rewrite (proj2 (IHsz _ _ _ _ _) x y). 4: reflexivity. 3,2: auto. simpl. lia.
      + rewrite 2!pattern_interpretation_app_simpl. fold evar_open.
        rewrite (proj2 (IHsz _ _ _ _ _) x y). 4: rewrite (proj2 (IHsz _ _ _ _ _) x y). lia.
        eapply evar_is_fresh_in_app_l. apply Hfrx.
        eapply evar_is_fresh_in_app_l. apply Hfry.
        lia.
        eapply evar_is_fresh_in_app_r. apply Hfrx.
        eapply evar_is_fresh_in_app_r. apply Hfry.
        reflexivity.
      + rewrite (proj2 (IHsz _ _ _ _ _) x y). 4: reflexivity. 3,2: auto. simpl. lia.
      + rewrite 2!pattern_interpretation_imp_simpl. fold evar_open.
        rewrite (proj2 (IHsz _ _ _ _ _) x y). 4: rewrite (proj2 (IHsz _ _ _ _ _) x y). lia.
        eapply evar_is_fresh_in_app_l. apply Hfrx.
        eapply evar_is_fresh_in_app_l. apply Hfry.
        lia.
        eapply evar_is_fresh_in_app_r. apply Hfrx.
        eapply evar_is_fresh_in_app_r. apply Hfry.
        reflexivity.
      + rewrite 2!pattern_interpretation_ex_simpl. fold evar_open. simpl.
        apply f_equal. apply functional_extensionality. intros e.
        remember (fresh_evar (evar_open (dbi + 1) x ϕ)) as x'.
        remember (fresh_evar (evar_open (dbi + 1) y ϕ)) as y'.
        remember ((@singleton evar (@EVarSet signature) _ x) ∪ ((singleton y) ∪ ((singleton x')
                 ∪ ((singleton y')
              ∪ ((free_evars (evar_open (dbi+1) x ϕ)) ∪ (free_evars (evar_open (dbi+1) y ϕ)
                ∪ (free_evars ϕ))))))) as B.
        remember (@evar_fresh (@variables signature) (elements B)) as fresh3.
        assert(HB: fresh3 ∉ B).
        {
          subst. apply set_evar_fresh_is_fresh'.
        }

        remember (free_evars (evar_open (dbi+1) y ϕ) ∪ (free_evars ϕ)) as B0.
        remember ((free_evars (evar_open (dbi+1) x ϕ)) ∪ B0) as B1.
        remember ({[y']} ∪ B1) as B2.
        remember ({[x']} ∪ B2) as B3.
        remember ({[y]} ∪ B3) as B4.
        pose proof (i := not_elem_of_union fresh3 {[x]} B4).
        pose proof (i0 := not_elem_of_union fresh3 {[y]} B3).
        pose proof (i1 := not_elem_of_union fresh3 {[x']} B2).
        pose proof (i2 := not_elem_of_union fresh3 {[y']} B1).
        pose proof (i3 := not_elem_of_union fresh3 
                                            (free_evars (evar_open (dbi+1) x ϕ)) 
                                            B0).
        subst B0. subst B1. subst B2. subst B3. subst B4. subst B.
        
        apply i in HB. clear i. destruct HB as [Hneqfr1 HB].        
        apply not_elem_of_singleton_1 in Hneqfr1.

        apply i0 in HB. clear i0. destruct HB as [Hneqfr2 HB].
        apply not_elem_of_singleton_1 in Hneqfr2.

        apply i1 in HB. clear i1. destruct HB as [Hneqfr11 HB].
        apply not_elem_of_singleton_1 in Hneqfr11.

        apply i2 in HB. clear i2. destruct HB as [Hneqfr22 HB].
        apply not_elem_of_singleton_1 in Hneqfr22.

        apply i3 in HB. clear i3. destruct HB as [HnotinFree1 HB].
        apply not_elem_of_union in HB.
        destruct HB as [HnotinFree2 HnotinFree].
        rewrite (proj2 (IHsz _ _ _ _ _) x' fresh3). rewrite -evar_open_size. lia.
        rewrite Heqx'. apply set_evar_fresh_is_fresh. unfold evar_is_fresh_in. apply HnotinFree1.
        rewrite (proj2 (IHsz _ _ _ _ _) y' fresh3). rewrite -evar_open_size. lia.
        rewrite Heqy'. apply set_evar_fresh_is_fresh. unfold evar_is_fresh_in. apply HnotinFree2.
        rewrite (@evar_open_comm signature 0 (dbi+1) _ fresh3 x ϕ). lia.
        rewrite (@evar_open_comm signature 0 (dbi+1) _ fresh3 y ϕ). lia.
        rewrite (@update_evar_val_comm _ fresh3 x). apply Hneqfr1.
        rewrite (@update_evar_val_comm _ fresh3 y). apply Hneqfr2.
        apply evar_is_fresh_in_exists in Hfrx.
        apply evar_is_fresh_in_exists in Hfry.
        rewrite (proj2 (IHsz _ _ _ _ _) x y). rewrite -evar_open_size. lia.
        unfold evar_is_fresh_in.
        apply (@fresh_notin _ (size (evar_open 0 fresh3 ϕ))). rewrite -evar_open_size. lia.
        apply Hfrx. apply HnotinFree. intros Contra. symmetry in Contra. contradiction.
        apply (@fresh_notin _ (size (evar_open 0 fresh3 ϕ))). rewrite -evar_open_size. lia.
        apply Hfry. apply HnotinFree. intros Contra. symmetry in Contra. contradiction.
        reflexivity.
      + rewrite 2!pattern_interpretation_mu_simpl. fold evar_open. simpl.
        apply f_equal. apply functional_extensionality.
        intros S'.
        rewrite -2!svar_open_evar_open_comm.
        rewrite (proj2 (IHsz _ _ _ _ _) x y). rewrite -svar_open_size. lia.
        apply evar_is_fresh_in_mu in Hfrx.
        apply evar_is_fresh_in_mu in Hfry.
        apply evar_fresh_svar_open. apply Hfrx.
        apply evar_fresh_svar_open. apply Hfry.
        rewrite 2!svar_open_evar_open_comm.
        rewrite (proj1 (IHsz _ _ _ _ _) _ (fresh_svar (evar_open dbi y ϕ))). rewrite -evar_open_size. lia.
        apply svar_fresh_evar_open.
        rewrite fresh_svar_evar_open. apply set_svar_fresh_is_fresh.
        apply set_svar_fresh_is_fresh.
        reflexivity.
    }
    
Qed.


Lemma interpretation_fresh_evar_open M ϕ x y c dbi ρₑ ρₛ:
  evar_is_fresh_in x ϕ ->
  evar_is_fresh_in y ϕ ->
  @pattern_interpretation M (update_evar_val x c ρₑ) ρₛ (evar_open dbi x ϕ)
  = @pattern_interpretation M (update_evar_val y c ρₑ) ρₛ (evar_open dbi y ϕ).
Proof.
  move=> Hfrx Hfry.
  eapply (proj2 (@Private_interpretation_fresh_var_open M (size ϕ) ϕ dbi ρₑ ρₛ _) x y c); assumption.
  Unshelve. lia.
Qed.

Lemma interpretation_fresh_svar_open M ϕ X Y S dbi ρₑ ρₛ:
  svar_is_fresh_in X ϕ ->
  svar_is_fresh_in Y ϕ ->
  @pattern_interpretation M ρₑ (update_svar_val X S ρₛ) (svar_open dbi X ϕ)
  = @pattern_interpretation M ρₑ (update_svar_val Y S ρₛ) (svar_open dbi Y ϕ).
Proof.
  move=> HfrX HfrY.
  eapply (proj1 (@Private_interpretation_fresh_var_open M (size ϕ) ϕ dbi ρₑ ρₛ _) X Y S); assumption.
  Unshelve. lia.
Qed.

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
      pose proof (Hfresh_subst := @interpretation_fresh_evar_open M phi1' Xfr2' Xu c 0 evar_val svar_val2').
      pose proof (Hwbm := wfc_mu_to_wfc_body).
      specialize (Hwbm _ Hwfc1).
      unfold wfc_body_mu in Hwbm.
      rewrite -> free_svars_exists in Hwbm.
      specialize (Hwbm X H).
      rewrite !simpl_svar_open in Hwbm.
      apply wfc_ex_to_wfc_body in Hwbm.
      unfold wfc_body_ex in Hwbm.
      rewrite -> Hfresh_subst.
      2: { subst Xfr2'. apply set_evar_fresh_is_fresh. }
      2: { pose proof (Hfr := set_evar_fresh_is_fresh').
           specialize (Hfr (union (free_evars phi1') (free_evars phi2))).
           subst Xu.
           apply not_elem_of_union in Hfr. destruct Hfr as [Hfr _]. auto.
         }

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
        pose proof (HeqHoc' := HeqHoc).
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
        rewrite -> interpretation_fresh_evar_open with (y := Xu).
        apply Same_set_refl.
        { subst Xfr1.
          symmetry in HeqHoc'.
          pose proof (Hsubst := @bsvar_subst_not_occur_is_noop _ phi1 phi2 dbi HeqHoc').
          rewrite Hsubst. apply set_evar_fresh_is_fresh.
        }
        { pose proof (Hfr := set_evar_fresh_is_fresh').
          specialize (Hfr (union (free_evars (svar_open dbi X phi1)) (free_evars phi2))).
          subst Xu.
          apply not_elem_of_union in Hfr. destruct Hfr as [Hfr _].
          rewrite free_evars_svar_open in Hfr.
          rewrite free_evars_svar_open. auto.
        }
        {
          apply bsvar_occur_evar_open. symmetry. auto.
        }

    + (* Mu case *)
      rewrite 2!pattern_interpretation_mu_simpl. simpl.
      apply f_equal. apply functional_extensionality. intros E.
      assert (Htmp: dbi+1 = (S dbi)) by lia; rewrite !Htmp; clear Htmp.

      Check interpretation_fresh_svar_open.
      remember (bsvar_subst phi1 phi2 (S dbi)) as phi_subst.
      remember (union (union (union (union (union (free_svars phi_subst) (singleton (fresh_svar phi1))) (free_svars phi1)) (free_svars (svar_open (S dbi) X phi1))) (singleton X)) (free_svars phi2)) as B.

      remember (svar_fresh (elements B)) as Y.
      assert (Hfreshy: Y <> fresh_svar phi1).
      { solve_fresh_svar_neq. }

      assert (Hfreshy': svar_is_fresh_in Y phi1).
      {
        subst.
        eapply svar_is_fresh_in_richer'.
        2: apply set_svar_fresh_is_fresh'.
        solve_free_svars_inclusion 5.
      }

      assert (Hfreshy'': svar_is_fresh_in Y (svar_open (S dbi) X phi1)).
      {
        subst.
        eapply svar_is_fresh_in_richer'.
        2: apply set_svar_fresh_is_fresh'.
        solve_free_svars_inclusion 5.
      }

      assert (Hfreshy''': Y <> X).
      { solve_fresh_svar_neq. }

      assert (Hfreshy'''': svar_is_fresh_in Y phi2).
      {
        subst.
        eapply svar_is_fresh_in_richer'.
        2: apply set_svar_fresh_is_fresh'.
        solve_free_svars_inclusion 5.
      }
      
      

      remember (bsvar_occur phi1 (S dbi)) as Hoc.
      destruct Hoc.
      --
        subst phi_subst.

        (*
        rewrite svar_open_bsvar_subst.
        { assumption. }
        { lia. } *)
        
        Check interpretation_fresh_svar_open.
        rewrite (@interpretation_fresh_svar_open _ _ ((fresh_svar (svar_open (S dbi) X phi1))) Y).
        { apply set_svar_fresh_is_fresh. }
        { apply Hfreshy''. }
        
        rewrite update_svar_val_comm.
        { apply Hfreshy'''. }
        rewrite svar_open_comm.
        { lia. }

        (*remember (fresh_svar (svar_open (S dbi) X phi1)) as X'.*)
        remember ((update_svar_val Y E svar_val)) as svar_val'.

        assert (Hpieq: (pattern_interpretation evar_val svar_val' phi2) = (pattern_interpretation evar_val svar_val phi2)).
        { subst svar_val'.
          apply interpretation_fresh_svar.
          apply Hfreshy''''.
        }
        rewrite -Hpieq.
        clear Hpieq.
        
        rewrite <- IHsz.
        5: { apply svar_is_fresh_in_svar_open.
             apply not_eq_sym.
             apply Hfreshy'''.
             simpl in H.
             apply H.
        }
        4: { apply Hwfc2. }
        3: { admit. }
        2: { rewrite -svar_open_size. simpl in Hsz. lia. }
        
        subst svar_val'.
        rewrite svar_open_bsvar_subst.
        { apply Hwfc2. }
        { lia. }
        admit.
        (*
        
        pose proof (IH := @IHsz (S dbi) M (svar_open 0 Y phi1) phi2).
        erewrite <- IH.
        rewrite -> IHsz with (X := Y).
        5: admit.
        4: admit.
        3: admit.
        2: { rewrite -svar_open_size. simpl in Hsz. lia.  }
        
        remember (update_svar_val (fresh_svar (bsvar_subst phi1 phi2 (S dbi))) E svar_val) as svar_val'.
        rewrite svar_open_comm.
        { lia. }

        assert (Hpieq: pattern_interpretation evar_val svar_val' phi2
                       = pattern_interpretation evar_val svar_val phi2).
        {   admit. }
        rewrite Hpieq.
        simpl. (* subst. *)
        Check interpretation_fresh_svar_open.
        Search svar_open "comm".
        rewrite svar_open_comm. { lia. }
        (* rewrite -> interpretation_fresh_svar_open with (X := X) (Y := Y).*)
                                rewrite update_svar_val_comm.
        
        
        
        { admit. }
        rewrite interpretation_fresh_svar_open.
        2: apply set_svar_fresh_is_fresh.
        admit. admit. admit. admit.
*)
      --

        rewrite Heqphi_subst.
        rewrite bsvar_subst_not_occur_is_noop. { auto. }
        rewrite bsvar_subst_not_occur_is_noop in Heqphi_subst. { auto. }
        
        rewrite -> interpretation_fresh_svar_open with (X := fresh_svar phi1) (Y := Y).
        2: { apply set_svar_fresh_is_fresh. }
        2: { subst.
             eapply svar_is_fresh_in_richer'.
             2: apply set_svar_fresh_is_fresh'.
             solve_free_svars_inclusion 5.
        }

        simpl in Hsz.
        
        subst phi_subst. (*rewrite svar_open_bsvar_subst.
        { assumption. }
        { lia. }*)
        (*rewrite update_svar_val_comm. { admit. }*)

        Search svar_open bsvar_occur.
        Check @svar_open_not_occur_is_noop.
        rewrite -> svar_open_not_occur_is_noop with (X0 := X)(dbi0 := S dbi).
        2: { symmetry. apply HeqHoc. }
        Search pattern_interpretation svar_is_fresh_in.
        destruct (svar_eqdec X (fresh_svar phi1)).
        ++ subst X. rewrite update_svar_val_shadow.
           apply interpretation_fresh_svar_open.
           { apply Hfreshy'. }
           apply set_svar_fresh_is_fresh.
        ++ rewrite update_svar_val_comm.
           { apply not_eq_sym. apply n. }                              
           rewrite (@interpretation_fresh_svar _ X).
           { apply svar_is_fresh_in_svar_open.
             { apply n. }
             simpl in H. apply H.
           }
           apply interpretation_fresh_svar_open.
           { apply Hfreshy'. }
           apply set_svar_fresh_is_fresh.
Admitted.



Lemma Private_pattern_interpretation_free_evar_independent M ρₑ ρₛ x v sz ϕ:
  size ϕ <= sz ->
  evar_is_fresh_in x ϕ ->
  @pattern_interpretation M (update_evar_val x v ρₑ) ρₛ ϕ
  = @pattern_interpretation M ρₑ ρₛ ϕ.
Proof.
  generalize dependent v. generalize dependent x.
  generalize dependent ρₛ. generalize dependent ρₑ. generalize dependent ϕ.
  induction sz; intros ϕ ρₑ ρₛ x v; destruct ϕ; simpl; intros Hsz Hnotin; unfold evar_is_fresh_in in Hnotin;
    simpl in Hnotin.
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
  - apply IHsz. 2: { simpl. apply Hnotin. } simpl. lia.
  - apply IHsz. 2: { simpl. apply Hnotin. } simpl. lia.
  - apply IHsz. 2: { simpl. apply Hnotin. } simpl. lia.
  - apply IHsz. 2: { simpl. apply Hnotin. } simpl. lia.
  - apply IHsz. 2: { simpl. apply Hnotin. } simpl. lia.
  - repeat rewrite -> pattern_interpretation_app_simpl.
    simpl in Hnotin.
    apply not_elem_of_union in Hnotin. destruct Hnotin as [Hnotin1 Hnotin2].
    rewrite -> IHsz. 3: apply Hnotin1. 2: lia.
    rewrite -> IHsz. 3: apply Hnotin2. 2: lia.
    reflexivity.
  - apply IHsz. 2: { simpl. apply Hnotin. } simpl. lia.
  - repeat rewrite -> pattern_interpretation_imp_simpl.
    simpl in Hnotin.
    apply not_elem_of_union in Hnotin. destruct Hnotin as [Hnotin1 Hnotin2].
    rewrite -> IHsz. 3: apply Hnotin1. 2: lia.
    rewrite -> IHsz. 3: apply Hnotin2. 2: lia.
    reflexivity.
  - repeat rewrite -> pattern_interpretation_ex_simpl.
    simpl.
   
    apply f_equal. apply functional_extensionality. intros e.
    destruct (evar_eqdec (fresh_evar ϕ) x).
    + rewrite -> e0. rewrite -> update_evar_val_shadow. reflexivity.
    + rewrite -> update_evar_val_comm. 2: apply n.
      rewrite -> IHsz.
      3: { intros Contra.
           pose proof (Hfeeo := @free_evars_evar_open signature ϕ (fresh_evar ϕ) 0).
           rewrite -> elem_of_subseteq in Hfeeo.
           specialize (Hfeeo x Contra).
           apply elem_of_union in Hfeeo.
           destruct Hfeeo as [H|H].
           * apply elem_of_singleton_1 in H. symmetry in H. contradiction.
           * contradiction.
      }
      2: { rewrite <- evar_open_size. lia. }
      reflexivity.
  - repeat rewrite -> pattern_interpretation_mu_simpl. simpl.
    
    apply f_equal. apply functional_extensionality.
    intros e.
    rewrite -> IHsz.
    3: { intros Contra.
         rewrite -> free_evars_svar_open in Contra.
         contradiction.
    }
    2: {
      rewrite <- svar_open_size. lia.
    }
    reflexivity.
Qed.

Lemma pattern_interpretation_free_evar_independent M ρₑ ρₛ x v ϕ:
  evar_is_fresh_in x ϕ ->
  @pattern_interpretation M (update_evar_val x v ρₑ) ρₛ ϕ
  = @pattern_interpretation M ρₑ ρₛ ϕ.
Proof.
  intros.
  apply Private_pattern_interpretation_free_evar_independent with (sz := size ϕ).
  * lia.
  * assumption.
Qed.

Lemma Private_pattern_interpretation_free_svar_independent M ρₑ ρₛ X S sz ϕ:
  size ϕ <= sz ->
  svar_is_fresh_in X ϕ ->
  @pattern_interpretation M ρₑ (update_svar_val X S ρₛ) ϕ
  = @pattern_interpretation M ρₑ ρₛ ϕ.
Proof.
  generalize dependent S. generalize dependent X.
  generalize dependent ρₛ. generalize dependent ρₑ. generalize dependent ϕ.
  induction sz; intros ϕ ρₑ ρₛ X S; destruct ϕ; simpl; intros Hsz Hnotin; unfold svar_is_fresh_in in Hnotin;
    simpl in Hnotin.
  - repeat rewrite -> pattern_interpretation_free_evar_simpl.
    reflexivity.
  - repeat rewrite pattern_interpretation_free_svar_simpl.
    unfold update_svar_val.
    destruct (svar_eqdec X x); simpl.
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
  - lia.
  - repeat rewrite -> pattern_interpretation_bott_simpl.
    reflexivity.
  - lia.
  - lia.
  - lia.
  - apply IHsz. 2: { simpl. apply Hnotin. } simpl. lia.
  - apply IHsz. 2: { simpl. apply Hnotin. } simpl. lia.
  - apply IHsz. 2: { simpl. apply Hnotin. } simpl. lia.
  - apply IHsz. 2: { simpl. apply Hnotin. } simpl. lia.
  - apply IHsz. 2: { simpl. apply Hnotin. } simpl. lia.
  - repeat rewrite -> pattern_interpretation_app_simpl.
    simpl in Hnotin.
    apply not_elem_of_union in Hnotin. destruct Hnotin as [Hnotin1 Hnotin2].
    rewrite -> IHsz. 3: apply Hnotin1. 2: lia.
    rewrite -> IHsz. 3: apply Hnotin2. 2: lia.
    reflexivity.
  - apply IHsz. 2: { simpl. apply Hnotin. } simpl. lia.
  - repeat rewrite -> pattern_interpretation_imp_simpl.
    simpl in Hnotin.
    apply not_elem_of_union in Hnotin. destruct Hnotin as [Hnotin1 Hnotin2].
    rewrite -> IHsz. 3: apply Hnotin1. 2: lia.
    rewrite -> IHsz. 3: apply Hnotin2. 2: lia.
    reflexivity.
  - repeat rewrite -> pattern_interpretation_ex_simpl.
    simpl.
    apply f_equal. apply functional_extensionality. intros e.
    rewrite IHsz.
    { rewrite -evar_open_size. lia. }
    { apply svar_fresh_evar_open. apply Hnotin. }
    reflexivity.
  - repeat rewrite pattern_interpretation_mu_simpl. simpl.
    apply f_equal. apply functional_extensionality.
    intros e.
    destruct (svar_eqdec (fresh_svar ϕ) X).
    + rewrite e0. rewrite update_svar_val_shadow. reflexivity.
    + rewrite update_svar_val_comm.
      { apply n.  }
      rewrite IHsz.
      { rewrite -svar_open_size. lia.  }

      { intros Contra.
        pose proof (Hfeeo := @free_svars_svar_open signature ϕ (fresh_svar ϕ) 0).
        rewrite -> elem_of_subseteq in Hfeeo.
        specialize (Hfeeo X Contra).
        apply elem_of_union in Hfeeo.
        destruct Hfeeo as [H|H].
        * apply elem_of_singleton_1 in H. symmetry in H. contradiction.
        * contradiction.
      }
      reflexivity.
Qed.

Lemma pattern_interpretation_free_svar_independent M ρₑ ρₛ X S ϕ:
  svar_is_fresh_in X ϕ ->
  @pattern_interpretation M ρₑ (update_svar_val X S ρₛ) ϕ
  = @pattern_interpretation M ρₑ ρₛ ϕ.
Proof.
  intros.
  apply Private_pattern_interpretation_free_svar_independent with (sz := size ϕ).
  * lia.
  * assumption.
Qed.

Lemma interpretation_fresh_evar_subterm M ϕ₁ ϕ₂ c dbi ρₑ ρₛ :
  is_subformula_of_ind ϕ₁ ϕ₂ ->
  @pattern_interpretation M (update_evar_val (fresh_evar ϕ₂) c ρₑ) ρₛ (evar_open dbi (fresh_evar ϕ₂) ϕ₁)
  = @pattern_interpretation M (update_evar_val (fresh_evar ϕ₁) c ρₑ) ρₛ (evar_open dbi (fresh_evar ϕ₁) ϕ₁).
Proof.
  intros Hsub.
  apply interpretation_fresh_evar_open; auto.
  eapply evar_fresh_in_subformula. apply Hsub.
  apply set_evar_fresh_is_fresh.
Qed.


Lemma M_predicate_evar_open_fresh_evar_1 M x₁ x₂ ϕ :
  evar_is_fresh_in x₁ ϕ ->
  evar_is_fresh_in x₂ ϕ ->
  M_predicate M (evar_open 0 x₁ ϕ) ->
  M_predicate M (evar_open 0 x₂ ϕ).
Proof.
  intros Hfr1 Hfr2.
  unfold evar_is_fresh_in in *.
  unfold M_predicate.
  intros H ρₑ ρₛ.
  rewrite -(@update_evar_val_same_2 M x₂ ρₑ).
  rewrite (@interpretation_fresh_evar_open M _ x₂ x₁); auto.
Qed.

Lemma M_predicate_evar_open_fresh_evar_2 M x ϕ :
  evar_is_fresh_in x ϕ ->
  M_predicate M (evar_open 0 (fresh_evar ϕ) ϕ) ->
  M_predicate M (evar_open 0 x ϕ).
Proof.
  intros Hfr H.
  apply M_predicate_evar_open_fresh_evar_1 with (x₁ := fresh_evar ϕ); auto.
Qed.

(* TODO similar for svar_open_nest_mu *)
Lemma Private_pattern_interpretation_evar_open_nest_ex M sz ϕ x dbi e ρₑ ρₛ :
  size ϕ <= sz ->
  evar_is_fresh_in x ϕ ->
  @pattern_interpretation M (update_evar_val x e ρₑ) ρₛ (evar_open dbi x (nest_ex_aux dbi ϕ))
  = @pattern_interpretation M ρₑ ρₛ ϕ.
Proof.
  move: ϕ x dbi e ρₑ ρₛ.
  induction sz; move=> ϕ x dbi e ρₑ ρₛ.
  - destruct ϕ; simpl; move=> Hsz Hfr; try reflexivity; try lia.
    apply pattern_interpretation_free_evar_independent.
    unfold evar_is_fresh_in in Hfr. apply Hfr.
    destruct (Nat.leb_spec0 dbi n).
    + destruct (eqb_reflect (S n) dbi); try lia.
      rewrite 2!pattern_interpretation_bound_evar_simpl. reflexivity.
    + destruct (eqb_reflect n dbi); try lia.
      rewrite 2!pattern_interpretation_bound_evar_simpl. reflexivity.
  - pose proof (Hnot0 := not_bevar_occur_0_nest_ex ϕ).
    destruct ϕ; simpl; move=> Hsz Hfr; try reflexivity.
    + (* duplicate *)
      apply pattern_interpretation_free_evar_independent.
      unfold evar_is_fresh_in in Hfr. apply Hfr.
    + destruct (Nat.leb_spec0 dbi n).
      * destruct (eqb_reflect (S n) dbi); try lia.
        rewrite 2!pattern_interpretation_bound_evar_simpl. reflexivity.
      * destruct (eqb_reflect n dbi); try lia.
        rewrite 2!pattern_interpretation_bound_evar_simpl. reflexivity.        
    + simpl in Hnot0.
      apply orb_false_iff in Hnot0. destruct Hnot0 as [Hnot1 Hnot2].
      rewrite 2!pattern_interpretation_app_simpl.
      rewrite IHsz. lia. eapply evar_is_fresh_in_app_l. apply Hfr.
      rewrite IHsz. lia. eapply evar_is_fresh_in_app_r. apply Hfr.
      reflexivity.
    + simpl in Hnot0.
      apply orb_false_iff in Hnot0. destruct Hnot0 as [Hnot1 Hnot2].
      rewrite 2!pattern_interpretation_imp_simpl.
      rewrite IHsz. lia. eapply evar_is_fresh_in_app_l. apply Hfr.
      rewrite IHsz. lia. eapply evar_is_fresh_in_app_r. apply Hfr.
      reflexivity.
    + simpl in Hnot0.
      rewrite 2!pattern_interpretation_ex_simpl. simpl.
      apply f_equal. apply functional_extensionality.
      intros c.
      remember (evar_open (S dbi) x (nest_ex_aux (S dbi) ϕ)) as ϕ'.
      remember (fresh_evar (evar_open (S dbi) x (nest_ex_aux (S dbi) ϕ))) as x'.

      assert (Hplus1: dbi+1 = S dbi). lia. rewrite Hplus1. clear Hplus1.

      (* replace x' with x'' such that x'' <> x (and x'' is fresh in ϕ) *)

      remember ((@singleton evar (@EVarSet signature) _ x)
                  ∪ ((free_evars (evar_open (S dbi) x (nest_ex_aux (S dbi) ϕ)))
               ∪ (free_evars ϕ))) as B.
      remember (evar_fresh (elements B)) as x''.
      assert(HB: x'' ∉ B).
      { subst. apply set_evar_fresh_is_fresh'. }
      rewrite HeqB in HB.
      apply not_elem_of_union in HB.
      destruct HB as [Hx''neqx HB].
      apply not_elem_of_singleton_1 in Hx''neqx.
      apply not_elem_of_union in HB.
      destruct HB as [Hfree1 Hfree2].
      
      fold (evar_is_fresh_in x'' (evar_open (S dbi) x (nest_ex_aux (S dbi) ϕ))) in Hfree1.
      rewrite (@interpretation_fresh_evar_open _ _ _ x'').
      apply set_evar_fresh_is_fresh. apply Hfree1.
      
      rewrite evar_open_nest_ex_aux_comm in Heqϕ'.
      destruct (compare_nat (S dbi) (S dbi)); try lia.

      rewrite evar_open_comm. lia.
      rewrite (evar_open_nest_ex_aux_comm _ _ 0).
      destruct (compare_nat 0 (S dbi)); try lia.

      rewrite update_evar_val_comm. apply Hx''neqx.
      rewrite (IHsz _ x (S dbi)). rewrite -evar_open_size. lia.
      apply evar_is_fresh_in_evar_open. intros Contra. symmetry in Contra. contradiction.
      apply evar_is_fresh_in_exists in Hfr. apply Hfr.

      apply interpretation_fresh_evar_open. apply Hfree2.
      apply set_evar_fresh_is_fresh.
    + simpl in Hnot0.
      fold (nest_ex ϕ) in Hnot0.

      rewrite 2!pattern_interpretation_mu_simpl. simpl.
      apply f_equal. apply functional_extensionality.

      intros S.
      rewrite -svar_open_evar_open_comm.
      rewrite svar_open_nest_ex_aux_comm.
      rewrite IHsz. rewrite -svar_open_size. lia.
      apply evar_fresh_svar_open.
      apply evar_is_fresh_in_mu in Hfr. apply Hfr.
      rewrite (@interpretation_fresh_svar_open _ _ _ (fresh_svar ϕ)).
      rewrite fresh_svar_evar_open. rewrite fresh_svar_nest_ex_aux.
      1,2: apply set_svar_fresh_is_fresh.
      reflexivity.
Qed.

(*
Lemma Private_pattern_interpretation_svar_open_nest_mu M sz ϕ X dbi S' ρₑ ρₛ :
  size ϕ <= sz ->
  svar_is_fresh_in X ϕ ->
  @pattern_interpretation M ρₑ (update_svar_val X S' ρₛ) (svar_open dbi X (nest_mu_aux dbi ϕ))
  = @pattern_interpretation M ρₑ ρₛ ϕ.
Proof.
  move: ϕ X dbi S' ρₑ ρₛ.
  induction sz; move=> ϕ X dbi S' ρₑ ρₛ.
  - destruct ϕ; simpl; move=> Hsz Hfr; try reflexivity; try lia.
    apply pattern_interpretation_free_svar_independent.
    unfold svar_is_fresh_in in Hfr. apply Hfr.
    destruct (Nat.leb_spec0 dbi n).
    + destruct (eqb_reflect (S n) dbi); try lia. 
      rewrite 2!pattern_interpretation_bound_svar_simpl. reflexivity.
    + destruct (eqb_reflect n dbi); try lia.
      rewrite 2!pattern_interpretation_bound_svar_simpl. reflexivity.
  - pose proof (Hnot0 := not_bsvar_occur_0_nest_mu ϕ).
    destruct ϕ; simpl; move=> Hsz Hfr; try reflexivity.
    + (* duplicate *)
      apply pattern_interpretation_free_svar_independent.
      unfold evar_is_fresh_in in Hfr. apply Hfr.
    + destruct (Nat.leb_spec0 dbi n).
      * destruct (eqb_reflect (S n) dbi); try lia.
        rewrite 2!pattern_interpretation_bound_svar_simpl. reflexivity.
      * destruct (eqb_reflect n dbi); try lia.
        rewrite 2!pattern_interpretation_bound_svar_simpl. reflexivity.
    + simpl in Hnot0.
      apply orb_false_iff in Hnot0. destruct Hnot0 as [Hnot1 Hnot2].
      rewrite 2!pattern_interpretation_app_simpl.
      rewrite IHsz. lia. eapply svar_is_fresh_in_app_l. apply Hfr.
      rewrite IHsz. lia. eapply svar_is_fresh_in_app_r. apply Hfr.
      reflexivity.
    + simpl in Hnot0.
      apply orb_false_iff in Hnot0. destruct Hnot0 as [Hnot1 Hnot2].
      rewrite 2!pattern_interpretation_imp_simpl.
      rewrite IHsz. lia. eapply svar_is_fresh_in_app_l. apply Hfr.
      rewrite IHsz. lia. eapply svar_is_fresh_in_app_r. apply Hfr.
      reflexivity.
    + simpl in Hnot0.
      rewrite 2!pattern_interpretation_ex_simpl. simpl.
      apply f_equal. apply functional_extensionality.
      intros c.

      rewrite svar_open_evar_open_comm.
      rewrite evar_open_nest_mu_aux_comm.
      rewrite IHsz.
      { rewrite -evar_open_size. lia.  }
      { apply svar_fresh_evar_open. apply svar_is_fresh_in_exists in Hfr. apply Hfr. }
      rewrite (@interpretation_fresh_evar_open _ _ _ (fresh_evar ϕ)).
      { rewrite fresh_evar_svar_open. rewrite fresh_evar_nest_mu_aux. apply set_evar_fresh_is_fresh. }
      { apply set_evar_fresh_is_fresh. }
      reflexivity.
      
    + simpl in Hnot0.
      rewrite 2!pattern_interpretation_mu_simpl. simpl.
      apply f_equal. apply functional_extensionality.
      intros c.

      assert (Hplus1: dbi+1 = S dbi). lia. rewrite Hplus1. clear Hplus1.

      remember (svar_open (S dbi) X (nest_mu_aux (S dbi) ϕ)) as ϕ'.
      remember (fresh_svar ϕ') as X'.
      
      (* replace X' with X'' such that X'' <> X (and X'' is fresh in ϕ) *)

      remember ((@singleton svar (@SVarSet signature) _ X)
                  ∪ ((free_svars (svar_open (S dbi) X (nest_mu_aux (S dbi) ϕ)))
               ∪ (free_svars ϕ))) as B.
      remember (svar_fresh (elements B)) as X''.

      assert (X'' <> X).
      { solve_fresh_svar_neq. }

      assert (svar_is_fresh_in X'' ϕ).
      {
        eapply svar_is_fresh_in_richer'.
        2: { rewrite HeqX''. apply set_svar_fresh_is_fresh'. }
        subst.
        solve_free_svars_inclusion 5.
      }

      assert (svar_is_fresh_in X'' ϕ').
      {
        eapply svar_is_fresh_in_richer'.
        2: { rewrite HeqX''. apply set_svar_fresh_is_fresh'. }
        subst.
        solve_free_svars_inclusion 5.
      }

      assert (svar_is_fresh_in X' ϕ').
      { subst. apply set_svar_fresh_is_fresh. }

      assert (svar_is_fresh_in X (svar_open 0 X'' ϕ)).
      {
        apply svar_is_fresh_in_svar_open.
        { apply nesym. assumption. }
        assumption.
      }
      
      rewrite (@interpretation_fresh_svar_open _ _ _ X'').
      { assumption. }
      { assumption. }

      rewrite Heqϕ'.
      rewrite svar_open_comm.
      { lia. }

      rewrite svar_open_nest_mu_aux_comm.
      destruct (compare_nat 0 (S dbi)); try lia.

      rewrite update_svar_val_comm.
      { assumption. }
      
      rewrite IHsz.
      { rewrite -svar_open_size. lia. }
      { assumption. }
      
      apply interpretation_fresh_svar_open.
      { assumption. }
      apply set_svar_fresh_is_fresh.
Qed.
*)


Lemma pattern_interpretation_evar_open_nest_ex M ϕ x e ρₑ ρₛ :
  evar_is_fresh_in x ϕ ->
  @pattern_interpretation M (update_evar_val x e ρₑ) ρₛ (evar_open 0 x (nest_ex ϕ))
  = @pattern_interpretation M ρₑ ρₛ ϕ.
Proof.
  intros Hfr. apply Private_pattern_interpretation_evar_open_nest_ex with (sz := size ϕ). lia. assumption.
Qed.

Lemma pattern_interpretation_evar_open_nest_ex' M ϕ x ρₑ ρₛ :
  evar_is_fresh_in x ϕ ->
  @pattern_interpretation M ρₑ ρₛ (evar_open 0 x (nest_ex ϕ))
  = @pattern_interpretation M ρₑ ρₛ ϕ.
Proof.
  intros Hfr.
  rewrite -{1}(@update_evar_val_same_2 M x ρₑ).
  apply pattern_interpretation_evar_open_nest_ex.
  apply Hfr.  
Qed.



Lemma Private_pattern_interpretation_svar_open_nest_mu_aux M sz ϕ X dbi S ρₑ ρₛ :
  size ϕ <= sz ->
  svar_is_fresh_in X ϕ ->
  @pattern_interpretation M ρₑ (update_svar_val X S ρₛ) (svar_open dbi X (nest_mu_aux dbi ϕ))
  = @pattern_interpretation M ρₑ ρₛ ϕ.
Proof.
  move: ϕ X dbi S ρₑ ρₛ.
  induction sz; move=> ϕ X dbi S ρₑ ρₛ.
  - destruct ϕ; simpl; move=> Hsz Hfr; try reflexivity; try lia.
    apply pattern_interpretation_free_svar_independent.
    unfold evar_is_fresh_in in Hfr. apply Hfr.
    destruct (Nat.leb_spec0 dbi n).
    + destruct (eqb_reflect (Datatypes.S n) dbi); try lia. simpl.
      rewrite 2!pattern_interpretation_bound_svar_simpl. reflexivity.
    + destruct (eqb_reflect n dbi); try lia.
      rewrite 2!pattern_interpretation_bound_svar_simpl. reflexivity.
  - pose proof (Hnot0 := not_bsvar_occur_0_nest_mu ϕ).
    destruct ϕ; simpl; move=> Hsz Hfr; try reflexivity.
    + (* duplicate *)
      apply pattern_interpretation_free_svar_independent.
      unfold evar_is_fresh_in in Hfr. apply Hfr.
    + destruct (Nat.leb_spec0 dbi n).
      * destruct (eqb_reflect (Datatypes.S n) dbi); try lia.
        rewrite 2!pattern_interpretation_bound_svar_simpl. reflexivity.
      * destruct (eqb_reflect n dbi); try lia.
        rewrite 2!pattern_interpretation_bound_svar_simpl. reflexivity.
    + simpl in Hnot0.
      apply orb_false_iff in Hnot0. destruct Hnot0 as [Hnot1 Hnot2].
      rewrite 2!pattern_interpretation_app_simpl.
      rewrite IHsz. lia. eapply svar_is_fresh_in_app_l. apply Hfr.
      rewrite IHsz. lia. eapply svar_is_fresh_in_app_r. apply Hfr.
      reflexivity.
    + simpl in Hnot0.
      apply orb_false_iff in Hnot0. destruct Hnot0 as [Hnot1 Hnot2].
      rewrite 2!pattern_interpretation_imp_simpl.
      rewrite IHsz. lia. eapply svar_is_fresh_in_app_l. apply Hfr.
      rewrite IHsz. lia. eapply svar_is_fresh_in_app_r. apply Hfr.
      reflexivity.
    + simpl in Hnot0.
      rewrite 2!pattern_interpretation_ex_simpl. simpl.
      apply f_equal. apply functional_extensionality.
      intros c.
      rewrite svar_open_evar_open_comm.
      rewrite evar_open_nest_mu_aux_comm.
      rewrite IHsz.
      { rewrite -evar_open_size. lia. }
      { apply svar_fresh_evar_open. apply svar_is_fresh_in_exists in Hfr. apply Hfr. }
      rewrite (@interpretation_fresh_evar_open _ _ _ (fresh_evar ϕ)).
      rewrite fresh_evar_svar_open. rewrite fresh_evar_nest_mu_aux.
      1,2: apply set_evar_fresh_is_fresh.
      reflexivity.      
      
    + simpl in Hnot0.
      rewrite 2!pattern_interpretation_mu_simpl. simpl.
      apply f_equal. apply functional_extensionality.
      intros S'.

      assert (Hplus1: dbi+1 = 1+dbi).
      { lia. }
      rewrite Hplus1. clear Hplus1. simpl.
      
      remember (svar_open (Datatypes.S dbi) X (nest_mu_aux (Datatypes.S dbi) ϕ)) as ϕ'.
      remember (fresh_svar ϕ') as X'.


      (* replace x' with x'' such that x'' <> x (and x'' is fresh in ϕ) *)

      remember ((@singleton svar (@SVarSet signature) _ X)
                  ∪ ((free_svars (svar_open (Datatypes.S dbi) X (nest_mu_aux (Datatypes.S dbi) ϕ)))
               ∪ (free_svars ϕ))) as B.
      remember (svar_fresh (elements B)) as X''.
      assert(HB: X'' ∉ B).
      { subst. apply set_svar_fresh_is_fresh'. }
      rewrite HeqB in HB.
      apply not_elem_of_union in HB.
      destruct HB as [Hx''neqx HB].
      apply not_elem_of_singleton_1 in Hx''neqx.
      apply not_elem_of_union in HB.
      destruct HB as [Hfree1 Hfree2].
      
      fold (svar_is_fresh_in X'' (svar_open (Datatypes.S dbi) X (nest_mu_aux (Datatypes.S dbi) ϕ))) in Hfree1.
      rewrite (@interpretation_fresh_svar_open _ _ _ X'').
      { subst. apply set_svar_fresh_is_fresh. }
      { subst. apply Hfree1. }
      
      rewrite Heqϕ'.    
      rewrite svar_open_comm.
      { lia. }
      rewrite (svar_open_nest_mu_aux_comm _ _ 0).
      destruct (compare_nat 0 (Datatypes.S dbi)); try lia.


      rewrite update_svar_val_comm.
      { apply Hx''neqx. }
      
      rewrite (IHsz _ X (Datatypes.S dbi)).
      { rewrite -svar_open_size. lia. }
      { apply svar_is_fresh_in_svar_open. intros Contra. symmetry in Contra. contradiction.
        apply svar_is_fresh_in_mu in Hfr. apply Hfr.
      }

      apply interpretation_fresh_svar_open. { apply Hfree2. }
      apply set_svar_fresh_is_fresh.
Qed.


Lemma pattern_interpretation_svar_open_nest_mu_aux M ϕ X dbi S ρₑ ρₛ :
  svar_is_fresh_in X ϕ ->
  @pattern_interpretation M ρₑ (update_svar_val X S ρₛ) (svar_open dbi X (nest_mu_aux dbi ϕ))
  = @pattern_interpretation M ρₑ ρₛ ϕ.
Proof.
  apply Private_pattern_interpretation_svar_open_nest_mu_aux with (sz := size ϕ).
  lia.
Qed.

Lemma pattern_interpretation_svar_open_nest_mu M ϕ X S ρₑ ρₛ :
  svar_is_fresh_in X ϕ ->
  @pattern_interpretation M ρₑ (update_svar_val X S ρₛ) (svar_open 0 X (nest_mu ϕ))
  = @pattern_interpretation M ρₑ ρₛ ϕ.
Proof.
  apply pattern_interpretation_svar_open_nest_mu_aux.
Qed.

Lemma pattern_interpretation_svar_open_nest_mu' M ϕ X ρₑ ρₛ :
  svar_is_fresh_in X ϕ ->
  @pattern_interpretation M ρₑ ρₛ (svar_open 0 X (nest_mu ϕ))
  = @pattern_interpretation M ρₑ ρₛ ϕ.
Proof.
  intros Hfr.
  rewrite -{1}(@update_svar_val_same_2 M X ρₛ).
  apply pattern_interpretation_svar_open_nest_mu.
  apply Hfr.
Qed.


Lemma Private_pattern_interpretation_nest_ex_aux M sz ϕ level ρₑ ρₛ :
  size ϕ <= sz ->
  @pattern_interpretation M ρₑ ρₛ (nest_ex_aux level ϕ)
  = @pattern_interpretation M ρₑ ρₛ ϕ.
Proof.
  move: ϕ level ρₑ ρₛ.
  induction sz; move=> ϕ; destruct ϕ; move=> level ρₑ ρₛ Hsz; simpl; simpl in Hsz; try reflexivity; try lia.
  - rewrite 2!pattern_interpretation_app_simpl.
    rewrite IHsz. lia. rewrite IHsz. lia.
    reflexivity.
  - rewrite 2!pattern_interpretation_imp_simpl.
    rewrite IHsz. lia. rewrite IHsz. lia.
    reflexivity.
  - rewrite 2!pattern_interpretation_ex_simpl.
    simpl. apply f_equal. apply functional_extensionality.
    intros m.
    rewrite evar_open_nest_ex_aux_comm. simpl.
    rewrite IHsz. rewrite -evar_open_size. lia.
    rewrite fresh_evar_nest_ex_aux.
    reflexivity.
  - rewrite 2!pattern_interpretation_mu_simpl.
    simpl. apply f_equal. apply functional_extensionality.
    intros S.
    rewrite svar_open_nest_ex_aux_comm.
    rewrite IHsz. rewrite -svar_open_size. lia.
    rewrite fresh_svar_nest_ex_aux.
    reflexivity.
Qed.

Lemma pattern_interpretation_nest_ex_aux M ϕ level ρₑ ρₛ :
  @pattern_interpretation M ρₑ ρₛ (nest_ex_aux level ϕ)
  = @pattern_interpretation M ρₑ ρₛ ϕ.
Proof.
  apply Private_pattern_interpretation_nest_ex_aux with (sz := size ϕ).
  lia.
Qed.

Lemma Private_pattern_interpretation_nest_mu_aux M sz ϕ level ρₑ ρₛ :
  size ϕ <= sz ->
  @pattern_interpretation M ρₑ ρₛ (nest_mu_aux level ϕ)
  = @pattern_interpretation M ρₑ ρₛ ϕ.
Proof.
  move: ϕ level ρₑ ρₛ.
  induction sz; move=> ϕ; destruct ϕ; move=> level ρₑ ρₛ Hsz; simpl; simpl in Hsz; try reflexivity; try lia.
  - rewrite 2!pattern_interpretation_app_simpl.
    rewrite IHsz. lia. rewrite IHsz. lia.
    reflexivity.
  - rewrite 2!pattern_interpretation_imp_simpl.
    rewrite IHsz. lia. rewrite IHsz. lia.
    reflexivity.
  - rewrite 2!pattern_interpretation_ex_simpl.
    simpl. apply f_equal. apply functional_extensionality.
    intros m.
    rewrite evar_open_nest_mu_aux_comm. simpl.
    rewrite IHsz. rewrite -evar_open_size. lia.
    rewrite fresh_evar_nest_mu_aux.
    reflexivity.
  - rewrite 2!pattern_interpretation_mu_simpl.
    simpl. apply f_equal. apply functional_extensionality.
    intros S.
    rewrite svar_open_nest_mu_aux_comm.
    rewrite IHsz. rewrite -svar_open_size. lia.
    rewrite fresh_svar_nest_mu_aux.
    reflexivity.
Qed.

Lemma pattern_interpretation_nest_mu_aux M ϕ level ρₑ ρₛ :
  @pattern_interpretation M ρₑ ρₛ (nest_mu_aux level ϕ)
  = @pattern_interpretation M ρₑ ρₛ ϕ.
Proof.
  apply Private_pattern_interpretation_nest_mu_aux with (sz := size ϕ).
  lia.
Qed.

Lemma Private_free_svar_subst_update_exchange {m : Model}: ∀ sz phi psi X svar_val evar_val,
  le (Syntax.size phi) sz → well_formed psi → well_formed_closed phi → 
  pattern_interpretation evar_val svar_val (free_svar_subst phi psi X) =
  pattern_interpretation evar_val (@update_svar_val m X 
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
      pose (@pattern_interpretation_free_evar_independent m evar_val svar_val fresh c psi).
      rewrite -> e0 in e. clear e0.
      rewrite -> (@evar_open_free_svar_subst_comm) in H.
      rewrite -> e in H.
      exact H. inversion Hwfc. apply wfc_ind_wfc. eapply (H9 fresh). 
      unfold evar_is_fresh_in in H6. assumption. destruct Hwf. assumption. assumption.
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
      pose (@pattern_interpretation_free_evar_independent m evar_val svar_val fresh c psi).
      rewrite -> e0 in e. clear e0.
      rewrite -> (evar_open_free_svar_subst_comm).
      rewrite -> e.
      exact H. inversion Hwfc. apply wfc_ind_wfc. eapply (H9 fresh). 
      unfold evar_is_fresh_in in H6. assumption.
      destruct Hwf. assumption. assumption. assumption. assumption.
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
      pose (@pattern_interpretation_free_evar_independent m evar_val svar_val fresh c psi).
      rewrite -> e0 in e. clear e0.
      rewrite -> (evar_open_free_svar_subst_comm) in H1.
      rewrite -> e in H1.
      exact H1. inversion Hwfc. apply wfc_ind_wfc. eapply (H10 fresh). 
      unfold evar_is_fresh_in in H6. assumption.
      destruct Hwf. assumption. assumption. assumption. assumption.
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
      pose (@pattern_interpretation_free_evar_independent m evar_val svar_val fresh c psi).
      rewrite -> e0 in e. clear e0.
      rewrite -> (evar_open_free_svar_subst_comm).
      rewrite -> e.
      exact H1. inversion Hwfc. apply wfc_ind_wfc. eapply (H10 fresh). 
      unfold evar_is_fresh_in in H6. assumption.
      destruct Hwf. assumption. assumption. assumption. assumption.
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
      erewrite -> (@interpretation_fresh_svar_open m _ MuX MuZ); try assumption.
      erewrite -> (@interpretation_fresh_svar_open m _ MuY MuZ); try assumption.
      erewrite -> svar_open_free_svar_subst_comm; try assumption.
      rewrite update_svar_val_comm; try assumption. 
      {
        simpl in H1. apply not_elem_of_singleton_1 in H1. assumption.
      }
      epose (IHsz (svar_open 0 MuZ phi) psi X 
      (update_svar_val MuZ x svar_val) evar_val _ _ _).
      rewrite e. 
      erewrite (@pattern_interpretation_free_svar_independent m _ _ MuZ x psi).
      reflexivity.
      {
        inversion Hwfc. pose (H5 MuZ H). apply wfc_ind_wfc in w. assumption.
      }
      destruct Hwf. assumption.
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
      
      erewrite -> (@interpretation_fresh_svar_open m _ MuX MuZ); try assumption.
      erewrite -> (@interpretation_fresh_svar_open m _ MuY MuZ); try assumption.
      erewrite -> svar_open_free_svar_subst_comm; try assumption.
      rewrite update_svar_val_comm; try assumption. 
      {
        simpl in H2. apply not_elem_of_singleton_1 in H2. assumption.
      }
      epose (IHsz (svar_open 0 MuZ phi) psi X 
      (update_svar_val MuZ x svar_val) evar_val _ _ ).
      rewrite e. 
      {
        inversion Hwfc. pose (H6 MuZ H1). apply wfc_ind_wfc in w. assumption.
      }
      erewrite (@pattern_interpretation_free_svar_independent m _ _ MuZ x psi); try assumption.
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
    assumption.
    {
      subst sz. erewrite <- svar_open_size. reflexivity.
    }
    assumption.
    {
      inversion Hwfc. apply wfc_ind_wfc. eapply (H5 MuZ _).
    }
    subst sz. erewrite <- svar_open_size. lia.
    assumption. Unshelve.
    assumption.
Qed.

Lemma free_svar_subst_update_exchange {m : Model}: ∀ phi psi X svar_val evar_val,
  well_formed psi → well_formed_closed phi → 
  pattern_interpretation evar_val svar_val (free_svar_subst phi psi X) =
  pattern_interpretation evar_val (@update_svar_val m X 
                                  (pattern_interpretation evar_val svar_val psi) svar_val) 
                                  phi.
Proof. 
  intros. apply Private_free_svar_subst_update_exchange with (sz := size phi). 
  lia. assumption. assumption.
Qed.

Definition rel_of M ρₑ ρₛ ϕ: Domain M -> Ensemble (Domain M) :=
  λ m₁,
  (app_ext (@pattern_interpretation M ρₑ ρₛ ϕ) (Ensembles.Singleton (Domain M) m₁)).


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

(*Module Hints.*)
#[export]
        Hint Resolve M_predicate_impl : core.
#[export]
        Hint Resolve M_predicate_bott : core.
 #[export]
       Hint Resolve M_predicate_exists : core.
 #[export]
        Hint Extern 4 (M_predicate _ (evar_open _ _ _)) => rewrite !simpl_evar_open : core.
 #[export]
        Hint Extern 4 (T_predicate _ (evar_open _ _ _)) => rewrite !simpl_evar_open : core.
 #[export]
        Hint Extern 4 (M_predicate _ (svar_open _ _ _)) => rewrite !simpl_svar_open : core.
 #[export]
       Hint Extern 4 (T_predicate _ (svar_open _ _ _)) => rewrite !simpl_svar_open : core.
 #[export]
       Hint Resolve T_predicate_impl_M_predicate : core.
 #[export]
       Hint Resolve T_predicate_impl : core.
 #[export]
       Hint Resolve T_predicate_bot : core.
(*End Hints.*)
