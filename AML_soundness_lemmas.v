Require Import Arith.
Require Import ZArith.
Require Import List.
Require Import Coq.micromega.Lia.
Require Export String.
Require Export Coq.Lists.ListSet.
Require Export Coq.Program.Wf.
From Coq Require Import Bool.Bool.
From Coq Require Import Logic.FunctionalExtensionality.

Require Import extralibrary.
(*Require Import names.*)
Require Import ML.Signature.
Require Export locally_nameless.
Require Import Lattice.

Require Export Ensembles_Ext.


Import MLNotations.

Section soundness_lemmas.

  Context {sig : Signature}.


(* evar_open of fresh name does not change *)
Lemma evar_open_fresh (phi : Pattern) :
  forall n, well_formed phi -> evar_open n (evar_fresh (variables sig) (free_evars phi)) phi = phi.
Proof. Admitted. (*
  intros. generalize dependent n. induction phi; intros; simpl; try eauto.
  * inversion H. inversion H1.
  *  rewrite IHphi1. rewrite IHphi2. reflexivity.
    split; inversion H. inversion H0; assumption. inversion H1; assumption.
    split; inversion H. inversion H0; assumption. inversion H1; assumption.
  * rewrite IHphi1. rewrite IHphi2. reflexivity.
    split; inversion H. inversion H0; assumption. inversion H1; assumption.
    split; inversion H. inversion H0; assumption. inversion H1; assumption.
  * rewrite IHphi. reflexivity.
    split; inversion H. assumption.
    unfold well_formed_closed in *. simpl in H1. admit.
Admitted.*)

  
  (* Bp - Blacklist of Positive Occurrence - these variables can occur only negatively.
     Bn - Blacklist of Negative Occurrence - these variables can occur only positively *)
Definition respects_blacklist (phi : Pattern) (Bp Bn : Ensemble svar_name) : Prop :=
  forall (var : svar_name),
    (Bp var -> negative_occurrence_named var phi) /\ (Bn var -> @positive_occurrence_named sig var phi).

Lemma respects_blacklist_app : forall (phi1 phi2 : Pattern) (Bp Bn : Ensemble svar_name),
    respects_blacklist phi1 Bp Bn -> respects_blacklist phi2 Bp Bn ->
    respects_blacklist (phi1 $ phi2) Bp Bn.
Proof.
  intros. unfold respects_blacklist in *.
  intros. split; intros; constructor; firstorder; firstorder.
Qed.

Lemma respects_blacklist_app_1 : forall (phi1 phi2 : Pattern) (Bp Bn : Ensemble svar_name),
    respects_blacklist (phi1 $ phi2) Bp Bn -> respects_blacklist phi1 Bp Bn.
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
Lemma respects_blacklist_app_2 : forall (phi1 phi2 : Pattern) (Bp Bn : Ensemble svar_name),
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

Lemma respects_blacklist_impl : forall (phi1 phi2 : Pattern) (Bp Bn : Ensemble svar_name),
    respects_blacklist phi1 Bn Bp -> respects_blacklist phi2 Bp Bn ->
    respects_blacklist (phi1 --> phi2) Bp Bn.
Proof.
  unfold respects_blacklist.
  intros.
  specialize (H var).
  specialize (H0 var).
  destruct H as [H1neg H1pos].
  destruct H0 as [H2neg H2pos].
  split; intros; constructor; firstorder.
Qed.

Lemma respects_blacklist_impl_1 : forall (phi1 phi2 : Pattern) (Bp Bn : Ensemble svar_name),
    respects_blacklist (phi1 --> phi2) Bp Bn -> respects_blacklist phi1 Bn Bp.
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

Lemma respects_blacklist_impl_2 : forall (phi1 phi2 : Pattern) (Bp Bn : Ensemble svar_name),
    respects_blacklist (phi1 --> phi2) Bp Bn -> respects_blacklist phi2 Bp Bn.
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

Lemma respects_blacklist_ex : forall (phi : Pattern) (Bp Bn : Ensemble svar_name),
    respects_blacklist (patt_exists phi) Bp Bn -> respects_blacklist phi Bp Bn.
Proof.
  intros. unfold respects_blacklist in *.
  intros. specialize (H var). destruct H as [Hneg Hpos].
  split; intros.
  * specialize (Hneg H). inversion Hneg. assumption.
  * specialize (Hpos H). inversion Hpos. assumption.
Qed.

Lemma respects_blacklist_ex' : forall (phi : Pattern) (Bp Bn : Ensemble svar_name),
    respects_blacklist phi Bp Bn -> respects_blacklist (patt_exists phi) Bp Bn.
Proof.
  unfold respects_blacklist. intros.
  specialize (H var).
  destruct H as [Hneg Hpos].
  split; intros; constructor; firstorder.
Qed.

Lemma respects_blacklist_mu : forall (phi : Pattern) (Bp Bn : Ensemble svar_name),
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

Lemma respects_blacklist_mu' : forall (phi : Pattern) (Bp Bn : Ensemble svar_name),
    respects_blacklist phi Bp Bn -> respects_blacklist (patt_mu phi) Bp Bn.
Proof.
  unfold respects_blacklist. intros.
  specialize (H var).
  destruct H as [Hneg Hpos].
  split; intros; constructor; firstorder.
Qed.

Lemma respects_blacklist_union : forall (phi : Pattern) (Bp1 Bn1 Bp2 Bn2 : Ensemble svar_name),
    respects_blacklist phi Bp1 Bn1 ->
    respects_blacklist phi Bp2 Bn2 ->
    respects_blacklist phi (Union svar_name Bp1 Bp2) (Union svar_name Bn1 Bn2).
Proof.
  unfold respects_blacklist.
  induction phi; intros; split; intros;
    destruct H1; unfold In in *;
      try specialize (H x0); try specialize (H x);
      try specialize (H0 x0); try specialize (H0 x); firstorder; try constructor.
Qed.

Lemma well_formed_positive_mu_app_1 : forall (phi1 : Pattern) (phi2 : Pattern),
    well_formed_positive (mu, (phi1 $ phi2)) -> @well_formed_positive sig (mu, phi1)
.
Proof.
  auto.
Admitted.

Lemma not_free_implies_positive_negative_occurrence :
  forall (phi : Pattern) (X : svar_name),
    ~ set_In X (free_svars phi) ->
    @positive_occurrence_named sig X phi /\ negative_occurrence_named X phi.
Proof.
  unfold not.
  induction phi; simpl; intros; split; try constructor; try firstorder.
  * apply IHphi1. intros.
    assert (H': set_In X (set_union eq_svar_name (free_svars phi1) (free_svars phi2))).
    { apply set_union_intro1. assumption. }
    auto.
  * apply IHphi2. intros.
    assert (H': set_In X (set_union eq_svar_name (free_svars phi1) (free_svars phi2))).
    { apply set_union_intro2. assumption. }
    auto.
  * apply IHphi1.
    intros. auto using set_union_intro1.
  * apply IHphi2. intros. auto using set_union_intro2.
  * apply IHphi1. intros. auto using set_union_intro1.
  * apply IHphi2. intros. auto using set_union_intro2.
  * apply IHphi1. intros. auto using set_union_intro1.
  * apply IHphi2. intros. auto using set_union_intro2.
Qed.

(* taken from https://softwarefoundations.cis.upenn.edu/vfa-current/Perm.html *)
Lemma eqb_reflect : forall x y, reflect (x = y) (x =? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.eqb_eq.
Qed.

Lemma positive_negative_occurrence_db_named :
  forall (phi : Pattern) (dbi : db_index) (X : svar_name),
    (positive_occurrence_db dbi phi ->
    positive_occurrence_named X phi ->
    positive_occurrence_named X (@svar_open sig dbi X phi))
    /\ (negative_occurrence_db dbi phi ->
        negative_occurrence_named X phi ->
       negative_occurrence_named X (@svar_open sig dbi X phi)).
Proof.
  induction phi; intros; split; simpl; try firstorder.
  + destruct ( n =? dbi). constructor. constructor.
  + destruct (eqb_reflect n dbi).
    { inversion H. subst. lia. }
    { constructor. }
  + inversion H; subst. inversion H0; subst.
    constructor. firstorder. firstorder.
  + inversion H. inversion H0. subst.
    constructor. firstorder. firstorder.
  + inversion H. inversion H0. subst.
    constructor. firstorder. firstorder.
  + inversion H. inversion H0. subst.
    constructor. firstorder. firstorder.
  + inversion H. inversion H0. subst.
    constructor. firstorder.
  + inversion H. inversion H0. subst.
    constructor. firstorder.
  + inversion H. inversion H0. subst.
    constructor. firstorder.
  + inversion H. inversion H0. subst.
    constructor. firstorder.
Qed.

Lemma positive_occurrence_respects_blacklist_svar_open :
  forall (phi : Pattern) (dbi : db_index) (X : svar_name),
    positive_occurrence_db dbi phi ->
    ~ set_In X (free_svars phi) ->
    respects_blacklist (svar_open dbi X phi) (Empty_set svar_name) (Singleton svar_name X).
Proof.
  intros phi dbi X Hpodb Hni.
  pose proof (Hpno := not_free_implies_positive_negative_occurrence phi X Hni).
  unfold respects_blacklist. intros.
  split; intros.
  * firstorder using positive_negative_occurrence_db_named.
  * inversion H. subst.
    firstorder using positive_negative_occurrence_db_named.
Qed.
  
Lemma mu_wellformed_respects_blacklist : forall (phi : Pattern),
    well_formed_positive (patt_mu phi) ->
    let X := svar_fresh (variables sig) (free_svars phi) in
    respects_blacklist (svar_open 0 X phi) (Empty_set svar_name) (Singleton svar_name X).
Proof.
  intros. destruct H as [Hpo Hwfp].
  pose proof (Hfr := svar_fresh_is_fresh (variables sig) (free_svars phi)).
  auto using positive_occurrence_respects_blacklist_svar_open.
Qed.


(*
Lemma respects_blacklist_ex' : forall (phi : Pattern) (Bp Bn : Ensemble svar_name),
    respects_blacklist ()
respects_blacklist (evar_open 0 (evar_fresh (variables sig) (free_evars phi)) phi) Bp B
*)

Lemma evar_open_respects_blacklist :
  forall (phi : Pattern) (Bp Bn : Ensemble svar_name) (x : evar_name) (n : nat),
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
    specialize (IHphi Bp Bn x (n+1) H).
    auto using respects_blacklist_mu'.
Qed.

(*
Lemma respects_blacklist_implies_monotonic :
  forall (phi : Pattern) (Bp Bn : Ensemble svar_name),
    respects_blacklist phi Bp Bn ->
    forall (M : Model)
           (evar_val : evar_name -> Domain M)
           (svar_val : svar_name -> Power (Domain M))
           (X : svar_name)
           (S1 S2 : Ensemble (Domain M)),
      Included (Domain M) S1 S2 ->
      (Bp X ->
       Included (Domain M)
                (@ext_valuation sig M evar_val (update_svar_val X S2 svar_val) phi)
                (@ext_valuation sig M evar_val (update_svar_val X S1 svar_val) phi)
      ) /\ (Bn X ->
            Included (Domain M)
                     (@ext_valuation sig M evar_val (update_svar_val X S1 svar_val) phi)
                     (@ext_valuation sig M evar_val (update_svar_val X S2 svar_val) phi)
         )
.
Proof.
  induction phi.
  - (* EVar *)
    intros.
    assert (HEq : ext_valuation evar_val (update_svar_val X S2 svar_val) (patt_free_evar x)
                  = ext_valuation evar_val (update_svar_val X S1 svar_val) (patt_free_evar x)).
    { rewrite -> ext_valuation_free_evar_simpl. rewrite -> ext_valuation_free_evar_simpl. reflexivity. }
    rewrite -> HEq.
    split; intros; unfold Included; intros; assumption.
  - (* SVar *)
    intros. split; intros; repeat rewrite -> ext_valuation_free_svar_simpl.
    *
      assert (X <> x).
      { unfold respects_blacklist in H.
        specialize H with (var := X). destruct H.
        apply H in H1. inversion H1.
      }
      unfold update_svar_val.
      destruct (eq_svar_name X x). contradiction.
      unfold Included. auto.
    * unfold update_svar_val.
      destruct (eq_svar_name X x).
      assumption.
      unfold Included. intros. assumption.
  - (* bound EVar *)
    intros. repeat rewrite -> ext_valuation_bound_evar_simpl.
    unfold Included. unfold In. split; intros; assumption.
  - (* bound SVar *)
    intros. repeat rewrite -> ext_valuation_bound_svar_simpl.
    unfold Included. unfold In. split; intros; assumption.
  - (* Sym *)
    intros. repeat rewrite -> ext_valuation_sym_simpl.
    unfold Included. unfold In. split; intros; assumption.
  - (* App *)
    intros. repeat rewrite -> ext_valuation_app_simpl.
    (*unfold respects_blacklist in H.*)
    assert (respects_blacklist phi1 Bp Bn). admit.
    assert (respects_blacklist phi2 Bp Bn). admit.
    specialize (IHphi1 Bp Bn H1 M evar_val svar_val X S1 S2 H0).
    specialize (IHphi2 Bp Bn H2 M evar_val svar_val X S1 S2 H0).
    clear H1 H2.
    destruct IHphi1 as [IHphi1_1 IHphi1_2].
    destruct IHphi2 as [IHphi2_1 IHphi2_2].
    unfold Included in *.
    unfold In in *.
    unfold pointwise_ext.
    split; intros HBX x.
    * specialize (IHphi1_1 HBX). specialize (IHphi2_1 HBX).
      clear IHphi1_2. clear IHphi2_2.
      intros. destruct H1 as [Xl [Xr [Hxl [Hxr Happ]]]].
      exists Xl. exists Xr.
      split. apply IHphi1_1. assumption.
      split. apply IHphi2_1. assumption.
      assumption.
    * (*specialize (IHphi1_2 HBX). specialize (IHphi2_2 HBX).
      clear IHphi1_1. clear IHphi2_1.*)
      intros [Xl [Xr [Hxl [Hxr Happ]]]].
      exists Xl. exists Xr.
      split. apply IHphi1_2. assumption. assumption.
      split. apply IHphi2_2. assumption. assumption.
      assumption.
  - (* Bot *)
    intros.
    rewrite -> ext_valuation_bott_simpl.
    split; intros; unfold Included; unfold In in *; intros; inversion H2.
  - (* Impl *)
    intros.
    assert (Hrb1 : respects_blacklist phi1 Bn Bp).
    { unfold respects_blacklist in H. unfold respects_blacklist. intros.
      specialize (H var).
      destruct H as [H1 H2].
      split; intros.
      * specialize (H2 H).
        inversion H2. assumption.
      * specialize (H1 H).
        inversion H1. assumption.
    }
    assert (Hrb2 : respects_blacklist phi2 Bp Bn).
    { unfold respects_blacklist in *.
      intros.
      specialize (H var).
      destruct H as [H1 H2].
      split; intros.
      * specialize (H1 H).
        inversion H1. assumption.
      * specialize (H2 H).
        inversion H2. assumption.
    }
    clear H.
    specialize (IHphi1 Bn Bp Hrb1 M evar_val svar_val X S1 S2 H0).
    specialize (IHphi2 Bp Bn Hrb2 M evar_val svar_val X S1 S2 H0).
    clear Hrb1 Hrb2.
    repeat rewrite -> ext_valuation_imp_simpl.
    destruct IHphi1 as [IHphi1_1 IHphi1_2].
    destruct IHphi2 as [IHphi2_1 IHphi2_2].
    unfold Included in *. unfold In in *.
    split; intros.
    * specialize (IHphi1_2 H).
      specialize (IHphi2_1 H).
      clear IHphi1_1 IHphi2_2.
      destruct H1.
      { left. unfold In in *. unfold Complement in *. unfold not in *. intros.
        apply H1. apply IHphi1_2. assumption.
      }
      { right. apply IHphi2_1. unfold In in H1. assumption. }
    * specialize (IHphi1_1 H).
      specialize (IHphi2_2 H).
      clear IHphi1_2 IHphi2_1.
      destruct H1.
      { left. unfold In in *. unfold Complement in *. unfold not in *. intros.
        apply H1. apply IHphi1_1. assumption.
      }
      { right. apply IHphi2_2. assumption. }
  - (* Ex *)
    intros.
    repeat rewrite -> ext_valuation_ex_simpl.
    assert (Hrb: respects_blacklist phi Bp Bn).
    {unfold respects_blacklist in *.
     intros. specialize (H var). destruct H as [H1 H2].
     split; intros.
     * specialize (H1 H). inversion H1. assumption.
     * specialize (H2 H). inversion H2. assumption.
    }
    specialize (IHphi Bp Bn Hrb M).
    split; intros.
    *
      unfold Included in *. unfold In in *.
      intros. destruct H2. destruct H2.
      constructor.
      exists x0.
      specialize (IHphi (update_evar_val (evar_fresh (variables sig) (free_evars phi)) x0 evar_val)).
      specialize (IHphi svar_val X S1 S2 H0).
      destruct IHphi as [IHphi1 IHphi2].
      specialize (IHphi1 H1 x).
      Search Pattern.
      Print evar_open.
      (* Now I would need some lemma stating that ext_valuation evaluates phi the same
         as its `evar_open`-ed equivalent *)
    (*apply IHphi1.*)
      admit.
   *  admit.
    
Admitted.
*)

Lemma well_formed_app_1 : forall (phi1 phi2 : Pattern),
    well_formed (phi1 $ phi2) -> @well_formed sig phi1.
Proof.
  unfold well_formed. intros.
  destruct H as [Hpos Hclos].
  inversion Hpos. inversion Hclos.
  split. assumption. unfold well_formed_closed. assumption.
Qed.

Lemma well_formed_app_2 : forall (phi1 phi2 : Pattern),
    well_formed (phi1 $ phi2) -> @well_formed sig phi2.
Proof.
  unfold well_formed. intros.
  destruct H as [Hpos Hclos].
  inversion Hpos. inversion Hclos.
  split. assumption. unfold well_formed_closed. assumption.
Qed.

Lemma free_svars_evar_open : forall (ϕ : Pattern) (dbi :db_index) (x : evar_name),
    free_svars (evar_open dbi x ϕ) = @free_svars sig ϕ.
Proof.
  induction ϕ; intros; simpl; try reflexivity.
  * destruct (n =? dbi); reflexivity.
  * rewrite -> IHϕ1. rewrite -> IHϕ2. reflexivity.
  * rewrite -> IHϕ1. rewrite -> IHϕ2. reflexivity.
  * rewrite -> IHϕ. reflexivity.
  * rewrite -> IHϕ. reflexivity.
Qed.

Lemma svar_open_evar_open_comm
  : forall (phi : Pattern) (dbi1 : db_index)(x : evar_name)(dbi2 : db_index)(X : svar_name),
    evar_open dbi1 x (svar_open dbi2 X phi) = svar_open dbi2 X (@evar_open sig dbi1 x phi).
Proof.
  induction phi; intros; simpl; try reflexivity.
  * destruct (n =? dbi1); reflexivity.
  * destruct (n =? dbi2); reflexivity.
  * rewrite -> IHphi1. rewrite -> IHphi2. reflexivity.
  * rewrite -> IHphi1. rewrite -> IHphi2. reflexivity.
  * rewrite -> IHphi. reflexivity.
  * rewrite -> IHphi. reflexivity.
Qed.

Lemma positive_negative_occurrence_evar_open : forall (ϕ : Pattern) (X : svar_name) (dbi : db_index) (x : evar_name),
    (positive_occurrence_named X (evar_open dbi x ϕ) <-> @positive_occurrence_named sig X ϕ)
    /\ (negative_occurrence_named X (evar_open dbi x ϕ) <-> @negative_occurrence_named sig X ϕ).
Proof.
  induction ϕ; intros; simpl; split; try reflexivity.
  + destruct (n =? dbi).
    split; intros H; inversion H; constructor. reflexivity.
  + destruct (n =? dbi).
    split; intros H; inversion H; constructor. reflexivity.
  + split; intros H; inversion H; subst; constructor; firstorder.
  + split; intros H; inversion H; subst; constructor; firstorder.
  + split; intros H; inversion H; subst; constructor; firstorder.
  + split; intros H; inversion H; subst; constructor; firstorder.
  + split; intros H; inversion H; subst; constructor; firstorder.
  + split; intros H; inversion H; subst; constructor; firstorder.
  + split; intros H; inversion H; subst; constructor; firstorder.
  + split; intros H; inversion H; subst; constructor; firstorder.
Qed.

Lemma positive_occurrence_evar_open : forall (ϕ : Pattern) (X : svar_name) (dbi : db_index) (x : evar_name),
    positive_occurrence_named X (evar_open dbi x ϕ) <-> @positive_occurrence_named sig X ϕ.
Proof.
  intros.
  pose proof (P := positive_negative_occurrence_evar_open ϕ X dbi x).
  destruct P as [P _]. exact P.
Qed.

Lemma negative_occurrence_evar_open : forall (ϕ : Pattern) (X : svar_name) (dbi : db_index) (x : evar_name),
    negative_occurrence_named X (evar_open dbi x ϕ) <-> @negative_occurrence_named sig X ϕ.
Proof.
  intros.
  pose proof (P := positive_negative_occurrence_evar_open ϕ X dbi x).
  destruct P as [_ P]. exact P.
Qed.

Lemma positive_negative_occurrence_db_evar_open : forall (phi : @Pattern sig) (db1 db2 : db_index) (x : evar_name),
    le db1 db2 ->
    (positive_occurrence_db db1 phi -> positive_occurrence_db db1 (evar_open db2 x phi))
    /\ (negative_occurrence_db db1 phi -> negative_occurrence_db db1 (evar_open db2 x phi)).
Proof.
  induction phi; intros; simpl; split; intros; try constructor; try inversion H0; subst; try firstorder.
  * destruct (n =? db2); intros. constructor. assumption.
  * destruct (n =? db2); intros. constructor. assumption.
  * apply IHphi. lia. assumption.
  * apply IHphi. lia. assumption.
  * apply IHphi. lia. assumption.
  * apply IHphi. lia. assumption.
Qed.

Lemma positive_occurrence_db_evar_open : forall (phi : @Pattern sig) (db1 db2 : db_index) (x : evar_name),
    le db1 db2 ->
    positive_occurrence_db db1 phi -> positive_occurrence_db db1 (evar_open db2 x phi).
Proof.
  intros.
  pose proof (H' := positive_negative_occurrence_db_evar_open phi db1 db2 x H).
  firstorder.
Qed.

Lemma negative_occurrence_db_evar_open : forall (phi : @Pattern sig) (db1 db2 : db_index) (x : evar_name),
    le db1 db2 ->
    negative_occurrence_db db1 phi -> negative_occurrence_db db1 (evar_open db2 x phi).
Proof.
  intros.
  pose proof (H' := positive_negative_occurrence_db_evar_open phi db1 db2 x H).
  firstorder.
Qed.

Lemma evar_open_wfp : forall (sz : nat) (phi : Pattern),
    le (size phi) sz ->
    forall(n : db_index) (x : evar_name),
    well_formed_positive phi -> @well_formed_positive sig (evar_open n x phi).
Proof.
  induction sz; destruct phi; intros Hsz dbi e Hwfp; simpl in *; auto; try inversion Hsz; subst.
  + destruct (n =? dbi). constructor. assumption.
  + destruct (n =? dbi). constructor. assumption.
  + destruct Hwfp as [Hwfp1 Hwfp2].
    split; apply IHsz. lia. assumption. lia. assumption.
  + destruct Hwfp as [Hwfp1 Hwfp2].
    split; apply IHsz. lia. assumption. lia. assumption.
  + destruct Hwfp as [Hwfp1 Hwfp2].
    split; apply IHsz. lia. assumption. lia. assumption.
  + destruct Hwfp as [Hwfp1 Hwfp2].
    split; apply IHsz. lia. assumption. lia. assumption.
  + apply IHsz. lia. assumption.
  + apply IHsz. lia. assumption.
  + split.
    * apply positive_occurrence_db_evar_open. lia. firstorder.
    * apply IHsz. lia. firstorder.
  + split.
    * apply positive_occurrence_db_evar_open. lia. firstorder.
    * apply IHsz. lia. firstorder.
Qed.

Lemma positive_occurrence_db_svar_open : forall (phi : Pattern) (dbi : db_index) (X : svar_name),
    (positive_occurrence_db dbi phi ->
    @positive_occurrence_db sig dbi (svar_open dbi X phi))
   /\ (negative_occurrence_db dbi phi -> @negative_occurrence_db sig dbi (svar_open dbi X phi)).
Proof.
  induction phi; intros; simpl; split; intros; try constructor; try inversion H; try firstorder.
  + destruct (n =? dbi); constructor.
  + destruct (n =? dbi).
    * constructor.
    * subst. constructor. assumption.
Qed.

(*
Lemma wfca_impl_pod0 :
  forall (phi : Pattern) (dbi : db_index) (X : svar_name),
    well_formed_closed_aux phi dbi ->
    ( @positive_occurrence_db sig 0 (svar_open dbi X phi)
      /\ @negative_occurrence_db sig 0 (svar_open dbi X phi)).
Proof.
  induction phi; intros; simpl; split;  try constructor; try inversion H; try firstorder.
  * destruct (n =? S n); constructor.
  * destruct (n =? S m); constructor.
  * destruct (n =? S n); constructor. subst. simpl in H. lia.
  * destruct (n =? S n); constructor.
  * 
  * destruct (n =? dbi); constructor.
  *)

Lemma well_formed_closed_aux_svar_open :
  forall (phi : Pattern) (dbi : db_index) (X : svar_name),
    well_formed_closed_aux phi dbi ->
    @well_formed_closed_aux sig (svar_open dbi X phi) dbi.
Proof.
  induction phi; intros; simpl in *; auto.
  * destruct (eqb_reflect n dbi). lia. auto.
  * firstorder.
  * firstorder.
Qed.


Lemma positive_negative_occurrence_db_svar_open_le : forall (phi : Pattern) (dbi1 dbi2 : db_index) (X : svar_name),
    dbi1 < dbi2 ->
    (
    positive_occurrence_db dbi1 phi ->
    @positive_occurrence_db sig dbi1 (svar_open dbi2 X phi)
    )
    /\ (negative_occurrence_db dbi1 phi -> @negative_occurrence_db sig dbi1 (svar_open dbi2 X phi)).
Proof.
  induction phi; intros dbi1 dbi2 X Hneq; split; intros H; inversion H; subst; intros; simpl in *; auto.
  + destruct (n =? dbi2); constructor.
  + destruct (n =? dbi2); constructor. auto.
  + constructor; firstorder.
  + constructor; firstorder.
  + constructor; firstorder.
  + constructor; firstorder.
  + constructor. apply IHphi. lia. assumption.
  + constructor. apply IHphi. lia. assumption.
  + constructor. apply IHphi. lia. assumption.
  + constructor. apply IHphi. lia. assumption.
Qed.

Lemma wfp_svar_open : forall (phi : Pattern) (dbi : db_index) (X : svar_name),
    well_formed_positive phi ->
    @well_formed_positive sig (svar_open dbi X phi).
Proof.
  induction phi; intros.
  + constructor.
  + constructor.
  + constructor.
  + simpl. destruct (n =? dbi); constructor.
  + constructor.
  + inversion H. firstorder.
  + constructor.
  + inversion H. firstorder.
  + simpl in H. simpl. auto.
  + simpl in H. simpl. Search well_formed_closed_aux.
    split.
    * apply positive_negative_occurrence_db_svar_open_le.
      lia. firstorder.
    * firstorder.
Qed.


Lemma positive_negative_occurrence_named_svar_open :
  forall (phi : Pattern) (X Y : svar_name) (dbi : db_index),
    X <> Y ->
    (
    negative_occurrence_named X phi ->
    negative_occurrence_named X (@svar_open sig dbi Y phi)
    ) /\ (
    positive_occurrence_named X phi ->
    positive_occurrence_named X (@svar_open sig dbi Y phi)
    ).
Proof.
  induction phi; intros X Y dbi XneY; split; intros Hneg; inversion Hneg; subst;
    simpl in *; try constructor; try firstorder.
  - destruct (n =? dbi); constructor. 
    unfold not. intros. assert (X = Y). symmetry. assumption.
    unfold not in XneY. destruct (XneY H0).
  - destruct (n =? dbi); constructor.
Qed.

Section with_model.

  Context {M : @Model sig}.
  Let A := Ensemble (@Domain sig M).
  Let OS := EnsembleOrderedSet (@Domain sig M).
  Let L := PowersetLattice (@Domain sig M).


  Lemma update_svar_val_comm :
    forall (X1 X2 : @svar_name sig) (S1 S2 : Power (Domain M)) (svar_val : @SVarVal sig M),
      X1 <> X2 ->
      update_svar_val X1 S1 (update_svar_val X2 S2 svar_val)
      = update_svar_val X2 S2 (update_svar_val X1 S1 svar_val).
  Proof.
    intros.
    unfold update_svar_val.
    apply functional_extensionality.
    intros.
    destruct (eq_svar_name X1 x),(eq_svar_name X2 x); subst.
    * unfold not in H. assert (x = x). reflexivity. apply H in H0. destruct H0.
    * reflexivity.
    * reflexivity.
    * reflexivity.
  Qed.

  Lemma update_svar_shadow : forall (X : @svar_name sig)
                                    (S1 S2 : Power (Domain M))
                                    (svar_val : @SVarVal sig M),
      update_svar_val X S1 (update_svar_val X S2 svar_val) = update_svar_val X S1 svar_val.
  Proof.
    intros. unfold update_svar_val. apply functional_extensionality.
    intros. destruct (eq_svar_name X x); reflexivity.
  Qed.
  

  Lemma respects_blacklist_implies_monotonic' :
    forall (n : nat) (phi : Pattern),
      le (size phi) n -> well_formed_positive phi ->
      forall (Bp Bn : Ensemble svar_name),
        respects_blacklist phi Bp Bn ->
        forall (evar_val : evar_name -> Domain M)
               (svar_val : svar_name -> Power (Domain M))
               (X : svar_name),
          (Bp X ->
           @AntiMonotonicFunction A OS (fun S : Ensemble (Domain M) =>
                                  (@ext_valuation sig M evar_val (update_svar_val X S svar_val) phi)
                              )
          ) /\
          (Bn X ->
                @MonotonicFunction A OS (fun S : Ensemble (Domain M) =>
                                           (@ext_valuation sig M evar_val (update_svar_val X S svar_val) phi))
               )
  .
  Proof.
    induction n.
    - (* n = 0 *)
      intros. destruct phi; simpl in H; try inversion H.
      * (* EVar free *)
        admit.
      * (* SVar free *)
        admit.
      * (* EVar bound *)
        admit.
      * (* SVar bound *)
        admit.
      * (* Patt *)
        admit.
      * (* Bot *)
        admit.
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
        admit.
      * (* Bot *)
        apply IHn. simpl. lia. assumption. assumption.
      * (* Impl *)
        remember (respects_blacklist_impl_1 phi1 phi2 Bp Bn Hrb) as Hrb1. clear HeqHrb1.
        remember (respects_blacklist_impl_2 phi1 phi2 Bp Bn Hrb) as Hrb2. clear HeqHrb2.
        admit.
      * (* Ex *)
        simpl. remember (respects_blacklist_ex phi Bp Bn Hrb) as Hrb'. clear HeqHrb'.
        specialize (IHn (evar_open 0 (evar_fresh (variables sig) (free_evars phi)) phi)).
        rewrite <- evar_open_size in IHn.
        assert (Hsz': size phi <= n). simpl in *. lia.
        remember (evar_fresh (variables sig) (free_evars phi)) as fresh.
        pose proof (Hwfp' := evar_open_wfp n phi Hsz' 0 fresh Hwfp).
        specialize (IHn Hsz' Hwfp' Bp Bn).
        pose proof (Hrb'' := evar_open_respects_blacklist phi Bp Bn fresh 0 Hrb').
        unfold MonotonicFunction in *. unfold AntiMonotonicFunction in *.
        unfold leq. simpl.
        unfold Included in *. unfold In in *.
        (*rewrite -> ext_valuation_ex_simpl in *.*)
        split; intros HBp S1 S2 Hincl; rewrite -> ext_valuation_ex_simpl; simpl;
          intros m [x [c Hc]]; rewrite -> ext_valuation_ex_simpl; simpl; constructor; exists c;
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
        auto.
      * (* Mu *)
        remember Hwfp as Hwfpmu. clear HeqHwfpmu.
        simpl in Hsz.
        assert (Hsz': size phi <= n). { lia. }
        split.
        {
          unfold AntiMonotonicFunction. intros.
          repeat rewrite -> ext_valuation_mu_simpl.
          Arguments LeastFixpointOf : simpl never.
          Arguments leq : simpl never.
          simpl.

          remember (svar_fresh (variables sig) (free_svars phi)) as X'.
          remember (svar_open 0 X' phi) as phi'.
          pose proof (Hszeq := svar_open_size sig 0 X' phi).
          assert (Hsz'': size phi' <= n).
          { rewrite -> Heqphi'. rewrite <- Hszeq. assumption. }
          specialize (IHn phi' Hsz'').
          simpl in Hwfp. destruct Hwfp as [Hpo Hwfp].
          
          assert (Hrb': respects_blacklist phi' (Empty_set svar_name) (Singleton svar_name X')).
          { subst. apply mu_wellformed_respects_blacklist. assumption. }

          assert (Hwfp' : well_formed_positive phi').
          { subst. apply wfp_svar_open. assumption. }

          remember IHn as IHn'. clear HeqIHn'.
          specialize (IHn' Hwfp' (Empty_set svar_name) (Singleton svar_name X') Hrb' evar_val).
          remember IHn' as Hy. clear HeqHy.
          rename IHn' into Hx.
          specialize (Hx (update_svar_val V x svar_val) X').
          specialize (Hy (update_svar_val V y svar_val) X').

          apply lfp_preserves_order.
          - apply Hy. constructor.
          - apply Hx. constructor.
          - clear Hx. clear Hy.
            intros.
            destruct (svar_eq (variables sig) X' V).
            + (* X' = V *)
              rewrite <- e.
              repeat rewrite -> update_svar_shadow.
              unfold leq. simpl. unfold Included. unfold In. auto.
            + (* X' <> V*)
              pose proof (Uhsvcx := update_svar_val_comm X' V x0 x svar_val n0).
              rewrite -> Uhsvcx.
              pose proof (Uhsvcy := update_svar_val_comm X' V x0 y svar_val n0).
              rewrite -> Uhsvcy.

              assert (HrbV: respects_blacklist phi' (Singleton svar_name V) (Empty_set svar_name)).
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
                    unfold not. intros. assert (svar_fresh (variables sig) (free_svars phi) = V).
                    {
                      symmetry. assumption.
                    }
                    unfold not in n0. destruct (n0 H3).
                  * inversion Hrbn. assumption.
                - intros. destruct H1.
              }

              specialize (IHn Hwfp' (Singleton svar_name V) (Empty_set svar_name) HrbV).
              specialize (IHn evar_val (update_svar_val X' x0 svar_val) V).
              destruct IHn as [IHam IHmo].
              apply IHam. constructor. assumption.
        }
        (* This is the same as the previous, with minor changes *)
        admit.
  Admitted.



(*
Lemma is_monotonic :
  forall (sm : Sigma_model)
         (evar_val : name -> M sm)
         (svar_val : db_index -> Power (M sm)) (phi : Sigma_pattern)
         (x : db_index),
    positive x phi ->
    well_formed phi ->
    forall (l r : Power (M sm)),
      Included (M sm) l r ->
      Included (M sm)
        (ext_valuation evar_val (change_val beq_nat 0 l db_val) phi)
        (ext_valuation freevar_val (change_val beq_nat 0 r db_val) phi).
Proof.
Admitted.
*)
(* if ext_valuation (phi1 --> phi2) = Full_set 
   then ext_valuation phi1 subset ext_valuation phi2
*)
Theorem ext_valuation_iff_subset {m : Model}
        (evar_val : evar_name -> Domain m) (svar_val : svar_name -> Power (Domain m))
        (phi1 : Pattern) (phi2 : Pattern) :
  Same_set (Domain m) (ext_valuation evar_val svar_val (phi1 --> phi2)) (Full_set (Domain m)) <->
  Included (Domain m) (ext_valuation evar_val svar_val phi1)
           (@ext_valuation sig m evar_val svar_val phi2).
Proof.
  intros; split; unfold Included; intros.
  * rewrite ext_valuation_imp_simpl in H.
    remember (ext_valuation evar_val svar_val phi1) as Xphi1.
    remember (ext_valuation evar_val svar_val phi2) as Xphi2.
    assert (In (Domain m) (Union (Domain m) (Complement (Domain m) Xphi1) Xphi2) x).
    apply Same_set_to_eq in H. rewrite H. constructor.
    inversion H1. contradiction. assumption.
  * rewrite ext_valuation_imp_simpl.
    remember (ext_valuation evar_val svar_val phi1) as Xphi1.
    remember (ext_valuation evar_val svar_val phi2) as Xphi2.
    constructor. constructor.
    assert (Union (Domain m) (Complement (Domain m) Xphi1) Xphi1 = Full_set (Domain m)).
    apply Same_set_to_eq; apply Union_Compl_Fullset. rewrite <- H0; clear H0.
    unfold Included; intros.
    inversion H0.
    left; assumption.
    right; apply H in H1; assumption.
Qed.

(* update_valuation with fresh name does not change *)
(* TODO(jan.tusil): I think that we need to generalize this
   to work with any variable that is not free in psi.
*)
Lemma update_valuation_fresh {m : Model}
      (evar_val : evar_name -> Domain m) (svar_val : svar_name -> Power (Domain m))
      (psi : Pattern) (x : Domain m) (c : Domain m) :
  ext_valuation (update_evar_val (evar_fresh (variables sig) (free_evars psi)) c evar_val) svar_val psi x
  = ext_valuation evar_val svar_val psi x.
Proof.
Admitted.

(* ext_valuation with free_svar_subst does not change *)
Lemma update_valuation_free_svar_subst {m : Model}
      (evar_val : evar_name -> Domain m) (svar_val : svar_name -> Power (Domain m))
      (phi : Pattern) (psi : Pattern) (X : svar_name) :
  ext_valuation evar_val svar_val phi
  = ext_valuation evar_val svar_val (@free_svar_subst sig phi psi X) .
Proof.
Admitted.


End with_model.

End soundness_lemmas.
