Require Import Arith.
Require Import ZArith.
Require Import List.
Require Import Coq.micromega.Lia.
Require Export String.
Require Export Coq.Lists.ListSet.
Require Export Coq.Program.Wf.

Require Import extralibrary.
(*Require Import names.*)
Require Import ML.Signature.
Require Export locally_nameless.
Require Import Lattice.

Require Export Ensembles_Ext.


Import MLNotations.

Section soundness_lemmas.

  Context {sig : Signature}.

Definition respects_blacklist (phi : Pattern) (Bp Bn : Ensemble svar_name) : Prop :=
  forall (var : svar_name),
    (Bp var -> negative_occurrence var phi) /\ (Bn var -> @positive_occurrence sig var phi).

(* TODO *)
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


Definition ModelPowersetLattice (M : Model) := PowersetLattice (@Domain sig M).


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
Search size.
Check le.
Lemma respects_blacklist_implies_monotonic' :
  forall (n : nat) (phi : Pattern),
    le (size phi) n ->
    forall (Bp Bn : Ensemble svar_name),
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
    intros. destruct phi; simpl in H; try inversion H; subst.
    * 


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

End soundness_lemmas.
