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
Require Import ML.Signature.
Require Export locally_nameless.
Require Import Lattice.

Require Export Ensembles_Ext.


Import MLNotations.
Open Scope ml_scope.

Section soundness_lemmas.

  Context {sig : Signature}.


(* evar_open of fresh name does not change *)
Lemma evar_open_fresh (phi : Pattern) (v : @evar_name sig) :
  forall n, well_formed phi -> ~List.In v (free_evars phi) ->
            evar_open n v phi = phi.
Proof. Admitted.
(*
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

(* Needed in update_valuation_fresh. Should be provable, right? *)
(* Lemma svar_open_fresh (phi : Pattern) (v : @svar_name sig) :
  forall n, well_formed phi -> ~List.In v (free_svars phi) ->
            svar_open n v phi = phi.
Proof. Admitted. *)

(* update_valuation with fresh name does not change *)
(* TODO(jan.tusil): I think that we need to generalize this
   to work with any variable that is not free in psi.
*)
Lemma update_valuation_fresh {m : Model}
      (evar_val : evar_name -> Domain m) (svar_val : svar_name -> Power (Domain m))
      (psi : Pattern) (x : Domain m) (c : Domain m) (v : @evar_name sig):
   (* Should be here, right? *)
   (* well_formed psi -> *)
  ~List.In v (free_evars psi) ->
  ext_valuation (update_evar_val v c evar_val) svar_val psi x
  = ext_valuation evar_val svar_val psi x.
Proof.
(* intro. generalize dependent x. generalize dependent c. 
  generalize dependent evar_val.
  generalize dependent svar_val. generalize dependent v.
  induction psi; try reflexivity.
  - intros. repeat rewrite ext_valuation_free_evar_simpl. simpl in H. unfold not in H. unfold update_evar_val. destruct (eq_evar_name v x) eqn:P.
    + rewrite e in H. destruct H. left. reflexivity.
    + reflexivity.
  - intros. repeat rewrite ext_valuation_app_simpl. simpl in H. 
    pose (set_union_iff (@eq_evar_name sig) v (free_evars psi1) (free_evars psi2)).
    apply not_iff_compat in i. pose (iff_and i). destruct a. clear i. clear H1. 
    pose (H0 H). apply not_or_and in n. destruct n. clear H0. clear H. unfold pointwise_ext. 
    apply propositional_extensionality.
    split; intros.
    + destruct H. destruct H. pose (IHpsi1 v H1 svar_val evar_val c x0). 
        pose (IHpsi2 v H2 svar_val evar_val c x1). rewrite e, e0 in H. exists x0, x1. assumption.
    + destruct H. destruct H. pose (IHpsi1 v H1 svar_val evar_val c x0 ). 
        pose (IHpsi2 v H2 svar_val evar_val c x1). rewrite <- e, <- e0 in H. exists x0, x1. assumption.
  - intros. repeat rewrite ext_valuation_imp_simpl. simpl in H. 
    pose (set_union_iff (@eq_evar_name sig) v (free_evars psi1) (free_evars psi2)).
    apply not_iff_compat in i. pose (iff_and i). destruct a. clear i. clear H1. 
    pose (H0 H). apply not_or_and in n. destruct n. pose (IHpsi1 v H1 svar_val evar_val c x). 
    pose (IHpsi2 v H2 svar_val evar_val c x). clear H0. clear H. unfold In. apply propositional_extensionality. split.
    + intro. pose (Union_is_or (Domain m) ((Complement (Domain m)
                  (ext_valuation (update_evar_val v c evar_val) svar_val psi1))) 
                  ((ext_valuation (update_evar_val v c evar_val) svar_val psi2)) x).
        destruct i. clear H3. pose (H0 H).
        pose (Union_is_or (Domain m) ((Complement (Domain m)
        (ext_valuation evar_val svar_val psi1))) ((ext_valuation evar_val svar_val psi2)) x).
        destruct i. clear H3. apply H4. clear H4. destruct o.
      * unfold Complement, not, In in *. left. rewrite e in H3. assumption.
      * right. rewrite e0 in H3. assumption.
    + intro. pose (Union_is_or (Domain m) ((Complement (Domain m) 
               (ext_valuation evar_val svar_val psi1))) 
               ((ext_valuation evar_val svar_val psi2)) x).
        destruct i. clear H3. pose (H0 H). 
        pose (Union_is_or (Domain m) 
        ((Complement (Domain m)
        (ext_valuation (update_evar_val v c evar_val) svar_val psi1))) 
        (ext_valuation (update_evar_val v c evar_val) svar_val psi2) x).
        destruct i. clear H3. apply H4. clear H4. destruct o.
          * unfold Complement, not, In in *. left. rewrite e. assumption.
          * right. rewrite e0. assumption.
  - intros. repeat rewrite ext_valuation_ex_simpl. simpl. simpl in H. 
    apply propositional_extensionality. split.
    + intros. inversion H0. clear H0. pose (@FA_Uni_intro (Domain m)). apply i.
        clear i. destruct H1. exists x1. 
        pose (evar_fresh_is_fresh (variables sig) (free_evars psi)).
        assert (well_formed psi). admit. 
        pose (evar_open_fresh psi (evar_fresh (variables sig) (free_evars psi)) 0 H1 n).
        rewrite e in *. 
        pose (IHpsi (evar_fresh (variables sig) (free_evars psi)) n svar_val evar_val x1 x).
        rewrite e0. 
        pose (IHpsi (evar_fresh (variables sig) (free_evars psi)) n svar_val 
                    (update_evar_val v c evar_val) x1 x).
        rewrite e1 in H0.
        rewrite (IHpsi v H svar_val evar_val c x) in H0. assumption.
    + intros. inversion H0. pose (@FA_Uni_intro (Domain m)). apply i.
      clear i. destruct H1. exists x1. 
      pose (evar_fresh_is_fresh (variables sig) (free_evars psi)).
      assert (well_formed psi). admit. 
      pose (evar_open_fresh psi (evar_fresh (variables sig) (free_evars psi)) 0 H3 n).
      rewrite e in *.
      pose (IHpsi (evar_fresh (variables sig) (free_evars psi)) n svar_val 
                  (update_evar_val v c evar_val) x1 x).
      rewrite e0.
      pose (IHpsi (evar_fresh (variables sig) (free_evars psi)) n svar_val evar_val x1 x).
      rewrite e1 in H1.
      pose (IHpsi v H svar_val evar_val c x).
      rewrite e2. assumption.
  - intros. simpl in H. repeat rewrite ext_valuation_mu_simpl. simpl.
    unfold Meet, PrefixpointsOf, In. simpl. apply propositional_extensionality. split.
    + intros. pose (H0 e). unfold Included, In in e0.
      unfold Included, In in H1.
      pose (evar_fresh_is_fresh (variables sig) (free_evars psi)).
      assert (well_formed psi). admit.
      rewrite (svar_open_fresh psi 
                               (svar_fresh (variables sig) (free_svars psi))
                               0 H2
                               (svar_fresh_is_fresh (variables sig) (free_svars psi))) 
                               in *.
      pose (IHpsi v H 
            (update_svar_val (svar_fresh (variables sig) (free_svars psi)) e svar_val)
            (evar_val)
             c).
      apply e0. intros. pose (H1 x0). rewrite e1 in H3. pose (e2 H3). assumption.
    + intros. pose (H0 e). unfold Included, In in *. apply e0. intros.
      pose (evar_fresh_is_fresh (variables sig) (free_evars psi)).
      assert (well_formed psi). admit.
      rewrite (svar_open_fresh psi 
                               (svar_fresh (variables sig) (free_svars psi))
                               0 H3
                               (svar_fresh_is_fresh (variables sig) (free_svars psi))) 
                               in *.
      pose (H1 x0).
      pose (IHpsi v H 
            (update_svar_val (svar_fresh (variables sig) (free_svars psi)) e svar_val)
            (evar_val)
             c).
      rewrite e2 in e1. pose (e1 H2). assumption. *)
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
    constructor. apply IHphi. firstorder. assumption.
  + inversion H. inversion H0. subst.
    constructor. firstorder.
  + inversion H. inversion H0. subst.
    constructor. firstorder.
  + inversion H. inversion H0. subst.
    constructor. firstorder.
Qed.


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
    (*le db1 db2 ->*)
    (positive_occurrence_db db1 phi -> positive_occurrence_db db1 (evar_open db2 x phi))
    /\ (negative_occurrence_db db1 phi -> negative_occurrence_db db1 (evar_open db2 x phi)).
Proof.
  induction phi; intros; simpl; split; intros; try constructor; try inversion H; subst; try firstorder.
  * destruct (n =? db2); intros. constructor. assumption.
  * destruct (n =? db2); intros. constructor. assumption.
Qed.

Lemma positive_occurrence_db_evar_open : forall (phi : @Pattern sig) (db1 db2 : db_index) (x : evar_name),
    positive_occurrence_db db1 phi -> positive_occurrence_db db1 (evar_open db2 x phi).
Proof.
  intros.
  pose proof (H' := positive_negative_occurrence_db_evar_open phi db1 db2 x).
  firstorder.
Qed.

Lemma negative_occurrence_db_evar_open : forall (phi : @Pattern sig) (db1 db2 : db_index) (x : evar_name),
    negative_occurrence_db db1 phi -> negative_occurrence_db db1 (evar_open db2 x phi).
Proof.
  intros.
  pose proof (H' := positive_negative_occurrence_db_evar_open phi db1 db2 x).
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
    * apply positive_occurrence_db_evar_open. firstorder.
    * apply IHsz. lia. firstorder.
  + split.
    * apply positive_occurrence_db_evar_open. firstorder.
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

(* Lemma well_formed_closed_aux_svar_open :
  forall (phi : Pattern) (dbi1 dbi2 : db_index) (X : svar_name),
    well_formed_closed_aux phi dbi1 dbi2 ->
    @well_formed_closed_aux sig (svar_open dbi2 X phi) dbi1 dbi2.
Proof.
  induction phi; intros; simpl in *; auto.
  * destruct (eqb_reflect n dbi2). lia. auto.
  * firstorder.
  * firstorder.
  * 
Qed. *)


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
  + simpl in H. simpl.
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

(* Definitions and lemmas inside this section are useful for proving `is_monotonic`,
   but they are probably not usefull for any other purpose. *)
Section respects_blacklist.
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
  

  Lemma respects_blacklist_implies_monotonic :
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
      + (* EVar free *)
        unfold MonotonicFunction. unfold AntiMonotonicFunction. unfold leq. simpl. unfold Included.
        unfold In. split; intros; rewrite -> ext_valuation_free_evar_simpl in *; assumption.
      + (* SVar free *)
        unfold MonotonicFunction. unfold AntiMonotonicFunction. unfold leq. simpl. unfold Included.
        unfold In.
        split; intros; rewrite -> ext_valuation_free_svar_simpl in *;
          unfold update_svar_val in *; destruct (eq_svar_name X x); subst.
        * unfold respects_blacklist in H1.
          specialize (H1 x).
          destruct H1 as [Hneg Hpos].
          specialize (Hneg H2).
          inversion Hneg. subst. contradiction.
        * assumption.
        * auto.
        * assumption.
          
      + (* EVar bound *)
        unfold AntiMonotonicFunction. unfold MonotonicFunction. unfold leq. simpl.
        split; intros; repeat rewrite -> ext_valuation_bound_evar_simpl; unfold Included;
          unfold In; intros; assumption.
      + (* SVar bound *)
        unfold AntiMonotonicFunction. unfold MonotonicFunction. unfold leq. simpl.
        split; intros; repeat rewrite -> ext_valuation_bound_svar_simpl; unfold Included;
          unfold In; intros; assumption.
      + (* Sym *)
        unfold AntiMonotonicFunction. unfold MonotonicFunction. unfold leq. simpl.
        split; intros; repeat rewrite -> ext_valuation_sym_simpl; unfold Included;
          unfold In; intros; assumption.
      + (* Bot *)
        unfold AntiMonotonicFunction. unfold MonotonicFunction. unfold leq. simpl.
        split; intros; rewrite -> ext_valuation_bott_simpl; unfold Included; intros; inversion H4.
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
          repeat rewrite -> ext_valuation_app_simpl.
          unfold pointwise_ext. unfold leq in *. simpl in *.
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
          repeat rewrite -> ext_valuation_app_simpl.
          unfold pointwise_ext. unfold leq in *. simpl in *.
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
          repeat rewrite -> ext_valuation_imp_simpl.
          unfold leq in *. simpl in *. unfold Included in *. intros.
          destruct H0.
          + left. unfold Complement in *.
            unfold not in *. unfold In in *. intros.
            apply H0.
            
            destruct IHn1 as [IHn11 IHn12].
            apply (IHn12 HBp x y H x0).
            apply H1.
          + right. unfold In in *.
            destruct IHn2 as [IHn21 IHn22].
            apply (IHn21 HBp x y H x0 H0).
        }
        {
          intros HBn.
          intros. repeat rewrite -> ext_valuation_imp_simpl.
          unfold leq in *. simpl in *. unfold Included in *. intros.
          destruct H0.
          + left. unfold Complement in *.
            unfold not in *. unfold In in *. intros.
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
        assert (Hsz': size phi <= n).
        { lia. }
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
        {
          unfold MonotonicFunction. intros.
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
          - apply Hx. constructor.
          - apply Hy. constructor.
          - clear Hy. clear Hx.
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

              assert (HrbV: respects_blacklist phi' (Empty_set svar_name) (Singleton svar_name V)).
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
                    unfold not. intros. assert (svar_fresh (variables sig) (free_svars phi) = V).
                    {
                      symmetry. assumption.
                    }
                    unfold not in n0. destruct (n0 H3).
                  * inversion Hrbp. assumption.
              }

              specialize (IHn Hwfp' (Empty_set svar_name) (Singleton svar_name V) HrbV).
              specialize (IHn evar_val (update_svar_val X' x0 svar_val) V).
              destruct IHn as [IHam IHmo].
              apply IHmo. constructor. assumption.
        }
  Qed.

  Lemma is_monotonic : forall (phi : @Pattern sig)
                              (evar_val : @EVarVal sig M)
                              (svar_val : @SVarVal sig M),
      well_formed (mu, phi) ->
      let X := svar_fresh (variables sig) (free_svars phi) in
      @MonotonicFunction A OS
                         (fun S : Ensemble (Domain M) =>
                            (@ext_valuation sig M evar_val (update_svar_val X S svar_val)
                                            (svar_open 0 X phi))).
  Proof.
    simpl. intros. unfold well_formed in H. destruct H as [Hwfp Hwfc].
    pose proof (Hrb := mu_wellformed_respects_blacklist phi Hwfp).
    simpl in Hrb.
    inversion Hwfp.
    remember (svar_open 0 (svar_fresh (variables sig) (free_svars phi)) phi) as phi'.
    assert (Hsz : size phi' <= size phi').
    { lia. }
    pose proof (Hmono := respects_blacklist_implies_monotonic (size phi') phi').
    assert (Hwfp' : well_formed_positive phi').
    { subst. apply wfp_svar_open. assumption. }
    specialize (Hmono Hsz Hwfp').
    specialize (Hmono (Empty_set svar_name) (Singleton svar_name (svar_fresh (variables sig) (free_svars phi)))).
    specialize (Hmono Hrb evar_val svar_val (svar_fresh (variables sig) (free_svars phi))).
    destruct Hmono.
    apply H2.
    constructor.
  Qed.
End with_model.


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

(* ext_valuation with free_svar_subst does not change *)
Lemma update_valuation_free_svar_subst {m : Model}
      (evar_val : evar_name -> Domain m) (svar_val : svar_name -> Power (Domain m))
      (phi : Pattern) (psi : Pattern) (X : svar_name) :
  ext_valuation evar_val svar_val phi
  = ext_valuation evar_val svar_val (@free_svar_subst sig phi psi X) .
Proof.
Admitted.

Lemma proof_rule_prop_ex_right_sound {m : Model} (theory : Theory) (phi psi : Pattern)  
      (evar_val : @evar_name sig -> Domain m) (svar_val : @svar_name sig -> Power (Domain m)):
  (well_formed (patt_imp (patt_app (patt_exists phi) psi) (patt_exists (patt_app phi psi)))) ->
  (well_formed phi) -> (@well_formed sig psi) ->
  (forall axiom : Pattern,
     In Pattern (patterns theory) axiom ->
     forall (evar_val : evar_name -> Domain m)
       (svar_val : svar_name -> Power (Domain m)),
     Same_set (Domain m) (ext_valuation evar_val svar_val axiom)
       (Full_set (@Domain sig m))) ->
  Same_set (Domain m)
  (ext_valuation evar_val svar_val
     (patt_imp (patt_app (patt_exists phi) psi)
        (patt_exists (patt_app phi psi)))) (Full_set (Domain m)).
Proof.
  intros Hwf H H0 Hv.
  rewrite ext_valuation_imp_simpl.
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
    assert (~List.In (evar_fresh (variables sig)
                                 (set_union eq_evar_name (free_evars phi) (free_evars psi))) 
             (free_evars psi)).
    admit.
    assert (~List.In (evar_fresh (variables sig)
                                 (set_union eq_evar_name (free_evars phi) (free_evars psi))) 
             (free_evars phi)).
    admit.
    rewrite evar_open_fresh in Hext_re; try assumption.
    rewrite update_valuation_fresh in Hext_re; try assumption.
    repeat rewrite evar_open_fresh; try assumption.
    repeat rewrite update_valuation_fresh; try assumption.
    repeat split; assumption.
    admit. admit.
Admitted.

Lemma proof_rule_prop_ex_left_sound {m : Model} (theory : Theory) (phi psi : Pattern)  
      (evar_val : @evar_name sig -> Domain m) (svar_val : @svar_name sig -> Power (Domain m)):
  (well_formed (patt_imp (patt_app psi (patt_exists phi)) (patt_exists (patt_app psi phi)))) ->
  (well_formed phi) -> (well_formed psi) ->
  (forall axiom : Pattern,
     In Pattern (patterns theory) axiom ->
     forall (evar_val : evar_name -> Domain m)
       (svar_val : svar_name ->
                   Power (Domain m)),
     Same_set (Domain m)
       (ext_valuation evar_val svar_val axiom)
       (Full_set (Domain m))) ->
  (Same_set (Domain m)
  (ext_valuation evar_val svar_val
     (patt_imp (patt_app psi (patt_exists phi))
        (patt_exists (patt_app psi phi))))
  (Full_set (Domain m))).
Proof.
  intros Hwf H H0 Hv.
  rewrite ext_valuation_imp_simpl.
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
    assert (~List.In (evar_fresh (variables sig)
                                 (set_union eq_evar_name (free_evars psi) (free_evars phi))) 
             (free_evars psi)).
    admit.
    assert (~List.In (evar_fresh (variables sig)
                                 (set_union eq_evar_name (free_evars psi) (free_evars phi))) 
             (free_evars phi)).
    admit.
    rewrite evar_open_fresh in Hext_re; try assumption.
    rewrite update_valuation_fresh in Hext_re; try assumption.
    repeat rewrite evar_open_fresh; try assumption.
    repeat rewrite update_valuation_fresh; try assumption.
    repeat split; assumption.
    admit. admit.
Admitted.

Lemma l1 : forall (phi : @Pattern sig) (x : evar_name),
    well_formed_closed (ex, phi) -> well_formed_closed  (evar_open 0 x phi).
Proof.
  induction phi; try constructor; try firstorder.
  + admit.
  + admit.
  + admit.
Admitted.


(*
(ex, (ex, patt_bound_evar 0 /\ patt_bound_evar 1))
=>
(ex, patt_bound_evar 0 /\ patt_free_evar !X)
*)

End soundness_lemmas.
