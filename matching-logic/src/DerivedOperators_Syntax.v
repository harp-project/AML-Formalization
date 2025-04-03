From MatchingLogic Require Export Substitution.

Import MatchingLogic.Pattern.Notations.
Import MatchingLogic.Substitution.Notations.

Section with_signature.
  Context {Σ : Signature}.
  Open Scope ml_scope.

  Definition patt_not (phi : Pattern) := patt_imp phi patt_bott.

  Definition patt_or  (l r : Pattern) := patt_imp (patt_not l) r.

  Definition patt_and (l r : Pattern) :=
    patt_not (patt_or (patt_not l) (patt_not r)).

  Definition patt_top := (patt_not patt_bott).

  Definition patt_iff (l r : Pattern) :=
    patt_and (patt_imp l r) (patt_imp r l).

  Definition patt_forall (phi : Pattern) :=
    patt_not (patt_exists (patt_not phi)).

  Definition patt_nu (phi : Pattern) :=
    patt_not (patt_mu (patt_not (phi^[svar: 0 ↦ patt_not (patt_bound_svar 0)]))).

  Lemma well_formed_closed_mu_aux_iter_forall
    (ϕ ψ : Pattern) (n : nat)
    (pf : forall idx, (well_formed_closed_mu_aux ϕ idx -> well_formed_closed_mu_aux ψ idx)) :
    forall idx,
    well_formed_closed_mu_aux (Nat.iter n patt_forall ϕ) idx ->
    well_formed_closed_mu_aux (Nat.iter n patt_forall ψ) idx.
  Proof.
    move: pf.
    induction n; intros pf idx H; simpl in *.
    {
      apply pf. exact H.
    }
    {
      destruct_andb! H.
      apply andb_true_iff; split.
      apply andb_true_iff; split.
      2-3: reflexivity.
      specialize (IHn ltac:(auto)).
      apply IHn. apply H.
    }
  Qed.

  Lemma well_formed_positive_iter_forall
    (ϕ ψ : Pattern) (n : nat)
    (pf : (well_formed_positive ϕ -> well_formed_positive ψ)) :
    well_formed_positive (Nat.iter n patt_forall ϕ) ->
    well_formed_positive (Nat.iter n patt_forall ψ).
  Proof.
    move: pf.
    induction n; intros pf H; simpl in *.
    {
      apply pf. exact H.
    }
    {
      destruct_andb! H.
      apply andb_true_iff; split.
      apply andb_true_iff; split.
      2-3: reflexivity.
      specialize (IHn ltac:(auto)).
      apply IHn. apply H.
    }
  Qed.

  Lemma well_formed_closed_ex_aux_iter_forall
    (ϕ ψ : Pattern) (n : nat)
    (pf : forall idx, (well_formed_closed_ex_aux ϕ idx -> well_formed_closed_ex_aux ψ idx)) :
      forall idx,
      well_formed_closed_ex_aux (Nat.iter n patt_forall ϕ) idx ->
      well_formed_closed_ex_aux (Nat.iter n patt_forall ψ) idx.
  Proof.
    move: pf.
    induction n; intros pf idx H; simpl in *.
    {
      apply pf. exact H.
    }
    {
      destruct_andb! H.
      apply andb_true_iff; split.
      apply andb_true_iff; split.
      2-3: reflexivity.
      specialize (IHn ltac:(auto)).
      apply IHn. apply H.
  }
  Qed.

  Lemma well_formed_xy_forall (x y : nat) (ϕ : Pattern) :
    well_formed_xy x y (patt_forall ϕ) = well_formed_xy (S x) y ϕ.
  Proof.
    unfold well_formed_xy.
    simpl.
    rewrite !andb_true_r.
    reflexivity.
  Qed.

  Lemma well_formed_xy_iter_forall
    (f : Pattern -> Pattern)
    (pf :
      forall (x y : nat) (ϕ : Pattern) ,
      well_formed_xy x y ϕ ->
      well_formed_xy x y (f ϕ)
    ) :
    forall (n : nat) (x y : nat) (ϕ : Pattern),
    well_formed_xy x y (Nat.iter n patt_forall ϕ) ->
    well_formed_xy x y (Nat.iter n patt_forall (f ϕ)).
  Proof.
    induction n.
    {
      intros.
      simpl in *.
      apply pf.
      exact H.
    }
    {
      intros x y ϕ H.
      simpl in *.
      rewrite well_formed_xy_forall in H.
      rewrite well_formed_xy_forall.
      apply IHn.
      exact H.
    }
  Qed.

  Lemma well_formed_not (phi : Pattern) :
    well_formed phi = true ->
    well_formed (patt_not phi) = true.
  Proof.
    unfold well_formed, well_formed_closed. simpl.
    intros H.
    naive_bsolver.
  Qed.

  Lemma well_formed_top : well_formed patt_top.
  Proof. reflexivity. Qed.

  Lemma well_formed_or (phi1 phi2 : Pattern) :
    well_formed phi1 = true ->
    well_formed phi2 = true ->
    well_formed (patt_or phi1 phi2) = true.
  Proof.
    unfold patt_or.
    unfold well_formed, well_formed_closed. simpl.
    intros H1 H2.
    naive_bsolver.
  Qed.

  Lemma well_formed_iff (phi1 phi2 : Pattern) :
    well_formed phi1 = true ->
    well_formed phi2 = true ->
    well_formed (patt_iff phi1 phi2) = true.
  Proof.
    unfold patt_iff, patt_and, patt_or, patt_not. intros.
    unfold well_formed in *. simpl.
    unfold well_formed_closed in *. simpl.
    naive_bsolver.
  Qed.

  Lemma well_formed_and (phi1 phi2 : Pattern) :
    well_formed phi1 = true ->
    well_formed phi2 = true ->
    well_formed (patt_and phi1 phi2) = true.
  Proof.
    unfold patt_or.
    unfold well_formed. simpl.
    unfold well_formed_closed. simpl.
    intros H1 H2.
    naive_bsolver.
  Qed.

  Lemma well_formed_closed_ex_all φ : forall n,
    well_formed_closed_ex_aux (patt_forall φ) n
  <->
    well_formed_closed_ex_aux φ (S n).
  Proof.
    intros. simpl. do 2 rewrite andb_true_r. auto.
  Qed.

  Lemma well_formed_closed_mu_all φ : forall m,
    well_formed_closed_mu_aux (patt_forall φ) m
  <->
    well_formed_closed_mu_aux φ m.
  Proof.
    intros. simpl. do 2 rewrite andb_true_r. auto.
  Qed.

  Lemma well_formed_positive_all φ : 
    well_formed_positive (patt_forall φ)
  <->
    well_formed_positive φ.
  Proof.
    intros. simpl. do 2 rewrite andb_true_r. auto.
  Qed.

  Lemma svar_quantify_forall n X ϕ :
    (patt_forall ϕ)^{{svar: X ↦ n}} = patt_forall (ϕ^{{svar: X ↦ n}}).
  Proof. simpl. unfold patt_forall. unfold patt_not. reflexivity. Qed.

  Lemma well_formed_foldr_and (x : Pattern) (xs : list Pattern):
    well_formed x ->
    Pattern.wf xs ->
    well_formed (foldr patt_and x xs).
  Proof.
    intros wfx wfxs.
    induction xs; simpl.
    - assumption.
    - ospecialize* IHxs.
      { unfold Pattern.wf in wfxs. simpl in wfxs. naive_bsolver. }
      apply well_formed_and.
      { unfold Pattern.wf in wfxs. simpl in wfxs. naive_bsolver. }
      assumption.
  Qed.

  Lemma wf_rev l:
    Pattern.wf l ->
    Pattern.wf (rev l).
  Proof.
    intros H. induction l; simpl.
    { exact H. }
    {
      apply wf_app; unfold Pattern.wf in *; simpl in *. destruct_andb! H. split.
      {
        apply IHl. apply H1.
      }
      {
        naive_bsolver.
      }
    }
  Qed.

End with_signature.


Module Notations.

  Notation "! a"     := (patt_not   a  ) (at level 71, right associativity) : ml_scope.
  Notation "a 'or' b" := (patt_or    a b) (at level 73, left associativity) : ml_scope.
  Notation "a 'and' b" := (patt_and   a b) (at level 72, left associativity) : ml_scope.
  Notation "a <---> b" := (patt_iff a b) (at level 74, no associativity) : ml_scope.
  Notation "'Top'" := patt_top : ml_scope.
  Notation "'all' , phi" := (patt_forall phi) (at level 80) : ml_scope.
  Notation "'nu' , phi" := (patt_nu phi) (at level 80) : ml_scope.

End Notations.

(*Module Hints.*)
#[export]
 Hint Resolve well_formed_not : core.

#[export]
 Hint Resolve well_formed_or : core.

#[export]
 Hint Resolve well_formed_and : core.

#[export]
 Hint Resolve well_formed_iff : core.

 (*End Hints.*)
