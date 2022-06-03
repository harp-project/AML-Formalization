From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From stdpp Require Import base gmap.

From MatchingLogic.Utils
Require Import
    extralibrary
    stdpp_ext
.

From MatchingLogic
Require Import
    Pattern
.

Section freshness.
    Context {Σ : Signature}.


  (* fresh variables *)
  
  Definition evar_fresh (l : list evar) : evar := fresh l.
  Definition svar_fresh (l : list svar) : svar := fresh l.

  Definition evar_fresh_s (s : EVarSet) : evar := evar_fresh (elements s).
  Definition svar_fresh_s (s : SVarSet) : svar := svar_fresh (elements s).
  
  Definition fresh_evar ϕ := evar_fresh_s (free_evars ϕ).
  Definition fresh_svar ϕ := svar_fresh_s (free_svars ϕ).

  (* Lemmas about fresh variables *)

  Lemma set_evar_fresh_is_fresh' (S : EVarSet) : evar_fresh (elements S) ∉ S.
  Proof.
    intros H.
    pose proof (Hf := @infinite_is_fresh _ evar_infinite (elements S)).
    unfold elements in H. unfold gmap.gset_elements in H.
    apply gset_to_list_elem_of in H.
    unfold elements in Hf. unfold gmap.gset_elements in Hf.
    unfold evar_fresh in H. unfold fresh in Hf. contradiction.
  Qed.
  
  Lemma set_evar_fresh_is_fresh ϕ : evar_is_fresh_in (fresh_evar ϕ) ϕ.
  Proof.
    unfold evar_is_fresh_in.
    unfold fresh_evar.
    apply set_evar_fresh_is_fresh'.
  Qed.

  Hint Resolve set_evar_fresh_is_fresh : core.

  Lemma set_svar_fresh_is_fresh' (S : SVarSet) : svar_fresh (elements S) ∉ S.
  Proof.
    intros H.
    pose proof (Hf := @infinite_is_fresh _ svar_infinite (elements S)).
    unfold elements in H. unfold gset_elements in H.
    apply gset_to_list_elem_of in H.
    unfold elements in Hf. unfold gset_elements in Hf.
    unfold evar_fresh in H. unfold fresh in Hf. contradiction.
  Qed.
  
  Lemma set_svar_fresh_is_fresh ϕ : svar_is_fresh_in (fresh_svar ϕ) ϕ.
  Proof.
    unfold svar_is_fresh_in.
    unfold fresh_svar.
    apply set_svar_fresh_is_fresh'.
  Qed.

  Hint Resolve set_svar_fresh_is_fresh : core.
  
  Lemma evar_is_fresh_in_richer' x ϕ B:
    free_evars ϕ ⊆ B ->
    x ∉ B ->
    evar_is_fresh_in x ϕ.
  Proof.
    intros Hsub.
    unfold evar_is_fresh_in.
    intros Hnotin.
    eauto using not_elem_of_larger_impl_not_elem_of.
  Qed.
  
  Lemma evar_is_fresh_in_richer x ϕ₁ ϕ₂:
    free_evars ϕ₁ ⊆ free_evars ϕ₂ ->
    evar_is_fresh_in x ϕ₂ ->
    evar_is_fresh_in x ϕ₁.
  Proof.
    intros Hsub Hnotin.
    eapply evar_is_fresh_in_richer'; auto.
  Qed.

  Lemma svar_is_fresh_in_richer' X ϕ B:
    free_svars ϕ ⊆ B ->
    X ∉ B ->
    svar_is_fresh_in X ϕ.
  Proof.
    intros Hsub.
    unfold svar_is_fresh_in.
    intros Hnotin.
    eauto using not_elem_of_larger_impl_not_elem_of.
  Qed.

  Lemma svar_is_fresh_in_richer X ϕ₁ ϕ₂:
    free_svars ϕ₁ ⊆ free_svars ϕ₂ ->
    svar_is_fresh_in X ϕ₂ ->
    svar_is_fresh_in X ϕ₁.
  Proof.
    intros Hsub Hnotin.
    eapply svar_is_fresh_in_richer'; auto.
  Qed.

  (*
  Lemma fresh_neq_fresh_l ϕ₁ ϕ₂ :
    (*~ evar_is_fresh_in (fresh_evar ϕ₁) ϕ₂ ->*)
    free_evars ϕ₁ ⊈
    fresh_evar ϕ₁ ≠ fresh_evar ϕ₂.
  Proof.
    intros H.
    unfold fresh_evar at 2.
   *)

  Hint Resolve evar_is_fresh_in_richer : core.


  Lemma not_free_implies_positive_negative_occurrence :
    forall (phi : Pattern) (X : svar),
      X ∉ (free_svars phi) ->
      svar_has_positive_occurrence X phi = false /\ svar_has_negative_occurrence X phi = false.
  Proof.
    induction phi; simpl; intros Y H; split; try auto; cbn.
    * case_match; auto. set_solver.
    * now erewrite -> (proj1 (IHphi1 _ _)), -> (proj1 (IHphi2 _ _)).
    * now erewrite -> (proj2 (IHphi1 _ _)), -> (proj2 (IHphi2 _ _)).
    * now erewrite -> (proj2 (IHphi1 _ _)), -> (proj1 (IHphi2 _ _)).
    * now erewrite -> (proj1 (IHphi1 _ _)), -> (proj2 (IHphi2 _ _)).
    * now erewrite -> (proj1 (IHphi _ _)).
    * now erewrite -> (proj2 (IHphi _ _)).
    * now erewrite -> (proj1 (IHphi _ _)).
    * now erewrite -> (proj2 (IHphi _ _)).
    Unshelve. all: set_solver.
  Qed.


  Corollary evar_is_fresh_in_app_l x ϕ₁ ϕ₂ :
    evar_is_fresh_in x (patt_app ϕ₁ ϕ₂) -> evar_is_fresh_in x ϕ₁.
  Proof.
    unfold evar_is_fresh_in. simpl.
    move/not_elem_of_union => [H1 H2].
    done.
  Qed.

  Corollary svar_is_fresh_in_app_l X ϕ₁ ϕ₂ :
    svar_is_fresh_in X (patt_app ϕ₁ ϕ₂) -> svar_is_fresh_in X ϕ₁.
  Proof.
    unfold svar_is_fresh_in. simpl.
    move/not_elem_of_union => [H1 H2].
    done.
  Qed.
  
  (*Hint Resolve evar_is_fresh_in_app_l : core.*)

  Corollary evar_is_fresh_in_app_r x ϕ₁ ϕ₂ :
    evar_is_fresh_in x (patt_app ϕ₁ ϕ₂) -> evar_is_fresh_in x ϕ₂.
  Proof.
    unfold evar_is_fresh_in. simpl.
    move/not_elem_of_union => [H1 H2].
    done.
  Qed.

  Corollary svar_is_fresh_in_app_r X ϕ₁ ϕ₂ :
    svar_is_fresh_in X (patt_app ϕ₁ ϕ₂) -> svar_is_fresh_in X ϕ₂.
  Proof.
    unfold svar_is_fresh_in. simpl.
    move/not_elem_of_union => [H1 H2].
    done.
  Qed.
  
  Lemma evar_is_fresh_in_app x ϕ₁ ϕ₂ :
    evar_is_fresh_in x (patt_app ϕ₁ ϕ₂)
    <-> (evar_is_fresh_in x ϕ₁ /\ evar_is_fresh_in x ϕ₂).
  Proof.
    split; intros H.
    - split.
      + eapply evar_is_fresh_in_app_l. apply H.
      + eapply evar_is_fresh_in_app_r. apply H.
    - unfold evar_is_fresh_in in *.
      simpl.
      set_solver.
  Qed.

  Lemma svar_is_fresh_in_app X ϕ₁ ϕ₂ :
    svar_is_fresh_in X (patt_app ϕ₁ ϕ₂)
    <-> (svar_is_fresh_in X ϕ₁ /\ svar_is_fresh_in X ϕ₂).
  Proof.
    split; intros H.
    - split.
      + eapply svar_is_fresh_in_app_l. apply H.
      + eapply svar_is_fresh_in_app_r. apply H.
    - unfold svar_is_fresh_in in *.
      simpl.
      set_solver.
  Qed.
  
  (*Hint Resolve evar_is_fresh_in_app_r : core.*)

  Corollary evar_is_fresh_in_imp_l x ϕ₁ ϕ₂ :
    evar_is_fresh_in x (patt_imp ϕ₁ ϕ₂) -> evar_is_fresh_in x ϕ₁.
  Proof.
    unfold evar_is_fresh_in. simpl.
    move/not_elem_of_union => [H1 H2].
    done.
  Qed.

  Corollary svar_is_fresh_in_imp_l X ϕ₁ ϕ₂ :
    svar_is_fresh_in X (patt_imp ϕ₁ ϕ₂) -> svar_is_fresh_in X ϕ₁.
  Proof.
    unfold svar_is_fresh_in. simpl.
    move/not_elem_of_union => [H1 H2].
    done.
  Qed.
  
  (*Hint Resolve evar_is_fresh_in_imp_l : core.*)

  Corollary evar_is_fresh_in_imp_r x ϕ₁ ϕ₂ :
    evar_is_fresh_in x (patt_imp ϕ₁ ϕ₂) -> evar_is_fresh_in x ϕ₂.
  Proof.
    unfold evar_is_fresh_in. simpl.
    move/not_elem_of_union => [H1 H2].
    done.
  Qed.

  Corollary svar_is_fresh_in_imp_r X ϕ₁ ϕ₂ :
    svar_is_fresh_in X (patt_imp ϕ₁ ϕ₂) -> svar_is_fresh_in X ϕ₂.
  Proof.
    unfold svar_is_fresh_in. simpl.
    move/not_elem_of_union => [H1 H2].
    done.
  Qed.

  Lemma evar_is_fresh_in_imp x ϕ₁ ϕ₂ :
    evar_is_fresh_in x (patt_imp ϕ₁ ϕ₂)
    <-> (evar_is_fresh_in x ϕ₁ /\ evar_is_fresh_in x ϕ₂).
  Proof.
    split; intros H.
    - split.
      + eapply evar_is_fresh_in_imp_l. apply H.
      + eapply evar_is_fresh_in_imp_r. apply H.
    - unfold evar_is_fresh_in in *.
      simpl.
      set_solver.
  Qed.

  Lemma svar_is_fresh_in_imp X ϕ₁ ϕ₂ :
    svar_is_fresh_in X (patt_imp ϕ₁ ϕ₂)
    <-> (svar_is_fresh_in X ϕ₁ /\ svar_is_fresh_in X ϕ₂).
  Proof.
    split; intros H.
    - split.
      + eapply svar_is_fresh_in_imp_l. apply H.
      + eapply svar_is_fresh_in_imp_r. apply H.
    - unfold svar_is_fresh_in in *.
      simpl.
      set_solver.
  Qed.

  
  (*Hint Resolve evar_is_fresh_in_imp_r : core.*)

  Corollary evar_is_fresh_in_exists x ϕ :
    evar_is_fresh_in x (patt_exists ϕ) <-> evar_is_fresh_in x ϕ.
  Proof.
    unfold evar_is_fresh_in. simpl. done.
  Qed.

  (*Hint Resolve evar_is_fresh_in_exists : core.*)

  Corollary evar_is_fresh_in_mu x ϕ :
    evar_is_fresh_in x (patt_mu ϕ) <-> evar_is_fresh_in x ϕ.
  Proof.
    unfold evar_is_fresh_in. simpl. done.
  Qed.

  (*Hint Resolve evar_is_fresh_in_mu : core.*)

  Corollary svar_is_fresh_in_exists x ϕ :
    svar_is_fresh_in x (patt_exists ϕ) <-> svar_is_fresh_in x ϕ.
  Proof.
    unfold svar_is_fresh_in. simpl. done.
  Qed.

  Corollary svar_is_fresh_in_mu x ϕ :
    svar_is_fresh_in x (patt_mu ϕ) <-> svar_is_fresh_in x ϕ.
  Proof.
    unfold svar_is_fresh_in. simpl. done.
  Qed.

    
  Lemma X_eq_fresh_impl_X_notin_free_svars X ϕ:
    X = fresh_svar ϕ ->
    X ∉ free_svars ϕ.
  Proof.
    intros H.
    rewrite H.
    unfold fresh_svar.
    apply set_svar_fresh_is_fresh'.
  Qed.

  Lemma X_eq_evar_fresh_impl_X_notin_S X (S:EVarSet):
    X = evar_fresh (elements S) ->
    X ∉ S.
  Proof.
    intros H.
    rewrite H.
    apply set_evar_fresh_is_fresh'.
  Qed.
  
  Lemma X_eq_svar_fresh_impl_X_notin_S X (S:SVarSet):
    X = svar_fresh (elements S) ->
    X ∉ S.
  Proof.
    intros H.
    rewrite H.
    apply set_svar_fresh_is_fresh'.
  Qed.

  Hint Resolve X_eq_fresh_impl_X_notin_free_svars : core.


  Definition simpl_free_evars :=
    (
      (@left_id_L EVarSet  ∅ (@union _ _)),
      (@right_id_L EVarSet ∅ (@union _ _))
    ).



  Definition simpl_free_svars :=
      (
        (@left_id_L SVarSet  ∅ (@union _ _)),
        (@right_id_L SVarSet ∅ (@union _ _))
      ).
    

End freshness.


Ltac remember_fresh_svars :=
  unfold fresh_svar in *;
  repeat(
      match goal with
      | |- context G [svar_fresh ?Y] =>
        match goal with
        | H: ?X = svar_fresh Y |- _ => fail 2
        | _ => remember (svar_fresh Y)
        end
      | H1: context G [svar_fresh ?Y] |- _ =>
        match goal with
        | H2: ?X = svar_fresh Y |- _ => fail 2
        | _ => remember (svar_fresh Y)
        end
      end
    ).

Ltac remember_fresh_evars :=
  unfold fresh_evar in *;
  repeat(
      match goal with
      | |- context G [evar_fresh ?Y] =>
        match goal with
        | H: ?X = evar_fresh Y |- _ => fail 2
        | _ => remember (evar_fresh Y)
        end
      | H1: context G [evar_fresh ?Y] |- _ =>
        match goal with
        | H2: ?X = evar_fresh Y |- _ => fail 2
        | _ => remember (evar_fresh Y)
        end
      end
    ).


(* assumes a goal `x₁ ≠ x₂` and a hypothesis of the shape `x₁ = fresh_evar ...`
     or `x₂ = fresh_evar ...`
 *)
Ltac solve_fresh_neq :=
  subst; remember_fresh_evars;
  repeat (
      match goal with
      | Heq: (eq ?x ?t) |- not (eq ?x ?y) =>
        pose proof (X_eq_evar_fresh_impl_X_notin_S Heq); clear Heq
      | Heq: (eq ?x ?t) |- not (eq ?y ?x) =>
        pose proof (X_eq_evar_fresh_impl_X_notin_S Heq); clear Heq
      end
    );
  (idtac + apply nesym);
  match goal with
  | H: not (elem_of ?x ?S) |- not (eq ?x ?y) =>
    simpl in H;
    (do ? rewrite simpl_free_evars/= in H);
    auto;
    rewrite -?union_assoc_L in H;
    repeat (
        match goal with
        | H: (not (elem_of ?x (singleton ?y))) |- _ =>
          apply not_elem_of_singleton_1 in H;
          first [ exact H | clear H]
        | H: (not (elem_of ?x (union ?l ?r))) |- _ => (apply not_elem_of_union in H; destruct H)
        end
      );
    fail
  end.


Ltac solve_fresh_svar_neq :=
  subst; remember_fresh_svars;
  repeat (
      match goal with
      | Heq: (eq ?x ?t) |- not (eq ?x ?y) =>
        pose proof (X_eq_svar_fresh_impl_X_notin_S Heq); clear Heq
      | Heq: (eq ?x ?t) |- not (eq ?y ?x) =>
        pose proof (X_eq_svar_fresh_impl_X_notin_S Heq); clear Heq
      end
    );
  (idtac + apply nesym);
  match goal with
  | H: not (elem_of ?x ?S) |- not (eq ?x ?y) =>
    simpl in H;
    (do ? rewrite simpl_free_svars/= in H);
    auto;
    rewrite -?union_assoc_L in H;
    repeat (
        match goal with
        | H: (not (elem_of ?x (singleton ?y))) |- _ =>
          apply not_elem_of_singleton_1 in H;
          first [ exact H | clear H]
        | H: (not (elem_of ?x (union ?l ?r))) |- _ => (apply not_elem_of_union in H; destruct H)
        end
      );
    fail
  end.



Definition evar_fresh_dep {Σ : Signature} (S : EVarSet) : {x : evar & x ∉ S} :=
  @existT evar (fun x => x ∉ S) (evar_fresh_s S) (@set_evar_fresh_is_fresh' Σ S).

Definition svar_fresh_dep {Σ : Signature} (S : SVarSet) : {X : svar & X ∉ S} :=
  @existT svar (fun x => x ∉ S) (svar_fresh_s S) (@set_svar_fresh_is_fresh' _ S).


Fixpoint evar_fresh_seq {Σ : Signature} (avoid : EVarSet) (n : nat) : list evar :=
  match n with
  | 0 => []
  | S n' =>
    let x := (evar_fresh_s avoid) in
    x :: evar_fresh_seq ({[x]} ∪ avoid) (n')
  end.

Fixpoint svar_fresh_seq {Σ : Signature} (avoid : SVarSet) (n : nat) : list svar :=
  match n with
   | 0 => []
   | S n' =>
     let X := (svar_fresh_s avoid) in
     X :: svar_fresh_seq ({[X]} ∪ avoid) (n')
  end.