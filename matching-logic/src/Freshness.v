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
  
  Definition fresh_evar ϕ := evar_fresh (elements (free_evars ϕ)).
  Definition fresh_svar ϕ := svar_fresh (elements (free_svars ϕ)).

  Definition evar_is_fresh_in x ϕ := x ∉ free_evars ϕ.
  Definition svar_is_fresh_in x ϕ := x ∉ free_svars ϕ.

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

End freshness.