From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From stdpp Require Import base sets propset.
From Coq Require Import Logic.Classical_Prop.
From MatchingLogic.Utils Require Import Lattice stdpp_ext extralibrary.
From MatchingLogic
Require Import
  Syntax
  Semantics
  IndexManipulation
  PrePredicate
  DerivedOperators_Syntax
.

Import MatchingLogic.Syntax.Notations.
Import MatchingLogic.DerivedOperators_Syntax.Notations.

Section with_signature.
  Context {Σ : Signature}.

  Section with_model.
    Context {M : Model}.
    
    Lemma pattern_interpretation_not_simpl : forall (evar_val : EVarVal) (svar_val : SVarVal) (phi : Pattern),
        @pattern_interpretation Σ M evar_val svar_val (patt_not phi) = ⊤ ∖ (pattern_interpretation evar_val svar_val phi).
    Proof.
      intros. unfold patt_not.
      rewrite -> pattern_interpretation_imp_simpl.
      rewrite -> pattern_interpretation_bott_simpl.
      set_solver by fail.
    Qed.

    Lemma pattern_interpretation_or_simpl : forall (evar_val : EVarVal) (svar_val : SVarVal)
                                                   (phi1 phi2 : Pattern),
        pattern_interpretation evar_val svar_val (patt_or phi1 phi2)
        = (pattern_interpretation evar_val svar_val phi1) ∪ (@pattern_interpretation _ M evar_val svar_val phi2).
    Proof.
      intros. unfold patt_or.
      rewrite -> pattern_interpretation_imp_simpl.
      rewrite -> pattern_interpretation_not_simpl.
      assert (H: ⊤ ∖ (⊤ ∖ (pattern_interpretation evar_val svar_val phi1)) = pattern_interpretation evar_val svar_val phi1).
      { apply Compl_Compl_propset. }
      rewrite -> H. reflexivity.
    Qed.

    Lemma pattern_interpretation_or_comm : forall (evar_val : EVarVal) (svar_val : SVarVal)
                                                  (phi1 phi2 : Pattern),
        @pattern_interpretation Σ M evar_val svar_val (patt_or phi1 phi2)
        = pattern_interpretation evar_val svar_val (patt_or phi2 phi1).
    Proof.
      intros.
      repeat rewrite -> pattern_interpretation_or_simpl.
      set_solver by fail.
    Qed.

    Lemma pattern_interpretation_and_simpl : forall (evar_val : EVarVal) (svar_val : SVarVal)
                                                    (phi1 phi2 : Pattern),
        pattern_interpretation evar_val svar_val (patt_and phi1 phi2)
        = (pattern_interpretation evar_val svar_val phi1) ∩ (@pattern_interpretation _ M evar_val svar_val phi2).
    Proof.
      intros. unfold patt_and.
      rewrite -> pattern_interpretation_not_simpl.
      rewrite -> pattern_interpretation_or_simpl.
      repeat rewrite -> pattern_interpretation_not_simpl.
      apply Compl_Union_Compl_Inters_propset_alt.
    Qed.

    Lemma pattern_interpretation_and_comm : forall (evar_val : EVarVal) (svar_val : SVarVal)
                                                   (phi1 phi2 : Pattern),
        @pattern_interpretation Σ M evar_val svar_val (patt_and phi1 phi2)
        = pattern_interpretation evar_val svar_val (patt_and phi2 phi1).
    Proof.
      intros.
      repeat rewrite -> pattern_interpretation_and_simpl.
      set_solver by fail.
    Qed.

    Lemma pattern_interpretation_top_simpl : forall (evar_val : EVarVal) (svar_val : SVarVal),
        @pattern_interpretation Σ M evar_val svar_val patt_top = ⊤.
    Proof.
      intros. unfold patt_top.
      rewrite -> pattern_interpretation_not_simpl.
      rewrite -> pattern_interpretation_bott_simpl.
      set_solver by fail.
    Qed.

    (* TODO prove. Maybe some de-morgan laws could be helpful in proving this? *)
    Lemma pattern_interpretation_iff_or : forall (evar_val : EVarVal) (svar_val : SVarVal)
                                                 (phi1 phi2 : Pattern),
        @pattern_interpretation Σ M evar_val svar_val (patt_iff phi1 phi2)
        = pattern_interpretation evar_val svar_val (patt_or (patt_and phi1 phi2) (patt_and (patt_not phi1) (patt_not phi2))).
    Proof.

    Abort.

    Lemma pattern_interpretation_iff_comm : forall (evar_val : EVarVal) (svar_val : SVarVal)
                                                   (phi1 phi2 : Pattern),
        @pattern_interpretation Σ M evar_val svar_val (patt_iff phi1 phi2)
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
      pattern_interpretation evar_val svar_val (phi1 ---> phi2)%ml = ⊤ <->
      (pattern_interpretation evar_val svar_val phi1) ⊆
               (@pattern_interpretation _ M evar_val svar_val phi2).
    Proof.
      rewrite -> elem_of_subseteq.
      rewrite -> pattern_interpretation_imp_simpl.
      remember (pattern_interpretation evar_val svar_val phi1) as Xphi1.
      remember (pattern_interpretation evar_val svar_val phi2) as Xphi2.
      split; intros.
      - assert (x ∈ ((⊤ ∖ Xphi1) ∪ Xphi2)).
        { rewrite H. apply elem_of_top'. }
        set_unfold in H1.
        destruct H1.
        + destruct H1. contradiction.
        + assumption.
      -
        assert (H1: (⊤ ∖ Xphi1) ∪ Xphi1 = ⊤).
        { set_unfold. intros x. split; try auto. intros _.
          destruct (classic (x ∈ Xphi1)).
          + right. assumption.
          + left. split; auto.
        }
        rewrite <- H1.
        set_solver.
    Qed.

    Lemma M_predicate_not ϕ : M_predicate M ϕ -> M_predicate M (patt_not ϕ).
    Proof.
      intros. unfold patt_not. auto using M_predicate_impl, M_predicate_bott.
    Qed.

    Hint Resolve M_predicate_not : core.

    Lemma M_predicate_or ϕ₁ ϕ₂ : M_predicate M ϕ₁ -> M_predicate M ϕ₂ -> M_predicate M (patt_or ϕ₁ ϕ₂).
    Proof.
      intros. unfold patt_or. auto using M_predicate_not, M_predicate_impl.
    Qed.

    Hint Resolve M_predicate_or : core.

    Lemma M_predicate_and ϕ₁ ϕ₂ : M_predicate M ϕ₁ -> M_predicate M ϕ₂ -> M_predicate M (patt_and ϕ₁ ϕ₂).
    Proof.
      intros. unfold patt_and. auto using M_predicate_or, M_predicate_not.
    Qed.

    Hint Resolve M_predicate_and : core.


    Lemma M_predicate_top : M_predicate M patt_top.
    Proof.
      unfold patt_top. apply M_predicate_not. apply M_predicate_bott.
    Qed.

    Hint Resolve M_predicate_top : core.

    Lemma M_predicate_forall ϕ :
      let x := fresh_evar ϕ in
      M_predicate M (evar_open 0 x ϕ) -> M_predicate M (patt_forall ϕ).
    Proof.
      intros x Hpred.
      unfold patt_forall.
      apply M_predicate_not.
      apply M_predicate_exists.
      unfold evar_open.
      repeat (rewrite simpl_bevar_subst';[reflexivity|]).
      apply M_predicate_not.
      subst x.
      simpl.        
      rewrite -> sets.union_empty_r_L.
      apply Hpred.
    Qed.

    Hint Resolve M_predicate_forall : core.

    Lemma M_predicate_iff ϕ₁ ϕ₂ :
      M_predicate M ϕ₁ ->
      M_predicate M ϕ₂ ->
      M_predicate M (patt_iff ϕ₁ ϕ₂).
    Proof.
      intros H1 H2.
      unfold patt_iff.
      apply M_predicate_and; apply M_predicate_impl; auto.
    Qed.

    Hint Resolve M_predicate_iff : core.

    Lemma M_pre_predicate_not ϕ :
      M_pre_predicate M ϕ ->
      M_pre_predicate M (patt_not ϕ).
    Proof.
      intros H.
      unfold patt_not.
      apply M_pre_predicate_imp.
      { exact H. }
      { apply M_pre_predicate_bott. }
    Qed.

    Lemma M_pre_predicate_or ϕ₁ ϕ₂ :
      M_pre_predicate M ϕ₁ ->
      M_pre_predicate M ϕ₂ ->
      M_pre_predicate M (patt_or ϕ₁ ϕ₂).
    Proof.
      intros H1 H2. unfold patt_or.
      apply M_pre_predicate_imp.
      { apply M_pre_predicate_not. exact H1. }
      { exact H2. }
    Qed.

    Lemma M_pre_predicate_and ϕ₁ ϕ₂ :
      M_pre_predicate M ϕ₁ ->
      M_pre_predicate M ϕ₂ ->
      M_pre_predicate M (patt_and ϕ₁ ϕ₂).
    Proof.
      intros H1 H2. unfold patt_and.
      apply M_pre_predicate_not.
      apply M_pre_predicate_or.
      { apply M_pre_predicate_not. exact H1. }
      { apply M_pre_predicate_not. exact H2. }
    Qed.

    

    (* ML's 'set comprehension'/'set building' scheme.
 Pattern `∃ x. x ∧ P(x)` gets interpreted as {m ∈ M | P(m) holds}
     *)
    (* ϕ is expected to have dangling evar indices *)

    Lemma pattern_interpretation_set_builder ϕ ρₑ ρₛ :
      let x := fresh_evar ϕ in
      M_predicate M (evar_open 0 x ϕ) ->
      (pattern_interpretation ρₑ ρₛ (patt_exists (patt_and (patt_bound_evar 0) ϕ)))
      = PropSet
          (fun m : (Domain M) => pattern_interpretation (update_evar_val x m ρₑ) ρₛ (evar_open 0 x ϕ) = ⊤).
    
    Proof.
      simpl. intros Hmp.
      rewrite -> pattern_interpretation_ex_simpl.
      unfold fresh_evar. simpl free_evars.
      repeat rewrite -> union_empty_r_L.
      rewrite -> union_empty_l_L.
      rewrite -> evar_open_and.
      remember (evar_fresh (elements (free_evars ϕ))) as x.
      apply set_eq_subseteq.
      rewrite 2!elem_of_subseteq.
      split; intros m H.
      - unfold propset_fa_union in H.
        rewrite -> elem_of_PropSet in H.
        destruct H as [m' H].
        rewrite -> pattern_interpretation_and_simpl in H.
        set_unfold in H.
        destruct H as [Hbound Hϕ].
        assert (Heqmm' : m = m').
        { 
          simpl in Hbound.
          rewrite -> evar_open_bound_evar in Hbound.
          case_match; try lia.
          rewrite -> pattern_interpretation_free_evar_simpl in Hbound.
          apply elem_of_singleton in Hbound. subst m.
          rewrite update_evar_val_same. reflexivity.
        }
        rewrite <- Heqmm' in Hϕ.
        rewrite -> elem_of_PropSet.
        apply predicate_not_empty_iff_full.
        + subst. auto.
        + intros Contra.
          apply Not_Empty_iff_Contains_Elements in Contra.
          { exact Contra. }
          exists m. apply Hϕ.
      - unfold propset_fa_union.
        apply elem_of_PropSet.
        exists m.
        rewrite -> pattern_interpretation_and_simpl. constructor.
        +
          rewrite -> evar_open_bound_evar.
          case_match; try lia.
          rewrite -> pattern_interpretation_free_evar_simpl.
          rewrite -> update_evar_val_same. constructor.
        + rewrite -> elem_of_PropSet in H.
          rewrite -> set_eq_subseteq in H. destruct H as [H1 H2].
          rewrite -> elem_of_subseteq in H2.
          specialize (H2 m). apply H2. apply elem_of_top'.
    Qed.
    
    Lemma pattern_interpretation_forall_predicate ϕ ρₑ ρₛ :
      let x := fresh_evar ϕ in
      M_predicate M (evar_open 0 x ϕ) ->
      pattern_interpretation ρₑ ρₛ (patt_forall ϕ) = ⊤ <->
      ∀ (m : Domain M), pattern_interpretation (update_evar_val x m ρₑ) ρₛ (evar_open 0 x ϕ) = ⊤.
    Proof.
      intros x H.
      unfold patt_forall.
      rewrite -> pattern_interpretation_not_simpl.
      
      assert (Hscfie : ⊤ ∖ ⊤ = @empty (propset (Domain M)) _) by apply difference_diag_L.
      rewrite -> complement_full_iff_empty.
      rewrite -> pattern_interpretation_exists_empty.
      
      assert (Hfr: fresh_evar (! ϕ)%ml = fresh_evar ϕ).
      { unfold fresh_evar. apply f_equal. apply f_equal. simpl.
        rewrite -> union_empty_r_L. reflexivity.
      }

      rewrite -> Hfr. subst x.
      unfold evar_open.
      simpl_bevar_subst.
      split; intros H'.
      - intros m.
        specialize (H' m).
        rewrite -> pattern_interpretation_not_simpl in H'.
        rewrite -> complement_empty_iff_full in H'.
        exact H'.
      - intros m.
        specialize (H' m).
        rewrite -> pattern_interpretation_not_simpl.
        rewrite -> H'.
        rewrite Hscfie.
        reflexivity.
    Qed.


    Lemma pattern_interpretation_and_full ρₑ ρₛ ϕ₁ ϕ₂:
      @pattern_interpretation Σ M ρₑ ρₛ (patt_and ϕ₁ ϕ₂) = ⊤
      <-> (@pattern_interpretation Σ M ρₑ ρₛ ϕ₁ = ⊤
           /\ @pattern_interpretation Σ M ρₑ ρₛ ϕ₂ = ⊤).
    Proof.
      unfold Full.
      rewrite -> pattern_interpretation_and_simpl.
      split.
      - intros H.
        apply intersection_full_iff_both_full in H.
        apply H.
      - intros [H1 H2].
        rewrite H1. rewrite H2. set_solver.
    Qed.

    Lemma pattern_interpretation_predicate_not ρₑ ρₛ ϕ :
      M_predicate M ϕ ->
      pattern_interpretation ρₑ ρₛ (patt_not ϕ) = ⊤
      <-> @pattern_interpretation Σ M ρₑ ρₛ ϕ <> ⊤.
    Proof.
      intros Hpred.
      rewrite pattern_interpretation_not_simpl.
      split; intros H.
      - apply predicate_not_full_iff_empty.
        { apply Hpred. }
        apply complement_full_iff_empty in H.
        exact H.
      - apply predicate_not_full_iff_empty in H.
        2: { apply Hpred. }
        rewrite H.
        set_solver.
    Qed.
    
  End with_model.


  Lemma T_predicate_not Γ ϕ : T_predicate Γ ϕ -> T_predicate Γ (patt_not ϕ).
  Proof.
    unfold T_predicate.
    intros.
    auto using M_predicate_not.
  Qed.

  Hint Resolve T_predicate_not : core.

  Lemma T_predicate_or Γ ϕ₁ ϕ₂ : T_predicate Γ ϕ₁ -> T_predicate Γ ϕ₂ -> T_predicate Γ (patt_or ϕ₁ ϕ₂).
  Proof.
    unfold T_predicate.
    intros.
    auto using M_predicate_or.
  Qed.

  Hint Resolve T_predicate_or : core.

  Lemma T_predicate_and Γ ϕ₁ ϕ₂ : T_predicate Γ ϕ₁ -> T_predicate Γ ϕ₂ -> T_predicate Γ (patt_and ϕ₁ ϕ₂).
  Proof.
    unfold T_predicate.
    intros.
    auto using M_predicate_and.
  Qed.

  Hint Resolve T_predicate_or : core.


End with_signature.

(* TODO make these a separate hintdb. *)
#[export]
Hint Resolve M_predicate_not : core.
#[export]
Hint Resolve M_predicate_or : core.
#[export]
Hint Resolve M_predicate_and : core.
#[export]
Hint Resolve M_predicate_top : core.
#[export]
Hint Resolve M_predicate_forall : core.
#[export]
Hint Resolve M_predicate_iff : core.
#[export]
Hint Resolve T_predicate_not : core.
#[export]
Hint Resolve T_predicate_or : core.
#[export]
Hint Resolve T_predicate_or : core.

Lemma bcmcloseex_not {Σ : Signature} (l : list (db_index * evar)) (p : Pattern):
  bcmcloseex l (patt_not p) = patt_not (bcmcloseex l p).
Proof.
  unfold patt_not.
  rewrite bcmcloseex_imp.
  rewrite bcmcloseex_bott.
  reflexivity.
Qed.

Lemma bcmcloseex_all {Σ : Signature} (l : list (db_index * evar)) (q : Pattern) :
  bcmcloseex l (all , q)%ml =
  (all , bcmcloseex (map (λ p : nat * evar, (S p.1, p.2)) l) q)%ml.
Proof.
  unfold patt_forall.
  rewrite bcmcloseex_not.
  rewrite bcmcloseex_ex.
  rewrite bcmcloseex_not.
  reflexivity.
Qed.

Lemma M_pre_pre_predicate_forall {Σ : Signature} (k : db_index) M ϕ :
  M_pre_pre_predicate (S k) M ϕ ->
  M_pre_pre_predicate k M (patt_forall ϕ).
Proof.
  intros H.
  unfold patt_forall.
  apply M_pre_pre_predicate_imp.
  2: {
    apply M_pre_predicate_bott.
  }
  apply M_pre_pre_predicate_exists.
  apply M_pre_pre_predicate_imp.
  { assumption. }
  { apply M_pre_pre_predicate_bott. }
Qed.

Lemma M_pre_predicate_forall {Σ : Signature} M ϕ :
  M_pre_predicate M ϕ ->
  M_pre_predicate M (patt_forall ϕ).
Proof.
  intros H.
  apply M_pre_pre_predicate_impl_M_pre_predicate with (k := 0).
  apply M_pre_pre_predicate_forall.
  apply H.
Qed.