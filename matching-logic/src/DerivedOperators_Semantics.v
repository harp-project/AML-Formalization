From Coq Require Import ssreflect ssrfun ssrbool.

Require Setoid.
From stdpp Require Import base sets propset.
From Coq Require Import Logic.Classical_Prop Logic.FunctionalExtensionality.
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
Import MatchingLogic.Substitution.Notations.
Import MatchingLogic.DerivedOperators_Syntax.Notations.

Section with_signature.
  Context {Σ : Signature}.
  Open Scope ml_scope.

  Section with_model.
    Context {M : Model}.

    Lemma eval_not_simpl : forall (ρ : Valuation) (phi : Pattern),
        @eval Σ M ρ (patt_not phi) = ⊤ ∖ (eval ρ phi).
    Proof.
      intros. unfold patt_not.
      rewrite -> eval_imp_simpl.
      rewrite -> eval_bott_simpl.
      set_solver by fail.
    Qed.

    Lemma eval_or_simpl : forall (ρ : Valuation) (phi1 phi2 : Pattern),
        eval ρ (patt_or phi1 phi2)
        = (eval ρ phi1) ∪ (@eval _ M ρ phi2).
    Proof.
      intros. unfold patt_or.
      rewrite -> eval_imp_simpl.
      rewrite -> eval_not_simpl.
      assert (H: ⊤ ∖ (⊤ ∖ (eval ρ phi1)) = eval ρ phi1).
      { apply Compl_Compl_propset. }
      rewrite -> H. reflexivity.
    Qed.

    Lemma eval_or_comm : forall (ρ : Valuation) (phi1 phi2 : Pattern),
        @eval Σ M ρ (patt_or phi1 phi2)
        = eval ρ (patt_or phi2 phi1).
    Proof.
      intros.
      repeat rewrite -> eval_or_simpl.
      set_solver by fail.
    Qed.

    Lemma eval_and_simpl : forall (ρ : Valuation)
                                                    (phi1 phi2 : Pattern),
        eval ρ (patt_and phi1 phi2)
        = (eval ρ phi1) ∩ (@eval _ M ρ phi2).
    Proof.
      intros. unfold patt_and.
      rewrite -> eval_not_simpl.
      rewrite -> eval_or_simpl.
      repeat rewrite -> eval_not_simpl.
      apply Compl_Union_Compl_Inters_propset_alt.
    Qed.

    Lemma eval_and_comm : forall (ρ : Valuation)
                                                   (phi1 phi2 : Pattern),
        @eval Σ M ρ (patt_and phi1 phi2)
        = eval ρ (patt_and phi2 phi1).
    Proof.
      intros.
      repeat rewrite -> eval_and_simpl.
      set_solver by fail.
    Qed.

    Lemma eval_top_simpl : forall (ρ : Valuation),
        @eval Σ M ρ patt_top = ⊤.
    Proof.
      intros. unfold patt_top.
      rewrite -> eval_not_simpl.
      rewrite -> eval_bott_simpl.
      set_solver by fail.
    Qed.

    (* TODO prove. Maybe some de-morgan laws could be helpful in proving this? *)
    Lemma eval_iff_or : forall (ρ : Valuation)
                                                 (phi1 phi2 : Pattern),
        @eval Σ M ρ (patt_iff phi1 phi2)
        = eval ρ (patt_or (patt_and phi1 phi2) (patt_and (patt_not phi1) (patt_not phi2))).
    Proof.

    Abort.

    Lemma eval_iff_comm : forall (ρ : Valuation)
                                                   (phi1 phi2 : Pattern),
        @eval Σ M ρ (patt_iff phi1 phi2)
        = eval ρ (patt_iff phi2 phi1).
    Proof.
      intros.
      unfold patt_iff.
      rewrite -> eval_and_comm.
      reflexivity.
    Qed.

    (* TODO: forall, nu *)

  Lemma eval_iff_simpl ρ phi1 phi2:
    @eval Σ M ρ (patt_iff phi1 phi2)
    = (⊤ ∖ eval ρ phi1 ∪ eval ρ phi2) ∩ (⊤ ∖ eval ρ phi2 ∪ eval ρ phi1).
  Proof.
    unfold patt_iff.
    by rewrite -> eval_and_simpl, -> eval_imp_simpl, -> eval_imp_simpl.
  Qed.

        (* if eval (phi1 ---> phi2) = Full_set,
           then eval phi1 subset eval phi2
        *)
    Lemma eval_iff_subset (ρ : Valuation)
          (phi1 : Pattern) (phi2 : Pattern) :
      eval ρ (phi1 ---> phi2)%ml = ⊤ <->
      (eval ρ phi1) ⊆
               (@eval _ M ρ phi2).
    Proof.
      rewrite -> elem_of_subseteq.
      rewrite -> eval_imp_simpl.
      remember (eval ρ phi1) as Xphi1.
      remember (eval ρ phi2) as Xphi2.
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
      M_predicate M (ϕ^{evar: 0 ↦ x}) -> M_predicate M (patt_forall ϕ).
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

    Lemma eval_set_builder ϕ ρ :
      let x := fresh_evar ϕ in
      M_predicate M (ϕ^{evar: 0 ↦ x}) ->
      (eval ρ (patt_exists (patt_and (patt_bound_evar 0) ϕ)))
      = PropSet
          (fun m : (Domain M) => eval (update_evar_val x m ρ) (ϕ^{evar: 0 ↦ x}) = ⊤).
    
    Proof.
      simpl. intros Hmp.
      rewrite -> eval_ex_simpl.
      unfold fresh_evar. simpl free_evars.
      repeat rewrite -> union_empty_r_L.
      rewrite -> union_empty_l_L.
      mlSimpl.
      remember (evar_fresh (elements (free_evars ϕ))) as x.
      apply set_eq_subseteq.
      rewrite 2!elem_of_subseteq.
      split; intros m H.
      - unfold propset_fa_union in H.
        rewrite -> elem_of_PropSet in H.
        destruct H as [m' H].
        rewrite -> eval_and_simpl in H.
        set_unfold in H.
        destruct H as [Hbound Hϕ].
        assert (Heqmm' : m = m').
        {
          cbn in Hbound.
          rewrite -> eval_free_evar_simpl in Hbound.
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
        rewrite -> eval_and_simpl. constructor.
        +
          cbn.
          rewrite -> eval_free_evar_simpl.
          rewrite -> update_evar_val_same. constructor.
        + rewrite -> elem_of_PropSet in H.
          rewrite -> set_eq_subseteq in H. destruct H as [H1 H2].
          rewrite -> elem_of_subseteq in H2.
          specialize (H2 m). apply H2. apply elem_of_top'.
    Qed.

    Lemma eval_forall_predicate ϕ ρ :
      let x := fresh_evar ϕ in
      M_predicate M (ϕ^{evar: 0 ↦ x}) ->
      eval ρ (patt_forall ϕ) = ⊤ <->
      ∀ (m : Domain M), eval (update_evar_val x m ρ) (ϕ^{evar: 0 ↦ x}) = ⊤.
    Proof.
      intros x H.
      unfold patt_forall.
      rewrite -> eval_not_simpl.

      assert (Hscfie : ⊤ ∖ ⊤ = @empty (propset (Domain M)) _) by apply difference_diag_L.
      rewrite -> complement_full_iff_empty.
      rewrite -> eval_exists_empty.

      assert (Hfr: fresh_evar (! ϕ)%ml = fresh_evar ϕ).
      { unfold fresh_evar,evar_fresh_s. apply f_equal. apply f_equal. simpl.
        rewrite -> union_empty_r_L. reflexivity.
      }

      rewrite -> Hfr. subst x.
      unfold evar_open.
      mlSimpl.
      split; intros H'.
      - intros m.
        specialize (H' m).
        rewrite -> eval_not_simpl in H'.
        rewrite -> complement_empty_iff_full in H'.
        exact H'.
      - intros m.
        specialize (H' m).
        rewrite -> eval_not_simpl.
        rewrite -> H'.
        rewrite Hscfie.
        reflexivity.
    Qed.


    Lemma eval_and_full ρ ϕ₁ ϕ₂:
      @eval Σ M ρ (patt_and ϕ₁ ϕ₂) = ⊤
      <-> (@eval Σ M ρ ϕ₁ = ⊤
           /\ @eval Σ M ρ ϕ₂ = ⊤).
    Proof.
      unfold Full.
      rewrite -> eval_and_simpl.
      split.
      - intros H.
        apply intersection_full_iff_both_full in H.
        apply H.
      - intros [H1 H2].
        rewrite H1. rewrite H2. set_solver.
    Qed.

    Lemma eval_predicate_not ρ ϕ :
      M_predicate M ϕ ->
      eval ρ (patt_not ϕ) = ⊤
      <-> @eval Σ M ρ ϕ <> ⊤.
    Proof.
      intros Hpred.
      rewrite eval_not_simpl.
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


  Lemma bcmcloseex_not (l : list (db_index * evar)) (p : Pattern):
    bcmcloseex l (patt_not p) = patt_not (bcmcloseex l p).
  Proof.
    unfold patt_not.
    rewrite bcmcloseex_imp.
    rewrite bcmcloseex_bott.
    reflexivity.
  Qed.

  Lemma bcmcloseex_all (l : list (db_index * evar)) (q : Pattern) :
    bcmcloseex l (all , q)%ml =
    (all , bcmcloseex (map (λ p : nat * evar, (S p.1, p.2)) l) q)%ml.
  Proof.
    unfold patt_forall.
    rewrite bcmcloseex_not.
    rewrite bcmcloseex_ex.
    rewrite bcmcloseex_not.
    reflexivity.
  Qed.

  Lemma M_pre_pre_predicate_forall (k : db_index) M ϕ :
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

  Lemma M_pre_predicate_forall M ϕ :
    M_pre_predicate M ϕ ->
    M_pre_predicate M (patt_forall ϕ).
  Proof.
    intros H.
    apply M_pre_pre_predicate_impl_M_pre_predicate with (k := 0).
    apply M_pre_pre_predicate_forall.
    apply H.
  Qed.

  Lemma eval_all_simpl
    (M : Model)
    (ρ : Valuation)
    (ϕ : Pattern)
    :
    eval ρ (patt_forall ϕ) =
    (let x := fresh_evar ϕ in
     propset_fa_intersection (λ e : Domain M,
      @eval _ M (update_evar_val x e ρ) (ϕ^{evar: 0 ↦ x})
     )
    ).
  Proof.
    unfold patt_forall.
    rewrite eval_not_simpl.
    rewrite eval_ex_simpl.
    simpl.
    unfold evar_open.
    mlSimpl.
    under [fun e => _]functional_extensionality => e
    do rewrite eval_not_simpl.
    unfold propset_fa_union,propset_fa_intersection.
    remember (fresh_evar (! ϕ)%ml) as x.
    remember (fresh_evar ϕ) as x'.
    under [fun e => _]functional_extensionality => e.
    {
      under [λ c, _]functional_extensionality => c.
      {
        rewrite (@eval_fresh_evar_open Σ M ϕ x x').
        {
          subst x. eapply evar_is_fresh_in_richer.
          2: { apply set_evar_fresh_is_fresh. }
          simpl. clear. set_solver.
        }
        {
          subst x'. apply set_evar_fresh_is_fresh.
        }
        over.
      }
      over.
    }
    clear.
    unfold_leibniz.
    set_unfold.
    intros x.
    split; intros H.
    {
      destruct_and!.
      intros x0.
      apply NNPP.
      intros HContra.
      apply H1.
      exists x0.
      split;[exact I|].
      apply HContra.
    }
    {
      split;[exact I|].
      intros [y [_ Hy] ]. 
      specialize (H y).
      contradiction.
    }
  Qed.

  Lemma challenge : forall (M : Model) ρ φ,
      @eval _ M ρ (patt_exists (patt_and (patt_bound_evar 0) φ) --->
                  (patt_forall ((patt_bound_evar 0) ---> φ))) = ⊤.
  Proof.
    intros.
    rewrite eval_imp_simpl eval_ex_simpl eval_all_simpl.
    simpl.
    mlSimpl.
    cbn.
    apply set_eq. split. set_solver.
    intros.
    apply elem_of_union.
    destruct (classic (x ∈ propset_fa_intersection
      (λ e : M,
         eval (update_evar_val (fresh_evar ((patt_bound_evar 0) ---> φ)) e ρ)
           (patt_free_evar (fresh_evar ((patt_bound_evar 0) ---> φ)) --->
            φ^{evar:0↦fresh_evar ((patt_bound_evar 0) ---> φ)})))).
    {
      right. assumption.
    }
    {
      left. apply elem_of_difference. split. set_solver.
      intro. apply H0. clear H0.
      remember (fresh_evar ((patt_bound_evar 0) and φ)) as y.
      remember (fresh_evar ((patt_bound_evar 0) ---> φ)) as z.
      assert (y = z).
      {
        subst. unfold fresh_evar. simpl.
        repeat rewrite union_empty_l_L.
        repeat rewrite union_empty_r_L.
        reflexivity.
      }
      rewrite -> H0 in *. clear Heqy H0.
      destruct H1.
      unfold propset_fa_intersection.
      rewrite eval_and_simpl in H0.
      apply elem_of_intersection in H0 as [H0_1 H0_2].
      apply elem_of_PropSet. intro. rewrite eval_imp_simpl eval_free_evar_simpl.
      rewrite update_evar_val_same.
      destruct (classic (x = c)).
      {
        apply elem_of_union_r. subst x.
        rewrite eval_free_evar_simpl in H0_1.
        rewrite update_evar_val_same in H0_1. assert (c = x0) by set_solver.
        by subst.
      }
      {
        set_solver.
      }
    }
  Qed.

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