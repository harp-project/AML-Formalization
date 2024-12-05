From Coq Require Import ssreflect ssrfun ssrbool.

Require Import Equations.Prop.Equations.

From Coq Require Import String Setoid.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.Classical_Prop.
From Coq.Logic Require Import FunctionalExtensionality Eqdep_dec.
From Coq.Classes Require Import Morphisms_Prop.
From Coq.Unicode Require Import Utf8.
From Coq.micromega Require Import Lia.

From MatchingLogic Require Import Logic ProofMode.MLPM Substitution DerivedOperators_Semantics.
From MatchingLogic.Theories Require Import Definedness_Syntax Definedness_ProofSystem FOEquality_ProofSystem DeductionTheorem Definedness_Semantics.
From MatchingLogic.Utils Require Import stdpp_ext.

Require Import MatchingLogic.wftactics.

From stdpp Require Import base fin_sets sets propset proof_irrel option list tactics.

Import extralibrary.

Import MatchingLogic.Logic.Notations.
Import MatchingLogic.Theories.Definedness_Syntax.Notations.

Require Import Experimental.Unification.

Set Default Proof Mode "Classic".

Close Scope equations_scope. (* Because of [!] *)

Open Scope ml_scope.
Open Scope string_scope.
Open Scope list_scope.

Section MatchingEquivs.
  Context {Σ : Signature} {syntax : Syntax}.

  Context (Γ : Theory).
  Hypothesis (HΓ : theory ⊆ Γ).

  Lemma predicate_iff φ₁ φ₂ :
well_formed φ₁ ->
    well_formed φ₂ ->
    Γ ⊢ is_predicate_pattern φ₁ --->
        is_predicate_pattern φ₂ --->
        is_predicate_pattern (φ₁ <---> φ₂).
  Proof.
    intros Hwfφ₁ Hwfφ₂.
    toMLGoal. simpl. unfold is_predicate_pattern. wf_auto2.
    do 2 mlIntro.
    unfold patt_iff.
    opose proof* (predicate_and Γ (φ₁ ---> φ₂) (φ₂ ---> φ₁));
    [auto | wf_auto2 .. |].
    opose proof* (predicate_imp Γ φ₁ φ₂); auto.
    opose proof* (predicate_imp Γ φ₂ φ₁); auto.
mlAdd H. mlAdd H0. mlAdd H1. clear H H0 H1.
    mlAssert ("0dup" : (is_predicate_pattern φ₁)).
    wf_auto2. mlExact "0".
    mlAssert ("1dup" : (is_predicate_pattern φ₂)).
    wf_auto2. mlExact "1".
    mlApply "3" in "0". mlApply "0" in "1".
    mlApply "4" in "1dup". mlApply "1dup" in "0dup".
    mlApply "2" in "1". mlApply "1" in "0dup".
    mlExact "0dup".
  Defined.

  Lemma extract_common_from_equality_r_2 a b p :
    well_formed a -> well_formed b -> well_formed p ->
    Γ ⊢ is_predicate_pattern p --->
    (p ---> a =ml b) <---> (a and p) =ml (b and p).
  Proof.
    intros Hwfa Hwfb Hwfp.
    mlIntro.
    mlSplitAnd; mlIntro.
    - 
      assert (Γ ⊢ is_predicate_pattern (a =ml b)). {
        unfold patt_equal.
        mlFreshEvar as x.
        mlFreshEvar as y.
        mlFreshEvar as z.
        apply (floor_is_predicate Γ (a <---> b) AnyReasoning x y z).
        auto. wf_auto2. fm_solve. fm_solve. fm_solve. try_solve_pile.
      }
      opose proof* (predicate_imp Γ p (a =ml b));
      [auto .. | wf_auto2 |].
      mlAdd H. mlAdd H0. clear H H0.
      mlApply "3" in "0". mlApply "0" in "2". mlClear "0". mlClear "3".
      opose proof* (predicate_equiv Γ (p ---> a =ml b)).
      auto. wf_auto2.
      mlApplyMeta H in "2". mlDestructAnd "2". mlApply "0" in "1".
      mlClear "0". mlClear "3".
      mlFreshEvar as x.
      mlDeduct "1".
      remember (ExGen := _, SVSubst := _, KT:= _, AKT := _) as i.
      remember (_ ∪ _ : Theory) as Γ'.
      opose proof* (hypothesis Γ' (p ---> a =ml b)).
      wf_auto2. set_solver.
      use i in H0.
      opose proof* (total_phi_impl_phi Γ' (a <---> b) x).
      set_solver. fm_solve. wf_auto2.
      use i in H1.
      epose proof syllogism_meta _ _ _ H0 H1.
      pose proof extract_common_from_equivalence_r Γ' _ _ _ i Hwfp Hwfa Hwfb.
      epose proof pf_iff_proj2 _ _ _ _ _ _ H3.
      pose proof MP H2 H4.
      mlRewrite H5 at 1. mlReflexivity.
      Unshelve.
      subst i. simpl.
      admit. (* TODO: revise definedness to make solvable *)
      all: wf_auto2.
    -
      mlIntro.
      mlApplyMeta (predicate_equiv _ _ HΓ Hwfp) in "0".
      mlDestructAnd "0". mlApply "3" in "2".
      mlClear "3". mlClear "4".
      epose proof patt_total_and _ _ _ HΓ _ _.
      use AnyReasoning in H.
      epose proof pf_iff_proj2 _ _ _ _ _ _ H.
      mlConj "1" "2" as "0".
      mlApplyMeta H0 in "0".
      clear H H0. mlClear "1". mlClear "2".
      mlDeduct "0".
      remember (ExGen := _, SVSubst := _, KT:= _, AKT := _) as i.
      remember (_ ∪ _ : Theory) as Γ'.
      opose proof* (hypothesis Γ' (((a and p <---> b and p) and p))).
      wf_auto2. set_solver. use i in H.
      pose proof extract_common_from_equivalence_r Γ' _ _ _ i Hwfp Hwfa Hwfb.
      epose proof pf_iff_proj1 Γ' _ _ i _ _ H0.
      epose proof lhs_from_and Γ' _ _ _ i _ _ _ H1.
      pose proof MP H H2.
      mlRewrite H3 at 1.
      mlReflexivity.
      Unshelve.
      all: wf_auto2.
  Admitted.

  Lemma valami : forall l ti,
    well_formed (ex, l) ->
    well_formed ti ->
    mu_free l ->
    (forall x, Γ ⊢ is_functional l^{evar: 0 ↦ x}) ->
    Γ ⊢ is_functional ti ->
    Γ ⊢ (ex, (l =ml ti)) <---> ti ∈ml (ex, l).
  Proof.
    intros * wfl wfti mfl fpl fpti.
    mlFreshEvar as y.
    assert (y ∉ free_evars l ∪ free_evars ti)
      by (ltac2:(_fm_export_everything ()); set_solver).
    assert (forall x, ti^{evar:0↦x} = ti)
      by (intros; apply evar_open_not_occur; wf_auto2).
    mlSplitAnd; mlIntro.
    1: unshelve mlApplyMeta membership_exists_2; auto.
    2: unshelve mlApplyMeta membership_exists_1 in "0"; auto.
    all: mlDestructEx "0" as x; mlExists x.
    all: mlSimpl; rewrite ! H0.
    -
      mlRewriteBy "0" at 1.
      mlApplyMeta membership_refl.
      mlExactMeta fpti. auto.
    -
      opose proof* (membership_imp_equal Γ ti (l^{evar:0↦x})); auto.
      now apply mu_free_bevar_subst. wf_auto2.
      pose proof (MP fpti H1); clear H1.
      pose proof (MP (fpl x) H2); clear H2.
      mlSymmetry. now fromMLGoal.
  Defined.

  Fixpoint functional_when_applied (n : nat) (φ : Pattern) :=
    match n with
    | 0 => derives Γ (is_functional φ)
    | S m => forall x, functional_when_applied m (evar_open x 0 φ)
    end.

  Fixpoint many_ex_l (n : nat) (φ : Pattern) :=
    match n with
    | 0 => φ
    | S m => ex, many_ex_l m φ
    end.

  Fixpoint many_ex_r (n : nat) (φ : Pattern) :=
    match n with
    | 0 => φ
    | S m => many_ex_r m (ex, φ)
    end.

  Eval simpl in functional_when_applied 3 Top.

  Lemma many_ex_l_travels n : forall φ, (ex, many_ex_l n φ) = many_ex_l n (ex, φ).
  Proof.
    induction n; simpl; intros.
    reflexivity.
    rewrite IHn. reflexivity.
  Defined. 

  Lemma many_ex_r_travels n : forall φ, (ex, many_ex_r n φ) = many_ex_r n (ex, φ).
  Proof.
    induction n; simpl; intros.
    reflexivity.
    rewrite IHn. reflexivity.
  Defined.

  Lemma many_ex_lr n φ : many_ex_l n φ = many_ex_r n φ.
  Proof.
    induction n; simpl.
    reflexivity.
    rewrite IHn.
    apply many_ex_r_travels.
  Defined.

  Lemma many_ex_lr_equiv P n φ : P (many_ex_l n φ) <-> P (many_ex_r n φ).
  Proof.
    rewrite many_ex_lr. auto.
  Defined.

  Lemma well_formed_many_ex n : ∀ m φ,
    m <= n ->
    well_formed_closed_ex_aux φ m ->
    well_formed_closed_mu_aux φ 0 ->
    well_formed_positive φ ->
    well_formed (many_ex_r n φ).
  Proof.
    induction n; simpl; intros.
    inversion H; subst. wf_auto2.
    inversion H; subst.
    apply well_formed_closed_ex_all in H0.
    apply (IHn n (ex, φ)).
    reflexivity. 1-3: wf_auto2.
    apply (IHn m (ex, φ)).
    auto. 1-3: wf_auto2.
  Defined.

  Lemma free_evars_many_ex n φ : free_evars (many_ex_l n φ) = free_evars φ.
  Proof.
    now induction n.
  Defined.

  Lemma many_ex_subst n x φ : ∀ m, (many_ex_l n φ)^{evar:m↦x} = many_ex_l n (φ^{evar:m + n↦x}).
  Proof.
    induction n; simpl; intros.
    f_equal. auto.
    mlSimpl. rewrite (IHn (S m)). do 3 f_equal. auto.
  Defined.

  Lemma membership_many_ex n φ φ' :
    well_formed φ -> well_formed φ' ->
    Γ ⊢ φ ∈ml (many_ex_l n φ') <---> many_ex_l n (φ ∈ml φ').
  Proof.
    intros Hwfφ Hwfφ'.
    induction n; simpl.
    aapply pf_iff_equiv_refl. wf_auto2.
    assert (∀ p, well_formed p -> well_formed (many_ex_l n p)) as Hwfmexln. {
      intros * Hwfp.
      apply many_ex_lr_equiv. apply well_formed_many_ex with (m := 0).
      lia. all: wf_auto2.
    }
    specialize (Hwfmexln φ' Hwfφ') as Hwfmexlnφ'.
    specialize (Hwfmexln (φ ∈ml φ') ltac:(wf_auto2)).
    mlFreshEvar as y.
    opose proof (membership_exists Γ φ y (many_ex_l n φ') AnyReasoning HΓ _ _ _ _).
    1-2: wf_auto2.
    rewrite (free_evars_many_ex n φ'). ltac2:(fm_solve ()).
    try_solve_pile.
    toMLGoal. wf_auto2.
    mlRewrite H at 1.
    mlRewrite IHn at 1.
    mlReflexivity.
  Defined.

  (* Goal forall n m φ φ', *)
  (*   m <= n -> *)
  (*   well_formed_closed_ex_aux φ m -> *)
  (*   well_formed_closed_mu_aux φ 0 -> *)
  (*   well_formed_positive φ -> *)
  (*   well_formed_closed_ex_aux φ' m -> *)
  (*   well_formed_closed_mu_aux φ' 0 -> *)
  (*   well_formed_positive φ' -> *)
  (*   Γ ⊢ φ <---> φ' -> *)
  (*   Γ ⊢ many_ex_l n φ <---> many_ex_l n φ'. *)
  (* Proof. *)
  (*   induction n; simpl; intros. *)
  (*   - *)
  (*     assumption. *)
  (*   - *)
  (*     (1* apply le_lt_eq_dec in H as []. shelve. *1) *)
  (*     (1* subst. *1) *)
  (*     toMLGoal. shelve. *)
  (*     mlFreshEvar as y. *)
  (*     mlSplitAnd; mlIntro. *)
  (*     * *)
  (*       epose proof (MLGoal_destructEx Γ [] [] (ex, many_ex_l n φ') y "1" (many_ex_l n φ) AnyReasoning _ _ _ _ _). *)
  (*       simpl in X. apply X. clear X. *)
  (*       mlExists y. *)
  (*       rewrite ! many_ex_subst. *)
  (*       simpl. *)
  (*       ospecialize (IHn (φ^{evar:n↦y}) (φ'^{evar:n↦y}) _). shelve. *)
  (*       apply pf_iff_proj1 in IHn. mlApplyMeta IHn. mlAssumption. *)
  (*       shelve. shelve. *)
  (*     * *)
  (*       epose proof (MLGoal_destructEx Γ [] [] (ex, many_ex_l n φ) y "1" (many_ex_l n φ') AnyReasoning _ _ _ _ _). *)
  (*       simpl in X. apply X. clear X. *)
  (*       mlExists y. *)
  (*       rewrite ! many_ex_subst. *)
  (*       simpl. *)
  (*       ospecialize (IHn (φ'^{evar:n↦y}) (φ^{evar:n↦y}) _). shelve. *)
  (*       apply pf_iff_proj1 in IHn. mlApplyMeta IHn. mlAssumption. *)
  (*       shelve. shelve. *)
  (* Abort. *)



  Tactic Notation "aepose" "proof" uconstr(prf) "using" constr(pi) :=
    let H := fresh in epose proof prf as H; use pi in H.

  Tactic Notation "aepose" "proof" uconstr(prf) :=
    match goal with
    | [ |- of_MLGoal (mkMLGoal _ _ _ _ ?pi) ] => aepose proof prf using pi
    | [ |- derives_using _ _ ?pi ] => aepose proof prf using pi
    | [ |- derives _ _ ] => aepose proof prf using AnyReasoning
    end.

  (* Goal forall M ρ l ti, (∀ x p, ti^{evar:x↦p} = ti) -> free_evars ti = ∅ -> @eval _ M ρ ((ex , l =ml ti) <---> (ex , l) =ml ti) = ⊤. *)
  (* Proof. *)
  (*   intros. *)
  (*   rewrite ! eval_simpl. simpl. mlSimpl. *)
  (*   rewrite ! H. *)
  (*   rewrite ! union_empty_r_L. *)
  (*   rewrite ! Compl_Compl_propset. *)
  (*   assert (fresh_evar (l =ml ti) = fresh_evar l). { *)
  (*     intros. *)
  (*     unfold fresh_evar. simpl. *)
  (*     rewrite ! H0 ! union_empty_l_L ! union_empty_r_L. *)
  (*     f_equal. set_solver. *)
  (*   } *)
  (*   rewrite ! H1. *)
  (*   pose (λ p, propset_fa_union (λ e, eval (update_evar_val (fresh_evar l) e ρ) p)) as f. *)
  (*   repeat match goal with [ |- context[propset_fa_union (λ e, eval (update_evar_val (fresh_evar l) e ρ) ?p)] ] => fold (f p) end. *)
  (*   apply complement_full_iff_empty. *)
  (*   assert (∀ X Y : propset M, X ∪ Y = ∅ <-> X = ∅ /\ Y = ∅) by set_solver. *)
  (*   apply H2. split. *)
  (*   all: apply complement_empty_iff_full. *)
  (*   assert (forall X Y : propset M, ⊤ ∖ X ∪ ⊤ ∖ Y = ⊤ ∖ (X ∩ Y)). { *)
  (*     intros. set_unfold. *)
  (*     split; intros. *)
  (*     split. auto. *)
  (*     intros []. *)
  (*     destruct H3 as [ [_ ?] | [_ ?] ]. *)
  (*     1-2: contradiction. *)
  (*     Search elem_of propset. *)
  (*     epose proof elem_of_PropSet (propset_car X) x. *)
  (*     Search Prop "dec". *)
  (*   assert (forall X Y : propset M, ⊤ ∖ X ∪ ⊤ ∖ Y = ⊤ <-> X ## Y). { *)
  (*     intros. *)
  (*     set_unfold. *)
  (*     Search disjoint. *)
  (*     split; intros. *)
  (*     specialize (H3 x) as [_ ?]. *)
  (*     specialize (H3 I) as [ [_ ?] | [_ ?] ]. *)
  (*     1-2: contradiction. *)
  (*     Search (_ -> _ -> False). *)
  (*     Search (_ /\ _ -> False). *)
  (*     Search elem_of propset. *)
  (* Abort. *)




  (* Goal forall l ti n m, *)
  (*   m <= n -> *)
  (*   well_formed_closed_ex_aux l m -> *)
  (*   well_formed_closed_mu_aux l 0 -> *)
  (*   well_formed_positive l -> *)
  (*   well_formed ti -> *)
  (*   (1* mu_free l -> *1) *)
  (*   (1* functional_when_applied n l -> *1) *)
  (*   (1* Γ ⊢ is_functional ti -> *1) *)
  (*   Γ ⊢ many_ex_r n (ex , l =ml ti) <---> many_ex_r n ((ex , l) =ml ti). *)
  (* Proof. *)
  (*   intros * Hmlen Hwfceal Hwfcmal Hwfpl Hwfti. *)
  (*   pose proof (evar_open_closed ti ltac:(wf_auto2)). *)
  (*   generalize dependent l. *)
  (*   generalize dependent m. *)
  (*   induction n; simpl; intros. *)
  (*   - *)
      (* assert (∀ a b, Γ ⊢ ! a <---> ! b -> Γ ⊢ a <---> b). { *)
      (*   intros. *)
      (*   apply extract_wfp in H0 as ?. *)
      (*   apply extract_wfq in H0 as ?. *)
      (*   toMLGoal. wf_auto2. *)
      (*   mlSplitAnd; mlIntro; *)
      (*   [apply pf_iff_proj2 in H0 | apply pf_iff_proj1 in H0]; *)
      (*   auto; *)
      (*   [opose proof (P4 Γ b a _ _) | opose proof (P4 Γ a b _ _)]; *)
      (*   try solve [wf_auto2]; *)
      (*   use AnyReasoning in H3; *)
      (*   mlApplyMeta (MP H0 H3) in "0"; mlAssumption. *)
      (* } *)
      (* apply H0. *)
      (* unfold patt_equal, patt_total. *)




      (* Search patt_defined patt_total. *)
      (* Search patt_iff patt_not. *)
      (* match goal with [ |- context[?a <---> ?b] ] => pose proof (not_not_eq Γ a); pose proof (not_not_eq Γ b) end. *)
      (* specialize (H0 ltac:(wf_auto2)). *)
      (* specialize (H1 ltac:(wf_auto2)). *)
      (* apply pf_iff_equiv_sym in H0. 2-3: wf_auto2. *)
      (* use AnyReasoning in H0. *)
      (* use AnyReasoning in H1. *)
      (* apply pf_iff_equiv_trans with (4 := H0). *)
      (* 1-3: wf_auto2. *)
      (* apply pf_iff_equiv_trans with (5 := H1). *)
      (* 1-3: wf_auto2. *)
      (* Search patt_defined patt_exists. *)




      (* toMLGoal. inversion Hmlen; subst. wf_auto2. *)
      (* mlSplitAnd; mlIntro. *)
      (* mlDestructEx "0" as x. *)
      (* mlSimpl. rewrite H. *)
      (* mlSymmetry in "0". *)
      (* mlRewriteBy "0" at 1. *)
      (* mlClear "0". fromMLGoal. *)
      (* Search patt_total. *)
      (* apply phi_impl_total_phi_meta. *)
      (* wf_auto2. try_solve_pile. *)
      (* toMLGoal. wf_auto2. *)
      (* mlSplitAnd; mlIntro. *)
      (* mlFreshEvar as y. *)
      (* opose proof (MLGoal_destructEx Γ [] [] (l^{evar:0↦x}) y "0" l AnyReasoning _ _ _ _ _). *)
      (* try_solve_pile. *)
      (* ltac2:(fm_solve ()). *)
      (* ltac2:(fm_solve ()). *)
      (* ltac2:(fm_solve ()). *)
      (* Search free_evars evar_open. *)
      (* ltac2:(fm_solve ()). *)
  (* Abort. *)

  Goal forall φ n, functional_when_applied (S n) φ -> functional_when_applied n (ex, φ).
  Proof.
    induction n; simpl.
    intros. unfold is_functional in *.
    toMLGoal. admit.
    mlFreshEvar as y.
    (* mlExists y. mlSimpl. unfold evar_open at 2. simpl. *)
    specialize (H y).
    mlAdd H.
    mlFreshEvar as z.
    assert (∀ X : EVarSet, X ∪ X = X) by set_solver.
    opose proof (MLGoal_destructEx Γ [] [] (ex , (ex , φ) =ml b0) z "0" (φ^{evar:0↦y} =ml b0) AnyReasoning _ _ _ _ _).
    try_solve_pile.
    ltac2:(fm_solve ()).
    ltac2:(fm_solve ()).
    simpl. rewrite ! union_empty_l_L ! union_empty_r_L H0.
    apply evar_open_fresh_notin.
    ltac2:(fm_solve ()).
    ltac2:(fm_solve ()).
    ltac2:(fm_solve ()).
    simpl. rewrite ! union_empty_l_L ! union_empty_r_L H0.
    (* apply evar_open_fresh_notin. *)
    (* repeat (apply not_elem_of_union; split). *)
    (* 1,4: apply evar_open_fresh_notin. *)
    (* ltac2:(fm_solve ()). *)
    (* ltac2:(fm_solve ()). *)
    (* ltac2:(fm_solve ()). *)
    (* ltac2:(fm_solve ()). *)
    (* ltac2:(fm_solve ()). *)
    (* ltac2:(fm_solve ()). *)
    (* ltac2:(fm_solve ()). *)
    ltac2:(fm_solve ()).
    apply X. simpl. mlSimpl. unfold evar_open at 3. simpl.
    mlExists z. mlSimpl. unfold evar_open at 4. simpl.
    mlSymmetry in "0". mlRewriteBy "0" at 1. mlClear "0".
  Abort.


  (* Lemma func_applied_drop_high : forall n l y, *)
  (*   functional_when_applied (S n) l → functional_when_applied n l^{evar:n↦y}. *)
  (* Proof. *)
  (*   induction n; intros. *)
  (*   apply H. *)
  (*   simpl. intro. *)
  (*   rewrite evar_open_comm_higher. lia. simpl. *)
  (*   apply IHn. exact (H x). *)
  (* Defined. *)

  Lemma fwa_drop_one : forall n m l y,
    m <= n ->
    functional_when_applied (S n) l → functional_when_applied n l^{evar:m↦y}.
  Proof.
    induction n; intros.
    apply Nat.le_0_r in H. subst. apply H0.
    simpl. intro.
    compare m 0; intro.
    subst. simpl in H0. specialize (H0 y x). auto.
    rewrite evar_open_comm_higher. lia.
    apply IHn. lia. exact (H0 x).
  Defined.

  Goal ∀ n m l,
    m ≤ n ->
    well_formed_closed_ex_aux l m ->
    functional_when_applied m l ->
    functional_when_applied n l.
  Proof.
    induction n; intros.
    apply Nat.le_0_r in H as ->. assumption.
    apply le_lt_eq_dec in H as [| ->].
    2: auto.
    unfold lt in l0. apply le_S_n in l0.
    simpl. intro.
    pose proof evar_open_wfc_aux m n x l l0 H0.
  Abort.

  Tactic Notation "decide_le" hyp(Hle) :=
    apply le_lt_eq_dec in Hle as [Hle%Arith_prebase.lt_n_Sm_le | ->].

  Goal ∀ m n l y,
    m ≤ S n ->
    well_formed_closed_ex_aux l m ->
    functional_when_applied m l ->
    functional_when_applied n l^{evar:n↦y}.
  Proof.
    intros.
    decide_le H.
    2: now apply fwa_drop_one.
    pose proof evar_open_wfc_aux m n y l H H0 as ->.
    clear H0. generalize dependent m. induction n; intros.
    now apply Nat.le_0_r in H as ->.
    decide_le H.
    2: auto.
  Abort.

  Goal forall l ti n m,
    m <= n ->
    well_formed_closed_ex_aux l m ->
    well_formed_closed_mu_aux l 0 ->
    well_formed_positive l ->
    well_formed ti ->
    mu_free l ->
    functional_when_applied m l ->
    Γ ⊢ is_functional ti ->
    Γ ⊢ (many_ex_r n (l =ml ti)) <---> ti ∈ml (many_ex_r n l).
    (* Γ ⊢ (ti =ml (many_ex_r n l)) <---> ti ∈ml (many_ex_r n l). *)
    (* (exists x1...xn, l = ti) <---> ti ∈ (exists x1...xn, l) *)
  Proof.
    intros * Hmlen Hwfceal Hwfcmal Hwfpl Hwfti Hmfl Hfpl Hfpti.
    generalize dependent l.
    generalize dependent m.
    induction n; simpl; intros.
    -
      apply Nat.le_0_r in Hmlen; subst. simpl in Hfpl.
      epose proof membership_equal_equal Γ ti l HΓ Hmfl Hwfti ltac:(wf_auto2) Hfpti Hfpl.
      toMLGoal. wf_auto2.
      mlAdd H.
      mlRewriteBy "0" at 1.
      mlSplitAnd; mlIntro.
      mlSymmetry; mlAssumption.
      mlSymmetry; mlAssumption.
    -
      rewrite -! many_ex_r_travels.
      mlFreshEvar as y.
      opose proof (membership_exists Γ ti y (many_ex_r n l) AnyReasoning HΓ _ _ _ _).
      rewrite many_ex_r_travels.
      replace (many_ex_r n (ex, l)) with (many_ex_r (S n) l) by reflexivity.
      eapply well_formed_many_ex; eauto.
      auto.
      epose proof (free_evars_many_ex n l) as ->%many_ex_lr_equiv.
      ltac2:(fm_solve ()).
      try_solve_pile.
      apply pf_iff_equiv_sym in H.
      eapply pf_iff_equiv_trans with (5 := H).
      4: toMLGoal.
      4: simpl; apply well_formed_iff.
      all: try solve [(eapply extract_wfp + eapply extract_wfq); eauto].
      1,2: rewrite many_ex_r_travels; eapply well_formed_many_ex; only 1,5: reflexivity; wf_auto2.
      eassert (∀ p : Pattern, _) as ?H. {
        intro.
        pose proof free_evars_many_ex n p.
        apply many_ex_lr_equiv in H0.
        exact H0.
      }
      eassert (∀ p : Pattern, _) as ?H. {
        intro.
        pose proof many_ex_subst n y p 0.
        rewrite ! many_ex_lr in H1.
        exact H1.
      }
      mlSplitAnd; mlIntro;
      apply (MLGoal_destructEx Γ [] [] _ y "0" _ AnyReasoning);
      simpl; try rewrite H0.
      1,7: try_solve_pile.
      ltac2:(fm_solve ()).
      ltac2:(fm_solve ()).
      ltac2:(fm_solve ()).
      ltac2:(fm_solve ()).
      2: ltac2:(fm_solve ()).
      2: ltac2:(fm_solve ()).
      2: ltac2:(fm_solve ()).
      2: ltac2:(fm_solve ()).
      all: mlExists y; mlSimpl;
      rewrite ! H1; mlSimpl;
      rewrite ! (evar_open_wfc_aux 0 _ y ti);
      try solve [lia | wf_auto2];
      replace (0 + n) with n by reflexivity;
      decide_le Hmlen.
      1,3: rewrite ! (evar_open_wfc_aux m n); auto; specialize (IHn m Hmlen l Hwfceal Hwfcmal Hwfpl Hmfl Hfpl).
      3,4: ospecialize (IHn n _ l^{evar:n↦y} _ _ _ _ _); auto; [now apply mu_free_evar_open | now apply fwa_drop_one |].
      1,3: apply pf_iff_proj1 in IHn.
      7,8: apply pf_iff_proj2 in IHn.
      all: try solve [(eapply extract_wfp + eapply extract_wfq); eauto]; mlApplyMeta IHn in "0"; mlAssumption.
  Defined.
        

      (* ospecialize (IHn n _ (l^{evar:n↦y}) _ _ _ _ _). *)
      (* only 6,13: shelve; *)
      (* (1* try apply fwa_drop_one; *1) *)
      (* try solve [auto | now apply mu_free_evar_open | wf_auto2]. *)
      (* apply pf_iff_proj1 in IHn. *)
      (* 4: apply pf_iff_proj2 in IHn. *)
      (* all: try solve [(eapply extract_wfp + eapply extract_wfq); eauto]; *)
      (* mlApplyMeta IHn in "0"; mlAssumption. *)
      (* pose proof many_ex_subst. *)
      

      (* ospecialize (IHn n _ (ex, l) _ _ _ _ _). *)
      (* lia. 1-3: wf_auto2. auto. *)

      
      (* unfold functional_when_applied, is_functional. *)
      (* pose proof valami. *)
      (* Search patt_imp patt_exists. *)



      (* 8: subst; ospecialize (IHn n _ (ex, l) _ _ _ _ _). *)
      (* 1,8: lia. *)
      (* 1-3,7-9: wf_auto2. *)
      (* 1,4: auto. *)
      (* 1,3: shelve. *)
      (* toMLGoal. *)
      (* 3: toMLGoal. *)
      (* 1,3: apply well_formed_iff, well_formed_in; auto; eapply well_formed_many_ex; wf_auto2. *)
      (* all: apply pf_iff_equiv_sym_meta in IHn; *)
      (* mlRewrite IHn at 1; *)
      (* clear IHn. *)
      (* fromMLGoal. *)
      (* 2: fromMLGoal. *)
      (* generalize dependent l. *)
      (* induction n; simpl in *; intros. *)
      (* * *)
      (*   aepose proof (patt_equal_comm (ex, l) ti Γ HΓ ltac:(wf_auto2) Hwfti). *)
      (*   mlRewrite H at 1. *)
      (*   epose proof (membership_equal_equal Γ ti (ex, l) HΓ Hmfl Hwfti ltac:(wf_auto2) Hfpti _). *)
      (*   mlAdd H0. *)
      (*   mlSymmetry in "0". *)
      (*   mlRewriteBy "0" at 1. *)
      (*   mlFreshEvar as y. *)
      (*   epose proof (membership_exists Γ ti y l AnyReasoning HΓ _ Hwfti _ _). *)
      (*   mlRewrite H1 at 1. *)
      (*   epose proof (membership_equal_equal Γ ti l HΓ Hmfl Hwfti _ Hfpti _). *)
      (*   mlAdd H2. *)
      (*   mlRewriteBy "1" at 1. *)
      (*   mlSplitAnd; mlIntro. *)
      (*   mlDestructEx "2" as x. *)
      (*   mlExists x. *)
      (*   mlSimpl. mlSymmetry. mlAssumption. *)
      (*   mlDestructEx "2" as x. *)
      (*   mlExists x. *)
      (*   mlSimpl. mlSymmetry. mlAssumption. *)
      (* * *)
      (*   rewrite <- many_ex_r_travels. *)
      (*   rewrite <- (many_ex_r_travels n ((ex, l) =ml ti)). *)
      (*   toMLGoal. shelve. *)
      (*   mlSplitAnd; mlIntro. *)
      (*   mlFreshEvar as x. *)
      (*   opose proof (MLGoal_destructEx Γ [] [] (ex, many_ex_r n ((ex, l) =ml ti)) x "0" (many_ex_r n (ex, l =ml ti)) AnyReasoning _ _ _ _ _). *)
      (*   try_solve_pile. *)
      (*   ltac2:(fm_solve ()). *)
      (*   ltac2:(fm_solve ()). *)
      (*   pose proof free_evars_many_ex n (ex, l =ml ti) as ->%many_ex_lr_equiv. ltac2:(fm_solve ()). *)
      (*   simpl. pose proof free_evars_many_ex n ((ex, l) =ml ti) as ->%many_ex_lr_equiv. ltac2:(fm_solve ()). *)
      (*   apply X. clear X. simpl. mlExists x. *)
      (*   do 2 rewrite <- many_ex_lr. *)
      (*   rewrite ! many_ex_subst ! many_ex_lr. *)
      (*   mlSimpl. *)
      (*   epose proof evar_open_closed ti ltac:(wf_auto2). *)
      (*   rewrite ! H. *)
      (*   ospecialize (IHn (l^{evar:S n↦x}) _ _ _ _ _). *)
      (*   shelve. *)
      (*   1,2: wf_auto2. *)
      (*   now apply mu_free_evar_open. *)
      (*   shelve. *)
      (*   apply pf_iff_proj1 in IHn. mlApplyMeta IHn in "0". *)
      (*   mlAssumption. *)
      (*   1-2: shelve. *)

      (*   mlFreshEvar as x. *)
      (*   opose proof (MLGoal_destructEx Γ [] [] (ex, many_ex_r n (ex, l =ml ti)) x "0" (many_ex_r n ((ex,l) =ml ti)) AnyReasoning _ _ _ _ _). *)
      (*   try_solve_pile. *)
      (*   ltac2:(fm_solve ()). *)
      (*   ltac2:(fm_solve ()). *)
      (*   pose proof free_evars_many_ex n ((ex,l) =ml ti) as ->%many_ex_lr_equiv. ltac2:(fm_solve ()). *)
      (*   simpl. pose proof free_evars_many_ex n (ex, l =ml ti) as ->%many_ex_lr_equiv. ltac2:(fm_solve ()). *)
      (*   apply X. clear X. simpl. *)
      (*   mlExists x. *)
      (*   do 2 rewrite <- many_ex_lr. *)
      (*   rewrite ! many_ex_subst ! many_ex_lr. *)
      (*   mlSimpl. *)
      (*   epose proof evar_open_closed ti ltac:(wf_auto2). *)
      (*   rewrite ! H. *)
      (*   ospecialize (IHn (l^{evar:S n↦x}) _ _ _ _ _). *)
      (*   1-3: wf_auto2. *)
      (*   now apply mu_free_evar_open. *)
      (*   shelve. *)
      (*   apply pf_iff_proj2 in IHn. *)
      (*   mlApplyMeta IHn in "0". mlAssumption. *)
      (*   Unshelve. *)
      (*   eapply well_formed_many_ex. *)
      (*   3,4: wf_auto2. *)
        
        



      (* enough (Γ ⊢ (ex, l =ml ti) <---> ((ex, l) =ml ti)). *)
      (* mlFreshEvar as y. *)
      (* opose proof (prf_equiv_congruence _ _ _ {| pcEvar := y; pcPattern := many_ex_r n (patt_free_evar y) |} _ _ _ _ _ H). *)
      (* 1-3: try solve [wf_auto2]. *)
      (* Search patt_exists well_formed_closed_ex_aux. *)



      (* assert (Γ ⊢ (ex , many_ex n (ti =ml l)) <---> (ex , ti ∈ml many_ex n l)). *)
      (* toMLGoal. admit. *)
      (* mlSplitAnd; mlIntro. *)
      (* pose proof free_evars_many_ex. *)
      (* mlFreshEvar as x. *)
      (* opose proof (MLGoal_destructEx Γ [] [] (ex, ti ∈ml many_ex n l) x "0" (many_ex n (ti =ml l)) AnyReasoning _ _ _ _ _). *)
      (* try_solve_pile. *)
      (* 1,2: now set_unfold. *)
      (* 1,2: simpl; rewrite free_evars_many_ex. *)
      (* (1* Again, sequencing doesn't work *1) *)
      (* ltac2:(fm_solve ()). *)
      (* ltac2:(fm_solve ()). *)
      (* apply X. clear X. simpl. *)
      (* mlExists x. *)
      (* mlSimpl. rewrite ! many_ex_subst. mlSimpl. simpl. *)

      

      (* Search patt_exists "quan". *)
      (* Search patt_exists patt_iff. *)

  (* Abort. *)

  Fixpoint many_ex (n : nat) (φ : Pattern) :=
    match n with
    | 0 => φ
    | S m => many_ex m (ex, φ)
    end.

  (* Goal forall φ, *)
  (*   mu_free φ -> *)
  (*   well_formed_closed_ex_aux φ 0 -> *)
  (*   well_formed φ. *)
  (* Proof. *)
  (*   induction φ; intros Hmf Hwfcea; *)
  (*   unfold well_formed; apply andb_true_iff; split; *)
  (*   unfold well_formed_closed; try apply andb_true_iff; *)
  (*   repeat split; auto. *)
  (*   - *)
  (*     unfold well_formed_closed_mu_aux. case_match; auto. *)
  (*     simpl in *. *)
  (*     unfold well_formed_closed_ex_aux in Hwfcea. *)

    (* wf_auto2. *)
    (* induction φ eqn:Hφ; auto; simpl in *. *)
    (* 1,2: apply andb_true_iff in Hmf, Hwfcea; apply andb_true_iff. *)
  (* Abort. *)

    

  Goal forall l ti n,
    well_formed_closed_ex_aux l n ->
    well_formed_closed_mu_aux l 0 ->
    well_formed_positive l ->
    well_formed ti ->
    mu_free l ->
    functional_when_applied n l ->
    Γ ⊢ is_functional ti ->
    Γ ⊢ (many_ex n (l =ml ti)) <---> ti ∈ml (many_ex n l).
  Proof.
    intros * Hwfceal Hwfcmal Hwfpl Hwfti Hmfl Hfpl Hfpti.
    generalize dependent l.
    induction n; intros; simpl in *.
    (* induction n; simpl in *. *)
    -
      epose proof membership_equal_equal Γ ti l HΓ Hmfl Hwfti ltac:(wf_auto2) Hfpti Hfpl.
      toMLGoal. wf_auto2.
      mlAdd H.
      mlRewriteBy "0" at 1.
      mlSplitAnd; mlIntro.
      (* TODO: Why don't they work with sequencing? *)
      mlSymmetry; mlAssumption.
      mlSymmetry; mlAssumption.
    -
      opose proof* (lemma1 l ti); auto.
      admit.
      admit.
      toMLGoal. admit.
      mlRewrite H at 1.


      
      mlFreshEvar as y.
      ospecialize* (IHn l^{evar:0↦y}).
      apply wfc_mu_aux_body_ex_imp3. lia. auto.
      apply wfc_mu_aux_body_ex_imp1. auto.
      apply wfp_evar_open. auto.
      apply mu_free_evar_open. auto. auto.
      Search evar_open patt_exists.
  Abort.
  
  Goal forall l ti,
    well_formed (ex, l) ->
    well_formed ti ->
    mu_free ti ->
    (forall x, Γ ⊢ is_functional l^{evar:0↦x}) ->
    Γ ⊢ is_functional ti ->
    Γ ⊢ ⌈l^{evar: 0 ↦ fresh_evar l} and ti⌉ ---> (ex, l =ml ti).
  Proof.
    intros * wfl wfti mfti fpl fpti.
    remember (fresh_evar _) as y.
    pose proof evar_open_not_occur 0 y ti ltac:(wf_auto2).
    mlIntro.
      mlExists y. mlSimpl. rewrite H.
      fold (l^{evar:0↦y} ∈ml ti).
      epose proof membership_imp_equal Γ (l^{evar:0↦y}) ti HΓ mfti ltac:(wf_auto2) ltac:(wf_auto2).
      pose proof (MP (fpl y) H0). clear H0.
      pose proof (MP fpti H1). clear H1.
      now fromMLGoal.
  Defined.

  Goal forall y (sy : symbols), exists (M : Model), forall (ρ' : @Valuation _ M), exists ρ l ti,
    well_formed ti ->
    @eval _ M ρ ((ex, l =ml ti) ---> ⌈l^{evar: 0 ↦ y} and ti⌉) ≠ ⊤.
  Proof.
    intros.
    pose {| Domain := bool; sym_interp _ := {[true]}; app_interp _ _ := ⊤ |} as M.
    eexists M.
    intros.
    pose (false : M).
    exists (update_evar_val y d ρ'), b0, (patt_sym sy).
    intros wfti *.
    rewrite ! eval_simpl. simpl.
    remember (fresh_evar _) as y'.
    mlSimpl.
    remember (λ e : bool, eval _ _) as f.
    epose proof propset_fa_union_full f as [_ ?]. rewrite H.
    intros.
    pose (true : Domain M) as c.
    exists c. subst f.
    unfold evar_open. simpl.
    epose proof equal_iff_interpr_same M _ (patt_free_evar y') (patt_sym sy) (update_evar_val y' c (update_evar_val y d ρ')) as [_ ->].
    set_solver. clear _H.
    rewrite ! eval_simpl. simpl. rewrite decide_eq_same. subst c. auto.
    epose proof @difference_diag_L bool (propset M) _ _ _ _ _ _ _ _ ⊤.
    rewrite H0. rewrite (@union_empty_l_L bool (propset M)).
    rewrite decide_eq_same.
    assert (LeibnizEquiv (propset bool)). apply (@propset_leibniz_equiv _ M).
    rewrite ! union_empty_r_L.
    rewrite ! Compl_Compl_propset.
    rewrite Compl_Union_Compl_Inters_propset_alt.
    replace ({[d]} ∩ {[true]}) with (@empty (propset (@Domain Σ M)) (@propset_empty (@Domain Σ M))) by set_solver.
    unfold app_ext. simpl.
    remember (λ e, exists le re, _) as f'.
    epose proof set_eq (PropSet f') ⊤.
    apply not_iff_compat in H2. apply H2.
    intro. specialize (H3 false).
    pose proof elem_of_PropSet f' false.
    apply iff_sym in H4.
    apply (iff_trans H4) in H3. clear H4.
    epose proof elem_of_top false.
    apply (iff_trans H3) in H4. clear H3.
    destruct H4 as [_ ?]. specialize (H3 I).
    rewrite Heqf' in H3. decompose record H3.
    set_solver.
    Unshelve.
    1: {
      unfold satisfies_theory, satisfies_model. intros.
      inversion H0. subst. simpl. unfold axiom. case_match.
      rewrite ! eval_simpl. simpl. unfold app_ext.
      remember (λ e, exists le re, _) as f'.
      epose proof set_eq (PropSet f') ⊤. apply H2.
      intros.
      transitivity (f' x0). apply elem_of_PropSet.
      transitivity True. 2: { epose proof elem_of_top x0. apply iff_sym in H3. exact H3. }
      split. auto. intros [].
      rewrite Heqf'.
      do 2 eexists; repeat split.
    }
    Unshelve.
    all: typeclasses eauto.
  Defined.

  Context (σ : list (evar * Pattern)).
  Hypothesis (Hwfσ : wf (map snd σ)).

  Goal forall (sy : symbols) (x : evar) l, exists M ti σ, forall (ρ' : @Valuation _ M), exists ρ,
    @eval _ M ρ ((predicate_list σ ---> (l =ml ti)) <---> ((l and predicate_list σ) =ml ti)) ≠ ⊤.
  Proof.
    intros.
    pose {| Domain := bool; sym_interp _ := {[true]}; app_interp _ _ := ⊤ |} as M.
    exists M.
    exists (patt_sym sy).
    exists [(x, patt_sym sy)].
    intros.
    pose (false : M).
    pose (update_evar_val x d ρ') as ρ.
    exists ρ.
    
    assert (satisfies_theory M theory). {
      unfold satisfies_theory, satisfies_model.
      intros. inversion H. subst. simpl. unfold axiom.
      case_match. rewrite ! eval_simpl.
      simpl. unfold app_ext. remember (λ e, exists le re, _) as f.
      epose proof set_eq (PropSet f) ⊤ as [_ ?]. apply H1.
      intros. rewrite elem_of_top. repeat split.
      intros []. apply elem_of_PropSet. subst.
      exists true, (evar_valuation ρ0 ev_x). repeat split.
    }

    unfold predicate_list. simpl.
    assert (eval ρ (patt_free_evar x =ml patt_sym sy) = ∅). {
      pose proof not_equal_iff_not_interpr_same_1 M H (patt_free_evar x) (patt_sym sy) ρ as [_ ?]. apply H0.
      rewrite ! eval_simpl. simpl. rewrite decide_eq_same. subst d.
      intro. epose proof set_eq {[false]} {[true]} as [? _].
      specialize (H2 H1 false) as [? _]. ospecialize* H2.
      now apply elem_of_singleton_2.
      set_solver.
    }

    rewrite eval_iff_simpl.
    rewrite eval_imp_simpl.
    rewrite ! eval_and_simpl.
    rewrite H0.
    rewrite ! intersection_empty_l_L difference_empty_L.
    (* set_solver went on vacation *)
    (* TODO: extract these to stdpp_ext? *)
    assert (forall X : propset M, ⊤ ∪ X = ⊤) by (set_unfold; solve [repeat constructor]).
    rewrite ! H1.
    rewrite difference_diag_L union_empty_l_L.
    assert (forall X : propset M, X ∪ ⊤ = ⊤) by (set_unfold; solve [repeat constructor]).
    rewrite ! H2.
    assert (forall X : propset M, X ∩ ⊤ = X). {
      set_unfold. repeat constructor. now intros []. auto.
    }
    rewrite ! H3.
    epose proof not_equal_iff_not_interpr_same_1 M H _ _ ρ as [_ ?].
    erewrite H4. set_unfold. auto.
    rewrite ! eval_and_simpl eval_sym_simpl.
    rewrite H0 intersection_empty_l_L intersection_empty_r_L.
    simpl. symmetry. epose proof non_empty_singleton_L true. exact H5.
    Unshelve. all: try typeclasses eauto.
    (* TODO: possible to make this part of typeclasses eauto's search? *)
    all: exact (@propset_leibniz_equiv _ M).
  Defined.

  Goal forall l ti,
    well_formed (ex, l) ->
    well_formed ti ->
    Γ ⊢ ⌈(ex, l) and ti⌉ <---> (ti ∈ml ex, l).
  Proof.
    intros * wfl wfti.
    toMLGoal. wf_auto2.
    pose proof patt_and_comm Γ (ex, l) ti wfl wfti.
    use AnyReasoning in H. mlRewrite H at 1.
    fold (ti ∈ml (ex, l)). mlReflexivity.
  Defined.

  Goal forall l ti,
    forall M ρ,
    satisfies_theory M theory ->
    @eval _ M ρ (predicate_list σ) = ∅ ->
    @eval _ M ρ ti ≠ ∅ ->
    @eval _ M ρ ((predicate_list σ ---> (l =ml ti)) <---> ((l and predicate_list σ) =ml ti)) ≠ ⊤.
  Proof.
    intros * HM Hρ Hρ2.
    rewrite eval_iff_simpl.
    rewrite eval_imp_simpl.
    rewrite Hρ.
    rewrite ! difference_empty_L.
    assert (forall X : propset M, ⊤ ∪ X = ⊤) as Htop_l by set_solver.
    assert (forall X : propset M, X ∪ ⊤ = ⊤) as Htop_r by set_solver.
    rewrite ! Htop_l.
    rewrite difference_diag_L.
    rewrite Htop_r.
    assert (forall X : propset M, X ∩ ⊤ = X) as Htop_int by set_solver.
    rewrite Htop_int.
    rewrite union_empty_l_L.
    epose proof not_equal_iff_not_interpr_same_1 M HM (l and predicate_list σ) ti ρ as [_ ->].
    2: {
      rewrite eval_and_simpl.
      rewrite Hρ.
      rewrite intersection_empty_r_L.
      auto.
    }
    set_solver.
  Defined.

  Goal forall (sy : symbols) (a : evar), exists ti s M, forall ρ,
    satisfies_theory M theory /\
    @eval _ M ρ (predicate_list s) = ∅ /\
    @eval _ M ρ ti ≠ ∅.
  Proof.
    intros.
    exists (patt_sym sy).
    exists [(a, ⊥)].
    pose {| Domain := unit; app_interp _ _ := ⊤; sym_interp _ := ⊤ |} as M. exists M.
    intros.
    
    assert (forall X Y, (exists x, x ∈ X) -> (exists y, y ∈ Y) -> @app_ext _ M X Y = ⊤). {
      intros * HX HY. unfold app_ext.
      remember (fun e : Domain M => exists le re : M, _) as f.
      apply set_eq.
      intros e.
      transitivity (f e).
      apply elem_of_PropSet.
      transitivity True.
      2: symmetry; apply elem_of_top.
      split. auto.
      intros []. subst.
      destruct HX as [x HX], HY as [y HY].
      exists x, y. do ! split. all: auto.
    }

    do ! split.

    -
      unfold satisfies_theory, satisfies_model. intros.
      inversion H0. subst. simpl.
      unfold axiom. case_match. rewrite ! eval_simpl. rewrite H.
      3: reflexivity. all: set_solver.
    -
      simpl.
      rewrite ! eval_simpl.
      rewrite ! union_empty_r_L.
      rewrite ! Compl_Compl_propset.
      rewrite H. 3: now rewrite union_empty_r_L difference_diag_L.
      all: set_solver.
    -
      rewrite eval_simpl. simpl.
      apply Contains_Elements_Not_Empty. set_solver.
  Defined.
End MatchingEquivs.

