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

From stdpp Require Import base fin_sets sets propset proof_irrel option list.

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
      (* clear Heqi. *)
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

  Context (σ : list (evar * Pattern)).
  Hypothesis (Hwfσ : wf (map snd σ)).

  (* Lemma equal_iff_interpr M ρ φ1 φ2 : *)
  (*   satisfies_theory M theory -> *)
  (*   @eval _ M ρ (φ1 =ml φ2) = ⊤ \/ *)
  (*   @eval _ M ρ (φ1 =ml φ2) = ∅. *)
  (* Proof. *)
  (*   intros HM. *)
  (*   pose proof classic (@eval _ M ρ φ1 = @eval _ M ρ φ2) as []. *)
  (*   - *)
  (*     pose proof equal_iff_interpr_same M HM φ1 φ2 ρ as [_ Heq]. *)
  (*     left. auto. *)
  (*   - *)
  (*     pose proof not_equal_iff_not_interpr_same_1 M HM φ1 φ2 ρ as [_ Hneq]. *)
  (*     right. auto. *)
  (* Defined. *)

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

  Goal exists ti M ρ,
    satisfies_theory M theory /\
    @eval _ M ρ (predicate_list σ) = ∅ /\
    @eval _ M ρ ti ≠ ∅.
  Proof.
  Abort.

  (* TODO: multiexists *)
  Goal forall l ti,
    well_formed (ex, l) ->
    well_formed ti ->
    mu_free l ->
    Γ ⊢ is_functional l ->
    Γ ⊢ is_functional ti ->
    Γ ⊢ (ex, (l =ml ti)) <---> ti ∈ml (ex, l). 
  Proof.
    intros * wfl wfti mfl fpl fpti.
    mlFreshEvar as y.
    unshelve epose proof membership_exists Γ ti y l AnyReasoning HΓ ltac:(wf_auto2) wfti _ ltac:(try_solve_pile).
    (* TODO: why doesn't solve_fresh work here? *)
    ltac2:(_fm_export_everything ()). set_solver.
    (* pose proof pf_iff_equiv_sym_meta Γ _ _ _ H. clear H. *)
    (* pose proof patt_equal_comm l ti Γ HΓ wfl wfti. use AnyReasoning in H. *)
    toMLGoal. wf_auto2.
    mlRewrite H at 1.
    mlSplitAnd; mlIntro.
    mlDestructEx "0" as x. mlExists x. mlSimpl. mlRewriteBy "0" at 1.
    Search patt_in. mlApplyMeta membership_refl.
    mlAdd fpti. unfold is_functional.
    mlClear "0".
    mlDestructEx "1" as z.
    Search patt_exists patt_equal.


    pose proof membership_equal_equal Γ _ _ HΓ mfl wfti wfl fpti fpl.
    epose proof patt_equal_sym Γ _ _ HΓ _ _. use AnyReasoning in H2.
    pose proof (MP H1 H2). clear H1 H2.
    Unshelve. 2-3: wf_auto2.
    toMLGoal. wf_auto2.
    mlRewrite H at 1.
    mlAdd H3. mlRewriteBy "0" at 1.
    mlExactMeta H0.
  Defined.


  Goal forall l ti M ρ,
    satisfies_theory M theory ->
    @eval _ M ρ ((ex, l =ml ti) <---> ⌈l and ti⌉) ≠ ⊤.
  Proof.
    intros * HM.
    rewrite eval_iff_simpl.
    Search eval patt_defined.
    pose proof patt_defined_dec M HM (l and ti) ρ as [-> | ->].
    assert (forall X : propset M, X ∪ ⊤ = ⊤) as -> by set_solver.
    rewrite difference_diag_L union_empty_l_L.
    assert (forall X : propset M, ⊤ ∩ X = X) as -> by set_solver.
    2: rewrite union_empty_r_L difference_empty_L.
    2: assert (forall X : propset M, ⊤ ∪ X = ⊤) as -> by set_solver.
    2: assert (forall X : propset M, X ∩ ⊤ = X) as -> by set_solver.
    Search eval patt_exists.
  Abort.


  Goal forall l ti,
    well_formed l ->
    well_formed ti ->
    mu_free ti ->
    Γ ⊢ is_functional l ->
    Γ ⊢ is_functional ti ->
    Γ ⊢ (ex, (l =ml ti)) <---> ⌈l and ti⌉.
  Proof.
    intros * wfl wfti mfti fpl fpti.
    replace (⌈l and ti⌉) with (l ∈ml ti) by reflexivity.
    pose proof membership_equal_equal Γ _ _ HΓ mfti wfl wfti fpl fpti.
    toMLGoal. wf_auto2.
    mlAdd H as "H".
    mlRewriteBy "H" at 1.
    mlClear "H".
    fromMLGoal.
    Search patt_in patt_exists.
    (****************)
    Search patt_exists.
  Abort.

End MatchingEquivs.

Section Existentials.
  About Model.
  Goal exists (Σ : Signature) (syntax : @Syntax Σ) (M : @Model Σ) ρ l ti,
    satisfies_theory M theory /\
    @eval _ M ρ (ex, l =ml ti) ≠ ⊤ /\
    @eval _ M ρ (ex, l =ml ti) ≠ ∅.
  Proof.
    do ! eexists.
    Unshelve.
    4: {
      split. exact StringMLVariables.
      unshelve esplit. exact bool. all: typeclasses eauto.
    }
    4: {
      split. intros []. simpl. left.
    }
    4: {
      unshelve esplit. exact bool. typeclasses eauto.
      intros. exact empty.
      intros. exact {[sigma]}.
    }
    4: {
      split; simpl; intros. right. exact {[true]}.
    }
    4: exact b0.
    4: apply patt_sym; right.
    2: {
      simpl.
      rewrite eval_ex_simpl. simpl.
      remember (λ e, _) as f.
      intro.
      epose proof propset_fa_union_full f as [? _]. specialize (H0 H).
      clear H. subst. simpl in H0. remember (fresh_evar _) as y. 
      mlSimpl in H0.
      (*-------------------*)
      specialize (H0 false) as [].
      remember (update_evar_val _ _ _) as ρ'.
      epose proof not_equal_iff_not_interpr_same_1 _ _ (b0^{evar:0↦y}) (patt_sym _) ρ' as [_ ?]. rewrite H0 in H.
      2: set_solver.
      rewrite ! eval_simpl. simpl. subst. simpl.
      rewrite decide_eq_same. destruct x.
      (*********************)

      mlSimpl. cbn.
      Search propset_fa_union.
    Print Signature.
    Print MLSymbols.
End Existentials.
