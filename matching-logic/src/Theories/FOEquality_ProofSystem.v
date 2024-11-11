From Coq Require Import ssreflect ssrfun ssrbool.

From Ltac2 Require Import Ltac2.

From Coq Require Import String Setoid.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.Classical_Prop.
From Coq.Logic Require Import FunctionalExtensionality Eqdep_dec.
From Coq.Classes Require Import Morphisms_Prop.
From Coq.Unicode Require Import Utf8.
From Coq.micromega Require Import Lia.

From MatchingLogic Require Import Logic ProofMode.MLPM.
From MatchingLogic.Theories Require Import Definedness_Syntax Definedness_ProofSystem.
From MatchingLogic.Utils Require Import stdpp_ext.

Require Import MatchingLogic.wftactics.

From stdpp Require Import base fin_sets sets propset proof_irrel option list.

Import extralibrary.

Import MatchingLogic.Logic.Notations.
Import MatchingLogic.Theories.Definedness_Syntax.Notations.

Require Import MatchingLogic.Theories.DeductionTheorem.

Require MatchingLogic.Theories.Sorts_Syntax.
Import MatchingLogic.Theories.Sorts_Syntax.Notations.

Set Default Proof Mode "Classic".

Open Scope ml_scope.
Open Scope string_scope.
Open Scope list_scope.

Lemma membership_imp_equal {Σ : Signature} {syntax : Syntax} Γ φ φ' :
  theory ⊆ Γ -> mu_free φ' ->
  well_formed φ -> well_formed φ' ->
  Γ ⊢ (ex , (φ =ml b0)) --->
      (ex , (φ' =ml b0)) --->
      (φ ∈ml φ') ---> (φ =ml φ').
Proof.
  intros HΓ Mufree Wf1 Wf2.
  toMLGoal. wf_auto2.

  mlIntro "fun0". mlIntro "fun1".
  epose proof (@forall_functional_subst _ _ (⌈ b0 and φ' ⌉ ---> ⌊ b0 <---> φ' ⌋) φ 
                  Γ HΓ ltac:(wf_auto2) ltac:(wf_auto2) _ ltac:(wf_auto2)) as H.
  Unshelve.
  2: wf_auto2.
  mlSimpl in H. simpl in H.
  repeat rewrite bevar_subst_not_occur in H. wf_auto2.
  mlApplyMeta H. clear H.
  mlSplitAnd.
  2: mlExact "fun0".

  (* TODO: proposal: functional_reasoning tactic, which replaces a pattern with a 
                     free variable *)
  epose proof (forall_functional_subst (all, (⌈ b0 and b1 ⌉ ---> ⌊ b0 <---> b1 ⌋)) φ'
                  Γ HΓ ltac:(wf_auto2) ltac:(wf_auto2) _ ltac:(wf_auto2)) as H.
  Unshelve.
  2: wf_auto2.
  mlApplyMeta H. clear H.

  mlSplitAnd.
  2: mlExact "fun1".
  remember (fresh_evar patt_bott) as xx.
  remember (fresh_evar (patt_free_evar xx)) as yy.
  assert (xx <> yy) as XY.
  { solve_fresh_neq. }
  mlClear "fun0". mlClear "fun1".
  fromMLGoal.

  (* TODO: mlIntro for supporting 'all' *)

  pose proof (universal_generalization Γ (all , (⌈ b0 and patt_free_evar xx ⌉ ---> ⌊ b0 <---> patt_free_evar xx ⌋)) xx AnyReasoning (pile_any _)) as H1.
  simpl in H1.
  rewrite decide_eq_same in H1.
  apply H1.
  { wf_auto2. }
  clear H1.
  pose proof (@universal_generalization _ Γ (⌈ (patt_free_evar yy) and (patt_free_evar xx) ⌉ ---> ⌊ (patt_free_evar yy) <---> (patt_free_evar xx) ⌋) yy AnyReasoning (pile_any _)) as H1.
  simpl in H1.
  rewrite decide_eq_same in H1.
  destruct (decide (yy = xx)) eqn:Heqyx;[congruence|].
  apply H1.
  { wf_auto2. }
  clear H1.
  now apply overlapping_variables_equal.
Defined.

Lemma membership_imp_equal_meta {Σ : Signature} {syntax : Syntax} Γ φ φ' :
    theory ⊆ Γ -> mu_free φ' ->
    well_formed φ -> well_formed φ' ->
    Γ ⊢ (ex , (φ =ml b0)) ->
    Γ ⊢ (ex , (φ' =ml b0)) ->
    Γ ⊢ (φ ∈ml φ') ---> (φ =ml φ') .
Proof.
  intros HΓ Mufree Wf1 Wf2 H0 H1.
  toMLGoal.
  { wf_auto2. }
  mlAdd H1 as "H1".
  mlAdd H0 as "H0".
  fromMLGoal.
  apply membership_imp_equal; assumption.
Defined.

Lemma membership_impl_subseteq {Σ : Signature} {syntax : Syntax} Γ g ψ :
  theory ⊆ Γ -> mu_free ψ -> mu_free g ->
  well_formed g -> well_formed ψ ->
  Γ ⊢ (ex , (g =ml b0)) ->
  Γ ⊢ (g ∈ml ψ) ->
  Γ ⊢ (g ⊆ml ψ).
Proof.
  intros HΓ Hmfψ Hmfg wfg wfψ Hfung H.

  apply phi_impl_total_phi_meta.
  { wf_auto2. }
  { apply pile_any. }

  apply membership_elimination with (x := (fresh_evar (g ---> ψ))).
  { solve_fresh. }
  { apply pile_any. }
  { wf_auto2. }
  { set_solver. }

  remember (fresh_evar (b0 ∈ml (g ---> ψ))) as x.

  rewrite <- evar_quantify_evar_open with (phi := b0 ∈ml (g ---> ψ)) (n := 0) (x := x).
  2: {
    subst x.
    eapply evar_is_fresh_in_richer'.
    2: { apply set_evar_fresh_is_fresh'. }
    clear. set_solver.
  }
  2: { cbn. split_and!; try reflexivity; fold well_formed_closed_ex_aux; wf_auto2. }
  apply universal_generalization;[apply pile_any|wf_auto2|].
  mlSimpl. unfold evar_open. simpl.

  rewrite bevar_subst_not_occur.
  { wf_auto2. }
  rewrite bevar_subst_not_occur.
  { wf_auto2. }

  pose proof (Htmp := membership_imp Γ x g ψ).
  ospecialize* Htmp.
  { set_solver. }
  { wf_auto2. }
  { wf_auto2. }
  use AnyReasoning in Htmp.

  toMLGoal.
  { wf_auto2. }
  mlRewrite Htmp at 1. clear Htmp. fold AnyReasoning.

  mlIntro "H".

  pose proof (Htmp := membership_imp_equal_meta Γ (patt_free_evar x) g).
  ospecialize* Htmp.
  { assumption. }
  { assumption. }
  { wf_auto2. }
  { wf_auto2. }
  {
    pose proof (Hex := Ex_quan Γ (patt_free_evar x =ml b0) x).
    ospecialize* Hex.
    { wf_auto2. }
    use AnyReasoning in Hex.
    toMLGoal.
    { wf_auto2. }
    mlApplyMeta Hex. unfold instantiate. mlSimpl. simpl.
    fromMLGoal.
    aapply patt_equal_refl.
    { wf_auto2. }
  }
  { assumption. }

  mlApplyMeta Htmp in "H". clear Htmp.
  mlRevertLast.
  mlRewrite (useBasicReasoning AnyReasoning (patt_equal_comm (patt_free_evar x) g Γ HΓ ltac:(wf_auto2) ltac:(wf_auto2))) at 1.
  mlIntro "H".
  mlApplyMeta (equality_elimination_proj Γ g (patt_free_evar x) (b0 ∈ml ψ)) in "H". mlSimpl. simpl.
  rewrite bevar_subst_not_occur.
  { wf_auto2. }
  rewrite bevar_subst_not_occur.
  { wf_auto2. }
  mlApply "H".
  mlClear "H".
  fromMLGoal.
  assumption.
  { wf_auto2. }
  { wf_auto2. }
  { cbn. split_and!;[assumption|reflexivity|reflexivity]. }
  { assumption. }
Defined.

Lemma functional_pattern_defined {Σ : Signature} {syntax : Syntax} :
  forall Γ φ, theory ⊆ Γ -> well_formed φ ->
     Γ ⊢ (ex , (φ =ml b0)) ---> ⌈ φ ⌉.
Proof.
  intros Γ φ HΓ Wf.
  toMLGoal. wf_auto2.
  mlIntro "H0".
  mlApplyMeta (forall_functional_subst ⌈ b0 ⌉ φ _ HΓ ltac:(wf_auto2)
  ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2)).
  mlSplitAnd.
  * mlClear "H0". fromMLGoal. wf_auto2.
    remember (fresh_evar patt_bott) as x.
    pose proof (universal_generalization Γ ⌈patt_free_evar x⌉ x AnyReasoning (pile_any _)) 
      as H1'.
    cbn in H1'. case_match. 2: congruence. apply H1'. reflexivity.
    gapply defined_evar.
    { apply pile_any. }
    { exact HΓ. }
  * mlExact "H0".
Defined.

Lemma membership_equal_equal {Σ : Signature} {syntax : Syntax} :
  forall Γ φ φ',
    theory ⊆ Γ -> mu_free φ' ->
    well_formed φ -> well_formed φ' ->
    Γ ⊢ (ex , (φ =ml b0))  ->
    Γ ⊢ (ex , (φ' =ml b0))  ->
    Γ ⊢ (φ ∈ml φ') =ml (φ =ml φ') .
Proof.
  intros Γ φ φ' HΓ Mufree Wf1 Wf2 Func1 Func2.
  unfold patt_equal at 1.

  toMLGoal. wf_auto2.
  mlIntro.
  pose proof (bott_not_defined Γ) as H.
  use AnyReasoning in H.
  mlApplyMeta H.
  fromMLGoal. wf_auto2.

  apply ceil_monotonic; auto.
  { wf_auto2. }

  toMLGoal. wf_auto2.
  pose proof (not_not_intro Γ ((φ ∈ml φ' <---> φ =ml φ' ))
  ltac:(wf_auto2)) as H0.
  use AnyReasoning in H0.
  mlApplyMeta H0.
  mlSplitAnd; mlIntro.
  * mlApplyMeta membership_imp_equal_meta; auto. mlExactn 0.
  * mlApplyMeta equal_imp_membership; auto. mlExactn 0.
    Unshelve.
    toMLGoal. wf_auto2.
    (* clear h. *)
    mlApplyMeta functional_pattern_defined; auto.
    mlExactMeta Func2.
Defined.

Lemma funcional_application {Σ : Signature} {syntax : Syntax} Γ t1 t2 :
  theory ⊆ Γ ->
  well_formed t1 ->
  well_formed t2 ->
  Γ ⊢ (ex , t2 =ml b0) ---> (all , ex , (t1 ⋅ b1)%ml =ml b0) --->
    ex , (t1 ⋅ t2)%ml =ml b0.
Proof.
  intros HΓ wf1 wf2.
  mlIntro "H".
  mlDestructEx "H" as x.
  mlSimpl. cbn. rewrite evar_open_not_occur. wf_auto2.
  mlIntro "H0".
  mlSpecialize "H0" with x.
  mlSimpl. cbn. rewrite evar_open_not_occur. wf_auto2.
  mlDestructEx "H0" as y.
  mlSimpl. cbn. rewrite evar_open_not_occur. wf_auto2.
  mlExists y.
  mlSimpl. cbn. rewrite evar_open_not_occur. wf_auto2. rewrite evar_open_not_occur. wf_auto2.
  mlRewriteBy "H" at 1.
  mlAssumption.
Defined.

Section nary_functions.

  Context {Σ : Signature} {syntax : Syntax}.
  Fixpoint nary_function (f : Pattern) (n : nat) :=
    match n with
    | 0 => ex , f =ml b0
    | S n' => all , nary_function (f ⋅ patt_bound_evar (S n')) n'
    end.

  Definition nary_function_symbol (f : symbols) (n : nat) := nary_function (patt_sym f) n.

  Eval simpl in nary_function patt_bott 3.

  Lemma nary_function_well_formed_positive :
    forall n φ, well_formed_positive φ -> well_formed_positive (nary_function φ n).
  Proof.
    induction n; simpl; intros.
    wf_auto2.
    rewrite IHn. wf_auto2. reflexivity.
  Qed.

  Lemma nary_function_well_formed_closed_mu_aux :
    forall m n φ, well_formed_closed_mu_aux φ n ->
      well_formed_closed_mu_aux (nary_function φ m) n.
  Proof.
    induction m; simpl; intros.
    wf_auto2.
    rewrite IHm. wf_auto2. reflexivity.
  Qed.

  Lemma nary_function_well_formed_closed_ex_aux_helper :
    forall m n φ,
      n > m ->
      well_formed_closed_ex_aux φ n ->
      well_formed_closed_ex_aux (nary_function φ m) (n - S m).
  Proof.
    induction m; simpl; intros.
    wf_auto2.
    specialize (IHm n (φ ⋅ patt_bound_evar (S m)) ltac:(lia)).
    rewrite Nat.sub_succ_r. rewrite Nat.succ_pred_pos. lia.
    rewrite IHm. wf_auto2. case_match. lia. lia. reflexivity.
  Qed.

  Lemma nary_function_well_formed_closed_ex_aux :
    forall m n φ, well_formed_closed_ex_aux φ n ->
      well_formed_closed_ex_aux (nary_function φ m) (n - S m).
  Proof.
    intros m n. destruct (dec_gt n m).
    * intros. by apply nary_function_well_formed_closed_ex_aux_helper.
    * assert (n - S m = 0) by lia. rewrite H0.
      assert (n ≤ m) by lia. clear H H0.
      revert n H1. induction m; intros; cbn.
      - wf_auto2.
      - do 2 rewrite andb_true_r.
        replace 1 with (S (S m) - S m) by lia.
        apply nary_function_well_formed_closed_ex_aux_helper. lia.
        wf_auto2. case_match. lia. lia.
  Qed.

  Lemma nary_function_mu_free :
    forall m φ, mu_free φ -> mu_free (nary_function φ m).
  Proof.
    induction m; intros; simpl. wf_auto2.
    rewrite IHm; wf_auto2.
  Qed.

  Lemma nary_function_bevar_subst :
    forall m n φ ψ,
      (nary_function φ m)^[evar:n↦ψ] =
      (nary_function φ^[evar: S m + n ↦ ψ] m).
  Proof.
    induction m; intros.
    * by mlSimpl.
    * simpl nary_function. mlSimpl. rewrite IHm. mlSimpl.
      f_equal. f_equal.
      simpl.
      case_match. 2-3: lia.
      rewrite -Nat.add_succ_comm. reflexivity.
  Qed.

  Lemma function_application_many Γ l φ :
    theory ⊆ Γ ->
    wf l ->
    well_formed φ ->
    mu_free φ ->
    foldr andb true (map mu_free l) ->
    Γ ⊢ nary_function φ (length l) --->
        foldr (fun p acc => (ex , p =ml b0) ---> acc)
              (ex , foldl patt_app φ l =ml b0) l.
  Proof.
    revert φ.
    induction l; intros φ HΓ Hwfl Hwf HMF1 HMF2; cbn in *. mlIntro. mlAssumption.
    destruct_and!.
    opose proof* (IHl (φ ⋅ a) HΓ H2 ltac:(wf_auto2)).
    { simpl. by rewrite H HMF1. }
    { assumption. }
    toMLGoal.
    {
      simpl in *. clear Halmost H.
      repeat apply well_formed_imp. 2-3: wf_auto2.
      * assert (well_formed_positive (nary_function (φ ⋅ patt_bound_evar (S (length l))) (length l))). {
          apply nary_function_well_formed_positive. wf_auto2.
        }
        assert (well_formed_closed_mu_aux (nary_function (φ ⋅ patt_bound_evar (S (length l))) (length l)) 0). {
          apply nary_function_well_formed_closed_mu_aux. wf_auto2.
        }
        assert (well_formed_closed_ex_aux (nary_function (φ ⋅ patt_bound_evar (S (length l))) (length l)) 1). {
          replace 1 with (S (S (length l)) - S (length l)) by lia.
          apply nary_function_well_formed_closed_ex_aux. wf_auto2.
          case_match; lia.
        }
        wf_auto2.
      * apply wf_foldr with (t := fun p => (ex , p =ml b0)).
        - remember (fresh_evar (foldl patt_app (φ ⋅ a) l)) as x.
          pose proof (evar_quantify_well_formed (foldl patt_app (φ ⋅ a) l =ml patt_free_evar x) x).
          assert (well_formed (foldl patt_app (φ ⋅ a) l =ml patt_free_evar x)). {
            rewrite foldl_fold_left.
            apply well_formed_equal. 2: wf_auto2.
            apply wf_fold_left with (t := id). wf_auto2. by rewrite map_id.
            clear. intros. wf_auto2.
          }
          mlSimpl in H.
        - apply map_wf. assumption. clear. intros. wf_auto2.
        - clear. intros. wf_auto2.
    }
    mlIntro. mlIntro.
    mlApplyMeta IHl.
    2: { assumption. }
    2: { simpl. by rewrite H HMF1. }
    opose proof* (forall_functional_subst (nary_function (φ ⋅ patt_bound_evar (S (length l))) (length l)) a Γ HΓ).
    { apply nary_function_mu_free. wf_auto2. }
    { assumption. }
    {
      replace 1 with (S (S (length l)) - S (length l)) by lia.
      apply nary_function_well_formed_closed_ex_aux. wf_auto2.
      case_match; lia.
    }
    { apply nary_function_well_formed_closed_mu_aux. wf_auto2. }
    2: { assumption. }
    mlAdd H4. mlConj "0" "1" as "3".
    mlApply "2" in "3".
    rewrite nary_function_bevar_subst. mlSimpl. simpl.
    case_match. 1,3: lia.
    rewrite Nat.add_0_r.
    rewrite bevar_subst_not_occur. wf_auto2.
    mlAssumption.
  Defined.

End nary_functions.

Fixpoint deconstruct_function {Σ : Signature} (pat : Pattern) : option (symbols * list Pattern) :=
match pat with
| patt_app t1 t2 => match deconstruct_function t1 with
                    | Some (f, pats) => Some (f, pats ++ [t2])
                    | _ => None
                    end
| patt_sym s => Some (s, [])
| _ => None
end.

Ltac mlSplitAnds :=
match goal with
[ |- @of_MLGoal _ (@mkMLGoal _ ?Γ _ (patt_and _ _) _)] =>
  mlSplitAnd; mlSplitAnds
| _ => idtac
end.

Ltac solve_functional_var :=
lazymatch goal with
[ |- @of_MLGoal _ (@mkMLGoal _ ?Γ _ (ex, patt_free_evar ?x =ml b0) _)] =>
  mlExists x;
  mlSimpl; cbn; try (rewrite bevar_subst_not_occur; wf_auto2);
  mlReflexivity
| [ |- _ ] => fail "Not a functional variable claim"
end.

Ltac solve_functional_symbol :=
(* TODO: check the shape, this tactic is fragile *)
  fromMLGoal;
  gapply hypothesis;
  try assumption;
  wf_auto2;
  set_solver
.

Ltac solve_functional_step :=
  lazymatch goal with
  | [ |- @of_MLGoal _ (@mkMLGoal _ ?Γ _ (ex, ?p =ml patt_bound_evar 0) _)] =>
    lazymatch eval cbv in (deconstruct_function p) with
    | Some (?f, ?p::?pats) =>
      mlApplyMeta (function_application_many Γ (p::pats) (patt_sym f) ltac:(set_solver) ltac:(wf_auto2) ltac:(wf_auto2) ltac:(by simpl) ltac:(by simpl));
      try mlSplitAnds
    | Some (?f, []) => solve_functional_symbol
    | None => fail "Claim does not contain a first function symbol"
    end
  | _ => fail "Claim is not shaped as 'ex, <pat> =ml b0'"
  end.

Ltac solve_functional :=
  (repeat solve_functional_step); try solve_functional_var; try solve_functional_symbol.

Goal
  forall {Σ : Signature} {syntax: Syntax} f g one Γ x y,
    theory ⊆ Γ ->
    (all, all, all, ex, patt_app (patt_app (patt_app (patt_sym f) b3) b2) b1 =ml b0) ∈ Γ ->
    (all, ex, patt_app (patt_sym g) b1 =ml b0) ∈ Γ ->
    (ex , patt_sym one =ml b0) ∈ Γ ->
  Γ ⊢ ex, (patt_sym f ⋅ patt_free_evar x ⋅ (patt_sym g ⋅ patt_sym one) ⋅ (patt_sym g ⋅ patt_free_evar y))%ml =ml b0.
Proof.
  intros * HΓ Hf Hg Hone.
  toMLGoal. { wf_auto2. }
  solve_functional.
Defined.

Theorem exists_functional_subst_meta: ∀ {Σ : Signature} {syntax : Syntax} (Γ : Theory) (φ φ' : Pattern) ,
  Definedness_Syntax.theory ⊆ Γ ->
  mu_free φ ->
  well_formed φ' ->
  well_formed_closed_ex_aux φ 1 ->
  well_formed_closed_mu_aux φ 0 ->
  Γ ⊢ (ex , φ) ^ [φ'] ->
  Γ ⊢ is_functional φ' -> 
  Γ ⊢i (ex , φ) using AnyReasoning.
Proof.
  intros.
  toMLGoal.
  wf_auto2.
  now apply mu_free_wfp. 
  mlApplyMeta exists_functional_subst.
  2-3:assumption.
  2:eauto.
  2-3:assumption.
  mlSplitAnd.
  * mlExactMeta H4.
  * mlExactMeta H5.
Defined.

Theorem membership_monotone_functional: ∀ {Σ : Signature} {syntax : Syntax} (Γ : Theory) (φ₁ φ₂  t : Pattern)  (i : ProofInfo),
  Definedness_Syntax.theory ⊆ Γ ->
  well_formed φ₁ ->
  well_formed φ₂ ->
  well_formed t ->
  Γ ⊢i is_functional t using i ->
  Γ ⊢i φ₁ ---> φ₂ using i ->
  Γ ⊢i  t ∈ml φ₁ ---> t ∈ml φ₂ using i .
Proof.
  intros.
  unfold patt_in.
  apply ceil_monotonic.
  1: set_solver.
  1-2: wf_auto2.
  toMLGoal.
  wf_auto2.
  mlIntro "H".
  mlDestructAnd "H" as "H1" "H2".
  mlSplitAnd.
  * mlAssumption.
  * mlApplyMeta H4.
    mlAssumption.
Defined.
   
 Theorem membership_or_2_functional: ∀ {Σ : Signature} {syntax : Syntax} (Γ : Theory) (φ₁ φ₂ t : Pattern),
  well_formed φ₁ ->
  well_formed φ₂ ->
  well_formed t ->
  Definedness_Syntax.theory ⊆ Γ ->
  Γ ⊢i is_functional t ---> 
  t ∈ml φ₁ or t ∈ml φ₂ --->
  t ∈ml (φ₁ or φ₂) using AnyReasoning.
Proof.
  intros.
  toMLGoal.
  1: wf_auto2.
  mlIntro "H".
  unfold patt_in.
  epose proof (H3 := prf_prop_or_iff Γ AC_patt_defined ( t and φ₁) (t and φ₂) _ _ ).
  apply pf_iff_proj2 in H3.
  2-3: wf_auto2.
  mlClear "H".
  fromMLGoal.
  eapply syllogism_meta.
  4: gapply H3; try_solve_pile.
  1-3: wf_auto2.
  simpl.
  unshelve (eapply Framing_right).
  { wf_auto2. }
  { unfold BasicReasoning. try_solve_pile. }
  toMLGoal.
  1: wf_auto2.
  mlIntro. mlDestructOr "0".
  - mlDestructAnd "1". unfold patt_and. mlIntro. mlDestructOr "1".
    + mlApply "3". mlExactn 0.
    + mlApply "4". mlLeft. mlExactn 1.
  - mlDestructAnd "2". unfold patt_and. mlIntro. mlDestructOr "2".
    + mlApply "3". mlExactn 0.
    + mlApply "4". mlRight. mlExactn 1.
  Unshelve.
  1-2:wf_auto2.
Defined.
  
Theorem membership_or_2_functional_meta: ∀ {Σ : Signature} {syntax : Syntax} (Γ : Theory) (φ₁ φ₂ t : Pattern),
  well_formed φ₁ ->
  well_formed φ₂ ->
  well_formed t ->
  Definedness_Syntax.theory ⊆ Γ ->
  Γ ⊢i is_functional t using AnyReasoning -> 
  Γ ⊢i t ∈ml φ₁ or t ∈ml φ₂ --->  
  t ∈ml (φ₁ or φ₂) using AnyReasoning.
Proof.
  intros.
  toMLGoal.
  1:wf_auto2.
  mlIntro "H".
  pose proof membership_or_2_functional Γ (φ₁) (φ₂) t .
  ospecialize* H4.
  1-3: wf_auto2.
  set_solver.
  mlAdd H4.
  mlApply "0".
  simpl.
  mlSplitAnd.
  1: mlExactMeta H3.
  mlExact "H".
Defined.
    
Theorem membership_and_2_functional: ∀ {Σ : Signature} {syntax : Syntax} (Γ : Theory)  (φ₁ φ₂ t : Pattern),
  well_formed φ₁ ->
  well_formed φ₂ ->
  mu_free φ₁ ->
  mu_free φ₂ ->
  well_formed t ->
  Definedness_Syntax.theory ⊆ Γ ->
  Γ ⊢i is_functional t ---> 
  t ∈ml φ₁ and  t ∈ml φ₂ --->  
  t ∈ml (φ₁ and φ₂) using AnyReasoning.
Proof.
  intros.
  toMLGoal.
  1: wf_auto2.
  mlIntro "H".
  mlIntro "H1".
    
  remember ( fresh_evar( φ₁ ---> φ₂)  ) as x.
    
  pose proof membership_and_2 Γ x φ₁ φ₂ ltac:(wf_auto2)ltac:(wf_auto2) ltac:(set_solver).
  use (ExGen := {[ev_x; x]}, SVSubst := ∅, KT := false, AKT := false) in H5.
    
  apply universal_generalization with (x := x) in H5.
  2: try_solve_pile.
  2: wf_auto2. 
  use AnyReasoning in H5.
  mlAdd H5.
    
  mlConj "0" "H" as "H2". mlClear "0".
  mlApplyMeta forall_functional_subst in "H2".
  2:{ simpl. case_match.
      2:congruence. wf_auto2. 
    }
  2:{ simpl. case_match.
      2:congruence. wf_auto2. 
    }
  2:{ simpl. case_match.
      2:congruence. rewrite evar_quantify_fresh.
      1:{ subst x.  unfold evar_is_fresh_in. solve_fresh. }
      rewrite evar_quantify_fresh.
      1:{ subst x.  unfold evar_is_fresh_in. solve_fresh. }
      wf_auto2.
    }
  2:assumption.
    
  mlSimpl. simpl. case_match. 2:congruence.
  mlSimpl. simpl.
    
  rewrite evar_quantify_fresh.
  1:{ subst x.  unfold evar_is_fresh_in. solve_fresh. }
    
  rewrite evar_quantify_fresh.
  1:{ subst x.  unfold evar_is_fresh_in. solve_fresh. }
    
  rewrite bevar_subst_not_occur.
  1:wf_auto2.
    
  rewrite bevar_subst_not_occur.
  1:wf_auto2.
    
  mlApply "H2".
  mlAssumption.
Defined.
  
Theorem membership_and_2_functional_meta: ∀ {Σ : Signature} {syntax : Syntax} (Γ : Theory)  (φ₁ φ₂ t : Pattern),
  well_formed φ₁ -> 
  well_formed φ₂ ->
  mu_free φ₁ ->
  mu_free φ₂ ->
  well_formed t ->
  Definedness_Syntax.theory ⊆ Γ ->
  Γ ⊢ is_functional t -> 
  Γ ⊢i t ∈ml φ₁ and  t ∈ml φ₂ ---> 
  t ∈ml (φ₁ and φ₂) using AnyReasoning.
Proof.
  intros.
  toMLGoal.
  1:wf_auto2.
  mlIntro "H".
  epose proof membership_and_2_functional Γ (φ₁) (φ₂) t _ _ _ _ _ _.
  mlAdd H6.
  mlApply "0". simpl.
  mlSplitAnd.
  1:mlExactMeta H5.
  mlAssumption.
  Unshelve.
  1-5: wf_auto2.
  set_solver.
Defined.
  
Theorem  membership_symbol_ceil_aux_0_functional:∀ {Σ : Signature} {syntax : Syntax} (Γ : Theory) (φ t1 t2 : Pattern),
  Definedness_Syntax.theory ⊆ Γ ->
  well_formed φ ->
  mu_free φ ->
  well_formed t1 ->
  well_formed t2 ->
  mu_free t2 ->
  Γ ⊢i is_functional t1 ---> 
  is_functional t2 --->
  ⌈ t1 and φ ⌉ ---> 
  ⌈ t2 and ⌈ t1 and φ ⌉ ⌉ using AnyReasoning.
Proof.
  intros.
  toMLGoal.
  wf_auto2.
  mlIntro. 
  mlIntro.
  mlIntro.
    
  remember (fresh_evar(φ)  ) as x.
    
  remember ( fresh_evar( φ ---> patt_free_evar x ) ) as y.
    
  epose proof membership_symbol_ceil_aux_0 Γ (x) (y) (φ) AnyReasoning H ltac:(wf_auto2).

  apply universal_generalization with (x := x) in H5.
  2: try_solve_pile.
  2: wf_auto2.
  2: try_solve_pile.
    
  apply universal_generalization with (x := y) in H5.
  2: try_solve_pile.
  2:{ mlSimpl.
      all: try(case_match; reflexivity).
      all: try(case_match; case_match; reflexivity; case_match; reflexivity) .
    }
    
  mlSimpl in H5. simpl in H5. case_match. 2:congruence.
  case_match.
  * exfalso. apply x_eq_fresh_impl_x_notin_free_evars in Heqy. simpl in *. set_solver.
  * mlSimpl in H5. simpl in H5. case_match. 2:congruence.
    use AnyReasoning in H5.
    mlAdd H5.
    
    mlConj "3" "1" as "f".
    mlApplyMeta forall_functional_subst in "f".
    2-3: wf_auto2.
    2:{ simpl. rewrite evar_quantify_fresh.
        1:{ rewrite evar_quantify_fresh. subst x. unfold evar_is_fresh_in. solve_fresh. 
            subst y. unfold evar_is_fresh_in. solve_fresh. 
          }
        rewrite evar_quantify_fresh. 
        subst x. unfold evar_is_fresh_in. solve_fresh.
        wf_auto2.
      }
    2: set_solver.
    mlSimpl. simpl.
      
    mlConj "f" "0" as "g".
    mlApplyMeta forall_functional_subst in "g".
    2-3: wf_auto2.
    2:{ simpl. rewrite evar_quantify_fresh.
        1:{ rewrite evar_quantify_fresh. 
            subst x. unfold evar_is_fresh_in. solve_fresh. 
            subst y. unfold evar_is_fresh_in. solve_fresh. 
          }
        rewrite evar_quantify_fresh. 
        subst x. unfold evar_is_fresh_in. solve_fresh.
        rewrite bevar_subst_not_occur.
        1: wf_auto2.
        wf_auto2.
      }
    2: set_solver.
      
    mlClear "f";mlClear "3";clear H5.
    mlSimpl. simpl.
   
    rewrite evar_quantify_fresh.
    1:{ rewrite evar_quantify_fresh.
        1:{ subst x.  unfold evar_is_fresh_in. solve_fresh. }  
        1:{ subst y. unfold evar_is_fresh_in. solve_fresh. }
      }
        
    rewrite evar_quantify_fresh.
    1:{ subst x. unfold evar_is_fresh_in. solve_fresh. }
   
    rewrite bevar_subst_not_occur.
    1:{ rewrite bevar_subst_not_occur. all:wf_auto2. }
    
    rewrite bevar_subst_not_occur.
    1: wf_auto2.
      
    rewrite bevar_subst_not_occur.
    1: wf_auto2.
      
    mlApply "g".
    mlAssumption.
Defined.

Theorem proved_membership_functional:
  ∀ {Σ : Signature} {syntax : Definedness_Syntax.Syntax} 
   (Γ : Theory) (φ₁ φ₂ : Pattern),
    Definedness_Syntax.theory ⊆ Γ ->
    well_formed φ₁ ->
    well_formed φ₂ ->
    Γ ⊢i φ₁ using AnyReasoning ->
    Γ ⊢i is_functional φ₂ --->  φ₂ ∈ml φ₁  using AnyReasoning .
Proof.
  intros.
  unfold patt_in.
  apply provable_iff_top in H2.
  2:wf_auto2.
  mlRewrite H2 at 1.
  pose proof patt_and_id_r Γ φ₂ ltac:(wf_auto2).
  use AnyReasoning in H3.
  mlRewrite H3 at 1.
  unfold is_functional.
  mlIntro.
  remember (fresh_evar(φ₂)) as x.
  mlDestructEx "0" as x.
  mlSimpl. cbn.
  rewrite evar_open_not_occur.
  wf_auto2.
  mlRewriteBy "0" at 1.
  pose proof defined_evar Γ x H.
  use AnyReasoning in H4.
  mlExactMeta H4.
Defined.

Theorem proved_membership_functional_meta:
  ∀ {Σ : Signature} {syntax : Definedness_Syntax.Syntax} 
   (Γ : Theory) (φ₁ φ₂ : Pattern),
    Definedness_Syntax.theory ⊆ Γ ->
    well_formed φ₁ ->
    well_formed φ₂ ->
    Γ ⊢i is_functional φ₂ using AnyReasoning ->
    Γ ⊢i φ₁ using AnyReasoning ->
    Γ ⊢i  φ₂ ∈ml φ₁  using AnyReasoning .
Proof.
  intros.
  mlApplyMeta proved_membership_functional.
  mlExactMeta H2.
  mlExactMeta H3.
  set_solver.
Defined.

(* Equality elimination for substitution using a functional *)
(* pattern. *)
Lemma equality_elimination_functional_subst {Σ : Signature} {syntax : Syntax} (Γ : Theory) p q p1 p2 x :
  theory ⊆ Γ ->
  well_formed p ->
  well_formed q ->
  well_formed p1 ->
  well_formed p2 ->
  mu_free p ->
  mu_free q ->
  pattern_kt_well_formed p1 ->
  pattern_kt_well_formed p2 ->
  Γ ⊢ p =ml q ->
  Γ ⊢ p1 =ml p2 ->
  Γ ⊢ is_functional p1 ->
  Γ ⊢ p^[[evar: x ↦ p1]] =ml q^[[evar: x ↦ p2]].
Proof.
  intros HΓ Hwfp Hwfq Hwfp1 Hwfp2 Hmfp Hmfq Hktwfp1 Hktwfp2 Hpeqq Hp1eqp2 Hfuncp1.
  pose proof mf_imp_ktwf _ Hmfp as Hktwfp.
  pose proof mf_imp_ktwf _ Hmfq as Hktwfq.
  apply universal_generalization with (x := x) in Hpeqq;
  [| try_solve_pile | wf_auto2].
  eapply forall_functional_subst_meta with (φ' := p1) in Hpeqq;
  auto; [|rewrite <- mu_free_evar_quantify | ..];
  [| wf_auto2 ..].
  rewrite bevar_subst_evar_quantify in Hpeqq; [wf_auto2 |].
  mlSimpl in Hpeqq.
  mlFreshEvar as y.
  unshelve epose proof MP Hp1eqp2 (equality_elimination Γ p1 p2 {|pcPattern := p^[[evar: x ↦ p1]] =ml q^[[evar: x ↦ patt_free_evar y]]; pcEvar := y|} HΓ _ _ _ _); try solve [wf_auto2].
  simpl. rewrite ! pattern_kt_well_formed_free_evar_subst; auto.
  unfold emplace in H. mlSimpl in H. cbn in H.
  rewrite -> 2 free_evar_subst_chain in H; [| fm_solve ..].
  rewrite -> 2 (free_evar_subst_no_occurrence y) in H; [| fm_solve ..].
  exact (MP Hpeqq H).
Defined.

Section EqCon.
  Context {Σ : Signature} {syntax : Syntax}.

  (* The remainder works for any theory containing definedness. *)
  Context (Γ : Theory).
  Hypothesis (HΓ : theory ⊆ Γ).

  (* The patterns that will be equal, *)
  (* and the evars that they will replace. *)
  Context (σ : list (evar * Pattern * Pattern)).
  (* They are well-formed... *)
  Hypothesis (Hσ1 : wf (map (snd ∘ fst) σ)) (Hσ2 : wf (map snd σ)).
  (* ... mu-free ... *)
  Hypothesis (Hmfσ1 : foldr (fun c a => mu_free c && a) true (map (snd ∘ fst) σ)).
  Hypothesis (Hmfσ2 : foldr (fun c a => mu_free c && a) true (map snd σ)).
  (* ... and one of them is functional. *)
  Hypothesis (Hfpσ : foldr (fun c a => ((Γ ⊢ is_functional c.1.2) * a)%type) unit σ).

  (* Separate equalities as a hypothesis. *)
  Definition hypos : Type := foldr (fun x t => ((Γ ⊢ x.1.2 =ml x.2) * t)%type) unit σ.

  (* Same as `emplace`ing into a context with multiple holes. *)
  Definition goal (φ : Pattern) : Pattern := (foldr (fun x p => p^[[evar: x.1.1 ↦ x.1.2]]) φ σ) =ml (foldr (fun x p => p^[[evar: x.1.1 ↦ x.2]]) φ σ).

  (* For any pattern (which would serve as the core of the context), *)
  (* given the eqalities as hypothesis, substituting into the *)
  (* multihole context yields equality. *)
  Lemma eqcon : forall φ,
    well_formed φ ->
    mu_free φ ->
    hypos ->
    Γ ⊢ goal φ.
  Proof.
    intros ? Hwfφ Hmfφ.
    unfold hypos, goal.
    induction σ; simpl; intros.
    now aapply patt_equal_refl.
    simpl in Hσ1, Hσ2. apply wf_cons_iff in Hσ1 as [], Hσ2 as [].
    simpl in Hmfσ1, Hmfσ2. apply andb_true_iff in Hmfσ1 as [], Hmfσ2 as [].
    simpl in Hfpσ.
    destruct X as [? ?%(IHl H0 H2)]. clear IHl.
    apply equality_elimination_functional_subst; auto.
    - eapply wf_foldr. auto. exact H0.
      intros ? [[] ?] **. wf_auto2.
    - eapply wf_foldr. auto. exact H2.
      intros ? [[] ?] **. wf_auto2.
    - eapply mf_foldr. auto. exact H4.
      intros ? [[] ?] **. simpl in H8 |- *. now apply mu_free_free_evar_subst.
    - eapply mf_foldr. auto. exact H6.
      intros ? [[] ?] **. simpl in H8 |- *. now apply mu_free_free_evar_subst.
    - now apply mf_imp_ktwf.
    - now apply mf_imp_ktwf.
    - exact (Hfpσ.1).
    - auto.
    - auto.
    - exact (Hfpσ.2).
  Defined.
End EqCon.

Section Example.
  Context {Σ : Signature} {syntax : Syntax}.

  (* In any theory that contains the theory of definedness ... *)
  Context (Γ : Theory).
  Hypothesis (HΓ : theory ⊆ Γ).

  (* ... given some function/context ... *)
  Context (kseq_sym : symbols).
  Definition kseq x y := patt_sym kseq_sym ⋅ x ⋅ y.

  (* ... and two pairs of patterns ... *)
  Context (one two one' two' : Pattern).
  (* ... some of which are functional and all of which are *)
  (* well-formed and free of fixed points ... *)
  Hypothesis (fpone : Γ ⊢ is_functional one).
  Hypothesis (fptwo : Γ ⊢ is_functional two).
  Hypothesis (Hwf : well_formed one /\ well_formed two /\ well_formed one' /\ well_formed two').
  Hypothesis (Hmf : mu_free one /\ mu_free two /\ mu_free one' /\ mu_free two').
  (* ... and pairwise provable equal ... *)
  Hypothesis (Heqone : Γ ⊢ one =ml one').
  Hypothesis (Heqtwo : Γ ⊢ two =ml two').

  (* ... and given two different evars, one of which is free *)
  (* in two of the patterns ... *)
  Context (x y : evar).
  Hypothesis (Hxneqy : y ≠ x).
  Hypothesis (Hxfree : x ∉ free_evars two ∪ free_evars two').

  (* ... substituting the two into the same context *)
  (* is also equal. *)
  (*            one = one'       two = two'            *)
  (* ------------------------------------------------- *)
  (* (kseq □₁ □₂)[one, two] = (kseq □₁ □₂)[one', two'] *)
  Goal Γ ⊢ kseq one two =ml kseq one' two'.
  Proof.
    decompose record Hwf. clear Hwf.
    decompose record Hmf. clear Hmf.
    pose [(x, one, one'); (y, two, two')] as pairs.
    pose (kseq (patt_free_evar x) (patt_free_evar y)) as base_pat.

    opose proof* (eqcon Γ _ pairs _ _ _ _ _ base_pat);

    (* side conditions *)
    subst pairs base_pat; simpl.
    6,9: repeat split. all: auto.
    1-4: wf_auto2.

    (* simplification *)
    unfold goal in H6. simpl in H6.
    destruct (decide (y = x)). contradiction.
    simpl in H6. rewrite ! decide_eq_same in H6.
    rewrite ! free_evar_subst_no_occurrence in H6.
    1-2: set_solver.
    fold (kseq one two) in H6. fold (kseq one' two') in H6.

    assumption.
  Qed.
End Example.
 
Close Scope ml_scope.
Close Scope string_scope.
Close Scope list_scope.
