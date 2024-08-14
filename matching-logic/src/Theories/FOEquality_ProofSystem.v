From Coq Require Import ssreflect ssrfun ssrbool.

From Ltac2 Require Import Ltac2.

From Coq Require Import String Ensembles Setoid.
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
  mlRewrite (patt_equal_comm (patt_free_evar x) g Γ HΓ ltac:(wf_auto2) ltac:(wf_auto2)) at 1. fold AnyReasoning.
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
  Γ ⊢ (ex , t2 =ml b0) ---> (all , ex , (t1 $ b1)%ml =ml b0) --->
    ex , (t1 $ t2)%ml =ml b0.
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
    | S n' => all , nary_function (f $ patt_bound_evar (S n')) n'
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
    specialize (IHm n (φ $ patt_bound_evar (S m)) ltac:(lia)).
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
    opose proof* (IHl (φ $ a) HΓ H2 ltac:(wf_auto2)).
    { simpl. by rewrite H HMF1. }
    { assumption. }
    toMLGoal.
    {
      simpl in *. clear Halmost H.
      repeat apply well_formed_imp. 2-3: wf_auto2.
      * assert (well_formed_positive (nary_function (φ $ patt_bound_evar (S (length l))) (length l))). {
          apply nary_function_well_formed_positive. wf_auto2.
        }
        assert (well_formed_closed_mu_aux (nary_function (φ $ patt_bound_evar (S (length l))) (length l)) 0). {
          apply nary_function_well_formed_closed_mu_aux. wf_auto2.
        }
        assert (well_formed_closed_ex_aux (nary_function (φ $ patt_bound_evar (S (length l))) (length l)) 1). {
          replace 1 with (S (S (length l)) - S (length l)) by lia.
          apply nary_function_well_formed_closed_ex_aux. wf_auto2.
          case_match; lia.
        }
        wf_auto2.
      * apply wf_foldr with (t := fun p => (ex , p =ml b0)).
        - remember (fresh_evar (foldl patt_app (φ $ a) l)) as x.
          pose proof (evar_quantify_well_formed (foldl patt_app (φ $ a) l =ml patt_free_evar x) x).
          mlSimpl in H. simpl in H. rewrite decide_eq_same in H.
          rewrite evar_quantify_fresh in H. subst x. solve_fresh.
          apply H.
          apply well_formed_equal. 2: wf_auto2.
          rewrite foldl_fold_left.
          apply wf_fold_left with (t := id). wf_auto2. by rewrite map_id.
          clear. intros. wf_auto2.
        - apply map_wf. assumption. clear. intros. wf_auto2.
        - clear. intros. wf_auto2.
    }
    mlIntro. mlIntro.
    mlApplyMeta IHl.
    2: { assumption. }
    2: { simpl. by rewrite H HMF1. }
    opose proof* (forall_functional_subst (nary_function (φ $ patt_bound_evar (S (length l))) (length l)) a Γ HΓ).
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
  Γ ⊢ ex, (((patt_sym f $ patt_free_evar x) $ patt_sym g $ patt_sym one) $ patt_sym g $ patt_free_evar y)%ml =ml b0.
Proof.
  intros * HΓ Hf Hg Hone.
  toMLGoal. { wf_auto2. }
  solve_functional.
Defined.

Close Scope ml_scope.
Close Scope string_scope.
Close Scope list_scope.
