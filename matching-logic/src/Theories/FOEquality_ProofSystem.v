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

Close Scope ml_scope.
Close Scope string_scope.
Close Scope list_scope.
