From Coq Require Import ssreflect ssrfun ssrbool.

From Ltac2 Require Import Ltac2.

From Coq Require Import String Ensembles Setoid.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.Classical_Prop.
From Coq.Logic Require Import FunctionalExtensionality Eqdep_dec.
From Coq.Classes Require Import Morphisms_Prop.
From Coq.Unicode Require Import Utf8.
From Coq.micromega Require Import Lia.

From MatchingLogic Require Import Logic ProofMode.
From MatchingLogic.Theories Require Import Definedness_Syntax Definedness_ProofSystem.
From MatchingLogic.Utils Require Import stdpp_ext.

Require Import MatchingLogic.wftactics.

From stdpp Require Import base fin_sets sets propset proof_irrel option list.

Import extralibrary.

Import MatchingLogic.Logic.Notations.
Import MatchingLogic.Theories.Definedness_Syntax.Notations.

Set Default Proof Mode "Classic".

From MatchingLogic Require Import
  Theories.DeductionTheorem
  Theories.Sorts_Syntax
  Theories.Unification.

Import MatchingLogic.Theories.Sorts_Syntax.Notations.

Open Scope ml_scope.
Open Scope string_scope.
Open Scope list_scope.

(* TODO: Put in a different file? *)
Lemma ex_sort_impl_ex {Σ : Signature} {syntax : Syntax} Γ ϕ s :
  well_formed (ex , ϕ) ->
  theory ⊆ Γ ->
  Γ ⊢ ex (patt_sym s) , ϕ ---> (ex , ϕ).
Proof.
  intros wfϕ HΓ.

  unfold "ex _ , _".

  unfold nest_ex; simpl.

  remember (fresh_evar (b0 ∈ml 〚 patt_sym s 〛 and ϕ)) as x.
  rewrite <- evar_quantify_evar_open with (n := 0) (x := x) (phi := b0 ∈ml 〚 patt_sym s 〛 and ϕ).
  2: {
    subst x. eapply evar_is_fresh_in_richer'.
    2: apply set_evar_fresh_is_fresh'.
    clear. set_solver.
  }
  2: {
    wf_auto2.
  }

  gapply Ex_gen.
  { apply pile_any. }
  { apply pile_any. }
  {
    subst x. eapply evar_is_fresh_in_richer'.
    2: { apply set_evar_fresh_is_fresh'. }
    clear. set_solver.
  }

  mlSimpl. unfold evar_open. simpl.

  toMLGoal.
  { wf_auto2. }
  mlIntro "H".
  mlDestructAnd "H" as "H0" "H1".
  mlClear "H0".

  mlApplyMeta Ex_quan. simpl.
  mlExact "H1".
Defined.

Section nat_syntax.

  Context {Σ : Signature}.

  Inductive Symbols := sNat | sZero | sSucc.

  Class Syntax :=
    { inj : Symbols -> symbols;
      imported_sorts :> Sorts_Syntax.Syntax;
    }.
  Context {self : Syntax}.

  Definition Nat := patt_sym (inj sNat).
  Definition Zero := patt_sym (inj sZero).
  Definition Succ := patt_sym (inj sSucc).

End nat_syntax.

Section nat.
  Context
    {Σ : Signature}
    {syntax : Syntax}
  .

  Inductive AxiomName := 
  | AxFun1
  | AxFun2
  | AxNoConfusion1
  | AxNoConfusion2
  | AxInductiveDomain.

  Definition axiom (name : AxiomName) : Pattern :=
    match name with
    | AxFun1 => ex Nat , Zero =ml b0
    | AxFun2 => all Nat, ex Nat, Succ $ b1 =ml b0
    | AxNoConfusion1 => all Nat, !(Zero =ml Succ $ b0)
    | AxNoConfusion2 => all Nat, all Nat, (Succ $ b1 =ml Succ $ b0 ---> b1 =ml b0)
    | AxInductiveDomain => 〚 Nat 〛 =ml mu , Zero or Succ $ B0
    end.

  Program Definition named_axioms : NamedAxioms :=
    {|
      NAName := AxiomName;
      NAAxiom := axiom;
    |}.
  Next Obligation.
    destruct name; simpl; wf_auto2.
  Qed.

  Definition theory := Definedness_Syntax.theory ∪ theory_of_NamedAxioms named_axioms.

  Lemma use_nat_axiom ax Γ :
    theory ⊆ Γ ->
    Γ ⊢ axiom ax.
  Proof.
    intro HΓ.
    apply useBasicReasoning.
    apply BasicProofSystemLemmas.hypothesis.
    { destruct ax; wf_auto2. }
    {
      apply elem_of_weaken with (X := theory_of_NamedAxioms named_axioms).
      unfold theory_of_NamedAxioms, named_axioms, axiom; simpl.
      apply elem_of_PropSet.
      exists ax.
      reflexivity.
      set_solver.
    }
  Defined.

  Lemma nat_subset_imp_in X :
    theory ⊢ (〚 Nat 〛 ⊆ml patt_free_svar X) ---> (all Nat, b0 ∈ml patt_free_svar X).
  Proof.
    unfold patt_forall_of_sort.
    unfold patt_in.
    unfold nest_ex; simpl; fold Nat.
    unfold patt_subseteq.
    apply deduction_theorem with (gpi := (ExGen := {[fresh_evar ⊥]}, SVSubst := ∅, KT := false, FP := ⊤)).
    rewrite <- evar_quantify_evar_open with (n := 0) (phi := (⌈ b0 and 〚 Nat 〛 ⌉ ---> ⌈ b0 and patt_free_svar X ⌉)) (x := fresh_evar ⊥).
    apply universal_generalization.
    { try_solve_pile. }
    { wf_auto2. }
    {
      unfold evar_open.
      mlSimpl.
      simpl.
      apply ceil_monotonic.
      { set_solver. }
      { try_solve_pile. }
      { wf_auto2. }
      { wf_auto2. }
      apply and_weaken.
      { wf_auto2. }
      { wf_auto2. }
      { wf_auto2. }
      apply useBasicReasoning.
      apply BasicProofSystemLemmas.hypothesis.
      { wf_auto2. }
      { clear. set_solver. }
    }
    { clear. set_solver. }
    { wf_auto2. }
    { wf_auto2. }
    { wf_auto2. }
    { set_solver. }
    { set_solver. }
    { set_solver. }
  Defined.

  Theorem peano_induction X :
    theory ⊢ patt_free_svar X ⊆ml 〚 Nat 〛 ->
    theory ⊢ Zero ∈ml patt_free_svar X ->
    theory ⊢ all Nat, (b0 ∈ml patt_free_svar X ---> Succ $ b0 ∈ml patt_free_svar X) ->
    theory ⊢ all Nat, b0 ∈ml patt_free_svar X.
  Proof.
    intros XN Z S.

    toMLGoal.
    { wf_auto2. }

    mlApplyMeta nat_subset_imp_in.

    mlAdd (use_nat_axiom AxInductiveDomain theory ltac:(reflexivity)) as "ind". unfold axiom.
    mlRewriteBy "ind" at 1.
    { set_solver. }
    { reflexivity. }

    mlClear "ind".
    unfold "⊆ml".
    fromMLGoal.

    apply phi_impl_total_phi_meta.
    { wf_auto2. }
    { apply pile_any. }

    apply Knaster_tarski.
    { apply pile_any. }
    { wf_auto2. }
    unfold instantiate. mlSimpl. simpl.

    toMLGoal.
    { wf_auto2. }
    mlIntro "H".
    mlDestructOr "H" as "Z0" "S0".
    { (* Base case *)
      mlRevertLast.
      mlApplyMeta total_phi_impl_phi.
      2: set_solver.

      fromMLGoal.

      apply membership_impl_subseteq.
      { set_solver. }
      { reflexivity. }
      { reflexivity. }
      { wf_auto2. }
      { wf_auto2. }
      {
        toMLGoal.
        { wf_auto2. }
        mlApplyMeta ex_sort_impl_ex.
        2: set_solver.
        mlAdd (use_nat_axiom AxFun1 theory ltac:(reflexivity)) as "f"; unfold axiom.
        mlExact "f".
      }
      assumption.
    }
    { (* Inductive case *)
      fromMLGoal.
      apply membership_elimination.
      { apply pile_any. }
      { wf_auto2. }
      { set_solver. }

      remember (fresh_evar (b0 ∈ml (Succ $ patt_free_svar X ---> patt_free_svar X))) as x.

      rewrite <- evar_quantify_evar_open with (phi := b0 ∈ml (Succ $ patt_free_svar X ---> patt_free_svar X)) (n := 0) (x := x).
      2: {
        subst x.
        eapply evar_is_fresh_in_richer'.
        2: { apply set_evar_fresh_is_fresh'. }
        clear. set_solver.
      }
      2: { cbn. reflexivity. }
      apply universal_generalization;[apply pile_any|wf_auto2|].
      mlSimpl. unfold evar_open. simpl.

      pose proof (Htmp := membership_imp theory x (Succ $ patt_free_svar X) (patt_free_svar X)).
      feed specialize Htmp.
      { set_solver. }
      { wf_auto2. }
      { wf_auto2. }
      apply useAnyReasoning in Htmp.

      toMLGoal.
      { wf_auto2. }

      mlRewrite Htmp at 1. clear Htmp. fold AnyReasoning.

      unfold patt_forall_of_sort, nest_ex in S; simpl in S; fold Nat in S.

      pose proof (Htmp := membership_symbol_right theory (patt_free_svar X) Succ x).
      feed specialize Htmp.
      { set_solver. }
      { wf_auto2. }
      { wf_auto2. }
      { reflexivity. }
      { reflexivity. }
      mlIntro "H".
      mlApplyMeta Htmp in "H". clear Htmp.

      fromMLGoal.

      remember (fresh_evar (b0 ∈ml patt_free_svar X and patt_free_evar x ∈ml Succ $ b0)) as y.
      rewrite <- evar_quantify_evar_open with (n := 0) (x := y) (phi := b0 ∈ml patt_free_svar X and patt_free_evar x ∈ml Succ $ b0).
      2: {
        subst y. eapply evar_is_fresh_in_richer'.
        2: { apply set_evar_fresh_is_fresh'. }
        clear. set_solver.
      }
      2: {
        wf_auto2.
      }

      gapply Ex_gen.
      { apply pile_any. }
      { apply pile_any. }
      {
        subst y. eapply evar_is_fresh_in_richer'.
        2: { apply set_evar_fresh_is_fresh'. }
        clear. set_solver.
      }

      mlSimpl. unfold evar_open. simpl. fold AnyReasoning.

      toMLGoal.
      { wf_auto2. }
      mlIntro "H".
      mlDestructAnd "H" as "ys" "H0".

      pose proof (M := membership_imp_equal theory (patt_free_evar x) (Succ $ patt_free_evar y)).
      feed specialize M.
      { set_solver. }
      { reflexivity. }
      { wf_auto2. }
      { wf_auto2. }

      apply total_phi_impl_phi_meta in XN;[|set_solver|wf_auto2|apply pile_any].

      mlAdd M as "M". clear M.
      mlApplyMeta and_impl' in "M".
      mlApplyMeta and_impl' in "M".
      mlAssert ("M0" : (patt_free_evar x =ml Succ $ patt_free_evar y)).
      { wf_auto2. }
      {
        mlApply "M". mlClear "M".
        mlSplitAnd. mlSplitAnd.
        + mlClear "ys". mlClear "H0".
          mlApplyMeta Ex_quan.
          unfold instantiate. mlSimpl. simpl.
          fromMLGoal.
          aapply patt_equal_refl.
          { wf_auto2. }
        + mlApplyMeta ex_sort_impl_ex;[|set_solver].
          mlAdd (use_nat_axiom AxFun2 theory ltac:(set_solver)) as "H"; unfold axiom.
          unfold "all _ , _", nest_ex; simpl; fold Nat.
          rewrite <- evar_quantify_evar_open with (x := y) (n := 0) (phi := b0 ∈ml 〚 Nat 〛 ---> (ex Nat , Succ $ b1 =ml b0)).
          2: {
            subst y. eapply evar_is_fresh_in_richer'.
            2: apply set_evar_fresh_is_fresh'.
            clear. set_solver.
          }
          2: wf_auto2.
          mlApplyMeta forall_variable_substitution in "H". unfold evar_open. mlSimpl. simpl.
          mlApply "H". mlClear "H". mlClear "H0".
          unfold patt_in.
          fromMLGoal.
          aapply ceil_monotonic;[set_solver|wf_auto2|wf_auto2|].
          toMLGoal. wf_auto2.
          mlIntro "yX".
          mlDestructAnd "yX" as "y" "X".
          mlSplitAnd.
          * mlExact "y".
          * mlAdd XN as "H". mlApply "H". mlExact "X".
        + mlExact "H0".
      }
      mlClear "M".

      mlRewriteBy "M0" at 1;[set_solver|reflexivity|]. mlClear "M0".

      apply forall_elim with (x := y) in S.
      2: { wf_auto2. }
      2: {
        subst y. eapply evar_is_fresh_in_richer'.
        2: { apply set_evar_fresh_is_fresh'. }
        clear. set_solver.
      }
      2: { apply pile_any. }
      unfold evar_open in S. mlSimpl in S. simpl in S.
      mlAdd S as "S". clear S.
      mlApplyMeta and_impl' in "S".
      mlApply "S". mlClear "S".
      mlSplitAnd.
      + mlClear "H0".
        fromMLGoal.
        aapply ceil_monotonic;[set_solver|wf_auto2|wf_auto2|].
        toMLGoal. wf_auto2.
        mlAdd XN as "H".
        mlIntro "yX".
        mlDestructAnd "yX" as "y" "X".
        mlSplitAnd.
        * mlExact "y".
        * mlApply "H". mlExact "X". 
      + mlExact "ys".
    }
  Defined.

End nat.

Close Scope ml_scope.
Close Scope string_scope.
Close Scope list_scope.