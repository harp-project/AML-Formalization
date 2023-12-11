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

Set Default Proof Mode "Classic".

From MatchingLogic Require Import
  Theories.DeductionTheorem
  Theories.Sorts_Syntax
  FOEquality_ProofSystem
  Sorts_ProofSystem
  Nat_Syntax
.

Import MatchingLogic.Theories.Sorts_Syntax.Notations.

Open Scope ml_scope.
Open Scope string_scope.
Open Scope list_scope.

Section nat.
  Context
    {Σ : Signature}
    {syntax : Nat_Syntax.Syntax}
  .

  Lemma use_nat_axiom ax Γ :
    Nat_Syntax.theory ⊆ Γ ->
    Γ ⊢ axiom ax.
  Proof.
    intro HΓ.
    apply useBasicReasoning.
    apply BasicProofSystemLemmas.hypothesis.
    { destruct ax; wf_auto2. }
    {
      apply elem_of_weaken with (X := theory_of_NamedAxioms named_axioms).
      {
        unfold theory_of_NamedAxioms, named_axioms, axiom; simpl.
        apply elem_of_PropSet.
        exists ax.
        reflexivity.
      }
      {
        unfold theory in HΓ.
        set_solver.
      }
    }
  Defined.

  Lemma nat_subset_imp_in X :
    theory ⊢ (〚 Nat 〛 ⊆ml patt_free_svar X) ---> (all Nat, b0 ∈ml patt_free_svar X).
  Proof.
    unfold patt_forall_of_sort.
    unfold patt_in.
    unfold nest_ex; simpl; fold Nat.
    unfold patt_subseteq.
    apply deduction_theorem with (gpi := (ExGen := {[fresh_evar ⊥]}, SVSubst := ∅, KT := false, AKT := false)).
    rewrite <- evar_quantify_evar_open with (n := 0) (phi := (⌈ b0 and 〚 Nat 〛 ⌉ ---> ⌈ b0 and patt_free_svar X ⌉)) (x := fresh_evar ⊥).
    apply universal_generalization.
    { try_solve_pile. }
    { wf_auto2. }
    {
      unfold evar_open.
      mlSimpl.
      simpl.
      apply ceil_monotonic.
      { unfold theory. set_solver. }
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
    { unfold theory. set_solver. }
    { set_solver. }
    { set_solver. }
    { set_solver. }
  Defined.

  Theorem peano_induction_meta X :
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
    { unfold theory. set_solver. }

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
      2: instantiate (1 := fresh_evar ⊥); solve_fresh.
      2: { unfold theory. set_solver. }

      fromMLGoal.

      apply membership_impl_subseteq.
      { unfold theory. set_solver. }
      { reflexivity. }
      { reflexivity. }
      { wf_auto2. }
      { wf_auto2. }
      {
        toMLGoal.
        { wf_auto2. }
        mlApplyMeta ex_sort_impl_ex.
        2: { unfold theory. set_solver. }
        mlAdd (use_nat_axiom AxFun1 theory ltac:(reflexivity)) as "f"; unfold axiom.
        mlExact "f".
      }
      assumption.
    }
    { (* Inductive case *)
      fromMLGoal.
      apply membership_elimination with (x := ev_x).
      { solve_free_evars 1. }
      { apply pile_any. }
      { wf_auto2. }
      { unfold theory. set_solver. }

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
      ospecialize* Htmp.
      { unfold theory. set_solver. }
      { wf_auto2. }
      { wf_auto2. }
      use AnyReasoning in Htmp.

      toMLGoal.
      { wf_auto2. }

      mlRewrite Htmp at 1. clear Htmp. fold AnyReasoning.

      unfold patt_forall_of_sort, nest_ex in S; simpl in S; fold Nat in S.

      pose proof (Htmp := membership_symbol_right theory (patt_free_svar X) Succ x).
      ospecialize* Htmp.
      { unfold theory. set_solver. }
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

      gapply BasicProofSystemLemmas.Ex_gen.
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
      ospecialize* M.
      { unfold theory. set_solver. }
      { reflexivity. }
      { wf_auto2. }
      { wf_auto2. }

      apply total_phi_impl_phi_meta with (x := fresh_evar ⊥) in XN;
      [|unfold theory; set_solver|set_solver|wf_auto2|apply pile_any].

      mlAdd M as "M". clear M.
      mlApplyMeta and_impl' in "M".
      mlApplyMeta and_impl' in "M".
      mlAssert ("M0" : (patt_free_evar x =ml Succ $ patt_free_evar y)).
      { wf_auto2. }
      {
        mlApply "M". mlClear "M".
        mlSplitAnd. mlSplitAnd.
        + mlClear "ys". mlClear "H0".
          mlApplyMeta BasicProofSystemLemmas.Ex_quan.
          unfold instantiate. mlSimpl. simpl.
          fromMLGoal.
          aapply patt_equal_refl.
          { wf_auto2. }
        + mlApplyMeta ex_sort_impl_ex;[|unfold theory; set_solver].
          mlAdd (use_nat_axiom AxFun2 theory ltac:(set_solver)) as "H"; unfold axiom.
          unfold "all _ , _", nest_ex; simpl; fold Nat.
          rewrite <- evar_quantify_evar_open with (x := y) (n := 0) (phi := b0 ∈ml 〚 Nat 〛 ---> (ex Nat , Succ $ b1 =ml b0)).
          2: {
            subst y. eapply evar_is_fresh_in_richer'.
            2: apply set_evar_fresh_is_fresh'.
            clear. set_solver.
          }
          2: wf_auto2.
          mlApplyMeta forall_variable_substitution in "H".
          2-10: case_match;[wf_auto2|congruence].
          unfold evar_open. mlSimpl. simpl.
          case_match. 2: congruence.
          mlApply "H". mlClear "H". mlClear "H0".
          unfold patt_in.
          fromMLGoal.
          aapply ceil_monotonic;[unfold theory; set_solver|wf_auto2|wf_auto2|].
          toMLGoal. wf_auto2.
          mlIntro "yX".
          mlDestructAnd "yX" as "y" "X".
          mlSplitAnd.
          * mlExact "y".
          * mlAdd XN as "H". mlApply "H". mlExact "X". 
        + mlExact "H0".
      }
      mlClear "M".

      mlRewriteBy "M0" at 1;[unfold theory; set_solver|].

      mlClear "M0".

      apply forall_elim with (x := y) in S.
      2: { wf_auto2. }
      unfold evar_open in S. mlSimpl in S. simpl in S.
      mlAdd S as "S". clear S.
      mlApplyMeta and_impl' in "S".
      mlApply "S". mlClear "S".
      mlSplitAnd.
      + mlClear "H0".
        fromMLGoal.
        aapply ceil_monotonic;[unfold theory; set_solver|wf_auto2|wf_auto2|].
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

  Theorem peano_induction X :
    theory ⊢ patt_free_svar X ⊆ml 〚 Nat 〛 --->
             Zero ∈ml patt_free_svar X --->
             (all Nat, (b0 ∈ml patt_free_svar X ---> Succ $ b0 ∈ml patt_free_svar X))--->
             all Nat, b0 ∈ml patt_free_svar X.
  Proof.
    toMLGoal.
    { wf_auto2. }
    mlIntro "H".
    mlIntro "H1".
    mlIntro "H2".

    mlApplyMeta nat_subset_imp_in.
    remember (evar_fresh []) as x.
    pose proof membership_symbol_ceil_aux_aux_0 theory x ( patt_free_svar X) 
                                         ltac:( unfold theory;set_solver) ltac:(wf_auto2) as H.
   apply universal_generalization with (x:=x) in H.
   2: try_solve_pile.
   2: wf_auto2.
   mlSimpl in H. simpl in H.
   case_match. 2: congruence.
   assert ( theory ⊢ (ex , Zero =ml b0) ). {
     pose proof (hypothesis theory (ex Nat, Zero =ml b0) ltac:(wf_auto2)).
     ospecialize* H1.
     { unfold theory, named_axioms, theory_of_NamedAxioms. simpl.
       apply elem_of_union_r. exists AxFun1. reflexivity.
     }
     use AnyReasoning in H1.
     mlAdd H1 as "H".
     mlDestructEx "H" as x. mlSimpl. cbn. mlDestructAnd "H".
     mlExists x. mlAssumption.
   }
   use AnyReasoning in H.
(*    epose proof conj_intro_meta _ _ _ _ _ _ H H1.
   Unshelve.
   2-3: wf_auto2. *)
     mlSpecMeta H with Zero.
     2:unfold theory;set_solver.
     2:simpl;reflexivity.
     mlSimpl in H.
     simpl in H.
     mlApplyMeta H in "H1".

     Search patt_and patt_total.
     unfold patt_forall_of_sort.
     
     Search patt_exists patt_total derives_using.
    (* rephrase "H2" into a totality statement and use propagation of totality through conjuction  *)
 Admitted.

  Lemma floor_propagation_forall_1 :
    forall Γ φ,
      Definedness_Syntax.theory ⊆ Γ ->
      well_formed (ex, φ) ->
      Γ ⊢ (all , ⌊φ⌋) ---> ⌊all , φ⌋.
  Proof.
    intros Γ φ HΓ Hwf.
    unfold patt_forall.
    mlIntro "H". mlIntro "H0".
    mlApplyMeta def_not_phi_impl_not_total_phi in "H0". 2: assumption.
    pose proof (def_propagate_not Γ (ex, ! φ) HΓ ltac:(wf_auto2)) as H.
    use AnyReasoning in H. mlAdd H as "H1".
    mlDestructAnd "H1" as "H1_1" "H1_2".
    mlApply "H0". mlApply "H1_1". mlClear "H1_1". mlClear "H1_2".
    mlClear "H0".
    mlIntro "H0".
    mlApply "H". mlClear "H".
    mlApplyMeta ceil_propagation_exists_1 in "H0". 2: assumption.
    mlDestructEx "H0" as x. mlExists x. mlSimpl.
    mlApplyMeta def_not_phi_impl_not_total_phi in "H0". 2: assumption.
    mlAssumption.
  Defined.

  Lemma exists_exists_of_sort :
    forall Γ φ s,
      Definedness_Syntax.theory ⊆ Γ ->
      well_formed (ex, φ) ->
      well_formed s ->
      Γ ⊢ (ex s, φ) ---> ex, φ.
  Proof.
    intros Γ φ s HΓ wf1 wf2.
    mlIntro "H".
    remember (fresh_evar (s $ φ)) as x.
    mlDestructEx "H" as x. rewrite free_evars_nest_ex. solve_fresh.
    mlExists x. mlSimpl. cbn. mlDestructAnd "H". mlExact "1".
  Defined.

  Lemma predicate_imp :
    forall Γ φ ψ,
      Definedness_Syntax.theory ⊆ Γ ->
      well_formed φ ->
      well_formed ψ ->
      Γ ⊢ is_predicate φ --->
          is_predicate ψ --->
          is_predicate (φ ---> ψ).
  Proof.
    intros Γ φ ψ HΓ wf1 wf2.
    mlIntro "H". mlIntro "H0".
    unfold is_predicate. mlDestructOr "H"; mlDestructOr "H0".
    all: mlRewriteBy "0" at 1; mlRewriteBy "1" at 1.
    all: mlRewriteBy "0" at 1; mlRewriteBy "1" at 1.
  Defined.

  Lemma predicate_equiv :
    forall Γ φ,
      Definedness_Syntax.theory ⊆ Γ ->
      well_formed φ ->
      Γ ⊢ is_predicate φ ---> φ <---> ⌊φ⌋.
  Proof.
    
  Defined.

  Lemma patt_in_is_predicate :
    forall Γ φ ψ,
      Definedness_Syntax.theory ⊆ Γ ->
      well_formed φ ->
      well_formed ψ ->
      Γ ⊢ is_functional φ ---> is_predicate ψ ---> is_predicate (φ ∈ml ψ)

End nat.

Close Scope ml_scope.
Close Scope string_scope.
Close Scope list_scope.