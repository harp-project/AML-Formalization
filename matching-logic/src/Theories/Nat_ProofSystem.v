From Coq Require Import ssreflect ssrfun ssrbool.

From Ltac2 Require Import Ltac2.

From Coq Require Import String Ensembles Setoid.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.Classical_Prop.
From Coq.Logic Require Import FunctionalExtensionality Eqdep_dec.
From Coq.Classes Require Import Morphisms_Prop.
From Coq.Unicode Require Import Utf8.
From Coq.micromega Require Import Lia.

From MatchingLogic Require Export Logic ProofMode.MLPM SyntacticConstruct.
From MatchingLogic.Theories Require Export Definedness_Syntax Definedness_ProofSystem.
From MatchingLogic.Utils Require Export stdpp_ext.

Require Export MatchingLogic.wftactics.

From stdpp Require Import base fin_sets sets propset proof_irrel option list.

Import extralibrary.

Import MatchingLogic.Logic.Notations.
Import MatchingLogic.Theories.Definedness_Syntax.Notations.

Set Default Proof Mode "Classic".

Require Import MatchingLogic.Theories.DeductionTheorem.

Require Export MatchingLogic.Theories.Sorts_Syntax.
Export MatchingLogic.Theories.Sorts_Syntax.Notations.

From Coq Require Import ssreflect ssrfun ssrbool.

Require Import Setoid.
From Coq Require Import Unicode.Utf8.
From Coq.Logic Require Import Classical_Prop FunctionalExtensionality.
From Coq.Classes Require Import Morphisms_Prop.

From stdpp Require Import base sets.

From MatchingLogic Require Import Logic MLPM.
Import MatchingLogic.Logic.Notations.
Require Import MatchingLogic.Theories.Nat_Syntax.

Import MatchingLogic.Theories.Definedness_Syntax.Notations.
Import MatchingLogic.Theories.Nat_Syntax.Notations.
Import BoundVarSugar.

Set Default Proof Mode "Classic".

From MatchingLogic Require Import
  Theories.DeductionTheorem
  Theories.Sorts_Syntax
  FOEquality_ProofSystem
  Sorts_ProofSystem
  Nat_Syntax.

Import MatchingLogic.Theories.Sorts_Syntax.Notations.

Open Scope ml_scope.
Open Scope string_scope.
Open Scope list_scope.

  
  
  Theorem use_bigger_theory {Σ: Signature} :  forall Γ Γ' φ i, Γ ⊆ Γ' -> Γ ⊢i φ using i -> Γ' ⊢i φ using i.
  Proof.
  Admitted.
  
Section nat.
  Context
    {Σ : Signature}
    {syntax : Nat_Syntax.Syntax}
  .
  
(*   
  Lemma patt_defined_and_2:
  ∀ {Σ : Signature} {syntax : Definedness_Syntax.Syntax} (Γ : Theory) (φ ψ : Pattern),
    Definedness_Syntax.theory ⊆ Γ
    → well_formed φ
      → well_formed ψ → Γ ⊢i ⌈ φ ⌉ and ⌈ ψ ⌉  ---> ⌈ φ and ψ ⌉ using AnyReasoning.
  Proof.
  Admitted. *)

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
  
  Lemma Svar_subst (Γ : Theory) (ϕ ψ : Pattern) (X : svar)  (i : ProofInfo)
  {pile : ProofInfoLe (
        {| pi_generalized_evars := ∅;
           pi_substituted_svars := {[X]};
           pi_uses_kt := false ;
           pi_uses_advanced_kt := false ;
        |}) i} :
  well_formed ψ ->
  Γ ⊢i ϕ using i ->
  Γ ⊢i (ϕ^[[svar: X ↦ ψ]]) using i.
Proof.
  intros wfψ [pf Hpf].
  unshelve (eexists).
  {
   apply ProofSystem.Svar_subst.
   { pose proof (Hwf := proved_impl_wf _ _ pf). exact Hwf. }
   { exact wfψ. }
   { exact pf. }
  }
  {
    simpl.
    constructor; simpl.
    {
      destruct Hpf as [Hpf2 Hpf3 Hpf4].
      apply Hpf2.
    }
    {
      destruct Hpf as [Hpf2 Hpf3 Hpf4].
      pose proof (Hpile := pile_impl_allows_svsubst_X _ _ _ _ pile).
      clear -Hpile Hpf3.
      set_solver.
    }
    {
      destruct Hpf as [Hpf2 Hpf3 Hpf4].
      exact Hpf4.
    }
    {
      destruct Hpf as [Hpf2 Hpf3 Hpf4 Hpf5].
      exact Hpf5.
    }
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
    Search patt_mu derives_using.
    Search patt_defined patt_total derives_using.
    
    
    remember (evar_fresh [] ) as x.
    
    
    pose proof membership_symbol_ceil_aux_aux_0 theory x ( patt_free_svar X) 
                                         ltac:( unfold theory;set_solver) ltac:(wf_auto2).
   Check universal_generalization.
   apply universal_generalization with (x:=x) in H.
   2: try_solve_pile.
   2: wf_auto2.
   mlSimpl in H. simpl in H.
   case_match.
   2: congruence.
   Check forall_functional_subst.
   assert ( theory ⊢ (ex , Zero =ml b0) ).
   1:admit.
   Search patt_and derives_using.
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
                                   
(* 
    mlAdd (use_nat_axiom AxInductiveDomain theory ltac:(reflexivity)) as "ind". unfold axiom.
    mlRewriteBy "ind" at 1.
    { unfold theory. set_solver. }

    mlClear "ind".
    Search patt_subseteq derives_using.
    unfold "⊆ml".
(*     fromMLGoal.
 *)
    Check phi_impl_total_phi_meta.
    Search patt_total patt_imp derives_using.
    Search patt_subseteq derives_using.
    Check FixPoint.Knaster_tarski.
    apply phi_impl_total_phi_meta.
    { wf_auto2. }
    { apply pile_any. }

    apply FixPoint.Knaster_tarski.
    { apply pile_any. }
    { wf_auto2. }
    unfold instantiate. mlSimpl. simpl.
    Check patt_free_svar X.

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
 *) 
 Admitted.
  
  
  Theorem peano_induction_1 X :
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

    Print phi_impl_total_phi_meta.
    apply phi_impl_total_phi_meta.
    { wf_auto2. }
    { apply pile_any. }

    apply Knaster_tarski.
    { apply pile_any. }
    { wf_auto2. }
    unfold instantiate. mlSimpl. simpl.
    Check patt_free_svar X.

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
  
  
  Theorem add_zero_r : forall Γ , theory ⊆ Γ ->
                          Γ ⊢ all Nat, b0 +ml Zero =ml b0.
  Proof.
  intros.
  toMLGoal.
  wf_auto2.
  mlIntroAll x.
  unfold nest_ex. mlSimpl. cbn. fold Nat.
  pose proof use_nat_axiom AxDefAddId Γ H.
  simpl in H0. mlAdd H0 as "AddId".
  mlSpecialize "AddId" with x. mlSimpl. cbn.
  mlAssumption.
  Qed.
 
  
  Theorem add_zero_l : forall Γ , theory ⊆ Γ ->
                        Γ ⊢ all Nat, Zero +ml b0 =ml b0.
  Proof.
  intros.
  toMLGoal.
  wf_auto2.

  remember (svar_fresh []) as X.
  pose proof peano_induction X.
  
  (*   Ψ ≡ ∃z:Nat.z ∧ ϕ(z) *)
  
  apply Svar_subst with (X:= X) (ψ:= ex Nat, b0 and Zero +ml b0 =ml b0 )  in H0.
  
  2:try_solve_pile.
  2:wf_auto2.
  
  apply use_bigger_theory with (Γ':= Γ) in H0.
  
  2: assumption.
  
  mlAdd H0.
  clear H0.
  
  replace ((_--->_) ^[[svar:X↦ex Nat, b0 and Zero +ml b0 =ml b0]] ) with
   
      ( (ex Nat, b0 and Zero +ml b0 =ml b0) ⊆ml 〚 Nat 〛 --->
      
        Zero ∈ml (ex Nat, b0 and Zero +ml b0 =ml b0) --->
        
        ( all Nat, b0 ∈ml (ex Nat, b0 and Zero +ml b0 =ml b0) ---> 
          Succ $ b0 ∈ml (ex Nat, b0 and Zero +ml b0 =ml b0) ) --->
          
        (all Nat, b0 ∈ml (ex Nat, b0 and Zero +ml b0 =ml b0) ) ).
       
   2:{
        cbn.
        case_match.
        * reflexivity.
        * congruence.
    }
   
   mlAssert ( "H": ( (ex Nat, b0 and Zero +ml b0 =ml b0) ⊆ml 〚 Nat 〛)  ).
   1:wf_auto2.
   1:{
      
      unfold "⊆ml".
      Search patt_total derives_using.
     
      mlClear "0".
      fromMLGoal.

      apply phi_impl_total_phi_meta.
      1:wf_auto2.
      1:apply pile_any.
      mlIntro "H".
      mlDestructEx "H" as x. unfold nest_ex. simpl. fold Nat.  mlSimpl. simpl. cbn.
      mlDestructAnd "H".
      
       mlRevert "0".
      
      pose proof use_nat_axiom AxInductiveDomain Γ H. 
      simpl in H0.
      mlAdd H0 as "ind".
       
      mlRewriteBy "ind" at 1.
      1:unfold theory in H;set_solver.
      
      mlIntro "H".
      
      mlApplyMeta membership_implies_implication in "H".
     
      mlRewriteBy "ind" at 1.
      1:unfold theory in H;set_solver.
      mlApply "H".
      
      mlDestructAnd "1".
      mlAssumption.
   }
   
   mlAssert ( "H0": ( Zero ∈ml (ex Nat, b0 and Zero +ml b0 =ml b0) )  ).
   1:wf_auto2.
   1:{
   
      pose proof use_nat_axiom AxInductiveDomain Γ H. 
      simpl in H0.
      mlAdd H0 as "ind".
      
      Search patt_total derives_using.
      
(*       mlApplyMeta total_phi_impl_phi in "H".
 
      
      2: instantiate (1 := fresh_evar ⊥); solve_fresh.
      2: { unfold theory in H. set_solver. }
 *)     
      mlRevert "H".
      
      mlRewriteBy "ind" at 1.
      1:unfold theory in H;set_solver.
      mlIntro "H".
      mlClear "0".

      Search patt_exists derives_using.
       
(*       mlApplyMeta prenex_exists_and_2 in "H". *)
      
      Search patt_imp derives_using.
      Search patt_in derives_using.
      
      Search patt_mu derives_using.
      
      
      unfold "∈ml".
      mlApplyMeta phi_impl_defined_phi.
      2: instantiate (1 := fresh_evar ⊥); solve_fresh.
      2: { unfold theory in H. set_solver. }
      mlSplitAnd.
      *admit.
      *
      


      Search patt_in derives_using.
      
      Search patt_defined derives_using.
(*       patt_defined_and:
  ∀ {Σ : Signature} {syntax : Definedness_Syntax.Syntax} (Γ : Theory) (φ ψ : Pattern),
    Definedness_Syntax.theory ⊆ Γ
    → well_formed φ
      → well_formed ψ → Γ ⊢i ⌈ φ and ψ ⌉ ---> ⌈ φ ⌉ and ⌈ ψ ⌉ using AnyReasoning
       *)
       
      (* mlApplyMeta patt_defined_and_2.
      mlSplitAnd.
      *admit.
      * mlAssumption.
      
      mlApply "0" in "H".
        mlClear "0".
 *)   admit.
   }
   
   mlAssert ( "H1": ( (all Nat,
       b0 ∈ml (ex Nat, b0 and Zero +ml b0 =ml b0) --->
       Succ $ b0 ∈ml (ex Nat, b0 and Zero +ml b0 =ml b0)) )  ).
   1:wf_auto2.
   1:{
   admit.
   }
   
   mlApply "0" in "H".
   mlApply "H" in "H0".
   mlApply "H0" in "H1".
   mlClear "0".
   mlClear "H".
   mlClear "H0".
   mlIntroAll x.
   mlSpecialize "H1" with x.
   mlSimpl. simpl. 
   
   replace ( (ex Nat, b0 and Zero +ml b0 =ml b0)^{evar:0↦x} ) with 
   ( (ex Nat, b0 and Zero +ml b0 =ml b0) ).
   2:{
      reflexivity.
   }
   cbn.
   mlIntro "H".
   
  mlAssert ( "f" : ( patt_free_evar x ∈ml 〚 patt_sym (inj sNat) 〛 )  ).
  1:wf_auto2.
  1:admit.
     
     
   mlApply "H1" in "H".
   mlClear "H1".
    
   Search patt_in derives_using.
   
   mlApplyMeta membership_exists_1 in "H" .
   2:unfold theory in H;set_solver.
   
   Search patt_in patt_exists derives_using.
   
   
   mlDestructEx "H" as x.
   1-3:admit.
   mlSimpl. simpl. cbn.
   
   Search patt_in derives_using.
   
   
   mlApplyMeta membership_and_1 in "H".
   2:unfold theory in H;set_solver.

   mlDestructAnd "H".
   mlApplyMeta membership_and_1 in "1".
   2:unfold theory in H;set_solver.

   mlDestructAnd "1".
   
   Search patt_in derives_using.
   
   mlApplyMeta membership_implies_implication in "3".
   
(*    mlApplyMeta membership_implies_implication in "2". *)
   
   Search patt_imp derives_using.
   
   mlApply "3".

(*    mlApply "2". *)
   
   mlApplyMeta membership_implies_implication in "0".
   mlApplyMeta membership_implies_implication in "2". 
   
    mlApply "2".
  
   mlRevert "f".
   
   
(*    

  membership_implies_implication:
  ∀ {Σ : Signature} {syntax : Definedness_Syntax.Syntax} (Γ : Theory) 
    (ϕ : Pattern) (x : evar),
    well_formed ϕ
    → Γ ⊢i patt_free_evar x ∈ml ϕ ---> patt_free_evar x ---> ϕ using BasicReasoning



  membership_symbol_ceil_right:
  ∀ {Σ : Signature} {syntax : Definedness_Syntax.Syntax} (Γ : Theory) 
    (φ : Pattern) (x : evar),
    Definedness_Syntax.theory ⊆ Γ
    → well_formed φ
    
      → Γ ⊢i (ex , b0 ∈ml φ) ---> patt_free_evar x ∈ml ⌈ φ ⌉
      
        using (ExGen := ⊤, SVSubst := ∅, KT := false, AKT := false)
        
        
        
        membership_exists_1:
  ∀ {Σ : Signature} {syntax : Definedness_Syntax.Syntax} (Γ : Theory) 
    (x : evar) (φ : Pattern),
    Definedness_Syntax.theory ⊆ Γ
    → well_formed (ex , φ)
    
      → Γ ⊢i patt_free_evar x ∈ml (ex , φ) ---> (ex , patt_free_evar x ∈ml φ)
      
        using (ExGen := ⊤, SVSubst := ∅, KT := false, AKT := false)
        
        
        
        membership_and_1:
  ∀ {Σ : Signature} {syntax : Definedness_Syntax.Syntax} (Γ : Theory) 
    (x : evar) (φ₁ φ₂ : Pattern),
    well_formed φ₁
    → well_formed φ₂
      → Definedness_Syntax.theory ⊆ Γ
        → Γ
          ⊢i patt_free_evar x ∈ml (φ₁ and φ₂) --->
             patt_free_evar x ∈ml φ₁ and patt_free_evar x ∈ml φ₂
          using (ExGen := {[ev_x; x]}, SVSubst := ∅, KT := false, AKT := false)
    *)
    

   

   
   
   (* Zero ∈ml (ex Nat, b0 and Zero +ml b0 =ml b0) *)
  
  (* 1: exact (free_svar_subst (ex Nat, b0 and Zero +ml b0 =ml b0) X).
  1-3:eauto.
 *)
 
  
  
  Admitted.
             
    
  
  
  
  
End nat.

Close Scope ml_scope.
Close Scope string_scope.
Close Scope list_scope.