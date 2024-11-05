From Coq Require Import ssreflect ssrfun ssrbool.

From Ltac2 Require Import Ltac2.

From Coq Require Import String Ensembles Setoid.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.Classical_Prop.
From Coq.Logic Require Import FunctionalExtensionality Eqdep_dec.
From Coq.Classes Require Import Morphisms_Prop.
From Coq.Unicode Require Import Utf8.
From Coq.micromega Require Import Lia.

From MatchingLogic Require Export Logic ProofMode.MLPM.
From MatchingLogic.Theories Require Export Definedness_Syntax Definedness_ProofSystem.
From MatchingLogic.Utils Require Export stdpp_ext.

Require Export MatchingLogic.wftactics.

From stdpp Require Import base fin_sets sets propset proof_irrel option list.

Import extralibrary.

Import MatchingLogic.Logic.Notations.
Import MatchingLogic.Theories.Definedness_Syntax.Notations.

Set Default Proof Mode "Classic".

Require Import MatchingLogic.Theories.DeductionTheorem.

Require MatchingLogic.Theories.Sorts_Syntax.
Export MatchingLogic.Theories.Sorts_Syntax.Notations.

Require Import Setoid.
From Coq.Logic Require Import Classical_Prop FunctionalExtensionality.

From stdpp Require Import base sets.

From MatchingLogic Require Import Logic MLPM.
From MatchingLogic.Theories Require Import Sorts_ProofSystem FOEquality_ProofSystem.
Require Import MatchingLogic.Theories.Nat_Syntax.

Import MatchingLogic.Theories.Nat_Syntax.Notations.

Set Default Proof Mode "Classic".

Open Scope ml_scope.
Open Scope string_scope.
Open Scope list_scope.
  
Section nat.
  Context
    {Σ : Signature}
    {syntax : Nat_Syntax.Syntax}
  .
  
(* suppose \phi is_functional 
 *)
  Theorem membership_exists_subst:
    ∀ (Γ : Theory) (φ φ' : Pattern) (i : ProofInfo) ,
      Definedness_Syntax.theory ⊆ Γ -> 
      well_formed φ ->
      well_formed (ex , φ') ->
      Γ ⊢i φ ∈ml (ex, φ') --->
      φ'^[evar:0↦φ] using i.
  Proof.
    intros.
    mlIntro. mlApplyMeta membership_exists_1 in "0". 2-4: admit.
    mlDestructEx "0" as x. admit.
    mlSimpl.
    rewrite evar_open_not_occur. wf_auto2.
  Admitted.

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

  Theorem peano_induction X :
    theory ⊢ (* patt_free_svar X ⊆ml 〚 Nat 〛 --->  *)
    Zero ∈ml patt_free_svar X  --->
    ( all Nat, (b0 ∈ml patt_free_svar X ---> Succ ⋅ b0 ∈ml patt_free_svar X) ) --->
    all Nat, b0 ∈ml patt_free_svar X.
  Proof.
    (* toMLGoal.
    { wf_auto2. }
    do 2 mlIntro.
    unfold axiom.
    mlIntroAll x. cbn.
    mlIntro.
    mlSpecialize "1" with x. mlSimpl. cbn.

    mlAdd (use_nat_axiom AxInductiveDomain theory ltac:(reflexivity)) as "ind".
    unfold axiom. fold Nat.
    mlRevert "2".
    mlRewriteBy "ind" at 1. 1: unfold theory; set_solver.
    mlClear "ind".
    mlApplyMeta membership_imp_1. 2: unfold theory; set_solver.

    Search patt_in derives_using. *)
    


(*     mlApplyMeta nat_subset_imp_in.

    
    { unfold theory. set_solver. }

    mlClear "ind".
    mlIntro.
    Check Framing.
    Search patt_forall derives_using.

    
    
    
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

      remember (fresh_evar (b0 ∈ml (Succ ⋅ patt_free_svar X ---> patt_free_svar X))) as x.

      rewrite <- evar_quantify_evar_open with (phi := b0 ∈ml (Succ ⋅ patt_free_svar X ---> patt_free_svar X)) (n := 0) (x := x).
      2: {
        subst x.
        eapply evar_is_fresh_in_richer'.
        2: { apply set_evar_fresh_is_fresh'. }
        clear. set_solver.
      }
      2: { cbn. reflexivity. }
      apply universal_generalization;[apply pile_any|wf_auto2|].
      mlSimpl. unfold evar_open. simpl.

      pose proof (Htmp := membership_imp theory x (Succ ⋅ patt_free_svar X) (patt_free_svar X)).
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

      remember (fresh_evar (b0 ∈ml patt_free_svar X and patt_free_evar x ∈ml Succ ⋅ b0)) as y.
      rewrite <- evar_quantify_evar_open with (n := 0) (x := y) (phi := b0 ∈ml patt_free_svar X and patt_free_evar x ∈ml Succ ⋅ b0).
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

      pose proof (M := membership_imp_equal theory (patt_free_evar x) (Succ ⋅ patt_free_evar y)).
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
      mlAssert ("M0" : (patt_free_evar x =ml Succ ⋅ patt_free_evar y)).
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
          rewrite <- evar_quantify_evar_open with (x := y) (n := 0) (phi := b0 ∈ml 〚 Nat 〛 ---> (ex Nat , Succ ⋅ b1 =ml b0)).
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
    } *)
  Admitted.
  
  Theorem peano_induction_1 X :
    theory ⊢ patt_free_svar X ⊆ml 〚 Nat 〛 -> 
    theory ⊢ Zero ∈ml patt_free_svar X ->
    theory ⊢ all Nat, ( b0 ∈ml patt_free_svar X ---> Succ ⋅ b0 ∈ml patt_free_svar X ) -> 
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

      remember (fresh_evar (b0 ∈ml (Succ ⋅ patt_free_svar X ---> patt_free_svar X))) as x.

      rewrite <- evar_quantify_evar_open with (phi := b0 ∈ml (Succ ⋅ patt_free_svar X ---> patt_free_svar X)) (n := 0) (x := x).
      2:{
          subst x.
          eapply evar_is_fresh_in_richer'.
          2: { apply set_evar_fresh_is_fresh'. }
          clear. set_solver.
        }
      2: { cbn. reflexivity. }
      apply universal_generalization;[apply pile_any|wf_auto2|].
      mlSimpl. unfold evar_open. simpl.

      pose proof (Htmp := membership_imp theory x (Succ ⋅ patt_free_svar X) (patt_free_svar X)).
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

      remember (fresh_evar (b0 ∈ml patt_free_svar X and patt_free_evar x ∈ml Succ ⋅ b0)) as y.
      rewrite <- evar_quantify_evar_open with (n := 0) (x := y) (phi := b0 ∈ml patt_free_svar X and patt_free_evar x ∈ml Succ ⋅ b0).
      2:{
          subst y. eapply evar_is_fresh_in_richer'.
          2: { apply set_evar_fresh_is_fresh'. }
          clear. set_solver.
        }
      2: wf_auto2.

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

      pose proof (M := membership_imp_equal theory (patt_free_evar x) (Succ ⋅ patt_free_evar y)).
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
      mlAssert ("M0" : (patt_free_evar x =ml Succ ⋅ patt_free_evar y)).
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
          mlAdd (use_nat_axiom AxFun2 theory ltac:(set_solver)) as "H". unfold axiom.
          unfold "all _ , _", nest_ex. simpl. fold Nat.
          rewrite <- evar_quantify_evar_open with (x := y) (n := 0) (phi := b0 ∈ml 〚 Nat 〛 ---> (ex Nat , Succ ⋅ b1 =ml b0)).
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
  
  Theorem add_zero_r: forall Γ , theory ⊆ Γ -> 
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
  Defined.
  
  Theorem add_zero_l: forall Γ , theory ⊆ Γ ->
                       Γ ⊢ all Nat, Zero +ml b0 =ml b0.
  Proof.
    intros.
    toMLGoal.
    wf_auto2.
    unfold theory in H.
    
    remember (svar_fresh []) as X.
    pose proof peano_induction X.
  
    (*   Ψ ≡ ∃z:Nat.z ∧ ϕ(z)  *)
  
    apply Svar_subst with (X:= X) (ψ:= ex Nat, b0 and Zero +ml b0 =ml b0 )  in H0.
    2:try_solve_pile.
    2:wf_auto2.
    
    apply extend_theory with (Γ':= Γ) in H0.
    2: assumption.
    
    mlAdd H0.
    clear H0.

    mlSimpl.
    rewrite (@esorted_binder_morphism _ _ _ sorted_forall_binder _ _ _ (Fsvar_subst_swaps_ex_nesting _ _)). wf_auto2.
    rewrite (@esorted_binder_morphism _ _ _ sorted_forall_binder _ _ _ (Fsvar_subst_swaps_ex_nesting _ _)). wf_auto2.
    mlSimpl. cbn.
    case_match. 2: congruence.
    clear H0 e.
  
  
    mlAssert ( "H": ( (ex Nat, b0 and Zero +ml b0 =ml b0 ) ⊆ml 〚 Nat 〛 ) ).
    1:wf_auto2.
    1:{ 
        unfold "⊆ml".
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
      
        mlIntro "H".
      
        mlApplyMeta membership_implies_implication in "H".
        mlRewriteBy "ind" at 1.
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
        mlRevert "H".
        mlRewriteBy "ind" at 1.
        
        mlIntro "H".
        mlClear "0".
        
        unfold patt_exists_of_sort.
        mlFreshEvar as x.
        mlFreshEvar as y.
        
        epose proof membership_exists_2 Γ (patt_free_evar x) (b0 ∈ml 〚 nest_ex Nat 〛 and (b0 and Zero +ml b0 =ml b0)) y AnyReasoning ltac:(set_solver) ltac:(wf_auto2) ltac:(wf_auto2) ltac:(fm_solve) ltac:(try_solve_pile).
        unfold nest_ex in *. simpl in *. fold Nat in *.
        
        apply universal_generalization with (x := x ) in H1 .
        2:try_solve_pile.
        2:wf_auto2.
        
        use AnyReasoning in H1.
        apply forall_functional_subst_meta with ( φ' := Zero ) in H1.
        2: set_solver. 
        2:{ 
            simpl. case_match.
            2: congruence.
            reflexivity.
          } 
        2: wf_auto2.
        2:{
            simpl. case_match.
            2: congruence.
            reflexivity.
          }
        2:{
            simpl. case_match.
            2: congruence.
            reflexivity.
          }
        2:{
            mlApplyMeta ex_sort_impl_ex.
            2: set_solver.
            pose proof use_nat_axiom AxFun1 Γ H;simpl in H2;mlAdd H2 as "f";mlExact "f".
          }
          
        mlAdd H1. clear H1.
        mlSimpl. simpl. case_match. 2: congruence.
        
        simpl.
        mlApply "0".
          
        pose proof exists_functional_subst 
         (Zero ∈ml (b0 ∈ml 〚 Nat 〛 and (b0 and Zero +ml b0 =ml b0)))
         (Zero) Γ.
          
        mlApplyMeta H2.
        2-4: wf_auto2.
        2: set_solver.
          
        (* prove separatly is_functional zero  *)
        mlAssert( "P": (is_functional Zero)).
        1: wf_auto2.
        1:{ 
            mlApplyMeta ex_sort_impl_ex.
            2: set_solver.
            pose proof use_nat_axiom AxFun1 Γ H;simpl in H3;mlAdd H3 as "f";mlExact "f".
          }
           
        mlSplitAnd.
        * unfold instantiate. mlSimpl. simpl.
          clear H2.
          mlClear "0";mlClear "ind";mlClear "H".
          
          mlApplyMeta membership_and_2_functional_meta.
          2:{ 
              mlApplyMeta ex_sort_impl_ex.
              2: set_solver.
              pose proof use_nat_axiom AxFun1 Γ H; simpl in H2; mlAdd H2 as "f";mlExact "f".
            }
          2: set_solver.
          2-3: wf_auto2.
 
          mlSplitAnd.
          + assert ( P1: (  Γ ⊢ Zero ∈ml 〚 Nat 〛) ).
            1:{ 
                toMLGoal.
                wf_auto2.
                mlAdd H0 as "ind".
                mlRewriteBy "ind" at 1.
                    
                epose proof membership_monotone_functional Γ 
                 ( (mu , Zero or Succ ⋅ B0) ^ [mu , Zero or Succ ⋅ B0] ) 
                 (mu , Zero or Succ ⋅ B0) (Zero) (AnyReasoning) ltac:(set_solver) ltac:(wf_auto2) 
                  ltac:(wf_auto2) ltac:(wf_auto2) _ .
                    
                pose proof Pre_fixp Γ (Zero or Succ ⋅ B0) ltac:(wf_auto2).
                    
                use AnyReasoning in H3.
                specialize (H2 H3).
                unfold instantiate in H2. mlSimpl in H2. simpl in H2.
                
                mlApplyMeta H2.
                mlApplyMeta membership_or_2_functional_meta.
                2:{ 
                    mlApplyMeta ex_sort_impl_ex.
                    2: set_solver.
                    pose proof use_nat_axiom AxFun1 Γ H; simpl in H4; mlAdd H4 as "f";mlExact "f".
                  }
                2: set_solver.
                 
                mlLeft.
                mlApplyMeta membership_refl.
                2: set_solver.
                mlApplyMeta ex_sort_impl_ex.
                2: set_solver.
                pose proof use_nat_axiom AxFun1 Γ H; simpl in H4; mlAdd H4 as "f";mlExact "f".
              }
              
              epose proof membership_symbol_ceil_aux_0_functional Γ (〚 Nat 〛 ) (Zero) (Zero) ltac:(wf_auto2)
               ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2).
               
              mlApplyMeta H2.
              
              mlSplitAnd.
              1: mlAssumption.
              mlSplitAnd.
              1: mlAssumption.
              mlExactMeta P1.
          
          + mlApplyMeta membership_and_2_functional_meta.
            2:{ 
                mlApplyMeta ex_sort_impl_ex.
                2: set_solver.
                pose proof use_nat_axiom AxFun1 Γ H; simpl in H2; mlAdd H2 as "f";mlExact "f".
              }
            2: set_solver.
            2-3: wf_auto2.
            
            mlSplitAnd.
            - mlApplyMeta membership_refl.
              2: set_solver.
              mlAssumption.
              
            - assert ( P1: ( Γ ⊢ Zero +ml Zero =ml Zero) ).
              1: { 
                   toMLGoal.
                   wf_auto2.
                   pose proof use_nat_axiom AxDefAddId Γ H. simpl in H2.
                   apply forall_functional_subst_meta with (φ' := Zero) in H2.
                   2: set_solver.
                   2: reflexivity.
                   2-4: wf_auto2.
                   2:{ 
                       mlApplyMeta ex_sort_impl_ex.
                       2: set_solver.
                       pose proof use_nat_axiom AxFun1 Γ H; simpl in H3; mlAdd H3 as "f";mlExact "f".
                     }
                         
                   mlAdd H2.
                   mlSimpl. cbn. 
                   mlApply "0". fold Nat.
                   pose proof use_nat_axiom AxInductiveDomain Γ H.
                   simpl in H3. mlAdd H3 as "ind".
                   mlRewriteBy "ind" at 1.
                    
                   epose proof membership_monotone_functional Γ 
                    ( (mu , Zero or Succ ⋅ B0) ^ [mu , Zero or Succ ⋅ B0] ) 
                    (mu , Zero or Succ ⋅ B0) (Zero) (AnyReasoning) ltac:(set_solver) ltac:(wf_auto2) 
                    ltac:(wf_auto2) ltac:(wf_auto2) _ .
                    
                   pose proof Pre_fixp Γ (Zero or Succ ⋅ B0) ltac:(wf_auto2).
                    
                   use AnyReasoning in H5.
                   specialize (H4 H5).
                   unfold instantiate in H4. mlSimpl in H4. simpl in H4.
                   
                   mlApplyMeta H4.
                   mlApplyMeta membership_or_2_functional_meta.
                   2:{ 
                       mlApplyMeta ex_sort_impl_ex.
                       2: set_solver.
                       pose proof use_nat_axiom AxFun1 Γ H; simpl in H6; mlAdd H6 as "f";mlExact "f".
                     }
                   2: set_solver.
                   
                   mlLeft.
                   mlApplyMeta membership_refl.
                   2: set_solver.
                   mlApplyMeta ex_sort_impl_ex.
                   2: set_solver.
                   pose proof use_nat_axiom AxFun1 Γ H; simpl in H6; mlAdd H6 as "f";mlExact "f".
                 }
                 
              epose proof proved_membership_functional_meta Γ (Zero +ml Zero =ml Zero) Zero ltac:(set_solver) 
               ltac:(wf_auto2) ltac:(wf_auto2) _ P1.
              mlExactMeta H2.
      
        * mlAssumption.
      }
(*           
 pose membership_and_2 and universal generalisation into 2, use forall functional substitution
 
    prove that Zero ∈ml [[Nat]] --> this is total ---> it is equivalent to top -> ... ∈ml top (is true)   
    
    from the left side of the current goal
    
*)


(*  for the right hand side ---> use membership_and_2 
- ref in Zero in Zero 
- zero in zero +ml zero =ml zero 

same chain of thoughts as 1st one for totality.

*)

      
    mlAssert ( "H1": (  all Nat, b0 ∈ml (ex Nat, b0 and Zero +ml b0 =ml b0) 
                          ---> Succ ⋅ b0 ∈ml (ex Nat, b0 and Zero +ml b0 =ml b0) 
                     ) ).
    1:wf_auto2.
    1:{ 
        unfold patt_exists_of_sort. 
        mlIntroAll x. simpl. unfold nest_ex. simpl. fold Nat.
        mlIntro "H1".
        mlIntro "H2".
        mlClear "0";mlClear "H";mlClear "H0".

        mlFreshEvar as y.
        epose proof membership_exists_2 Γ (patt_free_evar x) (b0 ∈ml 〚 nest_ex Nat 〛 and (b0 and Zero +ml b0 =ml b0)) y AnyReasoning
         ltac:(set_solver) ltac:(wf_auto2) ltac:(wf_auto2) ltac:(fm_solve) ltac:(try_solve_pile).
       
        apply universal_generalization with (x := x ) in H0 .
        2:try_solve_pile.
        2:wf_auto2.
      
        use AnyReasoning in H0.
        mlSimpl in H0. simpl in H0. case_match. 2: congruence.
      
        mlAssert ( "P" : ( is_functional ( Succ ⋅ patt_free_evar x))).
        1: wf_auto2.
        1:{ 
            unfold is_functional.
            pose proof use_nat_axiom AxFun2 Γ H. simpl in H2.
            mlAdd H2. 
            mlSpecialize "0" with x. mlSimpl. mlSortedSimpl. mlSimpl. cbn.
            mlApplyMeta ex_sort_impl_ex.
            2: set_solver.
            mlApply "0". 
            mlExact "H1". 
          }
        
         mlAdd H0 as "f". clear H0. 
         mlConj "f" "P" as "H3". mlClear "f".
      
        mlApplyMeta forall_functional_subst in "H3".
        2-3: wf_auto2.
        2: reflexivity.
        2: set_solver.
      
        mlSimpl. simpl.
        mlApply "H3". mlClear "H3".
       
        pose proof exists_functional_subst 
         ( (Succ ⋅ patt_free_evar x) ∈ml (b0 ∈ml 〚 Nat 〛 and (b0 and Zero +ml b0 =ml b0)))
         (Succ ⋅ patt_free_evar x) Γ.
       
        mlApplyMeta H0.
        2-3: wf_auto2.
        2: reflexivity.
        2: set_solver.
      
       unfold instantiate. mlSimpl. simpl.
      
       mlSplitAnd.
       * clear H0.
         pose proof membership_exists_subst Γ (patt_free_evar x ) (b0 ∈ml 〚 Nat 〛 and (b0 and Zero +ml b0 =ml b0)) 
          (AnyReasoning) ltac:(set_solver) ltac:(wf_auto2) ltac:(wf_auto2).
         mlApplyMeta H0 in "H2".
         clear H0.
         mlSimpl. simpl.
         mlDestructAnd "H2".
         mlDestructAnd "1".
         mlClear "0". 
      
         pose proof membership_and_2_functional Γ 
          (Succ ⋅ patt_free_evar x ∈ml 〚 Nat 〛)
          (Succ ⋅ patt_free_evar x and Zero +ml (Succ ⋅ patt_free_evar x) =ml Succ ⋅ patt_free_evar x)
          (Succ ⋅ patt_free_evar x)
          ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2)  ltac:(set_solver).
         
         mlApplyMeta H0. clear H0.
        
          mlSplitAnd.
          1: mlAssumption.
         
          mlSplitAnd.
          - assert ( P2: ( Γ ⊢ patt_free_evar x ∈ml 〚 Nat 〛 ---> Succ ⋅ patt_free_evar x  ∈ml 〚 Nat 〛) ).
                1:{ 
                    mlIntro "H".
                    pose proof use_nat_axiom AxFun2 Γ H. simpl in H0.
                    mlAdd H0. mlSpecialize "0" with x. mlSimpl. mlSortedSimpl. mlSimpl. cbn.
                    mlApply "0" in "H".
                    mlDestructEx "H" as y.
                    mlSimpl. cbn.
                    mlDestructAnd "H". 
                    mlRewriteBy "2" at 1.
                    mlAssumption.
                  }
                  
            mlAssert ( "P1" : (  (Succ ⋅ patt_free_evar x)  ∈ml 〚 Nat 〛 ) ).
            1:{ wf_auto2. }
            1:{      
                mlApplyMeta P2.
                mlAssumption.
              }
            epose proof membership_symbol_ceil_aux_0_functional Γ 
             (〚 Nat 〛) (Succ ⋅ patt_free_evar x) (Succ ⋅ patt_free_evar x) ltac:(wf_auto2)
              ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2) .
            
            mlApplyMeta H0.
            mlSplitAnd.
            1: mlAssumption.
            mlSplitAnd.
            1-2: mlAssumption.
            
          - pose proof membership_and_2_functional Γ 
             (Succ ⋅ patt_free_evar x )
             (Zero +ml (Succ ⋅ patt_free_evar x) =ml Succ ⋅ patt_free_evar x)
             (Succ ⋅ patt_free_evar x)
             ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2) ltac:(set_solver) .
            
            mlApplyMeta H0. clear H0.
            
            mlSplitAnd.
            1: mlAssumption.
           
            mlSplitAnd.
            1:{ 
                mlApplyMeta membership_refl. 
                mlExact "P". 
                set_solver. 
              }
              
            mlAssert ( "P1" : ( Zero +ml (Succ ⋅ patt_free_evar x) =ml Succ ⋅ patt_free_evar x )).
            1: wf_auto2.
               1:{
                   pose proof use_nat_axiom AxDefAdd Γ H.
                   simpl in H0.
                   mlAdd H0. clear H0.
                   mlSpecialize "0" with x.
                   mlSimpl. mlSortedSimpl. mlSimpl.
                   simpl. cbn. 
                   mlApply "H1" in "0". mlClear "0".
                  
                   mlAssert( "P2": (is_functional Zero)).
                   1: wf_auto2.
                   1:{ 
                       mlApplyMeta ex_sort_impl_ex.
                       2: set_solver.
                       pose proof use_nat_axiom AxFun1 Γ H;simpl in H0;mlAdd H0 as "f";mlExact "f".
                     }
                  
                   mlConj "H1" "P2" as "H2".
                   mlClear "H1".
                  
                   mlApplyMeta forall_functional_subst in "H2".
                   2-3: wf_auto2.
                   2: reflexivity.
                   2: set_solver.
                  
                   mlSimpl. simpl.
                   
                   mlRevert "H2".
                   mlRewriteBy "3" at 1.
                   
                   mlIntro "H".
                   mlApply "H". unfold nest_ex. simpl. fold Nat.
                   
                   pose proof use_nat_axiom AxInductiveDomain Γ H. 
                   simpl in H0. mlAdd H0 as "ind". clear H0.
                   mlRewriteBy "ind" at 1.
                   
                   epose proof membership_monotone_functional Γ 
                    ( (mu , Zero or Succ ⋅ B0) ^ [mu , Zero or Succ ⋅ B0] ) 
                    (mu , Zero or Succ ⋅ B0) (Zero) (AnyReasoning) ltac:(set_solver) ltac:(wf_auto2) 
                    ltac:(wf_auto2) ltac:(wf_auto2) _ .
                    
                   pose proof Pre_fixp Γ (Zero or Succ ⋅ B0) ltac:(wf_auto2).
                    
                   use AnyReasoning in H2.
                   specialize (H0 H2).
                   unfold instantiate in H0. mlSimpl in H0. simpl in H0.
                   
                   mlApplyMeta H0.
                   mlApplyMeta membership_or_2_functional_meta.
                   2: { 
                        mlApplyMeta ex_sort_impl_ex.
                        2: set_solver.
                        pose proof use_nat_axiom AxFun1 Γ H; simpl in H3; mlAdd H3 as "f";mlExact "f".
                      }
                   2: set_solver.
                    
                   mlLeft.
                   mlApplyMeta membership_refl.
                   2: set_solver.
                   mlExact "P2". 
                 }
                 
            mlRewriteBy "P1" at 1.
            epose proof proved_membership_functional Γ
             (Succ ⋅ patt_free_evar x =ml Succ ⋅ patt_free_evar x)
             ( Succ ⋅ patt_free_evar x ) ltac:(set_solver) ltac:(wf_auto2) ltac:(wf_auto2). 
            mlApplyMeta H0.
             
            mlAssumption.
            mlReflexivity. 
           
       * mlAssumption.
       Unshelve.
       2,5: set_solver.
       
       1:{ 
           mlApplyMeta ex_sort_impl_ex.
           2: set_solver.
           pose proof use_nat_axiom AxFun1 Γ H;simpl in H2;mlAdd H2 as "f";mlExact "f".
         }
       1:{ 
           mlApplyMeta ex_sort_impl_ex.
           2: set_solver.
           pose proof use_nat_axiom AxFun1 Γ H;simpl in H4;mlAdd H4 as "f";mlExact "f".
         }
       1:{ 
           mlApplyMeta ex_sort_impl_ex.
           2: set_solver.
           pose proof use_nat_axiom AxFun1 Γ H;simpl in H2;mlAdd H2 as "f";mlExact "f".
         }
       1:{ 
           mlApplyMeta ex_sort_impl_ex.
           2: set_solver.
           pose proof use_nat_axiom AxFun1 Γ H;simpl in H0;mlAdd H0 as "f";mlExact "f".
         }
      }
   
    mlApply "0" in "H0".
    mlApply "H0" in "H1".
    mlClear "0".
    mlClear "H".
    mlClear "H0".
    mlIntroAll x.
 
    mlSpecialize "H1" with x.
    mlSimpl. simpl.
   
    mlSortedSimpl. mlSimpl. cbn. fold Nat.
   
    mlIntro "H".
   
    mlAssert ( "f" : ( patt_free_evar x ∈ml 〚 Nat 〛 )  ).
    1: wf_auto2.
    1: mlExact "H".
     
    mlApply "H1" in "H".
    mlClear "H1".
    unfold patt_exists_of_sort.
    
    pose proof membership_exists_subst Γ (patt_free_evar x ) (b0 ∈ml 〚 nest_ex Nat 〛 and (b0 and Zero +ml b0 =ml b0))
     (AnyReasoning) ltac:(set_solver) ltac:(wf_auto2) ltac:(wf_auto2).
    mlApplyMeta H0 in "H".
    clear H0.
    
    mlSimpl. simpl.
    mlDestructAnd "H".
    mlDestructAnd "1".
    mlAssumption.
  Defined.

End nat.

Close Scope ml_scope.
Close Scope string_scope.
Close Scope list_scope.