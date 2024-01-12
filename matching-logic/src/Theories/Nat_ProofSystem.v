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

From Coq Require Import ssreflect ssrfun ssrbool.

Require Import Setoid.
From Coq Require Import Unicode.Utf8.
From Coq.Logic Require Import Classical_Prop FunctionalExtensionality.
From Coq.Classes Require Import Morphisms_Prop.

From stdpp Require Import base sets.

From MatchingLogic Require Import Logic MLPM.
From MatchingLogic.Theories Require Import Definedness_ProofSystem Sorts_ProofSystem FOEquality_ProofSystem.
Import MatchingLogic.Logic.Notations.
Require Import MatchingLogic.Theories.Nat_Syntax.

Import MatchingLogic.Theories.Definedness_Syntax.Notations.
Import MatchingLogic.Theories.Nat_Syntax.Notations.

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
  Check forall_functional_subst.
  
  Theorem forall_functional_subst_meta 
     : ∀ (φ φ' : Pattern) (Γ : Theory),
         Definedness_Syntax.theory ⊆ Γ
         → mu_free φ
           → well_formed φ'
             → well_formed_closed_ex_aux φ 1
               → well_formed_closed_mu_aux φ 0
                -> Γ ⊢ is_functional φ' 
                 → Γ ⊢ (all , φ) -> Γ ⊢i φ^[evar:0↦φ'] using AnyReasoning.
   Proof.
    intros.
    toMLGoal.
    wf_auto2.
   Search well_formed_positive mu_free.
   now apply mu_free_wfp.
   Check forall_functional_subst.
   mlApplyMeta forall_functional_subst.
   2-5:assumption.
   mlSplitAnd.
   * mlExactMeta H5.
   * unfold is_functional in H4. mlExactMeta H4.
   Defined.
  
  Check exists_functional_subst.
  Theorem exists_functional_subst_meta 
     : ∀ (φ φ' : Pattern) (Γ : Theory),
         Definedness_Syntax.theory ⊆ Γ
         → mu_free φ
           → well_formed φ'
             → well_formed_closed_ex_aux φ 1
               → well_formed_closed_mu_aux φ 0
                 → Γ  ⊢ (ex , φ) ^ [φ'] 
                 -> Γ ⊢ is_functional φ' 
                 -> Γ ⊢i (ex , φ) using AnyReasoning.
   Proof.
    intros.
    toMLGoal.
    wf_auto2.
    Search well_formed_positive mu_free.
    now apply mu_free_wfp. 
    mlApplyMeta exists_functional_subst.
    2-3:assumption.
    2:eauto.
    2-3:assumption.
    mlSplitAnd.
    * mlExactMeta H4.
    * mlExactMeta H5.
  Defined.



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

    Check phi_impl_total_phi_meta.
    apply phi_impl_total_phi_meta.
    { wf_auto2. }
    { apply pile_any. }
    Check Knaster_tarski.

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
 
  
  Theorem membership_monotone_functional:
  ∀ {Σ : Signature} {syntax : Definedness_Syntax.Syntax} (Γ : Theory) 
    (φ₁ φ₂  t : Pattern)  (i : ProofInfo),
    Definedness_Syntax.theory ⊆ Γ
    → well_formed φ₁
      → well_formed φ₂
       → well_formed t
        → Γ ⊢i is_functional t using i
         → Γ ⊢i φ₁ ---> φ₂ using i
          → Γ ⊢i  t ∈ml φ₁ ---> t ∈ml φ₂ using i .
   Proof.
   Admitted.
   
  Check membership_monotone.
  
  
  Theorem  something:
  ∀ {Σ : Signature} {syntax : Definedness_Syntax.Syntax} (Γ : Theory) 
    (φ₁ φ₂ : Pattern)   (i : ProofInfo),
    Definedness_Syntax.theory ⊆ Γ
    → well_formed φ₁
      → well_formed φ₂
       → Γ ⊢i is_functional φ₂ using i
         → Γ ⊢i φ₁ using i
          → Γ ⊢i  φ₂ ∈ml φ₁  using i .
    Proof.
    Admitted.
  
  Theorem membership_and_2_functional
     : ∀ (Γ : Theory)  (φ₁ φ₂ t : Pattern) ( i : ProofInfo),
         well_formed φ₁
         → well_formed φ₂
           → Definedness_Syntax.theory ⊆ Γ
           → Γ ⊢i is_functional t using i 
             → Γ
               ⊢i t ∈ml φ₁ and  t ∈ml φ₂ --->
                  t ∈ml (φ₁ and φ₂)
               using i.
    Proof.
    Admitted.
    
  Theorem membership_or_2_functional
     : ∀ (Γ : Theory) (x : evar) (φ₁ φ₂ t : Pattern),
         well_formed φ₁
         → well_formed φ₂
           → Definedness_Syntax.theory ⊆ Γ
            → Γ ⊢ is_functional t 
             → Γ
               ⊢i t ∈ml φ₁ or t ∈ml φ₂ --->
                  t ∈ml (φ₁ or φ₂) using BasicReasoning.
    Proof.
    Admitted.
     
       (*    
    
    phi \in exists psi
​
    <--->

    psi[0 |-> phi]
    
    
      Theorem t1 
     : ∀ (φ φ' : Pattern) (Γ : Theory),
         Definedness_Syntax.theory ⊆ Γ
         
                 → Γ ⊢ φ ∈ml (ex, φ') <---> Γ ⊢i  φ' ^ [ evar: 0↦φ ] using AnyReasoning.
    
*)
    
  Theorem t1 
     : ∀ (Γ : Theory) (φ φ' : Pattern) (i : ProofInfo) ,
         Definedness_Syntax.theory ⊆ Γ 
         → well_formed φ
          → well_formed (ex , φ')
           →  Γ ⊢i φ ∈ml (ex, φ')    --->   φ'^[evar:0↦φ]  using i.
   Proof.
   Admitted.
  
  Theorem add_zero_l : forall Γ , theory ⊆ Γ ->
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
      
      Search patt_total derives_using.
     
      mlRevert "H".
      
      mlRewriteBy "ind" at 1.

      mlIntro "H".
      mlClear "0".

      Search patt_exists patt_in derives_using.
      
      unfold patt_exists_of_sort.
      
      remember (evar_fresh [] ) as x.
      epose proof membership_exists_2 Γ (x) (b0 ∈ml 〚 nest_ex Nat 〛 and (b0 and Zero +ml b0 =ml b0)) _ _.
      
      unfold nest_ex in *. simpl in *. fold Nat in *.
      
      Check universal_generalization.
      
      apply universal_generalization with (x := x ) in H1 .
      2:try_solve_pile.
      2:wf_auto2.
      
      use AnyReasoning in H1.
      apply forall_functional_subst_meta with ( φ' := Zero ) in H1.
      2: { unfold theory in H. set_solver. }
      2: { simpl. case_match.
           * reflexivity.
           * congruence.
         } 
       2:wf_auto2.
       2: {
            simpl. case_match.
            * reflexivity.
            * congruence.
          }
       2: {
            simpl. case_match.
            * reflexivity.
            * congruence.
          }
       2: {
            mlApplyMeta ex_sort_impl_ex.
            2:set_solver.
            pose proof use_nat_axiom AxFun1 Γ H;simpl in H2;mlAdd H2 as "f";mlExact "f".
          }
       mlAdd H1. clear H1.
        mlSimpl. simpl. case_match.
        * simpl.
      
          mlApply "0".
          
          Check exists_functional_subst.
          
          pose proof exists_functional_subst 
          (Zero ∈ml (b0 ∈ml 〚 Nat 〛 and (b0 and Zero +ml b0 =ml b0)))
          (Zero) Γ.
          
          mlApplyMeta H2.
          2-4: wf_auto2.
          2: set_solver.
          
          (* prove separatly is_functional zero  *)
          mlAssert( "P": (is_functional Zero)).
          1: wf_auto2.
          1:{ mlApplyMeta ex_sort_impl_ex.
              2: set_solver.
              pose proof use_nat_axiom AxFun1 Γ H;simpl in H3;mlAdd H3 as "f";mlExact "f".
            }
           
          mlSplitAnd.
          
          + unfold instantiate. mlSimpl. simpl.
            clear H2.
            mlClear "0".
            mlClear "ind".
            mlClear "H".

            Check membership_and_2_functional.
          
            mlApplyMeta membership_and_2_functional.
            2: { mlApplyMeta ex_sort_impl_ex.
                 2: set_solver.
                 pose proof use_nat_axiom AxFun1 Γ H; simpl in H2; mlAdd H2 as "f";mlExact "f".
               }
            2: set_solver.
 
            mlSplitAnd.
            ** assert ( P1: (  Γ ⊢ Zero ∈ml 〚 Nat 〛) ).
               1: { toMLGoal.
                    wf_auto2.
                    mlAdd H0 as "ind".
                    mlRewriteBy "ind" at 1.
                    
                    Check membership_monotone.
                    Check membership_monotone_functional.
                    
                    epose proof membership_monotone_functional Γ 
                    ( (mu , Zero or Succ $ B0) ^ [mu , Zero or Succ $ B0] ) 
                    (mu , Zero or Succ $ B0) (Zero) _ _ _ _ _ _ .
                    
                    pose proof Pre_fixp Γ (Zero or Succ $ B0) ltac:(wf_auto2).
                    
                    use AnyReasoning in H3.
                    specialize (H2 H3).
                    
                    unfold instantiate in H2. mlSimpl in H2. simpl in H2.
                    mlApplyMeta H2.
                    mlApplyMeta membership_or_2_functional.
                    2: {  mlApplyMeta ex_sort_impl_ex.
                          2: set_solver.
                          pose proof use_nat_axiom AxFun1 Γ H; simpl in H4; mlAdd H4 as "f";mlExact "f".
                       }
                    2: set_solver.
                    2: auto. 
                    
                    mlLeft.
                    mlApplyMeta membership_refl.
                    2: set_solver.
                    mlApplyMeta ex_sort_impl_ex.
                    2: set_solver.
                    pose proof use_nat_axiom AxFun1 Γ H; simpl in H4; mlAdd H4 as "f";mlExact "f".
                  }
                    
               epose proof something Γ ( Zero ∈ml 〚 Nat 〛) Zero  _ _ _ _ _ P1.
               mlExactMeta H2.
                    
            ** mlApplyMeta membership_and_2_functional.
               2: { mlApplyMeta ex_sort_impl_ex.
                    2: set_solver.
                    pose proof use_nat_axiom AxFun1 Γ H; simpl in H2; mlAdd H2 as "f";mlExact "f".
                  }
               2: set_solver.
               mlSplitAnd.
               ++ mlApplyMeta membership_refl.
                  2: set_solver.
                  mlAssumption.
               ++ assert ( P1: ( Γ ⊢ Zero +ml Zero =ml Zero) ).
                  1: { toMLGoal.
                       wf_auto2.
                       pose proof use_nat_axiom AxDefAddId Γ H. simpl in H2.
                       apply forall_functional_subst_meta with (φ' := Zero) in H2.
                       mlAdd H2.
                       1:{ mlSimpl. cbn. mlApply "0". fold Nat.
                           pose proof use_nat_axiom AxInductiveDomain Γ H.
                           simpl in H3. mlAdd H3 as "ind".
                           mlRewriteBy "ind" at 1.
                         
                           epose proof membership_monotone_functional Γ 
                           ( (mu , Zero or Succ $ B0) ^ [mu , Zero or Succ $ B0] ) 
                           (mu , Zero or Succ $ B0) (Zero) _ _ _ _ _ _ .
                    
                           pose proof Pre_fixp Γ (Zero or Succ $ B0) ltac:(wf_auto2).
                    
                           use AnyReasoning in H5.
                           specialize (H4 H5).
                    
                           unfold instantiate in H4. mlSimpl in H4. simpl in H4.
                           mlApplyMeta H4.
                           mlApplyMeta membership_or_2_functional.
                           2: {  mlApplyMeta ex_sort_impl_ex.
                                 2: set_solver.
                                 pose proof use_nat_axiom AxFun1 Γ H; simpl in H6; mlAdd H6 as "f";mlExact "f".
                              }
                           2: set_solver.
                           2: auto. 
                    
                          mlLeft.
                          mlApplyMeta membership_refl.
                          2: set_solver.
                          mlApplyMeta ex_sort_impl_ex.
                          2: set_solver.
                          pose proof use_nat_axiom AxFun1 Γ H; simpl in H6; mlAdd H6 as "f";mlExact "f".
                         }
                      1: set_solver.
                      1: reflexivity.
                      1-3: wf_auto2.
                      1:{ mlApplyMeta ex_sort_impl_ex.
                          2: set_solver.
                          pose proof use_nat_axiom AxFun1 Γ H; simpl in H3; mlAdd H3 as "f";mlExact "f".
                        }
                      
                     }
                     
                     epose proof something Γ _ Zero _ _ _ _ _ P1 .
                     mlExactMeta H2. 
      
               + mlAssumption.
          * congruence.
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

   }

      

   
   mlAssert ( "H1": ( 
   ( all Nat, b0 ∈ml (ex Nat, b0 and Zero +ml b0 =ml b0) --->
       Succ $ b0 ∈ml (ex Nat, b0 and Zero +ml b0 =ml b0) 
   ) )).
   1:wf_auto2.
   1:{ (* unfold patt_exists_of_sort.
       mlIntroAll x. simpl.
       mlIntro "H1".
       mlIntro "H2". *)
       
    (* mlApply "H" in "0".
       mlApply "H0" in "H". *)
       
       unfold patt_exists_of_sort. 
       mlIntroAll x. simpl. unfold nest_ex. simpl. fold Nat.
       mlIntro "H1".
       mlIntro "H2".
       mlApply "0" in "H". mlClear "0".
       mlApply "H" in "H0". mlClear "H".
       
       
       Check membership_exists_2.
       epose proof membership_exists_2 Γ (x) (b0 ∈ml 〚 nest_ex Nat 〛 and (b0 and Zero +ml b0 =ml b0)) _ _.
       
       apply universal_generalization with (x := x ) in H0 .
       2:try_solve_pile.
       2:wf_auto2.
      
      use AnyReasoning in H0.
      apply forall_functional_subst_meta with ( φ' := (Succ $ patt_free_evar x) ) in H0.
      2: set_solver. 
      2: { simpl. case_match.
           * reflexivity.
           * congruence.
         } 
       2:wf_auto2.
       2: {
            simpl. case_match.
            * reflexivity.
            * congruence.
          }
       2: { 
            simpl. case_match.
            * reflexivity.
            * congruence.
          }
       2: {
            mlApplyMeta ex_sort_impl_ex.
            2:set_solver.
            pose proof use_nat_axiom AxFun2 Γ H. simpl in H1.
            mlAdd H1 as "f".
            mlSpecialize "f" with x.
            mlSimpl. simpl. mlSortedSimpl. mlSimpl. cbn. fold Nat.
            mlApply "f". 
(*             mlExact "f". *) admit.
          }
           mlAdd H0. clear H0.
           mlSimpl. simpl. case_match.
           * simpl.
             mlApply "0". mlClear "0".
             
             Check exists_functional_subst.
             pose proof exists_functional_subst 
             ( (Succ $ patt_free_evar x) ∈ml (b0 ∈ml 〚 Nat 〛 and (b0 and Zero +ml b0 =ml b0)))
             (Succ $ patt_free_evar x) Γ.
             mlApplyMeta H1.
             2-3: wf_auto2.
             2: reflexivity.
             2: set_solver.
             unfold instantiate. mlSimpl. simpl.
             
             mlAssert( "P": (is_functional (Succ $ patt_free_evar x))).
             1: wf_auto2.
              1:{ unfold is_functional. 
                  Check forall_variable_substitution'.
                  Check forall_functional_subst.
                  admit.
                  
                }
             
             mlSplitAnd.
             + clear H1.
               mlApplyMeta membership_and_2_functional.
               2:admit.
               2: set_solver.
               mlSplitAnd.
               - Check membership_monotone_functional.
               
                 assert ( P1: (  Γ ⊢ (Succ $ patt_free_evar x)  ∈ml 〚 Nat 〛) ).
                 1:{ toMLGoal. wf_auto2.
                      1:{(* 
                          epose proof membership_monotone_functional Γ 
                          ( (mu , Zero or Succ $ B0) ^ [mu , Zero or Succ $ B0 ] ) 
                          (mu , Zero or Succ $ B0) (Succ $ patt_free_evar x ) _ _ _ _ _ _ .
                    
                          pose proof Pre_fixp Γ (Zero or Succ $ B0 ) ltac:(wf_auto2).
                    
                          use AnyReasoning in H2.
                          specialize (H1 H2).
                    
                          unfold instantiate in H2. mlSimpl in H2. simpl in H2.
                          pose proof use_nat_axiom AxInductiveDomain Γ H. simpl in H3. mlAdd H3 as "ind".
                          mlRewriteBy "ind" at 1.
                          mlApplyMeta H1.
                          unfold instantiate.
                          mlSimpl. simpl. mlApplyMeta membership_or_2_functional.
                          2-4:admit. *)admit.
                        }
                   }     
                    epose proof something Γ _ ( Succ $ patt_free_evar x ) _ _ _ _ _ P1 .
                    mlExactMeta H1.
                    
               - mlApplyMeta membership_and_2_functional.
                 mlSplitAnd.
                 3:admit.
                 3: set_solver.
                 
                 ** mlApplyMeta membership_refl.
                    2: set_solver.
                    unfold is_functional. mlAssumption.
                    
                 ** assert ( P1: (  Γ ⊢ Zero +ml (Succ $ patt_free_evar x) =ml Succ $ patt_free_evar x ) ).
                    1: { toMLGoal. wf_auto2.
                         1: { admit. }
                       }
                    epose proof something Γ _ ( Succ $ patt_free_evar x ) _ _ _ _ _ P1 .
                    mlExactMeta H1.
                 
             + clear H1.
               mlExact "P".

               (* remember (evar_fresh[]) as y.
               Check forall_variable_substitution.
               apply forall_variable_substitution_meta with ( x := y ) (φ := ex Nat, Succ $ b1 =ml b0) in "0".
               mlSpecialize "0" with x. mlSimpl. mlApply "H1" in "0".
               mlClear "0".
               
               unfold patt_exists_of_sort. mlSimpl. cbn. fold Nat.
               fold patt_exists_of_sort.
               Search patt_exists derives_using.
               mlDestructEx "H1" as y.
               
               remember (evar_fresh[ x ] ) as y.
               
(*                rewrite <- evar_quantify_evar_open with (n := 0) (x := y) (phi := b0 ∈ml 〚 Nat 〛 and Succ $ patt_free_evar x =ml b0).
               2: {
                    subst y. eapply evar_is_fresh_in_richer'.
                    2: { apply set_evar_fresh_is_fresh'. }
                    clear. set_solver.
                  }
                  2:wf_auto2.
                  mlSimpl. unfold evar_open. cbn.
                  ++ cbn.                 *)
               mlDestructEx "H1" as y.
(*                mlDestructEx "H1" as x.
               1-3: admit.
               mlSimpl. cbn. fold Nat.
               mlDestructAnd "H1".
               mlExists x. mlSimpl. cbn.
               mlExact "1". *)
                *)
             
           * congruence.
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
   
   mlSortedSimpl. mlSimpl. cbn. fold Nat.
   
   (* replace ( (ex Nat, b0 and Zero +ml b0 =ml b0)^{evar:0↦x} ) with 
   ( (ex Nat, b0 and Zero +ml b0 =ml b0) ).
   2:{
      reflexivity.
   }
   cbn. *)
   
   
   mlIntro "H".
   
  mlAssert ( "f" : ( patt_free_evar x ∈ml 〚 Nat 〛 )  ).
  1:wf_auto2.
  1:mlExact "H".
     
   mlApply "H1" in "H".
   mlClear "H1".
   mlApplyMeta t1 in "H".
   mlSimpl. simpl.
   mlDestructAnd "H".
   mlDestructAnd "1".
   mlAssumption.
   
(*    

  membership_implies_implication:
  ∀ {Σ : Signature} {syntax : Definedness_Syntax.Syntax} (Γ : Theory) 
    (ϕ : Pattern) (x : evar),
    well_formed ϕ
    → Γ ⊢i patt_free_evar x ∈ml ϕ ---> patt_free_evar x ---> ϕ using BasicReasoning

 *)
 
  
  
  Admitted.
             

  
  
  
End nat.

Close Scope ml_scope.
Close Scope string_scope.
Close Scope list_scope.