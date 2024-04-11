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
  SumSort_Syntax
.

Import MatchingLogic.Theories.Sorts_Syntax.Notations.
Import MatchingLogic.Theories.SumSort_Syntax.Notations.

Open Scope ml_scope.
Open Scope string_scope.
Open Scope list_scope.

Section sumsort.
  Context
      {Σ : Signature}
      (s1 s2 : Pattern)
      (wfs1 : well_formed s1 = true)
      (wfs2 : well_formed s2 = true)
      {syntax : SumSort_Syntax.Syntax s1 s2}
    .

    Local Notation "'(' phi ').mlInjectL'" := 
        (patt_app (patt_sym (inj (ml_injectL s1 s2))) phi)
        : ml_scope
    .

    Local Notation "'(' phi ').mlInjectR'" := 
        (patt_app (patt_sym (inj (ml_injectR s1 s2))) phi)
        : ml_scope
    .
    
    Local Notation "'(' phi ').mlEjectL'" := 
        (patt_app (patt_sym (inj (ml_ejectL s1 s2))) phi)
        : ml_scope
    .
    
    Local Notation "'(' phi ').mlEjectR'" := 
        (patt_app (patt_sym (inj (ml_ejectR s1 s2))) phi)
        : ml_scope
    .

 Lemma use_sumsort_axiom ax Γ  :
    SumSort_Syntax.theory s1 s2 wfs1 wfs2 ⊆ Γ ->
    Γ ⊢ axiom _ _ ax.
Proof.
    intro HΓ.
    apply useBasicReasoning.
    apply BasicProofSystemLemmas.hypothesis.
    { (* pose proof wfs1. pose proof wfs2. *) clear HΓ. destruct ax; wf_auto2. }
    {
      Check elem_of_weaken.
      apply elem_of_weaken with (X := theory_of_NamedAxioms (named_axioms _ _ wfs1 wfs2 ) ).
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
  
  Theorem inject_left_inj : forall Γ , theory s1 s2 wfs1 wfs2 ⊆ Γ ->
                              Γ ⊢ all s1, all s1, ( (b1).mlInjectL  =ml (b0).mlInjectL ) --->  
                               (b1 =ml b0).
  Proof.
    intros.
    toMLGoal.
    clear H. wf_auto2.
    remember (fresh_evar (s1)) as x.
    mlIntroAllManual x.
    cbn.
    1:{ 
        Search nest_ex free_evars. 
        rewrite free_evars_nest_ex. 
        solve_fresh.
      }
    mlSortedSimpl. mlSimpl. cbn.
    
    unfold nest_ex.
    rewrite simpl_free_evars.
     
    mlIntro "H".
    remember (fresh_evar ( patt_free_evar x ---> s1 )) as y.
    mlIntroAllManual y.
    1:{ 
        cbn. solve_fresh.
      }
    1:{ cbn. unfold nest_ex. rewrite bevar_subst_not_occur.
        1:{ clear H. wf_auto2. } 
        rewrite nest_ex_aux_wfcex.
        1:{ clear H. wf_auto2. }
        solve_fresh.
      }
    mlSimpl. simpl. cbn.
    mlIntro "H1".
    mlIntro "H2".
    pose proof use_sumsort_axiom AxInverseInja1 Γ H.
    simpl in H0. mlAdd H0 as "f".
    mlSpecialize "f" with x.
    mlSimpl. simpl. cbn. mlRevert "f".
    mlRewriteBy "H2" at 1.
    mlIntro.
    rewrite evar_open_not_occur.
    1:{ unfold nest_ex. rewrite nest_ex_aux_wfcex. clear H. wf_auto2. clear H. wf_auto2. }
    unfold nest_ex.
    rewrite simpl_free_evars.
    rewrite nest_ex_aux_wfcex.
    1:{ clear H. wf_auto2. }
    mlApply "0" in "H".
    mlSymmetry in "H".
    mlRewriteBy "H" at 1.
    
    mlAdd H0 as "g".
    mlSpecialize "g" with y.
    mlClear "H". mlClear "H2".
    mlSimpl. simpl. cbn.
    mlApply "g".
    rewrite evar_open_not_occur.
    1:{ unfold nest_ex. rewrite nest_ex_aux_wfcex. clear H. wf_auto2. clear H. wf_auto2. }
    unfold nest_ex.
    rewrite nest_ex_aux_wfcex.
    1:{ clear H. wf_auto2. }
    rewrite bevar_subst_not_occur.
    1:{ clear H. wf_auto2. }
    mlAssumption.
  Defined.
  
  Theorem inject_right_inj : forall Γ , theory s1 s2 wfs1 wfs2 ⊆ Γ ->
                              Γ ⊢ all s2, all s2, ( (b1).mlInjectR  =ml (b0).mlInjectR ) --->  
                               (b1 =ml b0).
  Proof.
    intros.
    toMLGoal.
    clear H. wf_auto2.
    remember (fresh_evar (s2)) as x.
    mlIntroAllManual x.
    cbn.
    1:{ 
        rewrite free_evars_nest_ex. 
        solve_fresh.
      }
    mlSortedSimpl. mlSimpl. cbn.
    
    unfold nest_ex.
    rewrite simpl_free_evars.
     
    mlIntro "H".
    remember (fresh_evar ( patt_free_evar x ---> s2)) as y.
    mlIntroAllManual y.
    1:{ 
        cbn. solve_fresh.
      }
    1:{ cbn. unfold nest_ex. rewrite bevar_subst_not_occur.
        1:{ clear H. wf_auto2. } 
        rewrite nest_ex_aux_wfcex.
        1:{ clear H. wf_auto2. }
        solve_fresh.
      }
    mlSimpl. simpl. cbn.
    mlIntro "H1".
    mlIntro "H2".
    pose proof use_sumsort_axiom AxInverseInja2 Γ H.
    simpl in H0. mlAdd H0 as "f".
    mlSpecialize "f" with x.
    mlSimpl. simpl. cbn. mlRevert "f".
    mlRewriteBy "H2" at 1.
    mlIntro.
    rewrite evar_open_not_occur.
    1:{ unfold nest_ex. rewrite nest_ex_aux_wfcex. clear H. wf_auto2. clear H. wf_auto2. }
    unfold nest_ex.
    rewrite simpl_free_evars.
    rewrite nest_ex_aux_wfcex.
    1:{ clear H. wf_auto2. }
    mlApply "0" in "H".
    mlSymmetry in "H".
    mlRewriteBy "H" at 1.
    
    mlAdd H0 as "g".
    mlSpecialize "g" with y.
    mlClear "H". mlClear "H2".
    mlSimpl. simpl. cbn.
    mlApply "g".
    rewrite evar_open_not_occur.
    1:{ unfold nest_ex. rewrite nest_ex_aux_wfcex. clear H. wf_auto2. clear H. wf_auto2. }
    unfold nest_ex.
    rewrite nest_ex_aux_wfcex.
    1:{ clear H. wf_auto2. }
    rewrite bevar_subst_not_occur.
    1:{ clear H. wf_auto2. }
    mlAssumption.
  Defined.
  
  Theorem t1:
    ∀ (Γ : Theory) (φ φ' : Pattern) (i : ProofInfo) ,
      Definedness_Syntax.theory ⊆ Γ -> 
      well_formed φ ->
      well_formed φ' ->
      Γ ⊢i φ ⊆ml φ' and  φ' ⊆ml φ   <--->
       φ =ml φ' using i.
    Proof.
    intros.
    toMLGoal.
    1:wf_auto2.
    epose proof patt_total_and Γ (φ ---> φ') (φ'--->φ) H ltac:(wf_auto2) ltac:(wf_auto2) .
    use i in H2.
    apply pf_iff_equiv_sym_nowf in H2.
    mlExactMeta H2.
    Qed.
    
   Theorem t2:
    ∀ (Γ : Theory) (φ  φ₁ φ₂ : Pattern) (i : ProofInfo) ,
      Definedness_Syntax.theory ⊆ Γ -> 
      well_formed φ ->
      well_formed φ₁ ->
      well_formed φ₂  ->
      Γ ⊢i   ( φ₁ or φ₂ )  ⊆ml φ   <--->
          φ₁ ⊆ml φ  and  φ₂  ⊆ml φ using i.
    Proof.
      intros.
      toMLGoal.
      1:wf_auto2.
      epose proof patt_total_and Γ (φ₁ ---> φ) (φ₂---> φ) H ltac:(wf_auto2) ltac:(wf_auto2) .
      use i in H3.
      unfold "⊆ml".
      mlRewrite <- H3 at 1.
      mlSplitAnd.
      * fromMLGoal.
        Check floor_monotonic.
        apply floor_monotonic.
        1:set_solver.
        1-2:wf_auto2.
        mlIntro "H".
        mlSplitAnd.
        + mlIntro.
          mlApply "H".
          mlLeft.
          mlAssumption.
        + mlIntro.
          mlApply "H".
          mlRight.
          mlAssumption.
      * fromMLGoal.
        apply floor_monotonic.
        1:set_solver.
        1-2:wf_auto2.
        mlIntro "H".
        mlIntro.
        mlDestructOr "0";
        mlDestructAnd "H".
        + mlApply "0".
          mlAssumption.
        + mlApply "1".
          mlAssumption.
    Qed.
    
    (*         we need : phi ---> phi' =  patt_top. if that is top, we can rewrite with it ---> x \in top

create two helper theorems 
1st ---> patt_total of phi ---> phi =ml patt_top 
2nd  ---> "everything is \in top"  patt_free_evar x \in patt_top.   *)
  Theorem  provable_iff_top:
    ∀ {Σ : Signature} (Γ : Theory) (φ : Pattern)   (i : ProofInfo),
      well_formed φ ->
      Γ ⊢i φ using i ->
      Γ ⊢i φ <--->  patt_top using i .
  Proof.
    intros.
    mlSplitAnd.
    2:{ mlIntro. mlExactMeta H0. }
    mlIntro.
    pose proof top_holds Γ.
    use i in H1.
    mlExactMeta H1.
  Defined.
  
  Theorem  patt_and_id_r:
    ∀ {Σ : Signature} (Γ : Theory) (φ : Pattern),
      well_formed φ ->
      Γ ⊢i φ and patt_top <--->  φ using BasicReasoning .
  Proof.
    intros.
    mlSplitAnd.
    * mlIntro.
      mlDestructAnd "0".
      mlAssumption.
    * mlIntro.
      mlSplitAnd.
      1: mlAssumption.
      mlIntro.
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


   Theorem unnamaed:
    ∀ (Γ : Theory) (φ : Pattern),
      Definedness_Syntax.theory ⊆ Γ -> 
      well_formed φ ->
      Γ ⊢i ⌊ φ ⌋ <--->  (φ =ml patt_top)     using AnyReasoning.
      Proof.
        intros.
        mlSplitAnd.
        * mlIntro.
          unfold patt_equal.
          mlRevert "0".
          fromMLGoal.
          apply floor_monotonic.
          1:set_solver.
          1-2:wf_auto2.
          mlIntro "H".
          mlSplitAnd.
          + mlIntro.
            pose proof top_holds Γ.
            use AnyReasoning in H1.
            mlExactMeta H1.
          + mlIntro.
            mlAssumption.
          * unfold patt_equal.
            fromMLGoal.
            apply floor_monotonic.
            1:set_solver.
            1-2:wf_auto2.
            mlIntro "H".
            mlDestructAnd "H".
            mlApply "1".
            pose proof top_holds Γ.
            use AnyReasoning in H1.
            mlExactMeta H1.
      Defined.
        

      Theorem unnamaed_1:
      ∀ (Γ : Theory) (x : evar),
      Definedness_Syntax.theory ⊆ Γ -> 
      Γ ⊢i patt_free_evar x  ∈ml patt_top     using AnyReasoning.
      Proof.
        intros.
        pose proof proved_membership_functional Γ (patt_top) (patt_free_evar x) ltac:(set_solver) 
         ltac:(wf_auto2) ltac:(wf_auto2).
       mlApplyMeta H0.
       * unfold  is_functional.
         mlExists x.
         mlSimpl. cbn.
         mlReflexivity.
       * pose proof top_holds Γ.
         use AnyReasoning in H1.
         mlExactMeta H1.
      Defined. 

    
   Theorem t3:
    ∀ (Γ : Theory) (φ φ' : Pattern),
      Definedness_Syntax.theory ⊆ Γ -> 
      well_formed φ ->
      well_formed φ' ->
      
      Γ ⊢i  φ  ⊆ml φ'   <--->
          ( all , b0 ∈ml φ ---> b0 ∈ml φ') using AnyReasoning.
    Proof.
      intros.
      toMLGoal.
      wf_auto2.
      mlSplitAnd.
      * mlIntro "H".
        mlIntroAll x.
        simpl.
        rewrite bevar_subst_not_occur.
        1:wf_auto2.
        
(*         fm_solve tactic for varibales freshness, when not using manual version of mlIntroAll. *)
        rewrite bevar_subst_not_occur.
        1:wf_auto2.
        mlIntro.
        
(*         unfold patt_in, patt_subseteq,patt_total. *)
        mlRevert "0".
        mlApplyMeta membership_imp_1.
        2:set_solver.
        unfold patt_subseteq.
        epose proof unnamaed Γ (φ ---> φ') ltac:(set_solver) ltac:(wf_auto2).
        apply pf_iff_proj1 in H2.
        2-3:wf_auto2. 
        mlApplyMeta H2 in "H" .
        mlRewriteBy "H" at 1.
        pose proof unnamaed_1 Γ (x) ltac:(wf_auto2).
        mlExactMeta H3.
      * mlIntro "H".
        
        remember (fresh_evar( φ ---> φ')) as x.
        (* mlSpecialize "H" with x.
        mlSimpl. simpl. cbn.
        rewrite evar_open_not_occur.
        wf_auto2.
        rewrite evar_open_not_occur.
        wf_auto2.
(*         unfold patt_in. *)
        Search patt_defined patt_imp derives_using. *)
 
        epose proof unnamaed Γ (φ ---> φ') ltac:(set_solver) ltac:(wf_auto2).
        (* mlApplyMeta membership_imp_2 in "H".
        2:set_solver.
        Search patt_in derives_using.
        
        unfold patt_in.
        Search patt_defined derives_using.
        mlApplyMeta patt_defined_and in "H".
        2:set_solver.
        mlDestructAnd "H". *)
        
        unfold patt_subseteq.
        (* Search patt_defined patt_exists derives_using.
        mlIntro.
        mlApply "H".
        Search patt_defined patt_free_evar derives_using.
(*         

         *)
        
        unfold patt_forall.
        mlRewrite H2 at 1.

        unfold patt_equal.
        Check floor_monotonic.
        Search patt_defined patt_total derives_using.
        mlApplyMeta def_phi_impl_tot_def_phi in "1".
        2:set_solver.
        mlClear "0".
        mlRevert "1".
        fromMLGoal.
        apply floor_monotonic.
        1:set_solver.
        1-2:wf_auto2.
        mlIntro "H".
        mlSplitAnd.
        + mlIntro.
          pose proof top_holds Γ.
          use AnyReasoning in H3.
          mlExactMeta H3.
        + mlIntro. 
        Search patt_top. mlIntro.
          
          Search patt_imp derives_using.
          
          
          Search patt_top.
          mlIntro.
  
        apply pf_iff_proj2 in H2.  *)
        
(*         membership_symbol_ceil_left_aux_0:
  ∀ {Σ : Signature} {syntax : Definedness_Syntax.Syntax} (Γ : Theory) (φ : Pattern),
    Definedness_Syntax.theory ⊆ Γ
    → well_formed φ
      → Γ ⊢i φ ---> (ex , ⌈ b0 and φ ⌉)
        using (ExGen := ⊤, SVSubst := ∅, KT := false, AKT := false)
        
membership_symbol_ceil_right_aux_0:
  ∀ {Σ : Signature} {syntax : Definedness_Syntax.Syntax} (Γ : Theory) (φ : Pattern),
    Definedness_Syntax.theory ⊆ Γ
    → well_formed φ
      → Γ ⊢i (ex , ⌈ b0 and φ ⌉ and b0) ---> φ
        using (ExGen := ⊤, SVSubst := ∅, KT := false, AKT := false)
         *)
    Admitted.
    
(*   
   3. ` x ∈ σ(ϕ1,.., ϕi−1, ϕi, ϕi+1,.., ϕn) = ∃y.(y ∈ ϕi ∧ x ∈ σ(ϕ1,.., ϕi−1, y, ϕi+1,.., ϕn) )
  
   x ∈ml (φ $ ψ) =ml ex , b0 ∈ml φ and x ∈ (b0 $ ψ)   ...(1)
   
   
   ex s1, (b0).mlInjectL =ml patt_free_evar x 
   
   
   second version : 
    x ∈ml (φ $ ψ) =ml ex , b0 ∈ml ψ and x ∈ml (φ $ b0)  
  
  
   *)
  
End sumsort.

Close Scope ml_scope.
Close Scope string_scope.
Close Scope list_scope.