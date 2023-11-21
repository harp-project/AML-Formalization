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
Require Import MatchingLogic.Theories.Bool_Syntax.

Import MatchingLogic.Theories.Definedness_Syntax.Notations.
Import MatchingLogic.Theories.Bool_Syntax.Notations.
Import BoundVarSugar.

Set Default Proof Mode "Classic".

Section bools.
Context
  { Σ : Signature}
  { syntax : Syntax}.

Open Scope ml_scope.
Open Scope string_scope.
Open Scope list_scope.
  
  Lemma use_bool_axiom ax Γ : 
    Bool_Syntax.theory ⊆ Γ ->
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

  Lemma functional_pattern_defined :
    forall Γ φ, Definedness_Syntax.theory ⊆ Γ -> well_formed φ ->
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


  Lemma membership_equal_equal :
    forall Γ φ φ',
      Definedness_Syntax.theory ⊆ Γ -> mu_free φ' ->
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
      clear hasserted. mlApplyMeta functional_pattern_defined; auto.
      mlExactMeta Func2.
  Defined.
  

  Theorem double_neg : forall Γ , theory ⊆ Γ ->
                        Γ ⊢ all mlBool,   (!b !b b0) =ml b0.
  Proof.
    intros.
    toMLGoal.
    wf_auto2.
    mlIntroAll x.
    simpl.
    mlIntro "H".
    (* Search patt_in derives_using. *)
    unfold nest_ex;simpl.
    fold mlBool.
    unfold theory in H.
    (* Search elem_of derives_using. *)
    pose proof use_bool_axiom AxInductiveDomain Γ H.
    simpl in H0.
    mlAdd H0 as "ind". 
    mlRevert "H".
    
    mlRewriteBy "ind" at 1.
    
    mlIntro "H".
    mlClear "ind".
    mlApplyMeta membership_or_1 in "H".
    {
      mlDestructOr "H".
      (* mlTrue case *) 
      * pose proof membership_equal_equal Γ (patt_free_evar x) mlTrue.
      ospecialize* H1.
      + unfold theory in H;set_solver.
      + simpl. auto.
      + wf_auto2.
      + wf_auto2.
      + mlExists x. mlSimpl. cbn. Search patt_equal derives_using. fromMLGoal. apply useBasicReasoning.  
        epose proof patt_equal_refl  (patt_free_evar x) Γ.
        apply H2. wf_auto2.
      + mlApplyMeta ex_sort_impl_ex.
        - pose proof use_bool_axiom AxFunTrue Γ H;simpl in H2;mlAdd H2 as "f";mlExact "f".
        - unfold theory in H;set_solver.
      + mlAdd H1.
        mlRevert "0".
        
        mlRewriteBy "1" at 1.
        mlIntro "H".

        mlRewriteBy "H" at 1.
        mlRewriteBy "H" at 1.
        
        pose proof use_bool_axiom AxDefNegTrue Γ H;simpl in H2.
        pose proof use_bool_axiom AxDefNegFalse Γ H;simpl in H3.
        mlAdd H2 as "negTrue";mlAdd H3 as "negFalse".
        
        mlRewriteBy "negTrue" at 1.

        mlRewriteBy "negFalse" at 1.
        mlReflexivity.
        
    (* mlFalse case   *)
    * pose proof membership_equal_equal Γ (patt_free_evar x) mlFalse. 
      ospecialize* H1.
      + unfold theory in H;set_solver.
      + simpl. auto.
      + wf_auto2.
      + wf_auto2.
      + mlExists x. mlSimpl. cbn. Search patt_equal derives_using. fromMLGoal. apply useBasicReasoning.  
        epose proof patt_equal_refl  (patt_free_evar x) Γ.
        apply H2. wf_auto2.
      + mlApplyMeta ex_sort_impl_ex.
        - pose proof use_bool_axiom AxFunFalse Γ H;simpl in H2;mlAdd H2 as "f";mlExact "f".
        - unfold theory in H;set_solver.
      + mlAdd H1.
        mlRevert "1".
        
        mlRewriteBy "0" at 1.
        mlIntro "H".
        
        mlRewriteBy "H" at 1.
        
        mlRewriteBy "H" at 1.
        pose proof use_bool_axiom AxDefNegTrue Γ H;simpl in H2.
        pose proof use_bool_axiom AxDefNegFalse Γ H;simpl in H3.
        mlAdd H2 as "negTrue";mlAdd H3 as "negFalse".
        
        mlRewriteBy "negFalse" at 1.
       
        mlRewriteBy "negTrue" at 1.
        mlReflexivity.
    }
    {
      unfold theory in H. set_solver.
    }
  Qed.

  
  Theorem true_andBool : forall Γ , theory ⊆ Γ ->
                        Γ ⊢ all mlBool,  b0 &&ml mlTrue =ml b0. 
  Proof.
  intros.
  toMLGoal.
  wf_auto2.
  mlIntroAll x.
  simpl.
  cbn. fold mlBool.
  unfold theory in H.
  pose proof use_bool_axiom AxInductiveDomain Γ H.
  simpl in H0. mlAdd H0 as "ind".
  mlRewriteBy "ind" at 1.

  mlIntro "H".
  mlApplyMeta membership_or_1 in "H".
  { 
    mlDestructOr "H". 
    * pose proof membership_equal_equal Γ (patt_free_evar x) mlTrue.
      ospecialize* H1.
      + unfold theory in H;set_solver.
      + simpl. auto.
      + wf_auto2.
      + wf_auto2.
      + mlExists x. mlSimpl. cbn. Search patt_equal derives_using. fromMLGoal. apply useBasicReasoning.  
        epose proof patt_equal_refl  (patt_free_evar x) Γ.
        apply H2. wf_auto2.
      + mlApplyMeta ex_sort_impl_ex.
        - pose proof use_bool_axiom AxFunTrue Γ H;simpl in H2;mlAdd H2 as "f";mlExact "f".
        - unfold theory in H;set_solver.
      + mlAdd H1. mlRevert "0".
        mlRewriteBy "1" at 1.
           
      mlIntro "H".
      pose proof use_bool_axiom AxDefAndRightTrue Γ H.
      simpl in H2. mlAdd H2.
        
      mlSpecialize "0" with x. mlSimpl. cbn. fold mlBool. 
      mlApply "0".
      mlRewriteBy "ind" at 1.
          
      mlApplyMeta membership_or_2.
      mlRewriteBy "1" at 1.
      {
         mlLeft. mlExact "H".
      }
      { unfold theory in H. set_solver.  }
       
     * pose proof membership_equal_equal Γ (patt_free_evar x) mlFalse.
       ospecialize* H1.
       + unfold theory in H;set_solver.
       + simpl. auto.
       + wf_auto2.
       + wf_auto2.
       + mlExists x. mlSimpl. cbn. Search patt_equal derives_using. fromMLGoal. apply useBasicReasoning.  
         epose proof patt_equal_refl  (patt_free_evar x) Γ.
         apply H2. wf_auto2.
       + mlApplyMeta ex_sort_impl_ex.
         - pose proof use_bool_axiom AxFunFalse Γ H;simpl in H2;mlAdd H2 as "f";mlExact "f".
         - unfold theory in H;set_solver.
       + mlAdd H1. mlRevert "1".
         mlRewriteBy "0" at 1.
       
       mlIntro "H".
       pose proof use_bool_axiom AxDefAndRightTrue Γ H.
       simpl in H2. mlAdd H2.
       mlSpecialize "1" with x. mlSimpl. cbn. fold mlBool. 
       mlApply "1".
       
       mlRewriteBy "ind" at 1.
   
       mlApplyMeta membership_or_2.
       mlRewriteBy "0" at 1. 
       {
         mlRight. mlExact "H".
       }
       { unfold theory in H. set_solver.  }
  }
  { unfold theory in H. set_solver.   }
  Qed.
  
  Theorem false_andBool : forall Γ , theory ⊆ Γ ->
                        Γ ⊢ all mlBool,  b0 &&ml mlFalse =ml mlFalse.
  Proof.
  intros.
  toMLGoal.
  wf_auto2.
  mlIntroAll x.
  simpl.
  cbn. fold mlBool.
  unfold theory in H.
  pose proof use_bool_axiom AxInductiveDomain Γ H.
  simpl in H0. mlAdd H0 as "ind".
  mlRewriteBy "ind" at 1.
  mlIntro "H".
  mlApplyMeta membership_or_1 in "H".
  { 
    mlDestructOr "H". 
    * pose proof membership_equal_equal Γ (patt_free_evar x) mlTrue.
      ospecialize* H1.
      + unfold theory in H;set_solver.
      + simpl. auto.
      + wf_auto2.
      + wf_auto2.
      + mlExists x. mlSimpl. cbn. Search patt_equal derives_using. fromMLGoal. apply useBasicReasoning.  
        epose proof patt_equal_refl  (patt_free_evar x) Γ.
        apply H2. wf_auto2.
      + mlApplyMeta ex_sort_impl_ex.
        - pose proof use_bool_axiom AxFunTrue Γ H;simpl in H2;mlAdd H2 as "f";mlExact "f".
        - unfold theory in H;set_solver.
      + mlAdd H1. mlRevert "0".
        mlRewriteBy "1" at 1.
        
      mlIntro "H".
      pose proof use_bool_axiom AxDefAndRightFalse Γ H.
      simpl in H2. mlAdd H2.
        
      mlSpecialize "0" with x. mlSimpl. cbn. fold mlBool. 
      mlApply "0".
      
      mlRewriteBy "ind" at 1.
          
      mlApplyMeta membership_or_2.
      mlRewriteBy "1" at 1.
      {
         mlLeft. mlExact "H".
      }
      { set_solver.  }
       
     * pose proof membership_equal_equal Γ (patt_free_evar x) mlFalse.
       ospecialize* H1.
       + unfold theory in H;set_solver.
       + simpl. auto.
       + wf_auto2.
       + wf_auto2.
       + mlExists x. mlSimpl. cbn. Search patt_equal derives_using. fromMLGoal. apply useBasicReasoning.  
         epose proof patt_equal_refl  (patt_free_evar x) Γ.
         apply H2. wf_auto2.
       + mlApplyMeta ex_sort_impl_ex.
         - pose proof use_bool_axiom AxFunFalse Γ H;simpl in H2;mlAdd H2 as "f";mlExact "f".
         - unfold theory in H;set_solver.
       + mlAdd H1. mlRevert "1".
         mlRewriteBy "0" at 1.
       mlIntro "H".
       pose proof use_bool_axiom AxDefAndRightFalse Γ H.
       simpl in H2. mlAdd H2.
       mlSpecialize "1" with x. mlSimpl. cbn. fold mlBool. 
       mlApply "1".
       
       mlRewriteBy "ind" at 1.
     
       mlApplyMeta membership_or_2.
       mlRewriteBy "0" at 1.
       {
         mlRight. mlExact "H".
       }
       { unfold theory in H. set_solver.  }
  }
  { unfold theory in H. set_solver.   }
  Qed.
  
  (* using new notation for andThen   *)
  Theorem true_andThenBool : forall Γ , theory ⊆ Γ ->
                        Γ ⊢ all mlBool,  b0 &&ml mlTrue =ml b0. 
  Proof.
  
  Qed.

  (* extending Bool_syntax.v *)
  Theorem false_andThenBool : forall Γ , theory ⊆ Γ ->
                        Γ ⊢ all,  b0 &&ml mlFalse =ml mlFalse. 
  Proof.
  Abort.


  Theorem comm_andBool : forall Γ , theory ⊆ Γ ->
                        Γ ⊢ all mlBool, all mlBool, b0 &&ml b1 =ml b1 &&ml b0.
 Proof.
 intros.
 toMLGoal.
 wf_auto2.
 mlIntroAll x.
 mlSortedSimpl.
 simpl_sorted_quantification.
 unshelve (erewrite (@esorted_binder_morphism _ patt_forall_of_sort
            _ _ _ (bevar_subst (patt_free_evar x)) _ _)).
  2-4: eauto.
  typeclasses eauto.
  mlSimpl.
  simpl.
 Admitted.

  (* Theorem comm_andBool_true : forall Γ , theory ⊆ Γ ->
                        Γ ⊢ all mlBool, b0 &&ml mlTrue =ml mlTrue &&ml b0.
 Proof.
 intros.
 toMLGoal.
 wf_auto2.
 mlIntroAll x.
 simpl.
 cbn.
 fold mlBool.
 unfold theory in H.
 pose proof use_bool_axiom AxInductiveDomain Γ H.
 simpl in H0.
 mlAdd H0 as "ind".
 mlRewriteBy "ind" at 1.
 mlIntro "H".
 mlApplyMeta membership_or_1 in "H".
 {
    mlDestructOr "H".
    (* mlTrue case *)
    * pose proof membership_equal_equal Γ ( patt_free_evar x) mlTrue.
      ospecialize* H1.
      + unfold theory in H;set_solver.
      + simpl. auto.
      + wf_auto2.
      + wf_auto2.
      + mlExists x. mlSimpl. cbn. Search patt_equal derives_using. fromMLGoal. apply useBasicReasoning.  
        epose proof patt_equal_refl  (patt_free_evar x) Γ.
        apply H2. wf_auto2.
      + mlApplyMeta ex_sort_impl_ex.
        - pose proof use_bool_axiom AxFunTrue Γ H;simpl in H2;mlAdd H2 as "f";mlExact "f".
        - unfold theory in H;set_solver.
      + mlAdd H1. mlRevert "0".
        mlRewriteBy "1" at 1.
        mlIntro "H".
        mlRewriteBy "H" at 1.
        mlRewriteBy "H" at 1.
        mlReflexivity.
    
    (* mlFalse case *)
    * pose proof membership_equal_equal Γ ( patt_free_evar x) mlFalse.
      ospecialize* H1.
      + unfold theory in H;set_solver.
      + simpl. auto.
      + wf_auto2.
      + wf_auto2.
      + mlExists x. mlSimpl. cbn. Search patt_equal derives_using. fromMLGoal. apply useBasicReasoning.  
        epose proof patt_equal_refl  (patt_free_evar x) Γ.
        apply H2. wf_auto2.
      + mlApplyMeta ex_sort_impl_ex.
        - pose proof use_bool_axiom AxFunFalse Γ H;simpl in H2;mlAdd H2 as "f";mlExact "f".
        - unfold theory in H;set_solver.
      + mlAdd H1. mlRevert "1".
        mlRewriteBy "0" at 1.
        mlIntro "H".
        mlRewriteBy "H" at 1.
        mlRewriteBy "H" at 1.
        pose proof use_bool_axiom AxDefAndRightTrue Γ H.
        simpl in H2. mlAdd H2. mlSpecialize "1" with x. mlSimpl. cbn. fold mlBool. mlRevert "1".
        mlRewriteBy "H" at 2.
        mlRewriteBy "H" at 2.
        mlIntro "1".
        mlAssert ("P":( mlFalse &&ml mlTrue =ml mlFalse  )).
        - wf_auto2.
        - mlApply "1".
          mlRewriteBy "ind" at 1.
          mlApplyMeta membership_or_2.
          mlRight.
          mlRewriteBy "0" at 1. 
          mlAssumption.
          set_solver.
        - mlRewriteBy "P" at 1.
          (*  need mlSymmetrt here          
            *)
          mlSymmetry.
        mlReflexivity.
 } 
 {  unfold theory in H. set_solver. }
 Admitted. *)


End bools.
Close Scope ml_scope.
Close Scope string_scope.
Close Scope list_scope.