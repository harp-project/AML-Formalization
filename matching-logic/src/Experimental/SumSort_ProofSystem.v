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

  Lemma use_sumsort_axiom ax Γ  :
    SumSort_Syntax.theory s1 s2 wfs1 wfs2 ⊆ Γ ->
      Γ ⊢ axiom _ _ ax.
  Proof.
    intro HΓ.
    apply useBasicReasoning.
    apply BasicProofSystemLemmas.hypothesis.
    { clear HΓ. destruct ax; wf_auto2. }
    {
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
                              Γ ⊢ all s1, all s1, ( (b1).mlInjectL( s1 , s2 )  =ml (b0).mlInjectL( s1 , s2 ) ) --->  
                               (b1 =ml b0).
  Proof.
    intros.
    toMLGoal.
    clear H. wf_auto2.
    remember (fresh_evar (s1)) as x.
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
                              Γ ⊢ all s2, all s2, ( (b1).mlInjectR( s1 , s2 )  =ml (b0).mlInjectR( s1 , s2 ) ) --->  
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

  Theorem subseteq_iff_membership:
    ∀ (Γ : Theory) (φ φ' : Pattern),
    Definedness_Syntax.theory ⊆ Γ -> 
    well_formed φ ->
    well_formed φ' ->
    Γ ⊢i  φ  ⊆ml φ'   <--->
        ( all , b0 ∈ml φ ---> b0 ∈ml φ') using AnyReasoning.
  Proof.
  Admitted.
  
  Theorem membership_axiom_v1: 
    ∀ (Γ : Theory) (φ φ' : Pattern) (x : evar),
    Definedness_Syntax.theory ⊆ Γ -> 
    well_formed φ ->
    well_formed φ' ->
    Γ ⊢i patt_free_evar x ∈ml ( φ $ φ' ) =ml ex , ( b0 ∈ml φ and patt_free_evar x ∈ml (b0 $ φ') ) using AnyReasoning.
  Proof.
  Admitted.
  
  Theorem membership_axiom_v2: 
    ∀ (Γ : Theory) (φ φ' : Pattern) (x : evar),
    Definedness_Syntax.theory ⊆ Γ -> 
    well_formed φ ->
    well_formed φ' ->
    Γ ⊢i patt_free_evar x ∈ml ( φ $ φ' ) =ml ex, (b0 ∈ml φ' and patt_free_evar x ∈ml (φ $ b0) ) using AnyReasoning.
  Proof.
  Admitted.
  
  Theorem sum_inj : forall Γ , theory s1 s2 wfs1 wfs2 ⊆ Γ ->
                              Γ ⊢ 〚 mlSum (s1, s2) 〛 =ml  ( (〚s1〛).mlInjectL( s1 , s2 )  or  (〚s2〛).mlInjectR( s1 , s2 ) ) .
  Proof.
    intros.
    toMLGoal.
    1:{ clear H. wf_auto2. }
    pose proof use_sumsort_axiom AxCoProduct Γ H.
    simpl in H0. mlAdd H0 as "coproduct".   
    pose proof use_sumsort_axiom AxInjectLeft Γ H.
    simpl in H1. mlAdd H1 as "INJECT Left".
    pose proof use_sumsort_axiom AxInjectRight Γ H.
    simpl in H2. mlAdd H2 as "INJECT Right".
    clear H0;clear H1;clear H2.
    
    mlAssert ( "P" : (  ( (〚s1〛).mlInjectL( s1 , s2 )  or  (〚s2〛).mlInjectR( s1 , s2 ) )  ⊆ml  〚 mlSum (s1, s2) 〛 ) ) .
    1:{ clear H;wf_auto2. }
    1:{ 
        epose proof subset_disj Γ (〚 mlSum (s1, s2) 〛)   ( (〚 s1 〛 ).mlInjectL( s1 , s2 ) ) ( (〚 s2 〛 ).mlInjectR( s1 , s2 )) 
         AnyReasoning ltac:(set_solver) ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2).
         
        mlRewrite H0 at 1.
        mlSplitAnd.
        (* (〚 s1 〛 ).mlInjectL ⊆ml 〚 mlSum (s1, s2) 〛 *)
        * clear H0.
          epose proof subseteq_iff_membership Γ ((〚 s1 〛 ).mlInjectL( s1 , s2 )) ( 〚 mlSum (s1, s2) 〛) 
            ltac:(set_solver) ltac:(wf_auto2) ltac:(wf_auto2).
            
          mlRewrite H0 at 1.
          remember (fresh_evar ( s1 ---> s2)) as x.
          mlIntroAllManual x.
          1:{ cbn. unfold nest_ex. repeat rewrite nest_ex_aux_wfcex. 
              1-2:clear H; wf_auto2.
              solve_fresh.
            }
            
          simpl.
          rewrite bevar_subst_not_occur.
          1:{ clear H;wf_auto2. }
          mlIntro.
            
          mlAssert ("P" : ( ex s1, (b0).mlInjectL( s1 , s2 ) =ml patt_free_evar x ) ).
          1:{ clear H; wf_auto2. }
          1:{ unfold patt_exists_of_sort.
              unfold nest_ex.
              rewrite nest_ex_aux_wfcex.
              1:wf_auto2.
              rewrite nest_ex_aux_wfcex.
              1:{ clear H; wf_auto2. }
              epose proof membership_axiom_v2 Γ  (patt_sym (inj (ml_injectL s1 s2))) (〚 s1 〛) (x)
                ltac:(set_solver) ltac:(wf_auto2) ltac:(wf_auto2).
                   
              mlAdd H1. mlClear "INJECT Right";mlClear "coproduct".
              mlRevert "0".
              mlRewriteBy "1" at 1.
              mlIntro "H".
               
              remember (fresh_evar( patt_free_evar x ---> s1 ---> s2)) as y. 
              mlDestructEx "H" as y.
              1: { cbn. unfold nest_ex. rewrite nest_ex_aux_wfcex. 
                   clear H; wf_auto2. solve_fresh.
                 }
                
              mlExists y.
              mlSimpl. simpl. cbn.
              unfold evar_open.
              rewrite bevar_subst_not_occur.
              1:{ clear H;wf_auto2. }
                 
              mlDestructAnd "H".
              mlSplitAnd.
              1:mlAssumption.
              mlSpecialize "INJECT Left" with y.
              mlSimpl. unfold evar_open. simpl. cbn.
              unfold nest_ex.
              rewrite nest_ex_aux_wfcex.
              1:{clear H;wf_auto2. }
              rewrite bevar_subst_not_occur.
              1:{clear H;wf_auto2. }
              
              mlAssert ( "3" : (patt_free_evar y ∈ml 〚 s1 〛)).
              1:{ clear H. wf_auto2. }
              1:mlAssumption.
              mlApply "INJECT Left" in "0".
              
              opose proof*( membership_imp_equal Γ ( patt_free_evar x) ( (patt_free_evar y ).mlInjectL( s1 , s2 )) _ _ _ _ ).
              1:set_solver.
              1-3:wf_auto2.
              mlSymmetry.
              mlAdd H2.
              
              mlAssert ("F" : (ex , patt_free_evar x =ml b0)).
              1:wf_auto2.
              1:{ mlExists x. mlSimpl. cbn. mlReflexivity. }
              mlApply "4" in "F".
              mlAssert ("G" : ( ex , (patt_free_evar y ).mlInjectL( s1 , s2 ) =ml b0) ).
              1:wf_auto2.
              1:{ remember (fresh_evar(patt_free_evar x ---> patt_free_evar y ---> s1 ---> s2)) as z.
                  mlDestructEx "0" as z.
                  1-2:cbn; solve_fresh.
                  mlSimpl. cbn. 
                  mlDestructAnd "0".
                  mlExists z. 
                  mlAssumption.
                }
              mlClear "4";mlClear "1";mlClear "0";mlClear "3".  
              mlApply "F" in "G".
              mlApply "G".
              mlAssumption.
            }
          
          remember (fresh_evar( patt_free_evar x ---> s1 ---> s2)) as y.
          mlDestructEx "P" as y.
          1:{ cbn. unfold nest_ex. repeat rewrite nest_ex_aux_wfcex. 
              1-2:clear H; wf_auto2.
              solve_fresh.
            }
          1:{ cbn. unfold nest_ex. rewrite nest_ex_aux_wfcex. 
              clear H; wf_auto2.
              solve_fresh.
            }
          
          mlSimpl. simpl. cbn.
          unfold evar_open.
          rewrite bevar_subst_not_occur.
          1:{ unfold nest_ex. rewrite nest_ex_aux_wfcex.
              all:clear H;wf_auto2. 
            }
          unfold nest_ex.
          rewrite nest_ex_aux_wfcex.
          1:{ clear H;wf_auto2. }
          mlDestructAnd "P".
          mlSpecialize "INJECT Left" with y.
          mlSimpl.
          replace  ( (ex mlSum (s1, s2), (b1 ).mlInjectL( s1 , s2 ) =ml b0)^{evar:0↦y} ) with
            ( ex mlSum (s1, s2), (patt_free_evar y ).mlInjectL( s1 , s2 ) =ml b0) .
          2:{ mlSortedSimpl. mlSimpl. unfold evar_open. simpl. reflexivity. }
          cbn.
          unfold evar_open.
          rewrite bevar_subst_not_occur.
          1:{ unfold nest_ex. rewrite nest_ex_aux_wfcex.
              all:clear H;wf_auto2. 
            }
          unfold nest_ex.
          rewrite nest_ex_aux_wfcex.
          1:{ clear H; wf_auto2. }
          mlApply "INJECT Left" in "1".
          mlClear "INJECT Right";mlClear "INJECT Left".
            
          remember (fresh_evar(patt_free_evar x ---> patt_free_evar y ---> s1 ---> s2)) as z.
          mlDestructEx "1" as z.
          1-2:cbn;solve_fresh.
          mlSimpl. cbn.
          mlDestructAnd "1".
          mlSymmetry in "2".
          mlRewriteBy "2" at 1.
          mlRewriteBy "4" at 1.
          mlAssumption.
            
        (* (〚 s2 〛 ).mlInjectR ⊆ml 〚 mlSum (s1, s2) 〛 *) 
        * clear H0.
          epose proof subseteq_iff_membership Γ ((〚 s2 〛 ).mlInjectR( s1 , s2 )) (〚 mlSum (s1, s2) 〛) 
           ltac:(set_solver) ltac:(wf_auto2) ltac:(wf_auto2).
          
          mlRewrite H0 at 1.
          remember (fresh_evar ( s1 ---> s2)) as x.
          mlIntroAllManual x.
          1:{ cbn.  unfold nest_ex. repeat rewrite nest_ex_aux_wfcex. 
              1-2:clear H; wf_auto2.
              solve_fresh. 
            }
          simpl.
          rewrite bevar_subst_not_occur.
          1:{ clear H;wf_auto2. }
          mlIntro.
          
          mlAssert ("P" : ( ex s2, (b0).mlInjectR( s1 , s2 ) =ml patt_free_evar x ) ).
          1:{ clear H; wf_auto2. }
          1:{ unfold patt_exists_of_sort.
              unfold nest_ex.
              rewrite nest_ex_aux_wfcex.
              1:wf_auto2.
              rewrite nest_ex_aux_wfcex.
              1:clear H;wf_auto2.
              
              epose proof membership_axiom_v2 Γ  (patt_sym (inj (ml_injectR s1 s2))) (〚 s2 〛) (x)
               ltac:(set_solver) ltac:(wf_auto2) ltac:(wf_auto2).
              mlAdd H1.
              mlRevert "0".
              mlRewriteBy "1" at 1.
              mlIntro "H".
               
              remember (fresh_evar( patt_free_evar x ---> s1 ---> s2)) as y.
              mlDestructEx "H" as y.
              1:{ cbn. unfold nest_ex. repeat rewrite nest_ex_aux_wfcex. 
                  1-2:clear H; wf_auto2.
                  solve_fresh.
                }
              mlExists y. 
              mlSimpl. simpl. cbn.
              unfold evar_open.
              rewrite bevar_subst_not_occur.
              1:{ clear H;wf_auto2. } 
              mlDestructAnd "H".
              mlSplitAnd.
              1:mlAssumption.
                 
              mlSpecialize "INJECT Right" with y.
              mlSimpl. unfold evar_open. simpl. cbn.
              unfold nest_ex.
              rewrite nest_ex_aux_wfcex.
              1:{clear H;wf_auto2. }
              rewrite bevar_subst_not_occur.
              1:{clear H;wf_auto2. }
              
              mlAssert( "3" : (patt_free_evar y ∈ml 〚 s2 〛  )).
              1:{ clear H; wf_auto2. }
              mlAssumption.
              mlClear "1";mlClear "INJECT Left".
              mlApply "INJECT Right" in "0".
              
              opose proof* ( membership_imp_equal Γ (patt_free_evar x) (patt_free_evar y).mlInjectR( s1 , s2 ) _ _ _ _ ).
              1:set_solver.
              1-3:wf_auto2.
              mlAdd H2.
              
              mlAssert( "F" : ( ex, patt_free_evar x =ml b0  )).
              1:wf_auto2.
              1:{ mlExists x. mlSimpl. cbn.  mlReflexivity. }
              
              mlApply "1" in "F".
              mlClear "1".
              mlAssert( "G" : (ex , (patt_free_evar y).mlInjectR( s1 , s2 ) =ml b0 )).
              1:wf_auto2.
              1:{ remember (fresh_evar(patt_free_evar x ---> patt_free_evar y ---> s1 ---> s2)) as z.
                  mlDestructEx "0" as z.
                  1-2: cbn;solve_fresh.
                  mlSimpl. cbn.
                  mlDestructAnd "0".
                  mlExists z.
                  mlSimpl. cbn.
                  mlAssumption.
                }
              
              mlApply "F" in "G".
              mlSymmetry.
              mlApply "G".
              mlAssumption.
            }
            
          remember (fresh_evar( patt_free_evar x ---> s1 ---> s2)) as y.
          mlDestructEx "P" as y.
          1:{ cbn. unfold nest_ex. repeat rewrite nest_ex_aux_wfcex.
              1-2: clear H;wf_auto2.
              solve_fresh.
            }
          1:{ unfold nest_ex. rewrite nest_ex_aux_wfcex.
              clear H; wf_auto2.
              solve_fresh.
            } 
          mlSimpl. simpl. cbn.
          unfold evar_open.
          rewrite bevar_subst_not_occur.
          1:{ unfold nest_ex. rewrite nest_ex_aux_wfcex.
              all:clear H;wf_auto2. 
            }
          unfold nest_ex.
          rewrite nest_ex_aux_wfcex.
          1:{ clear H;wf_auto2. }
          mlDestructAnd "P".
          mlSpecialize "INJECT Right" with y.
       
          mlSimpl.
          replace  ( (ex mlSum (s1, s2), (b1 ).mlInjectR( s1 , s2 ) =ml b0)^{evar:0↦y} ) with
            ( ex mlSum (s1, s2), (patt_free_evar y ).mlInjectR( s1 , s2 ) =ml b0) .
          2:{
              mlSortedSimpl. mlSimpl. unfold evar_open. simpl. reflexivity.
             }
          cbn.
          unfold evar_open.
          rewrite bevar_subst_not_occur.
          1:{ unfold nest_ex. rewrite nest_ex_aux_wfcex.
              all:clear H;wf_auto2. 
            }
          unfold nest_ex.
          rewrite nest_ex_aux_wfcex.
          1:{ clear H; wf_auto2. }
          mlApply "INJECT Right" in "1".
          mlClear "INJECT Right";mlClear "INJECT Left".
            
          remember (fresh_evar(patt_free_evar x ---> patt_free_evar y ---> s1 ---> s2)) as z.
          mlDestructEx "1" as z.
          1-2: cbn;solve_fresh.
          mlSimpl. cbn.
          mlDestructAnd "1".
          mlSymmetry in "2".
          mlRewriteBy "2" at 1.
          mlRewriteBy "4" at 1.
          mlAssumption.
      }
      
    mlConj  "coproduct" "P" as "f".
    
    
    epose proof subset_iff_eq Γ (〚 mlSum (s1, s2) 〛) ( (〚 s1 〛 ).mlInjectL( s1 , s2 ) or (〚 s2 〛 ).mlInjectR( s1 , s2 ) ) 
     AnyReasoning _ _ _ .
    
    apply pf_iff_proj1 in H0.
    2-3:clear H;wf_auto2.
    mlApplyMeta H0.
    mlAssumption.
    Unshelve.
    set_solver.
    all:clear H;wf_auto2.
  Defined.
  
End sumsort.

Close Scope ml_scope.
Close Scope string_scope.
Close Scope list_scope.