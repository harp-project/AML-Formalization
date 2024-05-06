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
  ProductSort
.

Import MatchingLogic.Theories.Sorts_Syntax.Notations.
Import MatchingLogic.Theories.ProductSort.Notations.

Open Scope ml_scope.
Open Scope string_scope.
Open Scope list_scope.

Section productsort.
  Context
      {Σ : Signature}
      (s1 s2 : Pattern)
      (wfs1 : well_formed s1 = true)
      (wfs2 : well_formed s2 = true)
      {syntax : ProductSort.Syntax s1 s2}
    .
    
(*     Local Notation "'(' phi1 ',ml' phi2 ')'" := 
        (patt_app (patt_app (patt_sym (inj (ml_pair s1 s2))) phi1) phi2)
        : ml_scope
    .

    Local Notation "'(' phi ').mlProjL'" := 
        (patt_app (patt_sym (inj (ml_projL s1 s2))) phi)
        : ml_scope
    .

    Local Notation "'(' phi ').mlProjR'" := 
        (patt_app (patt_sym (inj (ml_projR s1 s2))) phi)
        : ml_scope
    . *)
    
  Lemma use_productsort_axiom ax Γ  :
      ProductSort.theory s1 s2 wfs1 wfs2 ⊆ Γ -> 
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
  
  Theorem prod_sort : forall Γ , theory s1 s2 wfs1 wfs2 ⊆ Γ ->
                              Γ ⊢ all mlProd(s1,s2), ex s1, ex s2,  ( b1 ∷ s1 , b0 ∷ s2 ) =ml b2  .
  Proof.
    intros.
    toMLGoal.
    1: clear H;wf_auto2.
    remember (fresh_evar( s1 ---> s2)) as x.
    mlIntroAllManual x.
    1:{ cbn. unfold nest_ex. repeat rewrite nest_ex_aux_wfcex.
        1-2:clear H;wf_auto2.
        solve_fresh.
      }
    mlSortedSimpl. 
    mlSimpl.
    mlIntro.
    mlSortedSimpl.
    mlSimpl. simpl. cbn.
    repeat rewrite bevar_subst_not_occur.
    1-2: clear H;wf_auto2.
    
    pose proof use_productsort_axiom AxProjLeft Γ H.
    pose proof use_productsort_axiom AxProjRight Γ H.
    pose proof use_productsort_axiom InversePairProjb Γ H.
    
    simpl in *.
    mlAdd H0 as "f".
    mlAdd H1 as "g".
    mlAdd H2 as "z".
    
    mlSpecialize "f" with x.
    mlSimpl.
    
    pose proof sorted_exists_binder as BE. destruct BE as [BE].
    erewrite (BE _ (evar_open _)); eauto.
    mlSimpl. simpl. cbn.
    unfold evar_open.
    rewrite bevar_subst_not_occur.
    1:{ clear H. wf_auto2. }
    
    mlAssert ("C" : ( patt_free_evar x ∈ml 〚 mlProd (s1, s2) 〛) ).
    1:wf_auto2.
    1:mlAssumption.
    mlApply "C" in "f".
      
    remember (fresh_evar( s1 ---> s2 ---> patt_free_evar x)) as y.
    mlDestructEx "C" as y.
    1:{ simpl. cbn. unfold nest_ex. repeat rewrite nest_ex_aux_wfcex.
        1-2:clear H;wf_auto2.
        solve_fresh.
      }
    1:{ unfold nest_ex. rewrite nest_ex_aux_wfcex.
        1:clear H;wf_auto2.
        solve_fresh.
      }
    1:{ unfold nest_ex. repeat rewrite nest_ex_aux_wfcex.
        1-2:clear H;wf_auto2.
        solve_fresh.
      }
      
    unfold evar_open. mlSimpl. simpl. unfold nest_ex. rewrite nest_ex_aux_wfcex.
    1:{ clear H. wf_auto2. }
    rewrite bevar_subst_not_occur. 
    1:{ clear H. wf_auto2. }
    mlDestructAnd "C".
    mlClear "f".
      
    mlSpecialize "g" with x.
    mlSimpl.
    erewrite (BE _ (evar_open _)); eauto.
    mlSimpl. simpl. cbn.
    unfold evar_open.
    rewrite bevar_subst_not_occur.
    1:{ clear H. wf_auto2. }
    
    mlAssert ("C" : ( patt_free_evar x ∈ml 〚 mlProd (s1, s2) 〛) ).
    1:wf_auto2.
    1:mlAssumption.
    mlApply "C" in "g".
    
    remember (fresh_evar( s1 ---> s2 ---> patt_free_evar x ---> patt_free_evar y)) as z.
    mlDestructEx "C" as z.
    1:{ simpl. cbn. unfold nest_ex. repeat rewrite nest_ex_aux_wfcex.
          1-2:clear H;wf_auto2.
          solve_fresh.
      }
    1:{ unfold nest_ex. rewrite nest_ex_aux_wfcex.
          1:clear H;wf_auto2.
          solve_fresh.
        }
    1:{ unfold nest_ex. repeat rewrite nest_ex_aux_wfcex.
          1-2:clear H;wf_auto2.
          solve_fresh.
      }
    unfold evar_open. mlSimpl. simpl. unfold nest_ex. rewrite nest_ex_aux_wfcex.
    1:clear H;wf_auto2.
    rewrite bevar_subst_not_occur. 
    1:clear H;wf_auto2.
    mlDestructAnd "C".
    mlClear "g".
    
    mlExists y. mlSimpl. 
    mlSplitAnd.
    * unfold evar_open. mlSimpl. simpl. unfold nest_ex. rewrite nest_ex_aux_wfcex.
      1:clear H;wf_auto2. 
      rewrite bevar_subst_not_occur. 
      1:clear H;wf_auto2. 
      mlAssumption.
    * mlSortedSimpl. mlSimpl. simpl. cbn.
      unfold evar_open. rewrite bevar_subst_not_occur.
      1:{ clear H. wf_auto2. }
      mlExists z. mlSimpl. simpl. cbn. unfold nest_ex. rewrite nest_ex_aux_wfcex.
      1:clear H;wf_auto2. unfold evar_open.
      rewrite bevar_subst_not_occur.
      clear H;wf_auto2.
      mlSplitAnd.
      + mlAssumption.
      + mlSymmetry in "2". mlRewriteBy "2" at 1.
        mlSymmetry in "4". mlRewriteBy "4" at 1.
        mlSpecialize "z" with x. mlSimpl. simpl. cbn.
        mlApply "z".
        mlAssumption.
  Defined.

End productsort.

Close Scope ml_scope.
Close Scope string_scope.
Close Scope list_scope.