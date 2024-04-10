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
  
End sumsort.

Close Scope ml_scope.
Close Scope string_scope.
Close Scope list_scope.