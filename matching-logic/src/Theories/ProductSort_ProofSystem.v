From MatchingLogic Require Export Sorts_ProofSystem
                                  ProductSort.
Import MatchingLogic.Logic.Notations
       MatchingLogic.Theories.Definedness_Syntax.Notations
       MatchingLogic.Theories.Sorts_Syntax.Notations
       MatchingLogic.Theories.ProductSort.Notations.

Set Default Proof Mode "Classic".

Open Scope list_scope.

Section productsort.
  Context
      {Σ : Signature}
      (s1 s2 : Pattern)
      (wfs1 : well_formed s1 = true)
      (wfs2 : well_formed s2 = true)
      {syntax : ProductSort.Syntax s1 s2}
    .

  Lemma use_productsort_axiom ax Γ  :
      ProductSort.theory s1 s2 wfs1 wfs2 ⊆ Γ -> 
        Γ ⊢ axiom _ _ ax.
  Proof.
    intro HΓ.
    apply useBasicReasoning.
    apply hypothesis.
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
    mlIntroAll x.
    mlSimpl.
    mlIntro.
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
    unfold evar_open.
    rewrite bevar_subst_not_occur.
    1:{ clear H. wf_auto2. }
    
    mlAssert ("C" : ( patt_free_evar x ∈ml ⟦ mlProd (s1, s2) ⟧) ).
    1:wf_auto2.
    1:mlAssumption.
    mlApply "C" in "f".

    mlDestructEx "C" as y.

    mlSimpl. unfold nest_ex. rewrite nest_ex_aux_wfcex.
    1:{ clear H. wf_auto2. }

    rewrite evar_open_not_occur. 
    1:{ clear H. wf_auto2. }
    mlDestructAnd "C".
    mlClear "f".

    mlSpecialize "g" with x.
    mlSimpl.
    rewrite evar_open_not_occur.
    1:{ clear H. wf_auto2. }

    mlAssert ("C" : ( patt_free_evar x ∈ml ⟦ mlProd (s1, s2) ⟧) ).
    1:wf_auto2.
    1:mlAssumption.
    mlApply "C" in "g".

    mlDestructEx "C" as z.

    mlSimpl. unfold nest_ex. rewrite nest_ex_aux_wfcex.
    1:clear H;wf_auto2.
    rewrite evar_open_not_occur. 
    1:clear H;wf_auto2.
    mlDestructAnd "C".
    mlClear "g".

    mlExists y. mlSimpl. 
    mlSplitAnd.
    * mlSimpl. unfold nest_ex. rewrite nest_ex_aux_wfcex.
      1:clear H;wf_auto2. 
      rewrite evar_open_not_occur. 
      1:clear H;wf_auto2. 
      mlAssumption.
    * mlSimpl.
      rewrite evar_open_not_occur.
      1:{ clear H. wf_auto2. }
      mlExists z. mlSimpl. unfold nest_ex. rewrite nest_ex_aux_wfcex.
      1:clear H;wf_auto2.
      rewrite evar_open_not_occur.
      clear H;wf_auto2.
      mlSplitAnd.
      + mlAssumption.
      + mlSymmetry in "2". mlRewriteBy "2" at 1.
        mlSymmetry in "4". mlRewriteBy "4" at 1.
        mlSpecialize "z" with x. mlSimpl.
        mlApply "z".
        mlAssumption.
  Defined.

End productsort.
