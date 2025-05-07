From MatchingLogic Require Export Sorts_ProofSystem
                                  Bool_Syntax.
Import MatchingLogic.Logic.Notations
       MatchingLogic.Theories.Definedness_Syntax.Notations
       MatchingLogic.Theories.Sorts_Syntax.Notations
       MatchingLogic.Theories.Bool_Syntax.Notations.

Set Default Proof Mode "Classic".

Open Scope list_scope.

Section bools.
Context
  { Σ : Signature}
  { syntax : Syntax}.

  Lemma use_bool_axiom ax Γ : 
    Bool_Syntax.theory ⊆ Γ ->
      Γ ⊢ axiom ax.
  Proof.
    intro HΓ.
    apply useBasicReasoning.
    apply hypothesis.
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
    fromMLGoal.

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
    cbn. fold mlBool.
    unfold theory in H.
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
      + mlExists x. mlSimpl. cbn. fromMLGoal. apply useBasicReasoning.  
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
      + mlExists x. mlSimpl. cbn. fromMLGoal. apply useBasicReasoning.  
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
    cbn. fold mlBool.
    unfold theory in H.
    pose proof use_bool_axiom AxDefAndRightTrue Γ H.
    simpl in H0. mlAdd H0.
    mlSpecialize "0" with x. mlSimpl. cbn. fold mlBool.
    mlAssumption.
  Qed.
  
  
  Theorem false_andBool : forall Γ , theory ⊆ Γ ->
                           Γ ⊢ all mlBool,  b0 &&ml mlFalse =ml mlFalse.
  Proof.
    intros.
    toMLGoal.
    wf_auto2.
    mlIntroAll x.
    cbn. fold mlBool.
    unfold theory in H.
    pose proof use_bool_axiom AxDefAndRightFalse Γ H.
    simpl in H0. mlAdd H0.
    mlSpecialize "0" with x. mlSimpl. cbn. fold mlBool. 
    mlAssumption.
  Qed.
  
  
  Theorem comm_andBool : forall Γ , theory ⊆ Γ ->
                          Γ ⊢ all mlBool, all mlBool, b0 &&ml b1 =ml b1 &&ml b0.
  Proof.
    intros.
    toMLGoal.
    wf_auto2.
    mlIntroAll x.
    mlSimpl. fold mlBool.
    unfold theory in H.
    pose proof use_bool_axiom AxInductiveDomain Γ H.
    simpl in H0. mlAdd H0 as "ind".
    mlRewriteBy "ind" at 1.
    mlIntro "H".
    mlApplyMeta membership_or_1 in "H".
    {
      mlDestructOr "H".
      (* mlTrue case *)
      * pose proof membership_equal_equal Γ ( patt_free_evar x) mlTrue.
        ospecialize* H1.
        + set_solver.
        + simpl. auto.
        + wf_auto2.
        + wf_auto2.
        + mlExists x. mlSimpl. fromMLGoal. apply useBasicReasoning.  
          epose proof patt_equal_refl  (patt_free_evar x) Γ.
          apply H2. wf_auto2.
        + mlApplyMeta ex_sort_impl_ex.
          - pose proof use_bool_axiom AxFunTrue Γ H;simpl in H2;mlAdd H2 as "f";mlExact "f".
          - set_solver.
        + mlAdd H1. mlRevert "0".
          mlRewriteBy "1" at 1.
          mlIntro "H".
          mlRewriteBy "H" at 1.
          mlRewriteBy "H" at 1.
          mlClear "1";mlClear "ind"; mlClear "H".
          mlIntroAll y.
          cbn. fold mlBool.
          mlAdd H0 as "ind".
          mlRewriteBy "ind" at 1.
          mlIntro "H".
          mlApplyMeta membership_or_1 in "H".
          {
            mlDestructOr "H".
            (* y = mlTrue  *)
            * pose proof membership_equal_equal Γ ( patt_free_evar y) mlTrue.
              ospecialize* H2.
              + set_solver.
              + simpl. auto.
              + wf_auto2.
              + wf_auto2.
              + mlExists y. mlSimpl. fromMLGoal. apply useBasicReasoning.  
                epose proof patt_equal_refl  (patt_free_evar y) Γ.
                apply H3. wf_auto2.
              + mlApplyMeta ex_sort_impl_ex.
                - pose proof use_bool_axiom AxFunTrue Γ H;simpl in H3;mlAdd H3 as "f";mlExact "f" .
                - set_solver.
              + mlAdd H2. mlRevert "0". mlRewriteBy "1" at 1. mlIntro "H".
                mlRewriteBy "H" at 1.
                mlRewriteBy "H" at 1.
                mlReflexivity.
             (* y = mlFalse *)
             * pose proof membership_equal_equal Γ ( patt_free_evar y) mlFalse.
              ospecialize* H2.
              + set_solver.
              + simpl. auto.
              + wf_auto2.
              + wf_auto2.
              + mlExists y. mlSimpl. fromMLGoal. apply useBasicReasoning.  
                epose proof patt_equal_refl  (patt_free_evar y) Γ.
                apply H3. wf_auto2.
              + mlApplyMeta ex_sort_impl_ex.
                - pose proof use_bool_axiom AxFunFalse Γ H;simpl in H3;mlAdd H3 as "f";mlExact "f" .
                - set_solver.
              + mlAdd H2. mlRevert "1". mlRewriteBy "0" at 1. mlIntro "H".
                mlRewriteBy "H" at 1.
                mlRewriteBy "H" at 1.
                pose proof use_bool_axiom AxDefAndRightTrue Γ H.
                simpl in H3. mlAdd H3. mlSpecialize "1" with y. mlSimpl. fold mlBool. mlRevert "1".
                mlRewriteBy "H" at 2.
                mlRewriteBy "H" at 2.
                mlIntro "H1".
                mlAssert ("P":( mlTrue &&ml mlFalse  =ml mlFalse  )).
                1: wf_auto2.
                1: { mlClear "H1".
                  pose proof use_bool_axiom AxDefAndLeftTrue Γ H.
                  simpl in H4. mlAdd H4.
                  mlSpecialize "1" with y. mlSimpl. fold mlBool. mlRevert "1".
                  mlRewriteBy "H" at 2.
                  mlRewriteBy "H" at 2.
                  mlIntro "H1". mlApply "H1".
                  mlRewriteBy "ind" at 1.
                  mlApplyMeta membership_or_2.
                  mlRewriteBy "0" at 1.
                  {
                    mlRight.
                    mlAssumption.
                  }
                  { set_solver. }
                }
                mlRewriteBy "P" at 1.
                mlApply "H1".
                mlRewriteBy "ind" at 1.
                mlApplyMeta membership_or_2.
                mlRewriteBy "0" at 1.
                {
                  mlRight. mlExact "H".
                }
                { unfold theory in H. set_solver.  }
          }
          { set_solver. } 
        
      (* mlFalse case *)     
      * pose proof membership_equal_equal Γ ( patt_free_evar x) mlFalse.
        ospecialize* H1.
        + set_solver.
        + simpl. auto.
        + wf_auto2.
        + wf_auto2.
        + mlExists x. mlSimpl. fromMLGoal. apply useBasicReasoning.  
          epose proof patt_equal_refl  (patt_free_evar x) Γ.
          apply H2. wf_auto2.
        + mlApplyMeta ex_sort_impl_ex.
          - pose proof use_bool_axiom AxFunFalse Γ H;simpl in H2;mlAdd H2 as "f";mlExact "f".
          - set_solver.
        + mlAdd H1. mlRevert "1".
          mlRewriteBy "0" at 1.
          mlIntro "H".
          mlRewriteBy "H" at 1.
          mlRewriteBy "H" at 1.
          mlClear "0"; mlClear "ind";mlClear "H".
          mlIntroAll y.
          cbn. fold mlBool.
          mlAdd H0 as "ind".
          mlRewriteBy "ind" at 1.
          mlIntro "H".
          mlApplyMeta membership_or_1 in "H".
          {
            mlDestructOr "H".
            (* y = mlTrue  *)
            * pose proof membership_equal_equal Γ ( patt_free_evar y) mlTrue.
            ospecialize* H2.
            + set_solver.
            + simpl. auto.
            + wf_auto2.
            + wf_auto2.
            + mlExists y. mlSimpl. fromMLGoal. apply useBasicReasoning.  
              epose proof patt_equal_refl  (patt_free_evar y) Γ.
              apply H3. wf_auto2.
            + mlApplyMeta ex_sort_impl_ex.
              - pose proof use_bool_axiom AxFunTrue Γ H;simpl in H3;mlAdd H3 as "f";mlExact "f" .
              - set_solver.
            + mlAdd H2. mlRevert "0". mlRewriteBy "1" at 1. mlIntro "H".
              mlRewriteBy "H" at 1.
              mlRewriteBy "H" at 1.
              pose proof use_bool_axiom AxDefAndRightFalse Γ H.
              simpl in H3. mlAdd H3. mlSpecialize "0" with y. mlSimpl. fold mlBool. mlRevert "0".
              mlRewriteBy "H" at 2.
              mlIntro "H1".
              mlAssert ("P" : (mlFalse &&ml mlTrue =ml mlFalse)).
              1: wf_auto2.
              1: { mlClear "H1".
                  pose proof use_bool_axiom AxDefAndLeftFalse Γ H.
                  simpl in H4. mlAdd H4.
                  mlSpecialize "0" with y. mlSimpl. fold mlBool. mlRevert "0".
                  mlRewriteBy "H" at 2.
                  mlIntro "H1". mlApply "H1".
                  mlRewriteBy "ind" at 1.
                  mlApplyMeta membership_or_2.
                  mlRewriteBy "1" at 1.
                  {
                    mlLeft.
                    mlAssumption.
                  }
                  { set_solver. }
              }
              mlRewriteBy "P" at 1.
              mlApply "H1".
              mlRewriteBy "ind" at 1.
              mlApplyMeta membership_or_2.
              mlRewriteBy "1" at 1.
              {
                mlLeft.
                mlAssumption.
              }
              { set_solver. }
            
            (* y = mlFalse *)
            * pose proof membership_equal_equal Γ ( patt_free_evar y) mlFalse.
            ospecialize* H2.
            + set_solver.
            + simpl. auto.
            + wf_auto2.
            + wf_auto2.
            + mlExists y. mlSimpl. fromMLGoal. apply useBasicReasoning.  
              epose proof patt_equal_refl  (patt_free_evar y) Γ.
              apply H3. wf_auto2.
            + mlApplyMeta ex_sort_impl_ex.
              - pose proof use_bool_axiom AxFunFalse Γ H;simpl in H3;mlAdd H3 as "f";mlExact "f" .
              - set_solver.
            + mlAdd H2. mlRevert "1". mlRewriteBy "0" at 1. mlIntro "H".
              mlRewriteBy "H" at 1.
              mlRewriteBy "H" at 1.
              mlReflexivity.
          } 
          { set_solver. }
    }
    { set_solver. }
  Qed.
 
 
  Theorem true_andThenBool : forall Γ , theory ⊆ Γ ->
                              Γ ⊢ all mlBool,  b0 andThen mlTrue =ml b0. 
  Proof.
    intros.
    toMLGoal.
    wf_auto2.
    mlIntroAll x.
    cbn. fold mlBool.
    unfold theory in H.
    pose proof use_bool_axiom AxDefAndThenRightTrue Γ H.
    simpl in H0. mlAdd H0. 
    mlSpecialize "0" with x. mlSimpl. fold mlBool.
    mlAssumption. 
  Qed.


  Theorem false_andThenBool : forall Γ , theory ⊆ Γ ->
                               Γ ⊢ all,  b0 andThen mlFalse =ml mlFalse. 
  Proof.
    intros.
    toMLGoal.
    wf_auto2.
    mlIntroAll x.
    cbn.
    pose proof use_bool_axiom AxDefAndThenRightFalse Γ H.
    simpl in H0. mlAdd H0. mlSpecialize "0" with x. mlSimpl.
    mlAssumption. 
  Qed.


End bools.
Close Scope ml_scope.
Close Scope string_scope.
Close Scope list_scope.
