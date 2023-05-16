From Coq Require Import String.

From MatchingLogic Require Import
    Logic
    DerivedOperators_Syntax
    ProofSystem
    ProofMode.MLPM
    FreshnessManager
.

From MatchingLogic.Theories Require Import Definedness_Syntax
                                           Definedness_Semantics
                                           Sorts_Syntax
                                           Sorts_Semantics
                                           Definedness_ProofSystem
                                           DeductionTheorem.

Import
  MatchingLogic.Logic.Notations
  MatchingLogic.DerivedOperators_Syntax.Notations
  MatchingLogic.Theories.Definedness_Syntax.Notations.

Open Scope string_scope.
Open Scope list_scope.
Open Scope ml_scope.

Section running.
  Notation definedness_theory := Theories.Definedness_Syntax.theory.
  Notation definedness_syntax := Theories.Definedness_Syntax.Syntax.
  Context
    {Σ : Signature}
    {defsyntax : definedness_syntax}
    (Γ : Theory)
    (HΓ : Theories.Definedness_Syntax.theory ⊆ Γ).

  Lemma running
    (x : evar)
    (f ϕ₁ ϕ₂ : Pattern)
    :
    mu_free f ->
    well_formed f ->
    well_formed (ex, ϕ₁) ->
    well_formed (ex, ϕ₂) ->
    Γ ⊢ (((all, (ϕ₂ =ml ϕ₁)) and (f $ (evar_open x 0 ϕ₁))) ---> 
        ex, (f $ ϕ₂))
  .
  Proof.
    (* begin snippet running *)
    intros mff wff wfϕ₁ wfϕ₂. (* .no-in .unfold .no-hyps *)
    mlIntro "H". (* .unfold .no-hyps *)
    mlDestructAnd "H" as "H1" "H2". (* .unfold .no-hyps .in .no-out *) mlSpecialize "H1" with x. (* .unfold .no-hyps *)
    mlExists x. (* .in .no-out *) mlSimpl. (* .unfold .no-hyps .no-out .in *) rewrite [f^{evar:0↦x}]evar_open_closed;[wf_auto2|]. (* .unfold .no-hyps *)
    mlRewriteBy "H1" at 1;[assumption|(apply mu_free_in_path; simpl; by rewrite mff)|]. (* .unfold .no-hyps *)
    mlExact "H2". (* .unfold .no-hyps *)
    (* end snippet running *)
  Defined.

  Lemma running_functional_subst (φ φ' : Pattern) :
    mu_free φ → well_formed φ' → well_formed_closed_ex_aux φ 1 →
    well_formed_closed_mu_aux φ 0 →
    Γ ⊢i φ^[evar:0↦φ'] and (ex , φ' =ml b0) ---> (ex , φ)
              using AnyReasoning.
  Proof.
    intros HMF HWF1 HWF2 HWF3.
    apply mu_free_wfp in HMF as HMFWF.
    toMLGoal. wf_auto2.
    mlIntro "H".
    mlDestructAnd "H" as "H1" "H2".
    mlDestructEx "H2" as x.
    mlSimpl. cbn.

    (* Using equality elimination: *)
    unfold evar_open. rewrite (bevar_subst_not_occur _ _ φ'). wf_auto2.
    feed pose proof (equality_elimination_basic Γ φ' (patt_free_evar x) 
      {|pcEvar := x; pcPattern := φ^{evar:0 ↦ x}|}); auto.
    { wf_auto2. }
    { cbn. by apply mu_free_evar_open. }
    cbn in H.
    mlApplyMeta H in "H2".

    (* Technical: subst cleanup *)
    erewrite <-bound_to_free_variable_subst with (m := 1); auto.
    2: wf_auto2. 2: fm_solve.
    erewrite <-bound_to_free_variable_subst with (m := 1); auto.
    2: wf_auto2. 2: fm_solve.
    (***)
    mlDestructAnd "H2" as "H2_1" "H2_2".
    mlExists x. mlApply "H2_1". mlAssumption.
  Defined.

  Lemma running_forall_functional_subst (φ φ' : Pattern) :
    mu_free φ → well_formed φ' → well_formed_closed_ex_aux φ 1 →
    well_formed_closed_mu_aux φ 0 →
    Γ ⊢i (all , φ) and (ex , φ' =ml b0) ---> φ^[evar:0↦φ']
              using AnyReasoning.
  Proof.
    intros HMF HWF1 HWF2 HWF3.
    apply mu_free_wfp in HMF as HMFWF.
    toMLGoal. wf_auto2.
    mlIntro "H". mlDestructAnd "H" as "H1" "H2".
    mlAdd (running_functional_subst (! φ) φ' ltac:(simpl;auto) HWF1 ltac:(wf_auto2) ltac:(wf_auto2)) as "H0".
    mlSimpl.
    mlApplyMeta Misc.notnot_taut_1. mlIntro "H3".
    mlAssert ("H5" : (ex , ! φ)).
    { wf_auto2. }
    { mlApply "H0". mlSplitAnd; mlAssumption. }
    mlDestructEx "H5" as x. mlSimpl.
    mlApply "H5". mlSpecialize "H1" with x.
    mlAssumption.
  Defined.

  Local Lemma lhs_from_and_low:
    ∀ (a b c : Pattern) (i : ProofInfo),
    well_formed a
      → well_formed b
        → well_formed c
          → Γ ⊢i a ---> b ---> c using i → Γ ⊢i a and b ---> c using i.
  Proof.
    intros a b c i Ha Hb Hc H.
    eapply MP. 2: gapply prf_contraction. 3-4: wf_auto2. 2: try_solve_pile.
    eapply prf_strenghten_premise_meta_meta. 4: gapply pf_conj_elim_l.
    1-3, 5-6: wf_auto2. try_solve_pile.
    eapply reorder_meta. 1-3: wf_auto2.
    eapply prf_strenghten_premise_meta_meta. 4: gapply pf_conj_elim_r.
    1-3, 5-6: wf_auto2. try_solve_pile.
    eapply reorder_meta. 1-3: wf_auto2.
    assumption.
  Defined.

  Lemma running_low
    (x : evar)
    (f ϕ₁ ϕ₂ : Pattern)
    :
    mu_free f ->
    well_formed f ->
    well_formed (ex, ϕ₁) ->
    well_formed (ex, ϕ₂) ->
    Γ ⊢ (((all, (ϕ₂ =ml ϕ₁)) and (f $ (evar_open x 0 ϕ₁))) ---> 
        ex, (f $ ϕ₂))
  .
  Proof.
    intros mff wff wfϕ₁ wfϕ₂.
    eapply prf_weaken_conclusion_meta_meta. 1-3: shelve.
    gapply (Ex_quan _ _ x). 1-2: shelve.
    cbn. rewrite bevar_subst_not_occur; [shelve|].
    (* apply lhs_from_and. 1-3: shelve. <- this is proven by the proof mode *)
    apply lhs_from_and_low. 1-3: shelve.
    eapply prf_strenghten_premise_meta_meta.
    4: gapply (forall_variable_substitution _ _ x). 1-5: shelve.
    remember (fresh_evar f) as y.
    remember ({| pcEvar := y; pcPattern := f $ patt_free_evar y |}) as C.
    epose proof (equality_elimination_basic Γ (ϕ₂^{evar:0 ↦ x}) (ϕ₁^{evar:0 ↦ x}) C _ _ _ _ _).
    subst C. cbn in H.
    destruct decide in H. 2: congruence.
    repeat rewrite free_evar_subst_no_occurrence in H. (* 2 rewrite *) 1-2: shelve.
    eapply prf_weaken_conclusion_meta_meta in H. 2-4: shelve.
    exact H.
    eapply prf_strenghten_premise_meta_meta. 1-3: shelve.
    gapply pf_conj_elim_r. 1-3: shelve.
    gapply A_impl_A. 1-2: shelve.
  Unshelve.
    (* 32 subgoals *)
    (* 4 proof info goals *)
    4,13,28,31: try_solve_pile.
    (* 1 mu_free goal: *)
    17: subst C; cbn; auto.
    (* 2 free variable inclusion goal *)
    17-18: subst y; solve_fresh.
    (* 25 well_formed goals *)
    1-25: wf_auto2.
  Defined.

End running.

Section compute.
  From stdpp Require Import base fin_sets sets propset finite.

  Inductive Symbols :=
  | sym_import_definedness (d : Definedness_Syntax.Symbols)
  | Zero | Succ (* constructors for Nats *)
  | TT | FF
  | even
  .

  Instance Symbols_eqdec : EqDecision Symbols.
  Proof. solve_decision. Defined.

  #[local]
  Program Instance Symbols_fin : Finite Symbols :=
  {|
  enum := [Zero; Succ; TT ; FF; even;
  sym_import_definedness Definedness_Syntax.definedness] ;
  |}.
  Next Obligation.
  repeat constructor; set_solver.
  Qed.
  Next Obligation.
  destruct x; try set_solver.
  destruct d; set_solver.
  Qed.

  Instance signature : Signature :=
  {| variables := StringMLVariables ;
  ml_symbols := {|
  symbols := Symbols ;
  |}
  |}.

  Instance definedness_syntax : Definedness_Syntax.Syntax :=
  {|
  Definedness_Syntax.inj := sym_import_definedness;
  |}.

  Open Scope string_scope.
  Let X0 := patt_free_evar "X0".
  Let Y := patt_free_evar "Y".
  Let sym_even := patt_sym even.
  Let sym_succ := patt_sym Succ.
  Let sym_zero := patt_sym Zero.
  Let sym_tt := patt_sym TT.
  Let sym_ff := patt_sym FF.
  (* axioms *)
  Definition defined : Pattern := Definedness_Syntax.axiom AxDefinedness.

  Definition A : Pattern := patt_bound_evar 0.
  Definition B : Pattern := patt_app sym_succ Y.

  (*
    (∀z. S y = z) ∧ even x ---> ∃z. even (S y)
  *)
  Definition proof_running_low :=
    running_low theory ltac:(set_solver) "X"
    sym_even A B
    ltac:(auto) ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2).
  Definition proof_running_pm :=
    running theory ltac:(set_solver) "X"
    sym_even A B
    ltac:(auto) ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2).

End compute.
