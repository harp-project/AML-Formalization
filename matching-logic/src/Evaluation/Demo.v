From Coq Require Import String.

From MatchingLogic.Theories Require Import Definedness_Syntax
                                           Definedness_Semantics
                                           Sorts_Syntax
                                           Sorts_Semantics
                                           Definedness_ProofSystem
                                           DeductionTheorem.

From MatchingLogic Require Import
    Logic
    DerivedOperators_Syntax
    ProofSystem
    ProofMode.MLPM
    BasicProofSystemLemmas
    FreshnessManager
.

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
    (P ϕ₁ ϕ₂ : Pattern)
    :
    mu_free P ->
    well_formed P ->
    well_formed (ex, ϕ₁) ->
    well_formed (ex, ϕ₂) ->
    Γ ⊢ (((all, (ϕ₂ =ml ϕ₁)) and (P $ (evar_open x 0 ϕ₁))) ---> 
        ex, (P $ ϕ₂))
  .
  Proof.
    intros mff wff wfϕ₁ wfϕ₂.
    eapply prf_weaken_conclusion_meta_meta. 1-3: shelve.
    gapply (Ex_quan _ _ x). 1-2: shelve.
    cbn. rewrite bevar_subst_not_occur; [shelve|].
    apply lhs_from_and_low. 1-3: shelve.
    eapply prf_strenghten_premise_meta_meta.
    4: gapply (forall_variable_substitution _ _ x). 1-5: shelve.
    remember (fresh_evar P) as y.
    remember ({| pcEvar := y; pcPattern := P $ patt_free_evar y |}) as C.
    epose proof (equality_elimination_basic Γ (ϕ₂^{evar:0 ↦ x}) (ϕ₁^{evar:0 ↦ x}) C _ _ _ _ _).
    subst C. cbn in H.
    destruct decide in H. 2: congruence.
    repeat rewrite free_evar_subst_no_occurrence in H. 1-2: shelve.
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
    17: subst C; cbn; rewrite mff; auto.
    (* 2 free variable inclusion goal *)
    17-18: subst y; solve_fresh.
    (* 25 well_formed goals *)
    1-25: wf_auto2.
  Defined.

  Lemma running
    (x : evar)
    (P ϕ₁ ϕ₂ : Pattern)
    :
    mu_free P ->
    well_formed P ->
    well_formed (ex, ϕ₁) ->
    well_formed (ex, ϕ₂) ->
    Γ ⊢ (((all, (ϕ₂ =ml ϕ₁)) and (P $ (evar_open x 0 ϕ₁))) ---> 
        ex, (P $ ϕ₂))
  .
  Proof.
    intros mff wff wfϕ₁ wfϕ₂.
    mlIntro "H".
    mlDestructAnd "H" as "H1" "H2". mlSpecialize "H1" with x.
    mlExists x. mlSimpl.
    rewrite [P^{evar:0↦x}]evar_open_closed;[wf_auto2|]. (* <- 1 well-formedness constraint *)
    mlRewriteBy "H1" at 1.
    mlExact "H2".
  Defined.


  (* this is the dual version of Lemma 61 in
     https://fsl.cs.illinois.edu/publications/chen-rosu-2019-tr.pdf
   *)
  Lemma exists_functional_subst φ φ' :
    mu_free φ -> well_formed φ' -> well_formed_closed_ex_aux φ 1 -> well_formed_closed_mu_aux φ 0 ->
    Γ ⊢i φ^[evar:0↦φ'] and is_functional φ' ---> (ex , φ)
    using AnyReasoning.
  Proof.
    intros MF WF WFB WFM.
    remember (fresh_evar (φ $ φ')) as Zvar.
    remember (patt_free_evar Zvar) as Z.
    assert (well_formed Z) as WFZ.
    { shelve. }

    assert (well_formed (instantiate (ex , φ) φ')) as WF1. {
      shelve.
    }
    assert (well_formed (instantiate (ex , φ) Z)) as WF2. {
      shelve.
    }
    assert (well_formed (ex, φ)) as WFEX.
    { shelve. }
    pose proof (EQ := BasicProofSystemLemmas.Ex_quan Γ φ Zvar WFEX).
    (* change constraint in EQ. *)
    use AnyReasoning in EQ.
    epose proof (PC := prf_conclusion Γ (patt_equal φ' Z) (instantiate (ex , φ) (patt_free_evar Zvar) ---> ex , φ) AnyReasoning ltac:(shelve) _ EQ).

    assert (Γ ⊢ patt_equal φ' Z ---> (ex , φ) ^ [φ'] ---> ex , φ) as HSUB.
    {
      pose proof (EE := equality_elimination_proj Γ φ' Z φ HΓ
                                               MF WF WFZ WFB WFM).

      epose proof (PSP := prf_strenghten_premise Γ ((patt_equal φ' Z) and (instantiate (ex , φ) Z))
                                                 ((patt_equal φ' Z) and (instantiate (ex , φ) φ'))
                                                 (ex , φ) _ _ _).
      eapply MP.
      2: useBasicReasoning; apply and_impl.
      2,3,4: shelve.
      eapply MP.
      2: eapply MP.
      3: useBasicReasoning; exact PSP.

      * unshelve (epose proof (AI := and_impl' Γ (patt_equal φ' Z) (φ^[evar: 0 ↦ Z]) (ex , φ) _ _ _)).
        1,2,3: shelve.
        unfold instantiate.
        eapply MP. 2: useBasicReasoning; exact AI.
        rewrite <- HeqZ in PC.
        exact PC.
      * apply and_drop. 1-3: shelve.
        unshelve(epose proof (AI := and_impl' Γ (patt_equal φ' Z) (instantiate (ex , φ) φ') (instantiate (ex , φ) Z) _ _ _)).
        1-3: shelve.
        eapply MP. 2: useBasicReasoning; exact AI.
        { exact EE. }
    }

    eapply (BasicProofSystemLemmas.Ex_gen Γ _ _ Zvar) in HSUB.
    3: {
      shelve.
    }
    2: { apply pile_any. }
    (* simplifications *)
    unfold exists_quantify in HSUB.
    mlSimpl in HSUB.
    rewrite -> HeqZ, -> HeqZvar in HSUB.
    simpl evar_quantify in HSUB.
    rewrite decide_True in HSUB. reflexivity.

    rewrite evar_quantify_fresh in HSUB.
    { shelve. }
    (*---*)
    eapply MP. 2: useBasicReasoning; apply and_impl'. 2-4: shelve.
    apply reorder_meta. 1-3: shelve.
    exact HSUB.
    Unshelve.
      (* 27 well-formedness side conditions *)
      all: try wf_auto2.
      1-2: by apply mu_free_wfp.
      (* 2 freshness conditions *)
      clear. 2: solve_fresh.
      pose proof (free_evars_bevar_subst φ φ' 0).
      pose proof (set_evar_fresh_is_fresh' (free_evars φ ∪ free_evars φ')).
      set_solver.
  Defined.

  Lemma running_functional_subst (φ φ' : Pattern) :
    mu_free φ → well_formed φ' → well_formed_closed_ex_aux φ 1 →
    well_formed_closed_mu_aux φ 0 →
    Γ ⊢i φ^[evar:0↦φ'] and is_functional φ' ---> (ex , φ)
              using AnyReasoning.
  Proof.
    intros HMF HWF1 HWF2 HWF3.
    apply mu_free_wfp in HMF as HMFWF.
    mlIntro "H".
    mlDestructAnd "H" as "H1" "H2".
    mlDestructEx "H2" as x.
    mlSimpl. cbn.

    (* Use equality elimination to rewrite under substitution: *)
    unfold evar_open. rewrite (bevar_subst_not_occur _ _ φ'). shelve.
    opose proof* (equality_elimination_basic Γ φ' (patt_free_evar x) 
      {|pcEvar := x; pcPattern := φ^{evar:0 ↦ x}|}); auto.
    { shelve. }
    { shelve. }
    cbn in H.
    mlApplyMeta H in "H2".

    (* Technical: subst cleanup *)
    erewrite <-bound_to_free_variable_subst with (m := 1); auto.
    2-3: shelve.
    erewrite <-bound_to_free_variable_subst with (m := 1); auto.
    2: shelve.
    (***)
    mlDestructAnd "H2" as "H2_1" "H2_2".
    mlExists x. mlApply "H2_1". mlAssumption.
  Unshelve.
    (* 4 well-formedness constraints *)
    1-4: wf_auto2.
    1: by apply mu_free_bevar_subst.
    (* 2 freshness constraints *)
    * fm_solve.
    * fm_solve.
  Defined.

End running.
