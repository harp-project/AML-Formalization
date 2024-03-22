From Coq Require Import String.

From MatchingLogic Require Import
    Logic
    ProofMode.MLPM
    FreshnessManager
    Theories.Definedness_Syntax
    Theories.Definedness_ProofSystem.

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
    {Σ         : Signature}
    {defsyntax : definedness_syntax}
    (Γ         : Theory)
    (HΓ        : definedness_theory ⊆ Γ).

  Context
    (φ₁ φ₂ P : Pattern)
    (wfφ₁    : well_formed (ex, φ₁))
    (wfφ₂    : well_formed (ex, φ₂))
    (wfP     : well_formed P)
    (mfP     : mu_free P)
    (x       : evar).

  (*
  Γ ⊢ ∀z.(φ₂ z = φ₁ z) ∧ P (φ₁ x) ---> ∃y. P (φ₂ y)
  *)
  Lemma running_low :
    Γ ⊢ (all, (φ₂ =ml φ₁)) and P $ φ₁^{evar:0 ↦ x} ---> 
        ex, (P $ φ₂).
  Proof.
    eapply prf_weaken_conclusion_meta_meta. 1-3: shelve.
    * gapply (Ex_quan _ _ x). 1-2: shelve.
    * cbn. rewrite bevar_subst_not_occur; [shelve|].
      apply lhs_from_and. 1-3: shelve.
      eapply prf_strenghten_premise_meta_meta.
      4: gapply (forall_variable_substitution _ _ x). 1-5: shelve.
      remember (fresh_evar P) as y.
      remember ({| pcEvar := y; pcPattern := P $ patt_free_evar y |}) as C.
      epose proof (equality_elimination_basic Γ (φ₂^{evar:0 ↦ x}) (φ₁^{evar:0 ↦ x})
                                              C _ _ _ _ _).
      subst C. cbn in H.
      destruct decide in H. 2: congruence.
      repeat rewrite free_evar_subst_no_occurrence in H. 1-2: shelve.
      eapply prf_weaken_conclusion_meta_meta in H. 2-4: shelve.
      - exact H.
      - eapply prf_strenghten_premise_meta_meta. 1-3: shelve.
        + gapply pf_conj_elim_r. 1-3: shelve.
        + gapply A_impl_A. 1-2: shelve.

  Unshelve.
    (* 32 subgoals *)
    (* 4 proof info goals *)
    4,13,28,31: try_solve_pile.
    (* 1 mu_free goal: *)
    17: subst C; cbn; rewrite mfP; auto.
    (* 2 free variable inclusion goal *)
    17-18: subst y; solve_fresh.
    (* 25 well_formed goals *)
    1-25: wf_auto2.
  Defined.
  (* Proof above is 28 LOC *)

  (*
  Γ ⊢ (∀z.φ₂ z = φ₁ z) ∧ P (φ₁ x) → ∃y. P (φ₂ y)
  *)
  Lemma running :
    Γ ⊢ (all, (φ₂ =ml φ₁)) and P $ φ₁^{evar:0 ↦ x} ---> 
        ex, (P $ φ₂).
  Proof.
    mlIntro "H".
    mlDestructAnd "H" as "H1" "H2". mlSpecialize "H1" with x.
    mlExists x. mlSimpl.
    rewrite [P^{evar:0↦x}]evar_open_closed;[wf_auto2|]. (* <- 1 well-formedness constraint *)
    mlRewriteBy "H1" at 1.
    mlExact "H2".
  Defined.
  (* Proof above is 6 LOC *)

End running.

Section functional_subst.
  Notation definedness_theory := Theories.Definedness_Syntax.theory.
  Notation definedness_syntax := Theories.Definedness_Syntax.Syntax.
  Context
    {Σ         : Signature}
    {defsyntax : definedness_syntax}
    (Γ         : Theory)
    (HΓ        : definedness_theory ⊆ Γ).

  Context
    (φ ψ : Pattern)
    (wfφ : well_formed (ex, φ))
    (mfφ : mu_free φ)
    (wfψ : well_formed ψ).

  (* this is the dual version of Lemma 61 in
     https://fsl.cs.illinois.edu/publications/chen-rosu-2019-tr.pdf

    Γ ⊢ φ[t/x] ∧ (∃z. t = z) → ∃x.φ
   *)
  Lemma exists_functional_subst :
    Γ ⊢ φ^[evar:0↦ψ] and is_functional ψ ---> (ex , φ).
  Proof.
    remember (fresh_evar (φ $ ψ)) as Zvar.
    remember (patt_free_evar Zvar) as Z.

    (* assertions about well-formedness *)
    assert (well_formed Z) as WFZ.
    { shelve. }

    assert (well_formed (instantiate (ex , φ) ψ)) as WF1. {
      shelve.
    }
    assert (well_formed (instantiate (ex , φ) Z)) as WF2. {
      shelve.
    }
    assert (well_formed (ex, φ)) as WFEX.
    { shelve. }
    (****)


    pose proof (EQ := BasicProofSystemLemmas.Ex_quan Γ φ Zvar WFEX).
    (* change constraint in EQ. *)
    use AnyReasoning in EQ.
    epose proof (PC := prf_conclusion Γ (patt_equal ψ Z) (instantiate (ex , φ) (patt_free_evar Zvar) ---> ex , φ) AnyReasoning ltac:(shelve) _ EQ).

    assert (Γ ⊢ patt_equal ψ Z ---> (ex , φ) ^ [ψ] ---> ex , φ) as HSUB.
    {
      epose proof (EE := equality_elimination_proj Γ ψ Z φ HΓ
                                               mfφ wfψ WFZ _ _).

      epose proof (PSP := prf_strenghten_premise Γ ((patt_equal ψ Z) and (instantiate (ex , φ) Z))
                                                 ((patt_equal ψ Z) and (instantiate (ex , φ) ψ))
                                                 (ex , φ) _ _ _).
      eapply MP.
      2: useBasicReasoning; apply and_impl.
      2,3,4: shelve.
      eapply MP.
      2: eapply MP.
      3: useBasicReasoning; exact PSP.
      * unshelve (epose proof (AI := and_impl' Γ (patt_equal ψ Z) (φ^[evar: 0 ↦ Z]) (ex , φ) _ _ _)).
        1,2,3: shelve.
        unfold instantiate.
        eapply MP. 2: useBasicReasoning; exact AI.
        rewrite <- HeqZ in PC.
        exact PC.
      * apply and_drop. 1-3: shelve.
        unshelve(epose proof (AI := and_impl' Γ (patt_equal ψ Z) (instantiate (ex , φ) ψ) (instantiate (ex , φ) Z) _ _ _)).
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
    (****)


    eapply MP. 2: useBasicReasoning; apply and_impl'. 2-4: shelve.
    apply reorder_meta. 1-3: shelve.
    exact HSUB.


  Unshelve.
    (* 29 well-formedness side conditions *)
    all: try wf_auto2.
    (* 2 freshness conditions *)
    clear. 2: solve_fresh.
    pose proof (free_evars_bevar_subst φ ψ 0).
    pose proof (set_evar_fresh_is_fresh' (free_evars φ ∪ free_evars ψ)).
    set_solver.
  Defined.
  (* Proof above is ~80 LOC *)

  Lemma running_functional_subst :
    Γ ⊢ φ^[evar:0↦ψ] and is_functional ψ ---> (ex , φ).
  Proof.
    mlIntro "H".
    mlDestructAnd "H" as "H1" "H2".
    mlDestructEx "H2" as x.
    mlSimpl. cbn.

    (* Use equality elimination to rewrite under substitution: *)
    unfold evar_open. rewrite (bevar_subst_not_occur _ _ ψ). shelve. (*!*)
    opose proof* (equality_elimination_basic Γ ψ (patt_free_evar x) 
      {|pcEvar := x; pcPattern := φ^{evar:0 ↦ x}|}); auto. (*!*)
    { shelve. }
    { shelve. }
    cbn in H.
    mlApplyMeta H in "H2".

    (* Technical: subst cleanup *)
    erewrite <-bound_to_free_variable_subst with (m := 1); auto. (*!*)
    2-4: shelve.
    erewrite <-bound_to_free_variable_subst with (m := 1); auto. (*!*)
    2-3: shelve.
    (****)

    mlDestructAnd "H2" as "H2_1" "H2_2".
    mlExists x. mlApply "H2_1". mlAssumption.


  Unshelve. (* These all come from manual application of lemmas (marked with !) *)
    (* 5 well-formedness constraints *)
    1-5,7: wf_auto2.
    (* 1 mu_free contraint *)
    by apply mu_free_bevar_subst.
    (* 2 freshness constraints *)
    fm_solve. fm_solve.
  Defined.
  (* Proof above is ~30 LOC *)

End functional_subst.
