From MatchingLogic Require Import Theories.DeductionTheorem.

Import MatchingLogic.Logic.Notations
       MatchingLogic.Theories.Definedness_Syntax.Notations.

Set Default Proof Mode "Classic".

Section running.
  Notation definedness_theory := Theories.Definedness_Syntax.theory.
  Notation definedness_syntax := Theories.Definedness_Syntax.Syntax.
  Context
    {Σ         : Signature}
    {defsyntax : definedness_syntax}
    (Γ         : Theory)
    (HΓ        : definedness_theory ⊆ Γ).

  Context
    (f g P : Pattern)
    (wff   : well_formed (ex, f))
    (wfg   : well_formed (ex, g))
    (wfP   : well_formed P)
    (mfP   : mu_free P)
    (x     : evar).

  (*
     Γ ⊢ (∀z.g z = f z) ∧ P (f x) → ∃y. P (g y)
  *)
  Lemma running_low :
    Γ ⊢ (all, (g =ml f)) and P ⋅ f^{evar:0 ↦ x} ---> 
        ex, (P ⋅ g).
  Proof.
    eapply prf_weaken_conclusion_meta_meta. 1-3: shelve.
    * gapply (Ex_quan _ _ x). 1-2: shelve.
    * cbn. rewrite bevar_subst_not_occur; [shelve|].
      apply lhs_from_and. 1-3: shelve.
      eapply prf_strenghten_premise_meta_meta.
      4: gapply (forall_variable_substitution _ _ x). 1-5: shelve.
      remember (fresh_evar P) as y.
      remember ({| pcEvar := y; pcPattern := P ⋅ patt_free_evar y |}) as C.
      epose proof (equality_elimination_basic Γ (g^{evar:0 ↦ x}) (f^{evar:0 ↦ x})
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
      Γ ⊢ (∀z . g z = f z) ∧ P (f x) → ∃y. P (g y)
  *)
  Lemma running :
    Γ ⊢ (all, (g =ml f)) and P ⋅ f^{evar:0 ↦ x} ---> 
        ex, (P ⋅ g).
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
    (φ t : Pattern)
    (wfφ : well_formed (ex, φ))
    (mfφ : mu_free φ)
    (wft : well_formed t).

  (* this is the dual version of Lemma 61 in
     https://fsl.cs.illinois.edu/publications/chen-rosu-2019-tr.pdf

    Γ ⊢ φ[t/x] ∧ (∃z. t = z) → ∃x.φ
   *)
  Lemma exists_functional_subst :
    Γ ⊢ φ^[evar:0↦t] and is_functional t ---> (ex , φ).
  Proof.
    remember (fresh_evar (φ ⋅ t)) as Zvar.
    remember (patt_free_evar Zvar) as Z.

    (* assertions about well-formedness *)
    assert (well_formed Z) as WFZ.
    { shelve. }

    assert (well_formed (instantiate (ex , φ) t)) as WF1. {
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
    epose proof (PC := prf_conclusion Γ (patt_equal t Z) (instantiate (ex , φ) (patt_free_evar Zvar) ---> ex , φ) AnyReasoning ltac:(shelve) _ EQ).

    assert (Γ ⊢ patt_equal t Z ---> (ex , φ)^[t] ---> ex , φ) as HSUB.
    {
      epose proof (EE := equality_elimination_proj Γ t Z φ HΓ
                                               mfφ wft WFZ _ _).

      epose proof (PSP := prf_strenghten_premise Γ ((patt_equal t Z) and (instantiate (ex , φ) Z))
                                                 ((patt_equal t Z) and (instantiate (ex , φ) t))
                                                 (ex , φ) _ _ _).
      eapply MP.
      2: useBasicReasoning; apply and_impl.
      2,3,4: shelve.
      eapply MP.
      2: eapply MP.
      3: useBasicReasoning; exact PSP.
      * unshelve (epose proof (AI := and_impl' Γ (patt_equal t Z) (φ^[evar: 0 ↦ Z]) (ex , φ) _ _ _)).
        1,2,3: shelve.
        unfold instantiate.
        eapply MP. 2: useBasicReasoning; exact AI.
        rewrite <- HeqZ in PC.
        exact PC.
      * apply and_drop. 1-3: shelve.
        unshelve(epose proof (AI := and_impl' Γ (patt_equal t Z) (instantiate (ex , φ) t) (instantiate (ex , φ) Z) _ _ _)).
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
    pose proof (free_evars_bevar_subst φ t 0).
    pose proof (set_evar_fresh_is_fresh' (free_evars φ ∪ free_evars t)).
    set_solver.
  Defined.
  (* Proof above is ~80 LOC *)

  Lemma running_functional_subst :
    Γ ⊢ φ^[evar:0↦t] and is_functional t ---> (ex , φ).
  Proof.
    mlIntro "H".
    mlDestructAnd "H" as "H1" "H2".
    mlDestructEx "H2" as x.
    mlSimpl. cbn.

    (* Use equality elimination to rewrite under substitution: *)
    unfold evar_open. rewrite (bevar_subst_not_occur _ _ t). shelve. (*!*)
    opose proof* (equality_elimination_basic Γ t (patt_free_evar x) 
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

Section exists_singleton.

  Notation definedness_theory := Theories.Definedness_Syntax.theory.
  Notation definedness_syntax := Theories.Definedness_Syntax.Syntax.
  Context
    {Σ         : Signature}
    {defsyntax : definedness_syntax}
    (Γ         : Theory)
    (HΓ        : definedness_theory ⊆ Γ).

  Context
    (f g P : Pattern)
    (wff   : well_formed (ex, f))
    (wfg   : well_formed (ex, g))
    (wfP   : well_formed P)
    (mfP   : mu_free P)
    (x     : evar).
(*     
    Γ ⊢ₕ φ₁ → ... → φₙ → ψ
    Γ ▷ φ₁, ..., φₙ ⊢ₛ ψ
 *)
  (*
      Γ ⊢ (∀z. g z = f z) ∧ P (f x) → ∃y. P (g y)
  *)
  Goal
    Γ ⊢ (all, (g =ml f)) and P ⋅ f^{evar:0 ↦ x} ---> ex, (P ⋅ g).
  Proof.
    toMLGoal.                       (* - switch to sequent calculus *)
    { wf_auto2. }                   (* - well-formedness of the initial pattern *)
    mlIntro "H".                    (* - implication introduction  *)
    mlDestructAnd "H" as "H1" "H2". (* - conjuction elimination *)
    mlSpecialize "H1" with x.       (* - universal elimination *)
    mlExists x.                     (* - existential introduction *)
    (* simplification of substitutions: *)
    mlSimpl. rewrite [P^{evar:0↦x}]evar_open_closed;[wf_auto2|].
    (***)
    mlRewriteBy "H1" at 1.          (* - equality elimination *)
    mlExact "H2".                   (* - hypothesis *)
  Defined.

  Context {φ : Pattern}
          {wfφ : well_formed (ex, φ)}
          {wfktφ : pattern_kt_well_formed φ}.

  (*
    Γ ⊢ (∃x.x ∧ φ) → ∀y.y → φ
  *)
  Goal
    Γ ⊢ (ex , b0 and φ) ---> (all, (b0 ---> φ)).
  Proof.
    (* first, we get rid of the ∃, and the conjunction *)
    mlIntro.               (* - implication introduction *)
    mlDestructEx "0" as z. (* - existential elimination *)
    mlSimpl. cbn.          (* - substitution simplification *)
    mlDestructAnd "0".     (* - conjuction elimination *)

    mlRevert "2".          (* - revert hypothesis (derived rule) *)
    mlRevert "1".          (* - revert hypothesis (derived rule) *)

    (* We introduce membership: x ∈ (φ(x) ---> ∀y.(y ---> φ(y))) *)
    mlApplyMeta membership_implies_implication.  (* - modus ponens *)
    (* We propagate membership to the primitive subpatterns: *)
    mlApplyMeta membership_imp_2. 2: assumption. (* - modus ponens *)
    mlIntro.                         (* - implication introduction *)
    mlFreshEvar as y.                (* - fresh variable generation for proof constraints *)
    mlApplyMeta membership_forall_2. (* - modus ponens *)
    2: instantiate (1 := y); fm_solve. 2: assumption. (* side conditions *)
    mlIntroAll y. simpl.             (* - universal introduction *)
    mlApplyMeta membership_imp_2.    (* - modus ponens *)
    2: assumption.
    mlIntro.                         (* - implication introduction *)
    (* at this point, we have x ∈ y and x ∈ φ(x) ---> x ∈ φ(y)
       this means that x = y
       and we can use equality elimination to swap φ(x) with φ(y)
     *)
    mlApplyMeta membership_var in "1". (* - modus ponens *)
    2: assumption.
    mlFreshEvar as w.

    (* The next lines contain the application of equality elimination manually *)
    (* TODO: write a theorem which is a corollary of equality elimination, and
       is capable of rewriting inside substitutions *)
    opose proof* (equality_elimination Γ (patt_free_evar z) (patt_free_evar y)
       {| pcEvar := w; pcPattern := patt_free_evar z ∈ml φ^{evar:0↦w}|} HΓ
       ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2)).
     {
       cbn. rewrite kt_well_formed_evar_open. assumption. reflexivity.
     }
     unfold emplace in H. mlSimpl in H. cbn in H.
     case_match. 1: subst w; ltac2:(_fm_export_everything()); exfalso; set_solver.
     erewrite <- !(bound_to_free_variable_subst) in H.
     2: instantiate (1 := 1); lia.
     5: instantiate (1 := 1); lia.
     2-3, 5-6: wf_auto2.
     2: fm_solve.
     2: fm_solve.
     mlApplyMeta H.
     (***)
     mlSplitAnd; mlAssumption.
  Defined.

End exists_singleton.


