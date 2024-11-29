From MatchingLogic Require Export FreshnessManager.
From MatchingLogic.ProofMode Require Export Firstorder.

Import MatchingLogic.Logic.Notations.

Set Default Proof Mode "Classic".


Lemma mu_monotone_quantify {Σ : Signature} Γ ϕ₁ ϕ₂ X (i : ProofInfo):
  ProofInfoLe ( (ExGen := ∅, SVSubst := {[X]}, KT := true, AKT := ~~ bound_svar_is_banned_under_mus ϕ₁^{{svar:X↦0}} 0 0)) i ->
  svar_has_negative_occurrence X ϕ₁ = false ->
  svar_has_negative_occurrence X ϕ₂ = false ->
  Γ ⊢i ϕ₁ ---> ϕ₂ using i->
  Γ ⊢i (patt_mu (ϕ₁^{{svar: X ↦ 0}})) ---> (patt_mu (ϕ₂^{{svar: X ↦ 0}}))
  using i.
Proof.
  intros pile nonegϕ₁ nonegϕ₂ Himp.
  pose proof (wfϕ12 := proved_impl_wf _ _ (proj1_sig Himp)).
  assert(wfϕ₁ : well_formed ϕ₁) by wf_auto2.
  assert(wfϕ₂ : well_formed ϕ₂) by wf_auto2.

  apply Knaster_tarski.
  { try_solve_pile. }
  {
    wf_auto2.
  }

  pose proof (Htmp := @Svar_subst Σ Γ (ϕ₁ ---> ϕ₂) (mu, ϕ₂^{{svar: X ↦ 0}}) X i).
  ospecialize* Htmp.
  { try_solve_pile. }
  { wf_auto2. }
  { exact Himp. }
  unfold free_svar_subst in Htmp.
  simpl in Htmp.
  fold free_svar_subst in Htmp.

  pose proof (Hpf := Pre_fixp Γ (ϕ₂^{{svar: X ↦ 0}})).
  simpl in Hpf.

  unshelve (eapply (cast_proof' Γ _ _) in Hpf).
  3: { 
  erewrite bound_to_free_set_variable_subst.
    5: { apply svar_quantify_not_free. }
    4: { wf_auto2. }
    3: { wf_auto2. }
    2: lia.
    reflexivity.
  }

  2: abstract (wf_auto2).

  eapply (cast_proof' Γ) in Hpf.
  2: { wf_auto2. }


  assert(well_formed_positive (ϕ₂^[[svar: X ↦ mu , ϕ₂^{{svar: X ↦ 0}}]]) = true).
  { wf_auto2. }

  assert(well_formed_closed_mu_aux (ϕ₂^[[svar: X ↦ mu , ϕ₂^{{svar: X ↦ 0}}]]) 0 = true). { wf_auto2. }

  assert(well_formed_closed_ex_aux (ϕ₂^[[svar: X ↦ mu , ϕ₂^{{svar: X ↦ 0}}]]) 0 = true). { wf_auto2. }

  assert(well_formed_positive (ϕ₁^[[svar: X ↦ mu , ϕ₂^{{svar: X ↦ 0}}]]) = true).
  { wf_auto2. }

  assert(well_formed_closed_mu_aux (ϕ₁^[[svar: X ↦ mu , ϕ₂^{{svar: X ↦ 0}}]]) 0 = true). { wf_auto2. }

  assert(well_formed_closed_ex_aux (ϕ₁^[[svar: X ↦ mu , ϕ₂^{{svar: X ↦ 0}}]]) 0 = true). { wf_auto2. }

  apply useBasicReasoning with (i := i) in Hpf.
  rewrite svar_open_svar_quantify in Hpf. wf_auto2.
  epose proof (Hsi := syllogism_meta _ _ _ Htmp Hpf).
  simpl.

  eapply (@cast_proof' Σ Γ).
  1: {
    erewrite bound_to_free_set_variable_subst with (X := X).
    5: { apply svar_quantify_not_free. }
    4: { wf_auto2. }
    3: { wf_auto2. }
    2: lia.
    reflexivity.
  }

  eapply (cast_proof' Γ).
  1: { wf_auto2. }
  rewrite svar_open_svar_quantify. wf_auto2.
  apply Hsi.
  Unshelve.
  all: abstract(wf_auto2).
Defined.

Lemma mu_monotone {Σ : Signature} Γ ϕ₁ ϕ₂ X (i : ProofInfo):
  ProofInfoLe ( (ExGen := ∅, SVSubst := {[X]}, KT := true, AKT := ~~ bound_svar_is_banned_under_mus ϕ₁ 0 0)) i ->
  well_formed (patt_mu ϕ₁) ->
  well_formed (patt_mu ϕ₂) ->
  X ∉ free_svars ϕ₁ ∪ free_svars ϕ₂ ->
  Γ ⊢i ϕ₁^{svar:0↦X} ---> ϕ₂^{svar:0↦X} using i->
  Γ ⊢i (patt_mu ϕ₁) ---> (patt_mu ϕ₂)
  using i.
Proof.
  intros.
  apply mu_monotone_quantify with (X := X) in H3.
  * rewrite svar_quantify_svar_open in H3. set_solver. wf_auto2.
    rewrite svar_quantify_svar_open in H3. set_solver. wf_auto2.
    assumption.
  * rewrite svar_quantify_svar_open. set_solver. wf_auto2. assumption.
  * apply positive_negative_occurrence_db_named.
    wf_auto2.
    wf_auto2.
    unfold svar_is_fresh_in. set_solver.
  * apply positive_negative_occurrence_db_named.
    wf_auto2.
    wf_auto2.
    unfold svar_is_fresh_in. set_solver.
Defined.

Lemma mu_iff_quantify {Σ : Signature} Γ ϕ₁ ϕ₂ X (i : ProofInfo):
  ProofInfoLe ( (ExGen := ∅, SVSubst := {[X]}, KT := true, AKT := true)) i ->
  svar_has_negative_occurrence X ϕ₁ = false ->
  svar_has_negative_occurrence X ϕ₂ = false ->
  Γ ⊢i ϕ₁ <---> ϕ₂ using i->
  Γ ⊢i (patt_mu (ϕ₁^{{svar: X ↦ 0}})) <---> (patt_mu (ϕ₂^{{svar: X ↦ 0}}))
  using i.
Proof.
  intros.
  
  apply pf_iff_split.
  { wf_auto2. }
  { wf_auto2. }
  {
    apply mu_monotone_quantify; try assumption.
    { try_solve_pile. }
    { 
      apply pf_iff_proj1 in H2.
      { exact H2. }
      { wf_auto2. }
      { wf_auto2. }
    }
  }
  {
    apply mu_monotone_quantify; try assumption.
    { try_solve_pile. }
    { 
      apply pf_iff_proj2 in H2.
      { exact H2. }
      { wf_auto2. }
      { wf_auto2. }
    }
  }
Defined.

Lemma move_mu_under_implication
  {Σ : Signature}
  Γ φ ψ :
    well_formed φ ->
    well_formed (mu , ψ) ->
    Γ ⊢i φ ---> (mu , ψ) ---> mu , (φ ---> ψ) using
      (ExGen := ∅,
       SVSubst := ∅,
       KT := true,
       AKT := ~~ bound_svar_is_banned_under_mus ψ 0 0).
Proof.
  intros.
  assert (no_positive_occurrence_db_b 0 φ). {
  (* TODO: wf_auto2 breaks without this assert later! *)
    wf_auto2.
  }
  do 2 mlIntro.
  mlApplyMeta (Knaster_tarski Γ ψ (mu, φ ---> ψ)) in "1".
  2: {
    toMLGoal. {
      wf_auto2.
    }
    mlIntro; mlApplyMeta Pre_fixp. simpl.
    mlIntro. mlAssumption.
  }
  mlAssumption.
Defined.
