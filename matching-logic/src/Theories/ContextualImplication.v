From MatchingLogic Require Export Definedness_ProofSystem.
Import MatchingLogic.Logic.Notations
       MatchingLogic.Theories.Definedness_Syntax.Notations.

Set Default Proof Mode "Classic".

(* TODO split this file into syntax / proof system parts*)

Record StructureContext {Σ : Signature} := mkStructureContext {
    sc_ac : Application_context ;
    sc_pred : Pattern ;
}.

Definition sc_valid
    {Σ : Signature}
    {definedness_syntax : Definedness_Syntax.Syntax}
    (Γ : Theory)
    (SC : StructureContext)
    := Γ ⊢ (sc_pred SC)
.

Definition sc_plug
    {Σ : Signature}
    {definedness_syntax : Definedness_Syntax.Syntax}
    (SC : StructureContext)
    (ϕ : Pattern)
    : Pattern
    := patt_and (subst_ctx (sc_ac SC) ϕ) (sc_pred SC)
.

Definition sc2pctx
    {Σ : Signature}
    {definedness_syntax : Definedness_Syntax.Syntax}
    (SC : StructureContext)
    : PatternCtx
    := 
    let boxvar := (evar_fresh_s ((free_evars_ctx (sc_ac SC)) ∪ (free_evars (sc_pred SC)))) in
    {| pcEvar := boxvar ;
       pcPattern := (ApplicationContext2Pattern boxvar (sc_ac SC)) and (sc_pred SC) ;
    |}
.

Definition patt_set_builder
    {Σ : Signature}
    (ψ : Pattern)
    : Pattern
    := patt_exists (patt_and (patt_bound_evar 0) ψ)
.

Lemma set_builder_full_1
    {Σ : Signature}
    {definedness_syntax : Definedness_Syntax.Syntax}
    (Γ : Theory)
    (ϕ : Pattern)
    :
    Definedness_Syntax.theory ⊆ Γ ->
    well_formed ϕ ->
    Γ ⊢ ϕ ---> (patt_set_builder ((patt_bound_evar 0) ∈ml ϕ))
.
Proof.
    intros HΓ wfϕ.
    unfold patt_set_builder.
    mlFreshEvar as x.

    apply membership_elimination with (x := x).
    {
        fm_solve.
    }
    {
        apply pile_any.
    }
    {
        wf_auto2.
    }
    {
        exact HΓ.
    }
    toMLGoal.
    { wf_auto2. }
    mlIntroAll y.
    mlSimpl.
    mlApplyMeta membership_imp_2.
    2: exact HΓ.
    mlIntro "H".

    mlApplyMeta membership_exists_2.
    3: exact HΓ.
    2: {
      cbn. instantiate (1:= x).
      ltac2:(_fm_export_everything()).
      pose proof (free_evars_bevar_subst ϕ (patt_free_evar y) 1).
      cbn in H5. set_solver.
    }
    mlExists y.
    mlApplyMeta membership_and_2.
    2: exact HΓ.
    fold bevar_subst.
    cbn.
    mlSplitAnd.
    {
        mlApplyMeta membership_refl.
        2: exact HΓ.
        mlExists y.
        mlSimpl.
        unfold evar_open. cbn.
        mlReflexivity.
    }
    {
        rewrite -> bevar_subst_not_occur with (n := 1).
        2: wf_auto2.
        mlApplyMeta membership_symbol_ceil_right.
        3: exact HΓ.
        2: {
          cbn. instantiate (1:= x).
          ltac2:(_fm_export_everything()).
          pose proof (free_evars_bevar_subst ϕ (patt_free_evar y) 0).
          cbn in H5. set_solver.
        }
        mlExists y.
        mlSimpl.
        mlApplyMeta membership_and_2.
        3: {
            eapply well_formed_closed_ex_aux_ind with (ind_evar1 := 0).
            { lia. }
            apply wfc_ex_aux_bevar_subst.
            { wf_auto2. }
            reflexivity.
        }
        2: exact HΓ.
        mlSplitAnd.
        {
            mlApplyMeta membership_refl.
            2: exact HΓ.
            mlExists y.
            mlSimpl.
            unfold evar_open. cbn.
            mlReflexivity.
        }
        unfold evar_open.
        rewrite -> bevar_subst_not_occur at 2.
        2: wf_auto2.
        mlExact "H".
    }
Defined.

Lemma set_builder_full_2
    {Σ : Signature}
    {definedness_syntax : Definedness_Syntax.Syntax}
    (Γ : Theory)
    (ϕ : Pattern)
    :
    Definedness_Syntax.theory ⊆ Γ ->
    well_formed ϕ ->
    Γ ⊢ (patt_set_builder ((patt_bound_evar 0) ∈ml ϕ)) ---> ϕ
.
Proof.
    intros HΓ wfϕ.
    unfold patt_set_builder.
    toMLGoal.
    { wf_auto2. }
    mlIntro "H".
    mlDestructEx "H" as x.
    mlSimpl.
    mlDestructAnd "H" as "H1" "H2".
    unfold evar_open.
    cbn.
    rewrite bevar_subst_not_occur.
    { wf_auto2. }
    mlRevert "H1".
    mlRevert "H2".
    fromMLGoal.
    gapply membership_implies_implication.
    { apply pile_any. }
    wf_auto2.
Defined.


Lemma set_builder_full_iff
    {Σ : Signature}
    {definedness_syntax : Definedness_Syntax.Syntax}
    (Γ : Theory)
    (ϕ : Pattern)
    :
    Definedness_Syntax.theory ⊆ Γ ->
    well_formed ϕ ->
    Γ ⊢ (ϕ) <---> (patt_set_builder ((patt_bound_evar 0) ∈ml ϕ))
.
Proof.
    intros.
    apply pf_iff_split.
    1,2: wf_auto2.
    apply set_builder_full_1; try assumption.
    apply set_builder_full_2; assumption.
Defined.

(*
  We need recursive symbols here, for which we need product sorts.
*)


Lemma set_builder_full
    {Σ : Signature}
    {definedness_syntax : Definedness_Syntax.Syntax}
    (Γ : Theory)
    (ϕ : Pattern)
    :
    Definedness_Syntax.theory ⊆ Γ ->
    well_formed ϕ ->
    Γ ⊢ (ϕ) =ml (patt_set_builder ((patt_bound_evar 0) ∈ml ϕ))
.
Proof.
    intros HΓ wfϕ.
    unfold patt_equal.
    apply phi_impl_total_phi_meta.
    { wf_auto2. }
    { apply pile_any. }
    apply set_builder_full_iff; assumption.
Defined.

Definition contextual_implication
    {Σ : Signature}
    {definedness_syntax : Definedness_Syntax.Syntax}
    (SC : StructureContext)
    (ψ : Pattern)
    := patt_set_builder (patt_subseteq (sc_plug SC (patt_bound_evar 0)) ψ)
.

Lemma wrap_unwrap_helper
    {Σ : Signature}
    {definedness_syntax : Definedness_Syntax.Syntax}
    (Γ : Theory)
    (SC : StructureContext)
    :
    Definedness_Syntax.theory ⊆ Γ ->
    sc_valid Γ SC ->
    (forall (ϕ ψ : Pattern),
        well_formed ϕ ->
        well_formed ψ ->
        Γ ⊢ is_predicate_pattern ψ ->
        Γ ⊢ (sc_plug SC (ϕ and ψ)) =ml ((sc_plug SC ϕ) and ψ)
    ) ->
    (* FIXME I didn't understood from the paper whether ϕ is quantified here,
       or whether it is the same as in the conclusion. *)
    (forall (ϕ: Pattern),
        well_formed (patt_exists ϕ) ->
        Γ ⊢ (sc_plug SC (patt_exists ϕ)) =ml patt_exists (sc_plug SC ϕ)
    ) ->
    forall (ϕ : Pattern),
        well_formed ϕ ->
        Γ ⊢ (sc_plug SC ϕ) =ml (ϕ ---> (contextual_implication SC ϕ))
.
Proof.
    intros HΓ HSC HCpred HCex.
    intros ϕ wfϕ.

    destruct SC as [AC pred].
    
Abort.