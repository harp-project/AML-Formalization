From MatchingLogic Require Export
  Logic
.
From MatchingLogicProver Require Import NamedProofSystem.
Set Default Proof Mode "Classic".


Section ProofConversionAbstractReader.

  Fixpoint covers
    {Σ : Signature}  
    (m : gmap Pattern (evar*svar)%type)
    {ϕ : Pattern}
    {Γ : Theory}
    (pf : ML_proof_system Γ ϕ)
    : Type
  :=
  match pf with
  | ML_hypothesis _ _ _ _ => True
  | ML_P1 _ _ _ _ _ => True
  | ML_P2 _ _ _ _ _ _ _ => True
  | ML_P3 _ _ _ => True
  | ML_Modus_ponens _ _ _ pf1 pf2
  => ((covers m pf1) * (covers m pf2))%type
  | ML_Ex_quan _ phi y _ => {ev : evar & {sv : svar & m !! phi = Some (ev,sv) } }
  | ML_Ex_gen _ phi1 phi2 x _ _ pf' _ => ({ev : evar & {sv : svar & m !! phi1 = Some (ev,sv)}} * covers m pf')%type
  | ML_Prop_bott_left _ _ _ => True
  | ML_Prop_bott_right _ _ _ => True
  | ML_Prop_disj_left _ _ _ _ _ _ _ => True
  | ML_Prop_disj_right _ _ _ _ _ _ _ => True
  | ML_Prop_ex_left _ phi psi _ _ =>
    (exists ev sv, m !! phi = Some (ev,sv)) /\ (m !! (patt_app phi psi)) = (m !! phi)
  | ML_Prop_ex_right _ phi psi _ _ =>
    (exists ev sv, m !! phi = Some (ev,sv)) /\ (m !! (patt_app psi phi)) = (m !! phi)
  | ML_Framing_left _ _ _ psi wfp pf' => (covers m pf')
  | ML_Framing_right _ _ _ psi wfp pf' => (covers m pf')
  | ML_Svar_subst _ _ _ _ _ _ pf' => (covers m pf')
  | ML_Pre_fixp _ phi _ => {ev : evar & {sv : svar & m !! phi = Some (ev,sv) } }
  | ML_Knaster_tarski _ _ phi psi pf' => ({ev : evar & {sv : svar & m !! phi = Some (ev,sv)}} * covers m pf')%type
  | ML_Existence _ => {ev : evar & {sv : svar & m !! (patt_bound_evar 0) = Some (ev,sv) } } (* HERE note that patterns in the map need not be well-formed-closed *)
  | ML_Singleton_ctx _ _ _ _ _ _ => True
  end.


  Record ImmutableState {Σ : Signature} := {
    one_distinct_evar : evar ;
    one_distinct_svar : svar ;
    patterns_from_proof : gset Pattern ;
    evars_to_avoid : gset evar;
  }.


  Fixpoint covers'
    {Σ : Signature}
    (s : ImmutableState)  
    {ϕ : Pattern}
    {Γ : Theory}
    (pf : ML_proof_system Γ ϕ)
    : Type
  :=
  match pf with
  | ML_hypothesis _ _ _ _ => True
  | ML_P1 _ _ _ _ _ => True
  | ML_P2 _ _ _ _ _ _ _ => True
  | ML_P3 _ _ _ => True
  | ML_Modus_ponens _ _ _ pf1 pf2
  => ((covers' s pf1) * (covers' s pf2))%type
  | ML_Ex_quan _ phi y _ => phi ∈ (patterns_from_proof s)
  | ML_Ex_gen _ phi1 phi2 x _ _ pf' _ => ((phi1 ∈ (patterns_from_proof s)) * (x ∈ evars_to_avoid s) * covers' s pf')%type
  | ML_Prop_bott_left _ _ _ => True
  | ML_Prop_bott_right _ _ _ => True
  | ML_Prop_disj_left _ _ _ _ _ _ _ => True
  | ML_Prop_disj_right _ _ _ _ _ _ _ => True
  | ML_Prop_ex_left _ phi psi _ _ =>
    ((phi ∈ (patterns_from_proof s)) * ((patt_app phi psi) ∈ (patterns_from_proof s)))%type
  | ML_Prop_ex_right _ phi psi _ _ =>
    ((phi ∈ (patterns_from_proof s)) * ((patt_app psi phi) ∈ (patterns_from_proof s)))%type
  | ML_Framing_left _ _ _ psi wfp pf' => (covers' s pf')
  | ML_Framing_right _ _ _ psi wfp pf' => (covers' s pf')
  | ML_Svar_subst _ _ _ _ _ _ pf' => (covers' s pf')
  | ML_Pre_fixp _ phi _ => phi ∈ (patterns_from_proof s)
  | ML_Knaster_tarski _ phi psi _ pf' => ((phi ∈ (patterns_from_proof s)) * (covers' s pf'))%type
  | ML_Existence _ => (patt_bound_evar 0) ∈ (patterns_from_proof s) (* HERE note that patterns in the map need not be well-formed-closed *)
  | ML_Singleton_ctx _ _ _ _ _ _ => True
  end.

  Class Ln2NamedProperties
    {Σ : Signature}
    (l2n : ImmutableState -> Pattern -> NamedPattern)
    := mkLn2NamedProperties {
        scan : forall {Γ} {ϕ}, ML_proof_system Γ ϕ -> ImmutableState ;
        scan_covers : forall {Γ} {ϕ} (pf : ML_proof_system Γ ϕ), covers' (scan pf) pf ;
        l2n_nwf : forall s ϕ, named_well_formed (l2n s ϕ) = true;
        l2n_imp: forall s ϕ₁ ϕ₂, l2n s (patt_imp ϕ₁ ϕ₂) = npatt_imp (l2n s ϕ₁) (l2n s ϕ₂) ;
        l2n_app: forall s ϕ₁ ϕ₂, l2n s (patt_app ϕ₁ ϕ₂) = npatt_app (l2n s ϕ₁) (l2n s ϕ₂) ;
        l2n_bott : forall s, l2n s patt_bott = npatt_bott ;
        l2n_ex : forall s phi,
          phi ∈ (patterns_from_proof s) ->
          l2n s (patt_exists phi) = npatt_exists (one_distinct_evar s) (l2n s phi) ;
        l2n_mu : forall s phi,
          phi ∈ (patterns_from_proof s) ->
          l2n s (patt_mu phi) = npatt_mu (one_distinct_svar s) (l2n s phi) ;
        l2n_evar_open : forall s ϕ y,
          ϕ ∈ (patterns_from_proof s) ->
          l2n s (evar_open y 0 ϕ) = rename_free_evar (l2n s ϕ) y (one_distinct_evar s) ;
        l2n_exists_quantify : forall s ϕ x,
          ϕ ∈ (patterns_from_proof s) ->
          l2n s (exists_quantify x ϕ) = npatt_exists x (l2n s ϕ) ;
        l2n_avoid : forall s x ϕ,
          x ∈ evars_to_avoid s ->
          x ∉ named_free_evars (l2n s ϕ) ;
        l2n_avoid_distinct_e : forall s ϕ,
          (one_distinct_evar s) ∉ named_free_evars (l2n s ϕ) ;
        l2n_svar_subst : forall s phi psi X,
          l2n s (free_svar_subst psi X phi) = named_svar_subst (l2n s phi) (l2n s psi) X ;
        l2n_bsvar_subst : forall s ϕ ψ,
          ϕ ∈ (patterns_from_proof s) ->
          l2n s (bsvar_subst ψ 0 ϕ) = named_svar_subst (l2n s ϕ) (l2n s ψ) (one_distinct_svar s) ;
        l2n_bevar : forall s n,
          patt_bound_evar n ∈ (patterns_from_proof s) ->
          l2n s (patt_bound_evar n) = npatt_evar (one_distinct_evar s) ;
        l2nctx : ImmutableState -> Application_context -> Named_Application_context ;
        l2n_subst_ctx : forall s C phi, l2n s (subst_ctx C phi) = named_subst_ctx (l2nctx s C) (l2n s phi) ;
        l2n_free_evar : forall s x, l2n s (patt_free_evar x) = npatt_evar x ;
  }.

  Context
    {Σ : Signature}
    (l2n : ImmutableState -> Pattern -> NamedPattern)
    {_ln2named_prop : Ln2NamedProperties l2n}
  .

  Definition pf_ln2named
    (Γ : Theory)
    (ϕ : Pattern)
    (wfϕ : well_formed ϕ)
    (pf : ML_proof_system Γ ϕ)
    : NP_ML_proof_system ((fun p => (l2n (scan pf) p)) <$> Γ) (l2n (scan pf) ϕ).
  Proof.
    pose proof (Hc := scan_covers pf).
    remember (scan pf) as myscan.
    clear Heqmyscan.
    move: myscan Hc.
    induction pf; intros myscan Hc; cbn in Hc.
    {
      apply N_hypothesis.
      { apply l2n_nwf. }
      {
        rewrite elem_of_fmap.
        exists axiom.
        split;[reflexivity|assumption].
      }
    }
    {
      rewrite !l2n_imp.
      apply N_P1; apply l2n_nwf.
    }
    {
      rewrite !l2n_imp.
      apply N_P2; apply l2n_nwf.
    }
    {
      rewrite !l2n_imp. rewrite l2n_bott.
      apply N_P3; apply l2n_nwf.
    }
    {
      destruct Hc as [Hc1 Hc2].
      specialize (IHpf1 ltac:(clear -pf1; wf_auto2) myscan Hc1).
      specialize (IHpf2 ltac:(clear -pf2; wf_auto2) myscan Hc2).
      rewrite !l2n_imp in IHpf2.
      eapply N_Modus_ponens.
      4: {
        apply IHpf2.
      }
      3: {
        apply IHpf1.
      }
      { apply l2n_nwf. }
      { cbn. rewrite 2!l2n_nwf. reflexivity. }
    }
    {
      unfold instantiate.
      fold (evar_open y 0 phi).
      rewrite l2n_imp.
      rewrite -> l2n_ex.
      2: { exact Hc. }
      rewrite -> l2n_evar_open.
      2: { exact Hc. }
      apply N_Ex_quan.
    }
    {
      destruct Hc as [[Hc1 Hc2] Hc3].
      specialize (IHpf ltac:(wf_auto2) myscan Hc3).
      rewrite l2n_imp.
      rewrite l2n_imp in IHpf.
      rewrite -> l2n_exists_quantify.
      2: { exact Hc1. }
      apply N_Ex_gen.
      { apply l2n_nwf. }
      { apply l2n_nwf. }
      { apply IHpf. }
      { 
        apply l2n_avoid.
        apply Hc2.
      }
    }
    {
        (* Prop_bott_left *)
        rewrite l2n_imp.
        rewrite l2n_app.
        rewrite l2n_bott.
        apply N_Prop_bott_left.
        { apply l2n_nwf. }
    }
    {
        (* Prop_bott_right *)
        rewrite l2n_imp.
        rewrite l2n_app.
        rewrite l2n_bott.
        apply N_Prop_bott_right.
        { apply l2n_nwf. }
    }
    {
        (* Prop_disj_left *)
        rewrite l2n_imp.
        rewrite l2n_app.
        unfold patt_or, patt_not.
        rewrite 4!l2n_imp.
        rewrite l2n_bott.
        rewrite 2!l2n_app.
        apply N_Prop_disj_left; apply l2n_nwf.
    }
    {
        (* Prop_disj_right *)
        rewrite l2n_imp.
        rewrite l2n_app.
        unfold patt_or, patt_not.
        rewrite 4!l2n_imp.
        rewrite l2n_bott.
        rewrite 2!l2n_app.
        apply N_Prop_disj_right; apply l2n_nwf.
    }
    {
        (* Prop_ex_left *)
        destruct Hc as [Hc1 Hc2].
        rewrite l2n_imp.
        rewrite l2n_app.
        rewrite l2n_ex.
        { exact Hc1. }
        rewrite l2n_ex.
        { exact Hc2. }
        rewrite l2n_app.
        apply N_Prop_ex_left.
        { cbn. apply l2n_nwf. }
        { apply l2n_nwf. }
        { apply l2n_avoid_distinct_e. }
    }
    {
        (* Prop_ex_right *)
        destruct Hc as [Hc1 Hc2].
        rewrite l2n_imp.
        rewrite l2n_app.
        rewrite l2n_ex.
        { exact Hc1. }
        rewrite l2n_ex.
        { exact Hc2. }
        rewrite l2n_app.
        apply N_Prop_ex_right.
        { cbn. apply l2n_nwf. }
        { apply l2n_nwf. }
        { apply l2n_avoid_distinct_e. }
    }
    {
        (* Framing_left *)
        specialize (IHpf ltac:(wf_auto2) myscan).
        rewrite l2n_imp.
        rewrite 2!l2n_app.
        apply N_Framing_left.
        rewrite l2n_imp in IHpf.
        apply IHpf.
        { exact Hc. }
    }
    {
        (* Framing_right *)
        specialize (IHpf ltac:(wf_auto2) myscan).
        rewrite l2n_imp.
        rewrite 2!l2n_app.
        apply N_Framing_right.
        rewrite l2n_imp in IHpf.
        apply IHpf.
        { exact Hc. }
    }
    {
        (* Svar_subst *)
        specialize (IHpf ltac:(wf_auto2) myscan Hc).
        rewrite l2n_svar_subst.
        apply N_Svar_subst.
        { apply l2n_nwf. }
        { apply l2n_nwf. }
        apply IHpf.
    }
    {
        (* Pre_fixp *)
        rewrite l2n_imp.
        unfold instantiate.
        rewrite l2n_bsvar_subst.
        { exact Hc. }
        rewrite l2n_mu.
        { exact Hc. }
        apply N_Pre_fixp.
    }
    {
        (* Knaster_tarski *)
        destruct Hc as [Hc1 Hc2]. 
        specialize (IHpf ltac:(wf_auto2) myscan Hc2).
        rewrite l2n_imp in IHpf.
        unfold instantiate in IHpf.
        rewrite l2n_imp.
        rewrite l2n_mu.
        { exact Hc1. }
        apply N_Knaster_tarski.

        rewrite l2n_bsvar_subst in IHpf.
        { exact Hc1. }
        apply IHpf.
    }
    {
        (* Existence *)
        rewrite l2n_ex.
        { exact Hc. }
        rewrite l2n_bevar.
        { exact Hc. }
        apply N_Existence.
    }
    {
        unfold patt_and,patt_or,patt_not.
        rewrite !l2n_imp.
        rewrite !l2n_subst_ctx.
        rewrite !l2n_imp.
        rewrite l2n_bott.
        pose proof (Htmp := N_Singleton_ctx ((l2n myscan) <$> Γ) (l2nctx myscan C1) (l2nctx myscan C2)).
        unfold npatt_and,npatt_or,npatt_not in Htmp.
        rewrite l2n_free_evar.
        apply Htmp.
    }
  Defined.
End ProofConversionAbstractReader.