From Coq Require Import ssreflect ssrfun ssrbool.

From Coq Require Import Strings.String.
From Coq Require Import Logic.PropExtensionality Logic.Eqdep_dec.

From Equations Require Import Equations.

From stdpp Require Export base gmap fin_sets sets list countable.
From MatchingLogic Require Import
  Syntax
  DerivedOperators_Syntax
  ProofSystem
  ProofInfo
  Utils.stdpp_ext
.
From MatchingLogicProver Require Import Named NamedProofSystem.

From stdpp Require Import base finite gmap mapset listset_nodup numbers propset list pretty strings.

Fixpoint evars_of_proof
  {Σ : Signature}  
  {ϕ : Pattern}
  {Γ : Theory}
  (pf : ML_proof_system Γ ϕ)
  : gset evar
:=
match pf with
| hypothesis _ ax _ _ => free_evars ax
| P1 _ phi psi _ _ => free_evars phi ∪ free_evars psi
| P2 _ phi psi xi _ _ _ => free_evars phi ∪ free_evars psi ∪ free_evars xi
| P3 _ phi _ => free_evars phi
| Modus_ponens _ _ _ pf1 pf2
=> evars_of_proof pf1 ∪ evars_of_proof pf2
| Ex_quan _ phi y _ => {[y]} ∪ free_evars phi
| Ex_gen _ phi1 phi2 x _ _ pf' _ => {[x]} ∪ (evars_of_proof pf') ∪ free_evars phi1 ∪ free_evars phi2
| Prop_bott_left _ phi _ => free_evars phi
| Prop_bott_right _ phi _ => free_evars phi
| Prop_disj_left _ phi psi xi _ _ _ => free_evars phi ∪ free_evars psi ∪ free_evars xi
| Prop_disj_right _ phi psi xi _ _ _ => free_evars phi ∪ free_evars psi ∪ free_evars xi
| Prop_ex_left _ phi psi _ _ =>
  free_evars phi ∪ free_evars psi
| Prop_ex_right _ phi psi _ _ =>
  free_evars phi ∪ free_evars psi
| Framing_left _ _ _ psi wfp pf' => free_evars psi ∪ (evars_of_proof pf')
| Framing_right _ _ _ psi wfp pf' => free_evars psi ∪ (evars_of_proof pf')
| Svar_subst _ _ psi _ _ _ pf' => free_evars psi ∪ (evars_of_proof pf')
| Pre_fixp _ phi _ => free_evars phi
| Knaster_tarski _ _ phi psi pf' => evars_of_proof pf'
| Existence _ => ∅
| Singleton_ctx _ C1 C2 phi x _ => {[x]} ∪ free_evars phi ∪ AC_free_evars C1 ∪ AC_free_evars C2
end.


Fixpoint svars_of_proof
  {Σ : Signature}  
  {ϕ : Pattern}
  {Γ : Theory}
  (pf : ML_proof_system Γ ϕ)
  : gset svar
:=
match pf with
| hypothesis _ ax _ _ => free_svars ax
| P1 _ phi psi _ _ => free_svars phi ∪ free_svars psi
| P2 _ phi psi xi _ _ _ => free_svars phi ∪ free_svars psi ∪ free_svars xi
| P3 _ phi _ => free_svars phi
| Modus_ponens _ _ _ pf1 pf2
=> svars_of_proof pf1 ∪ svars_of_proof pf2
| Ex_quan _ phi y _ => free_svars phi
| Ex_gen _ phi1 phi2 x _ _ pf' _ => svars_of_proof pf' ∪ free_svars phi1 ∪ free_svars phi2
| Prop_bott_left _ phi _ => free_svars phi
| Prop_bott_right _ phi _ => free_svars phi
| Prop_disj_left _ phi psi xi _ _ _ => free_svars phi ∪ free_svars psi ∪ free_svars xi
| Prop_disj_right _ phi psi xi _ _ _ => free_svars phi ∪ free_svars psi ∪ free_svars xi
| Prop_ex_left _ phi psi _ _ =>
  free_svars phi ∪ free_svars psi
| Prop_ex_right _ phi psi _ _ =>
  free_svars phi ∪ free_svars psi
| Framing_left _ _ _ psi wfp pf' => free_svars psi ∪ (svars_of_proof pf')
| Framing_right _ _ _ psi wfp pf' => free_svars psi ∪ (svars_of_proof pf')
| Svar_subst _ _ psi X _ _ pf' =>  {[X]} ∪ free_svars psi ∪ (svars_of_proof pf')
| Pre_fixp _ phi _ => free_svars phi
| Knaster_tarski _ _ phi psi pf' => svars_of_proof pf'
| Existence _ => ∅
| Singleton_ctx _ C1 C2 phi x _ => free_svars phi ∪ AC_free_svars C1 ∪ AC_free_svars C2
end.

Record ImmutableState
  {Σ : Signature}
  {Γ0 : Theory}
  {ϕ0 : Pattern}
  (pf : ML_proof_system Γ0 ϕ0)
  := {
  one_distinct_evar : evar ;
  one_distinct_svar : svar ;
  patterns_from_proof : gset Pattern ;
  evars_to_avoid : gset evar ;
  svars_to_avoid : gset svar ;
  ode_fresh :
    forall phi,
      phi ∈ patterns_from_proof ->
      one_distinct_evar ∉ free_evars phi ;
}.

Arguments patterns_from_proof {Σ Γ0 ϕ0} {pf} i.
Arguments evars_to_avoid {Σ Γ0 ϕ0} {pf} i.
Arguments svars_to_avoid {Σ Γ0 ϕ0} {pf} i.
Arguments one_distinct_evar {Σ Γ0 ϕ0} {pf} i.
Arguments one_distinct_svar {Σ Γ0 ϕ0} {pf} i.

Fixpoint covers'
  {Σ : Signature}
  {Γ0 : Theory}
  {ϕ0 : Pattern}
  {pf0 : ML_proof_system Γ0 ϕ0 }
  (s : @ImmutableState _ Γ0 ϕ0 pf0)  
  {ϕ : Pattern}
  {Γ : Theory}
  (pf : ML_proof_system Γ ϕ)
  : Type
:=
match pf with
| hypothesis _ _ _ _ => True
| P1 _ _ _ _ _ => True
| P2 _ _ _ _ _ _ _ => True
| P3 _ _ _ => True
| Modus_ponens _ _ _ pf1 pf2
=> ((covers' s pf1) * (covers' s pf2))%type
| Ex_quan _ phi y _ => phi ∈ (patterns_from_proof s)
| Ex_gen _ phi1 phi2 x _ _ pf' _ => ((phi1 ∈ (patterns_from_proof s)) * (x ∈ evars_to_avoid s) * covers' s pf')%type
| Prop_bott_left _ _ _ => True
| Prop_bott_right _ _ _ => True
| Prop_disj_left _ _ _ _ _ _ _ => True
| Prop_disj_right _ _ _ _ _ _ _ => True
| Prop_ex_left _ phi psi _ _ =>
((phi ∈ (patterns_from_proof s)) * ((patt_app phi psi) ∈ (patterns_from_proof s)))%type
| Prop_ex_right _ phi psi _ _ =>
((phi ∈ (patterns_from_proof s)) * ((patt_app psi phi) ∈ (patterns_from_proof s)))%type
| Framing_left _ _ _ psi wfp pf' => (covers' s pf')
| Framing_right _ _ _ psi wfp pf' => (covers' s pf')
| Svar_subst _ _ _ _ _ _ pf' => (covers' s pf')
| Pre_fixp _ phi _ => phi ∈ (patterns_from_proof s)
| Knaster_tarski _ phi psi _ pf' => ((phi ∈ (patterns_from_proof s)) * (covers' s pf'))%type
| Existence _ => (patt_bound_evar 0) ∈ (patterns_from_proof s) (* HERE note that patterns in the map need not be well-formed-closed *)
| Singleton_ctx _ _ _ _ _ _ => True
end.

Class Ln2NamedProperties
{Σ : Signature}
{Γ0 : Theory}
{ϕ0 : Pattern}
(pf0 : ML_proof_system Γ0 ϕ0)
(l2n : ImmutableState pf0 -> Pattern -> NamedPattern)
:= mkLn2NamedProperties {
    scan : forall {Γ} {ϕ} (pf : ML_proof_system Γ ϕ), (@ImmutableState _ Γ ϕ pf) ;
    scan_covers : forall {Γ} {ϕ} (pf : ML_proof_system Γ ϕ), covers' (scan pf) pf ;
    l2n_nwf :
      forall (s : ImmutableState pf0),
        forall ϕ,
          named_well_formed (l2n s ϕ) = true;
    l2n_imp:
      forall (s : ImmutableState pf0),
        forall ϕ₁ ϕ₂,
          l2n s (patt_imp ϕ₁ ϕ₂) = npatt_imp (l2n s ϕ₁) (l2n s ϕ₂) ;
    l2n_app:
      forall (s : ImmutableState pf0),
        forall ϕ₁ ϕ₂,
          l2n s (patt_app ϕ₁ ϕ₂) = npatt_app (l2n s ϕ₁) (l2n s ϕ₂) ;
    l2n_bott :
      forall (s : ImmutableState pf0),
        l2n s patt_bott = npatt_bott ;
    l2n_ex :
      forall (s : ImmutableState pf0),
        forall phi,
          phi ∈ (patterns_from_proof s) ->
          l2n s (patt_exists phi) = npatt_exists (one_distinct_evar s) (l2n s phi) ;
    l2n_mu :
    forall (s : ImmutableState pf0),
      forall phi,
        phi ∈ (patterns_from_proof s) ->
        l2n s (patt_mu phi) = npatt_mu (one_distinct_svar s) (l2n s phi) ;
    l2n_evar_open :
      forall (s : ImmutableState pf0),
        forall ϕ y,
          ϕ ∈ (patterns_from_proof s) ->
          l2n s (evar_open y 0 ϕ) = rename_free_evar (l2n s ϕ) y (one_distinct_evar s) ;
    l2n_exists_quantify :
      forall (s : ImmutableState pf0),
        forall ϕ x,
          ϕ ∈ (patterns_from_proof s) ->
          l2n s (exists_quantify x ϕ) = npatt_exists x (l2n s ϕ) ;
    l2n_avoid :
      forall (s : ImmutableState pf0),
      forall x ϕ,
        x ∈ evars_to_avoid s ->
        x ∉ named_free_evars (l2n s ϕ) ;
    l2n_avoid_distinct_e :
      forall (s : ImmutableState pf0),  
        forall ϕ,
          (one_distinct_evar s) ∉ named_free_evars (l2n s ϕ) ;
    l2n_svar_subst :
      forall (s : ImmutableState pf0),
        forall phi psi X,
          l2n s (free_svar_subst psi X phi) = named_svar_subst (l2n s phi) (l2n s psi) X ;
    l2n_bsvar_subst :
      forall (s : ImmutableState pf0),
        forall ϕ ψ,
          ϕ ∈ (patterns_from_proof s) ->
          l2n s (bsvar_subst ψ 0 ϕ) = named_svar_subst (l2n s ϕ) (l2n s ψ) (one_distinct_svar s) ;
    l2n_bevar :
      forall (s : ImmutableState pf0),
        forall n,
          patt_bound_evar n ∈ (patterns_from_proof s) ->
          l2n s (patt_bound_evar n) = npatt_evar (one_distinct_evar s) ;
    l2nctx :
      ImmutableState pf0 -> Application_context -> Named_Application_context ;
    l2n_subst_ctx :
      forall (s : ImmutableState pf0),
        forall C phi, l2n s (subst_ctx C phi) = named_subst_ctx (l2nctx s C) (l2n s phi) ;
    l2n_free_evar :
      forall (s : ImmutableState pf0),
        forall x, l2n s (patt_free_evar x) = npatt_evar x ;
}.


Section ProofConversionAbstractReader.


  Context
    {Σ : Signature}
    (l2n :
      forall {Γ0 : Theory} {ϕ0 : Pattern} {pf0 : ML_proof_system Γ0 ϕ0},
        ImmutableState pf0 ->
        Pattern ->
        NamedPattern
    )
    {_ln2named_prop :
      forall {Γ0 : Theory} {ϕ0 : Pattern} {pf0 : ML_proof_system Γ0 ϕ0},
        Ln2NamedProperties pf0 l2n
    }
  .

  Definition pf_ln2named
    (Γ : Theory)
    (ϕ : Pattern)
    (wfϕ : well_formed ϕ)
    (pf : ML_proof_system Γ ϕ)
    : 
      let l2n0 := (@l2n Γ ϕ pf) in
      let _ln2named_prop0 := (_ln2named_prop Γ ϕ pf) in
      let scan0 := (@scan Σ Γ ϕ pf l2n0 _ln2named_prop0 Γ ϕ pf) in
      NP_ML_proof_system
        (
          (fun p =>
            (@l2n Γ ϕ pf scan0 p)) <$> Γ
        )
        (@l2n Γ ϕ pf scan0 ϕ).
  Proof.
    intros l2n0 _ln2named_prop0 scan0.
    pose proof (Hc := @scan_covers Σ Γ ϕ pf l2n0 _ln2named_prop0 Γ ϕ pf).
    remember (scan pf) as myscan.
    clear Heqmyscan.
    unfold l2n0. clear l2n0. unfold _ln2named_prop0. clear _ln2named_prop0.
    unfold scan0. clear scan0.
    remember (pf) as pf0.
    move: myscan Hc.
    Set Printing Implicit.
    rewrite {3}Heqpf0.
    (*rewrite {1 2 4 5}Heqpf0.*)
    Set Printing Implicit.
    clear Heqpf0.
    remember ϕ as ϕ0.
    rewrite Heqϕ0 in wfϕ.
    move: pf.
    Set Printing Implicit.
    rewrite {1 4 7}Heqϕ0.
    clear Heqϕ0.
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
        rewrite l2n_free_evar.
        apply N_Singleton_ctx.
    }
  Defined.
End ProofConversionAbstractReader.


Fixpoint trigger_patterns
  {Σ : Signature}
  {ϕ : Pattern}
  {Γ : Theory}
  (pf : ML_proof_system Γ ϕ)
  : gset Pattern
:=
match pf with
| hypothesis _ _ _ _ => ∅
| P1 _ _ _ _ _ => ∅
| P2 _ _ _ _ _ _ _ => ∅
| P3 _ _ _ => ∅
| Modus_ponens _ _ _ pf1 pf2
=> trigger_patterns pf1 ∪ trigger_patterns pf2
| Ex_quan _ phi y _ => {[phi]}
| Ex_gen _ phi1 phi2 x _ _ pf' _ => {[phi1]} ∪ trigger_patterns pf'
| Prop_bott_left _ _ _ => ∅
| Prop_bott_right _ _ _ => ∅
| Prop_disj_left _ _ _ _ _ _ _ => ∅
| Prop_disj_right _ _ _ _ _ _ _ => ∅
| Prop_ex_left _ phi psi _ _ => {[phi]} ∪ {[patt_app phi psi]}
| Prop_ex_right _ phi psi _ _ => {[phi]} ∪ {[patt_app psi phi]}
| Framing_left _ _ _ psi wfp pf' => (trigger_patterns pf')
| Framing_right _ _ _ psi wfp pf' => (trigger_patterns pf')
| Svar_subst _ _ _ _ _ _ pf' => (trigger_patterns pf')
| Pre_fixp _ phi _ => {[phi]}
| Knaster_tarski _ phi psi _ pf' => {[phi]} ∪ (trigger_patterns pf')
| Existence _ => {[(patt_bound_evar 0)]}
| Singleton_ctx _ _ _ _ _ _ => ∅
end.

Definition l2n_scan
  {Σ : Signature} {Γ : Theory} {ϕ : Pattern}
  (pf : ML_proof_system Γ ϕ)
  : ImmutableState Γ ϕ
:=
  let eop := evars_of_proof pf in
  let sop := svars_of_proof pf in
  let ode := evar_fresh_s eop in
  let ods := svar_fresh_s sop in
  {|
    patterns_from_proof := trigger_patterns pf ;
    evars_to_avoid := eop ∪ {[ode]} ;
    svars_to_avoid := sop ∪ {[ods]} ;
    one_distinct_evar := ode ;
    one_distinct_svar := ods ;
  |}.


Equations? l2n {Σ : Signature} (s : ImmutableState) (ϕ : Pattern) : NamedPattern by wf (size' ϕ) lt :=
    l2n s (patt_bound_evar _) => npatt_bott ;
    l2n s (patt_bound_svar _) => npatt_bott ;
    l2n s (patt_free_evar x) => npatt_evar x ;
    l2n s (patt_free_svar X) => npatt_svar X ;
    l2n s patt_bott := npatt_bott ;
    l2n s (patt_sym s') := npatt_sym s' ;
    l2n s (patt_imp ϕ₁ ϕ₂)
      := npatt_imp (l2n s ϕ₁) (l2n s ϕ₂) ;
    l2n s (patt_app ϕ₁ ϕ₂)
      := npatt_app (l2n s ϕ₁) (l2n s ϕ₂) ;
    l2n s (patt_exists ϕ') with (decide (ϕ' ∈ patterns_from_proof s)) => {
      | left _ :=
        let x := one_distinct_evar s in 
        npatt_exists x (l2n s (evar_open x 0 ϕ'))
      | right _ :=
        let x := evar_fresh_s (free_evars ϕ' ∪ evars_to_avoid s) in
        npatt_exists x (l2n s (evar_open x 0 ϕ'))
    } ;
    l2n s (patt_mu ϕ') with (decide (ϕ' ∈ patterns_from_proof s)) => {
      | left _ :=
        let X := one_distinct_svar s in 
        npatt_mu X (l2n s (svar_open X 0 ϕ'))
      | right _ :=
        let X := svar_fresh_s (free_svars ϕ' ∪ svars_to_avoid s) in
        npatt_mu X (l2n s (svar_open X 0 ϕ'))
    } .
  Proof.
      all: simpl; try lia.
      { rewrite evar_open_size'. simpl. lia. }
      { rewrite evar_open_size'. simpl. lia. }
      { rewrite svar_open_size'. simpl. lia. }
      { rewrite svar_open_size'. simpl. lia. }
  Qed.

Lemma covers'_l2n_scan: ∀ (Σ : Signature) (Γ : Theory) (ϕ : Pattern) (pf : ML_proof_system Γ ϕ),
  covers' (l2n_scan pf) pf
.
Proof.
  intros.
  assert (He: evars_of_proof pf (*∪ {[evar_fresh_s (evars_of_proof pf)]} *) ⊆ evars_to_avoid (l2n_scan pf)).
  {
    cbn. set_solver.
  }
  assert (Hs: svars_of_proof pf (* ∪ {[svar_fresh_s (svars_of_proof pf)]} *) ⊆ svars_to_avoid (l2n_scan pf)).
  {
    cbn. set_solver.
  }
  assert (Hc : trigger_patterns pf ⊆ patterns_from_proof (l2n_scan pf)).
  { cbn. set_solver. }
  remember (l2n_scan pf) as sc.
  clear Heqsc.
  move: He Hs Hc.
  induction pf; cbn; intros He Hs Hc.
  {
     (* hypothesis*)
    exact I.
  }
  {
    (* P1 *)
    exact I.
  }
  {
    (* P2 *)
    exact I.
  }
  {
    (* P3 *)
    exact I.
  }
  {
    (* MP *)
    feed specialize IHpf1.
    { clear -He. set_solver. }
    { clear -Hs. set_solver. }
    { clear -Hc. set_solver. }
    feed specialize IHpf2.
    { clear -He. set_solver. }
    { clear -Hs. set_solver. }
    { clear -Hc. set_solver. }
    split; assumption.
  }
  {
    (* Ex_quan *) 
    set_solver.
  }
  {
    (* Ex_gen *)
    feed specialize IHpf.
    { clear -He. set_solver. }
    { clear -Hs. set_solver. }
    { clear -Hc. set_solver. }
    repeat split.
    { clear -Hc. set_solver. }
    { clear -He. set_solver. }
    { exact IHpf. }
  }
  {
    (* Prop_bott_left *)
    exact I.
  }
  {
    (* Prop_bott_right *)
    exact I.
  }
  {
    (* Proj_disj_left *)
    exact I.
  }
  {
    (* Prop_disj_right *)
    exact I.
  }
  {
    (* Prop_ex_left *)
    split; set_solver.
  }
  {
    (* Prop_ex_right *)
    split; set_solver.
  }
  {
    (* Framing_left *)
    apply IHpf; set_solver.
  }
  {
    (* Framing_right *)
    apply IHpf; set_solver.
  }
  {
    (* Svar_subst *)
    apply IHpf.
    { set_solver. }
    { set_solver. }
    { set_solver. }
  }
  {
    (* Pre_fixp *)
    set_solver.
  }
  {
    (* Knaster_tarski *)
    split.
    { set_solver. }
    {
      apply IHpf; set_solver.
    }
  }
  {
    (* Existence *)
    set_solver.
  }
  {
    (* Singleton_ctx *)
    exact I.
  }
Qed.

#[global]
Program Instance l2n_properties {Σ : Signature} : Ln2NamedProperties l2n :=
{|
  scan := @l2n_scan Σ ;
|}.
Next Obligation.
  intros. apply covers'_l2n_scan.
Qed.
Next Obligation.
  (* well-formedness *)
  intros.
Admitted.
Next Obligation.
  intros. simp l2n. reflexivity.
Qed.
Next Obligation.
  intros. simp l2n. reflexivity.
Qed.
Next Obligation.
  intros. simp l2n. reflexivity.
Qed.
Next Obligation.
  intros. simp l2n.
  unfold l2n_unfold_clause_9.
  destruct (decide (phi ∈ patterns_from_proof s)).
  {
    reflexivity.
  }
  reflexivity.
Qed.

