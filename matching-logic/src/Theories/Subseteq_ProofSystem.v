From Coq Require Import ssreflect ssrfun ssrbool.

From Ltac2 Require Import Ltac2.

Require Import Equations.Prop.Equations.

From Coq Require Import String Ensembles Setoid Btauto.
Require Import Coq.Program.Equality.
From Coq.Classes Require Import Morphisms_Prop.
From Coq.Unicode Require Import Utf8.
From Coq.micromega Require Import Lia.

From stdpp Require Import base fin_sets sets propset proof_irrel option list coGset finite infinite gmap.

From MatchingLogic Require Import
  Logic
  DerivedOperators_Syntax
  ProofMode.MLPM
.
From MatchingLogic.Theories Require Import Definedness_Syntax Definedness_ProofSystem DeductionTheorem.
From MatchingLogic.Utils Require Import stdpp_ext.
Import extralibrary.

Import MatchingLogic.Logic.Notations.
Import MatchingLogic.DerivedOperators_Syntax.Notations.
Import MatchingLogic.Syntax.BoundVarSugar.

Set Default Proof Mode "Classic".

Import Notations.

Open Scope ml_scope.
Open Scope string_scope.
Open Scope list_scope.

Lemma patt_subseteq_trans
    {Σ : Signature}
    {syntax : Definedness_Syntax.Syntax}
    (Γ : Theory)
    (ϕ₁ ϕ₂ ϕ₃ : Pattern)
    :
    well_formed ϕ₁ ->
    well_formed ϕ₂ ->
    well_formed ϕ₃ ->
    Definedness_Syntax.theory ⊆ Γ ->
    Γ ⊢ patt_subseteq ϕ₁ ϕ₂ --->
        patt_subseteq ϕ₂ ϕ₃ --->
        patt_subseteq ϕ₁ ϕ₃
.
Proof.
    intros wfϕ1 wfϕ2 wfϕ3 HΓ.
    toMLGoal.
    { wf_auto2. }
    mlIntro "H1".
    mlIntro "H2".
    mlAssert ("H3":((patt_subseteq ϕ₁ ϕ₂) and (patt_subseteq ϕ₂ ϕ₃))).
    { wf_auto2. }
    {
        mlSplitAnd; mlAssumption.
    }
    mlClear "H1".
    mlClear "H2".
    mlRevert "H3".
    pose proof (Htmp := patt_total_and Γ (ϕ₁ ---> ϕ₂) (ϕ₂ ---> ϕ₃) HΓ ltac:(wf_auto2) ltac:(wf_auto2)).
    apply useGenericReasoning with (i := AnyReasoning) in Htmp .
    2: { apply pile_any. }
    unfold patt_subseteq.
    mlRewrite <- Htmp at 1.
    clear Htmp.
    mlIntro "H3".
    mlDeduct "H3".
    fromMLGoal.
    apply phi_impl_total_phi_meta.
    { wf_auto2. }
    { try_solve_pile. }
    
    lazymatch goal with
    | [|- ?th ⊢i _ using ?i] => remember th as Γ'; remember i as pi
    end.
    assert (Hand: Γ' ⊢i ((ϕ₁ ---> ϕ₂) and (ϕ₂ ---> ϕ₃)) using pi).
    {
        gapply hypothesis.
        { subst. try_solve_pile. }
        { wf_auto2. }
        {
            subst. clear. set_solver.
        }
    }
    pose proof (H1 := Hand).
    apply pf_conj_elim_l_meta in H1.
    2,3: wf_auto2.
    pose proof (H2 := Hand).
    apply pf_conj_elim_r_meta in H2.
    2,3: wf_auto2.
    (* TODO rename to patt_imp_trans or similar *)
    eapply syllogism_meta.
    1,3: wf_auto2.
    2: apply H1.
    1: wf_auto2.
    apply H2.
Defined.