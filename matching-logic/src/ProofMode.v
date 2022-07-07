From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Ltac2 Require Import Ltac2.

From Coq Require Import Ensembles Bool.
From Coq.Logic Require Import FunctionalExtensionality Eqdep_dec.
From Equations Require Import Equations.

Require Import Coq.Program.Tactics.

From MatchingLogic Require Import Syntax DerivedOperators_Syntax ProofSystem IndexManipulation wftactics.

From stdpp Require Import list tactics fin_sets coGset gmap sets.

From MatchingLogic.Utils Require Import stdpp_ext.

Import extralibrary.

Import
  MatchingLogic.Syntax.Notations
  MatchingLogic.DerivedOperators_Syntax.Notations
  MatchingLogic.ProofSystem.Notations
.

Set Default Proof Mode "Classic".

(* Exports *)
From MatchingLogic Require Export
  ProofMode_base 
  ProofMode_propositional
.


Open Scope ml_scope.

Section FOL_helpers.

  Context {Σ : Signature}.



  Lemma liftPi (Γ : Theory) (ϕ : Pattern) (i₁ i₂ : ProofInfo)
    {pile : ProofInfoLe i₁ i₂}
    :
    Γ ⊢i ϕ using i₁ ->
    Γ ⊢i ϕ using i₂.
  Proof.
      intros [pf Hpf].
      apply pile in Hpf.
      exists pf.
      exact Hpf.
  Qed.


  (* Unfortunately, this depends on A_impl_A. It would be nice
     if we could make it use only the bult-in proof rules
   *)
  Lemma pile_evs_svs_kt_back evs1 evs2 svs1 svs2 kt1 kt2 fp1 fp2:
  ProofInfoLe
    ( (ExGen := evs1, SVSubst := svs1, KT := kt1, FP := fp1))
    ( (ExGen := evs2, SVSubst := svs2, KT := kt2, FP := fp2)) ->
    evs1 ⊆ evs2 /\ svs1 ⊆ svs2 /\ kt1 ==> kt2 /\ fp1 ⊆ fp2.
  Proof.
    intros pile.
    repeat split.
    {
      destruct pile as [pile].
      rewrite elem_of_subseteq.
      intros x Hx.
      remember (fresh_evar (patt_free_evar x)) as y.
      pose (pf1 := @A_impl_A Σ ∅ (patt_free_evar y) ltac:(wf_auto2)).
      pose (pf2 := @ProofSystem.Ex_gen Σ ∅ (patt_free_evar y) (patt_free_evar y) x ltac:(wf_auto2) ltac:(wf_auto2) (proj1_sig pf1) ltac:(simpl; rewrite elem_of_singleton; solve_fresh_neq)).
      specialize (pile ∅ _ pf2).
      feed specialize pile.
      {
        constructor.
        { simpl. clear -Hx. set_solver. }
        { simpl. clear. set_solver. }
        { simpl. reflexivity. }
        { simpl. set_solver. }
      }
      destruct pile as [Hm2 Hm3 Hm4 Hm5].
      simpl in *.
      clear -Hm2.
      set_solver.
    }
    {
      destruct pile as [pile].
      rewrite elem_of_subseteq.
      intros X HX.
      pose (pf1 := @A_impl_A Σ ∅ (patt_free_svar X) ltac:(wf_auto2)).
      pose (pf2 := @ProofSystem.Svar_subst Σ ∅ (patt_free_svar X ---> patt_free_svar X) patt_bott X ltac:(wf_auto2) ltac:(wf_auto2) (proj1_sig pf1)).
      specialize (pile ∅ _ pf2).
      feed specialize pile.
      {
        constructor; simpl.
        { clear. set_solver. }
        { clear -HX. set_solver. }
        { reflexivity. }
        { set_solver. }
      }
      destruct pile as [Hp2 Hp3 Hp4].
      simpl in *.
      clear -Hp3.
      set_solver.
    }
    {
      destruct pile as [pile].
      pose (pf1 := @A_impl_A Σ ∅ patt_bott ltac:(wf_auto2)).
      pose (pf2 := @ProofSystem.Knaster_tarski Σ ∅ (patt_bound_svar 0) patt_bott ltac:(wf_auto2) (proj1_sig pf1)).
      destruct kt1.
      2: { simpl. reflexivity. }
      specialize (pile ∅ _ pf2).
      feed specialize pile.
      {
        constructor; simpl.
        { clear. set_solver. }
        { clear. set_solver. }
        { reflexivity. }
        { set_solver. }
      }
      destruct pile as [Hp2 Hp3 Hp4].
      simpl in Hp4.
      rewrite Hp4.
      reflexivity.
    }
    {
      destruct pile as [pile].
      rewrite elem_of_subseteq.
      intros (*p*) [p wfp] Hp.
      (*assert (wfp : well_formed p) by admit.*)
      pose (pf1 := @A_impl_A Σ ∅ patt_bott ltac:(wf_auto2)).
      pose (pf2 := @Framing_left Σ ∅ patt_bott patt_bott p wfp (proj1_sig pf1)).
      pose (pf3 := @Framing_right Σ ∅ patt_bott patt_bott p wfp (proj1_sig pf1)).
      pose proof (pile1 := pile ∅ _ pf2).
      pose proof (pile2 := pile ∅ _ pf3).
      clear pile.
      feed specialize pile1.
      {
        constructor; simpl.
        { clear; set_solver. }
        { clear; set_solver. }
        { reflexivity. }
        { simpl. set_solver. }
      }
      feed specialize pile2.
      {
        constructor; simpl.
        { clear; set_solver. }
        { clear; set_solver. }
        { reflexivity. }
        { simpl. set_solver. }
      }
      destruct pile1, pile2. simpl in *.
      rewrite elem_of_subseteq in pwi_pf_fp0.
      setoid_rewrite elem_of_gset_to_coGset in pwi_pf_fp0.
      specialize (pwi_pf_fp0 (exist _ p wfp) ltac:(set_solver)).
      exact pwi_pf_fp0.
    }
  Qed.


  Lemma useGenericReasoning (Γ : Theory) (ϕ : Pattern) evs svs kt fp i:
    (ProofInfoLe ((ExGen := evs, SVSubst := svs, KT := kt, FP := fp)) i) ->
    Γ ⊢i ϕ using ((ExGen := evs, SVSubst := svs, KT := kt, FP := fp)) ->
    Γ ⊢i ϕ using i.
  Proof.
  intros pile [pf Hpf].
  exists pf.
  destruct Hpf as [Hpf2 Hpf3 Hpf4 Hpf5].
  simpl in *.
  destruct i.
  pose proof (Htmp := @pile_evs_svs_kt_back).
  specialize (Htmp evs pi_generalized_evars svs pi_substituted_svars kt pi_uses_kt fp pi_framing_patterns pile).
  destruct Htmp as [Hevs [Hsvs [Hkt Hfp] ] ].
  constructor; simpl.
  { clear -Hpf2 Hevs. set_solver. }
  { clear -Hpf3 Hsvs. set_solver. }
  { unfold implb in *. repeat case_match; try reflexivity; try assumption. inversion Hpf4. }
  { clear -Hpf5 Hfp. set_solver.  }
  Defined.
  


  Lemma Framing_left (Γ : Theory) (ϕ₁ ϕ₂ ψ : Pattern) (i : ProofInfo)
    (wfψ : well_formed ψ)
    {pile : ProofInfoLe ((ExGen := ∅, SVSubst := ∅, KT := false, FP := {[(exist _ ψ wfψ)]})) i}
    :
    Γ ⊢i ϕ₁ ---> ϕ₂ using i ->
    Γ ⊢i ϕ₁ $ ψ ---> ϕ₂ $ ψ using i.
  Proof.
    intros [pf Hpf].
    unshelve (eexists).
    {
      apply ProofSystem.Framing_left.
      { exact wfψ. }
      exact pf.
    }
    {
      destruct Hpf as [Hpf1 Hpf2 Hpf3 Hpf4].
      constructor; simpl.
      {
        assumption.
      }
      {
        assumption.
      }
      {
        assumption.
      }
      { 
        destruct i.
        simpl in *.
        apply pile_evs_svs_kt_back in pile.
        destruct_and!.
        (*
        destruct pi_framing_patterns0.
        { exfalso. set_solver. } *)
        clear H H1 H0.
        rewrite elem_of_subseteq.
        intros p0 Hp0.
        rewrite elem_of_gset_to_coGset in Hp0.
        rewrite elem_of_union in Hp0.
        destruct Hp0 as [Hp0|Hp0].
        {
          subst.
          remember ((@sval) Pattern (λ p : Pattern, well_formed p = true)) as F.
          rewrite elem_of_subseteq in H3.
          specialize (H3 (exist _ ψ wfψ)).
          feed specialize H3.
          {
            clear. set_solver.
          }
          subst F.
          clear -Hp0 H3.
          set_solver.
        }
        {
          set_solver.
        }
      }
    }
  Defined.

  Lemma Framing_right (Γ : Theory) (ϕ₁ ϕ₂ ψ : Pattern) (i : ProofInfo)
  (wfψ : well_formed ψ)
  {pile : ProofInfoLe ((ExGen := ∅, SVSubst := ∅, KT := false, FP := {[(exist _ ψ wfψ)]})) i}
  :
  Γ ⊢i ϕ₁ ---> ϕ₂ using i ->
  Γ ⊢i ψ $ ϕ₁ ---> ψ $ ϕ₂ using i.
Proof.
  intros [pf Hpf].
  unshelve (eexists).
  {
    apply ProofSystem.Framing_right.
    { exact wfψ. }
    exact pf.
  }
  {
    destruct Hpf as [Hpf1 Hpf2 Hpf3 Hpf4].
    constructor; simpl.
    {
      assumption.
    }
    {
      assumption.
    }
    {
      assumption.
    }
    {
      destruct i.
      simpl in *.
      apply pile_evs_svs_kt_back in pile.
      destruct_and!.
      clear H H1 H0.
      rewrite elem_of_subseteq.
      intros p0 Hp0.
      rewrite elem_of_gset_to_coGset in Hp0.
      rewrite elem_of_union in Hp0.
      destruct Hp0 as [Hp0|Hp0].
      {
        subst.
        remember ((@sval) Pattern (λ p : Pattern, well_formed p = true)) as F.
        rewrite elem_of_subseteq in H3.
        specialize (H3 (exist _ ψ wfψ)).
        feed specialize H3.
        {
          clear. set_solver.
        }
        subst F.
        clear -Hp0 H3. set_solver.
      }
      {
        set_solver.
      }
    }
  }
Defined.

  Lemma Prop_bott_left (Γ : Theory) (ϕ : Pattern) :
    well_formed ϕ ->
    Γ ⊢i ⊥ $ ϕ ---> ⊥ using BasicReasoning.
  Proof.
    intros wfϕ.
    unshelve (eexists).
    {
      apply ProofSystem.Prop_bott_left. exact wfϕ.
    }
    {
      constructor; simpl.
      {
        set_solver.
      }
      {
        set_solver.
      }
      {
        reflexivity.
      }
      {
        apply reflexivity.
      }
    }
  Defined.

  Lemma Prop_bott_right (Γ : Theory) (ϕ : Pattern) :
    well_formed ϕ ->
    Γ ⊢i ϕ $ ⊥ ---> ⊥ using BasicReasoning.
  Proof.
    intros wfϕ.
    unshelve (eexists).
    {
      apply ProofSystem.Prop_bott_right. exact wfϕ.
    }
    {
      constructor; simpl.
      {
        set_solver.
      }
      {
        set_solver.
      }
      {
        reflexivity.
      }
      {
        apply reflexivity.
      }
    }
  Defined.

  Arguments Prop_bott_left _ (_%ml) _ : clear implicits.
  Arguments Prop_bott_right _ (_%ml) _ : clear implicits.



Lemma pile_evs_subseteq evs1 evs2 svs kt fp:
  evs1 ⊆ evs2 ->
  ProofInfoLe
    ((ExGen := evs1, SVSubst := svs, KT := kt, FP := fp))
    ((ExGen := evs2, SVSubst := svs, KT := kt, FP := fp)).
Proof.
  intros Hsub.
  constructor.
  intros Γ ϕ pf Hpf.
  destruct Hpf as [Hpf2 Hpf3 Hpf4 Hpf5].
  constructor; simpl in *.
  { clear -Hsub Hpf2. set_solver. }
  { exact Hpf3. }
  { exact Hpf4. }
  { apply Hpf5. }
Qed.

Lemma pile_svs_subseteq evs svs1 svs2 kt fp:
  svs1 ⊆ svs2 ->
  ProofInfoLe
    ( (ExGen := evs, SVSubst := svs1, KT := kt, FP := fp))
    ( (ExGen := evs, SVSubst := svs2, KT := kt, FP := fp)).
Proof.
  intros Hsub.
  constructor.
  intros Γ ϕ pf Hpf.
  destruct Hpf as [Hpf2 Hpf3 Hpf4 Hpf5].
  constructor; simpl in *.
  { exact Hpf2. }
  { clear -Hsub Hpf3. set_solver. }
  { exact Hpf4. }
  { exact Hpf5. }
Qed.

Lemma pile_kt_impl evs svs kt1 kt2 fp:
  kt1 ==> kt2 ->
  ProofInfoLe
    ((ExGen := evs, SVSubst := svs, KT := kt1, FP := fp))
    ((ExGen := evs, SVSubst := svs, KT := kt2, FP := fp)).
Proof.
  intros Hsub.
  constructor.
  intros Γ ϕ pf Hpf.
  destruct Hpf as [Hpf2 Hpf3 Hpf4 Hpf5].
  constructor; simpl in *.
  { exact Hpf2. }
  { exact Hpf3. }
  { unfold implb in *.  destruct (uses_kt pf),kt1; simpl in *; try reflexivity.
    { exact Hsub. }
    { inversion Hpf4. }
  }
  { apply Hpf5. }
Qed.

Lemma pile_fp_subseteq evs svs kt fp1 fp2:
  fp1 ⊆ fp2 ->
  ProofInfoLe
    ((ExGen := evs, SVSubst := svs, KT := kt, FP := fp1))
    ((ExGen := evs, SVSubst := svs, KT := kt, FP := fp2)).
Proof.
  intros Hsub.
  constructor.
  intros Γ ϕ pf Hpf.
  destruct Hpf as [Hpf2 Hpf3 Hpf4 Hfp5].
  constructor; simpl in *.
  { exact Hpf2. }
  { exact Hpf3. }
  { exact Hpf4. }
  { set_solver. }
Qed.

Lemma pile_evs_svs_kt evs1 evs2 svs1 svs2 kt1 kt2 fp1 fp2:
evs1 ⊆ evs2 ->
svs1 ⊆ svs2 ->
kt1 ==> kt2 ->
fp1 ⊆ fp2 ->
ProofInfoLe
  ((ExGen := evs1, SVSubst := svs1, KT := kt1, FP := fp1))
  ((ExGen := evs2, SVSubst := svs2, KT := kt2, FP := fp2)).
Proof.
intros Hevs Hsvs Hkt Hfp.
eapply pile_trans.
{
  apply pile_evs_subseteq. apply Hevs.
}
eapply pile_trans.
{
  apply pile_svs_subseteq. apply Hsvs.
}
eapply pile_trans.
{
  apply pile_kt_impl.
  apply Hkt.
}
apply pile_fp_subseteq. apply Hfp.
Qed.


Lemma pile_any i:
  ProofInfoLe i AnyReasoning.
Proof.
  unfold AnyReasoning.
  destruct i.
  apply pile_evs_svs_kt.
  { clear. set_solver. }
  { clear. set_solver. }
  { unfold implb. destruct pi_uses_kt; reflexivity. }
  { clear. set_solver. }
Qed.


Lemma useAnyReasoning Γ ϕ i:
  Γ ⊢i ϕ using i ->
  Γ ⊢i ϕ using AnyReasoning.
Proof.  
  intros H.
  {
    destruct i.
    eapply useGenericReasoning.
    { apply pile_any. }
    apply H.
  }
Qed.


  Fixpoint frames_of_AC (C : Application_context)
  : coWfpSet :=
  match C with
  | box => ∅
  | (@ctx_app_l _ C' p wfp) => {[(exist _ p wfp)]} ∪ (frames_of_AC C')
  | (@ctx_app_r _ p C' wfp) => {[(exist _ p wfp)]} ∪ (frames_of_AC C')
  end.


  (* TODO rename into Prop_bot_ctx *)
  Lemma Prop_bot (Γ : Theory) (C : Application_context) :
    Γ ⊢i ((subst_ctx C patt_bott) ---> patt_bott)
    using (ExGen := ∅, SVSubst := ∅, KT := false, FP := frames_of_AC C).
  Proof.
    remember (frames_of_AC C) as foC.
    move: foC HeqfoC.
    induction C; intros foC HeqfoC; simpl in *.
    - apply useBasicReasoning.
      apply false_implies_everything.
      wf_auto2.
    - eapply syllogism_meta.
      5: { apply useBasicReasoning. apply (Prop_bott_left Γ p ltac:(wf_auto2)). }
      4: { simpl. subst foC.  eapply useGenericReasoning.
           2: eapply Framing_left with (wfψ := Prf).
           1: apply pile_refl.
           1: {
            eapply pile_evs_svs_kt.
            { apply reflexivity. }
            { apply reflexivity. }
            { reflexivity. }      
            { clear. set_solver. }      
           }
           eapply useGenericReasoning.
           2: apply IHC.
           2: reflexivity.
           apply pile_evs_svs_kt.
           { apply reflexivity. }
           { apply reflexivity. }
           { reflexivity. }      
           { clear. set_solver. }
      }
      all: wf_auto2.
       - eapply syllogism_meta.
           5: { apply useBasicReasoning. apply (Prop_bott_right Γ p ltac:(wf_auto2)). }
           4: { simpl. subst foC.  eapply useGenericReasoning.
                2: eapply Framing_right with (wfψ := Prf).
                1: apply pile_refl.
                1: {
                 eapply pile_evs_svs_kt.
                 { apply reflexivity. }
                 { apply reflexivity. }
                 { reflexivity. }      
                 { clear. set_solver. }      
                }
                eapply useGenericReasoning.
                2: apply IHC.
                2: reflexivity.
                apply pile_evs_svs_kt.
                { apply reflexivity. }
                { apply reflexivity. }
                { reflexivity. }      
                { clear. set_solver. }
           }
           all: wf_auto2.
  Defined.

  Lemma Framing (Γ : Theory) (C : Application_context) (A B : Pattern) (i : ProofInfo)
    {pile : ProofInfoLe
     ((ExGen := ∅, SVSubst := ∅, KT := false, FP := frames_of_AC C))
     i
    }
    :
    Γ ⊢i (A ---> B) using i ->
    Γ ⊢i ((subst_ctx C A) ---> (subst_ctx C B)) using i.
  Proof.
    intros H.
    pose proof H as [pf _].
    pose proof (HWF := @proved_impl_wf _ _ _ pf).
    assert (wfA: well_formed A) by wf_auto2.
    assert (wfB: well_formed B) by wf_auto2.
    clear pf HWF.

    move: wfA wfB H.
    induction C; intros WFA WFB H; simpl in *.
    - exact H.
    - destruct i.
      apply pile_evs_svs_kt_back in pile.
      destruct_and!. simpl in *.
      apply Framing_left with (wfψ := Prf).
      {
        apply pile_evs_svs_kt; try assumption.
        set_solver.
      }
      apply IHC.
      2,3: assumption.
      2: exact H.
      apply pile_evs_svs_kt; try assumption.
      set_solver.
    - destruct i.
      apply pile_evs_svs_kt_back in pile.
      destruct_and!. simpl in *.
      apply Framing_right with (wfψ := Prf).
      {
        apply pile_evs_svs_kt; try assumption.
        set_solver.
      }
      apply IHC.
      2,3: assumption.
      2: exact H.
      apply pile_evs_svs_kt; try assumption.
      set_solver.
  Defined.

  Lemma A_implies_not_not_A_ctx (Γ : Theory) (A : Pattern) (C : Application_context)
    (i : ProofInfo) {pile : ProofInfoLe ((ExGen := ∅, SVSubst := ∅, KT := false, FP := frames_of_AC C)) i}
    :
    well_formed A ->
    Γ ⊢i A using i ->
    Γ ⊢i (! (subst_ctx C ( !A ))) using i.
  Proof.
    intros WFA H.

    epose proof (ANNA := @A_implies_not_not_A_alt Σ  Γ _ i _ H).
    replace (! (! A)) with ((! A) ---> Bot) in ANNA by reflexivity.
    epose proof (EF := @Framing _ C (! A) Bot _ _ ANNA).
    epose proof (PB := Prop_bot Γ C).
    apply liftPi with (i₂ := i) in PB. 2: apply _.
    epose (TRANS := @syllogism_meta _ _ _ _ _ _ _ _ _ EF PB).
    apply TRANS.
    
    Unshelve.
    all: wf_auto2.
  Defined.



  Lemma ctx_bot_prop (Γ : Theory) (C : Application_context) (A : Pattern) 
    (i : ProofInfo)
    {pile : ProofInfoLe ((ExGen := ∅, SVSubst := ∅, KT := false, FP := frames_of_AC C)) i}
  :
    well_formed A ->
    Γ ⊢i (A ---> Bot) using i ->
    Γ ⊢i (subst_ctx C A ---> Bot) using i.
  Proof.
    intros WFA H.
    epose proof (FR := @Framing Γ C A Bot _ _ H).
    epose proof (BPR := @Prop_bot Γ C).
    apply liftPi with (i₂ := i) in BPR. 2: apply _.
    epose proof (TRANS := @syllogism_meta _ _ _ _ _ _ _ _ _ FR BPR).
    exact TRANS.
    Unshelve.
    all: wf_auto2.
  Defined.



End FOL_helpers.

Structure TaggedPattern {Σ : Signature} := TagPattern { untagPattern :> Pattern; }.

Definition reshape_nil {Σ : Signature} p := TagPattern p.
Canonical Structure reshape_cons {Σ : Signature} p := reshape_nil p.

Structure ImpReshapeS {Σ : Signature} (g : Pattern) (l : list Pattern) :=
ImpReshape
  { irs_flattened :> TaggedPattern ;
    irs_pf : (untagPattern irs_flattened) = foldr patt_imp g l ;
  }.

Lemma ImpReshape_nil_pf0:
  ∀ (Σ : Signature) (g : Pattern),
    g = foldr patt_imp g [].
Proof. intros. reflexivity. Qed.

Canonical Structure ImpReshape_nil {Σ : Signature} (g : Pattern) : ImpReshapeS g [] :=
  @ImpReshape Σ g [] (reshape_nil g) (ImpReshape_nil_pf0 g).


Program Canonical Structure ImpReshape_cons
        {Σ : Signature} (g x : Pattern) (xs : list Pattern) (r : ImpReshapeS g xs)
: ImpReshapeS g (x::xs) :=
  @ImpReshape Σ g (x::xs) (reshape_cons (x ---> untagPattern (reshape_cons r))) _.
Next Obligation.
  intros Σ g x xs r. simpl.
  rewrite irs_pf.
  reflexivity.
Qed.


Lemma reshape {Σ : Signature} (Γ : Theory) (g : Pattern) (xs: list Pattern) (i : ProofInfo) :
  forall (r : ImpReshapeS g (xs)),
     Γ ⊢i foldr (patt_imp) g (xs) using i ->
     Γ ⊢i (untagPattern (irs_flattened r)) using i.
Proof.
  intros r [pf Hpf].
  unshelve (eexists).
  {
    eapply cast_proof.
    { rewrite irs_pf; reflexivity. }
    exact pf.
  }
  {
    simpl.
    destruct Hpf as [Hpf2 Hpf3 Hpf4].
    constructor.
    {
      rewrite elem_of_subseteq in Hpf2.
      rewrite elem_of_subseteq.
      intros x Hx.
      specialize (Hpf2 x).
      apply Hpf2. clear Hpf2.
      rewrite elem_of_gset_to_coGset in Hx.
      rewrite uses_of_ex_gen_correct in Hx.
      rewrite elem_of_gset_to_coGset.
      rewrite uses_of_ex_gen_correct.
      rewrite indifferent_to_cast_uses_ex_gen in Hx.
      exact Hx.
    }
    {
      rewrite elem_of_subseteq in Hpf3.
      rewrite elem_of_subseteq.
      intros x Hx.
      specialize (Hpf3 x).
      apply Hpf3. clear Hpf3.
      rewrite elem_of_gset_to_coGset in Hx.
      rewrite uses_of_svar_subst_correct in Hx.
      rewrite elem_of_gset_to_coGset.
      rewrite uses_of_svar_subst_correct.
      rewrite indifferent_to_cast_uses_svar_subst in Hx.
      exact Hx.
    }
    {
      rewrite indifferent_to_cast_uses_kt.
      apply Hpf4.
    }
    {
      rewrite framing_patterns_cast_proof.
      destruct i;assumption.
    }
  }
Defined.


Local Example ex_reshape {Σ : Signature} Γ a b c d:
  well_formed a ->
  well_formed b ->
  well_formed c ->
  well_formed d ->
  Γ ⊢i a ---> (b ---> (c ---> d)) using BasicReasoning.
Proof.
  intros wfa wfb wfc wfd.
  apply reshape.
  (* Now the goal has the right shape *)
Abort.


Section FOL_helpers.

  Context {Σ : Signature}.

  Lemma MLGoal_weakenConclusion' Γ l g g' (i : ProofInfo):
    Γ ⊢i g ---> g' using i ->
    @mkMLGoal Σ Γ l g i ->
    @mkMLGoal Σ Γ l g' i.
  Proof.
    intros Hgg' Hlg.
    (*mlExtractWF wfl wfgp.*)
    unfold of_MLGoal in *. simpl in *.
    intros wfg' wfl.
    pose proof (wfimp := proved_impl_wf _ _ (proj1_sig Hgg')).
    apply well_formed_imp_proj1 in wfimp.
    eapply prf_weaken_conclusion_iter_meta_meta.
    5: apply Hlg.
    4: apply Hgg'.
    all: assumption.
  Defined.

  Lemma prf_contraction Γ a b:
    well_formed a ->
    well_formed b ->
    Γ ⊢i ((a ---> a ---> b) ---> (a ---> b)) using BasicReasoning.
  Proof.
    intros wfa wfb.
    assert (H1 : Γ ⊢i (a ---> ((a ---> b) ---> b)) using BasicReasoning).
    {
      apply modus_ponens; assumption.
    }
    assert (H2 : Γ ⊢i ((a ---> ((a ---> b) ---> b)) ---> ((a ---> (a ---> b)) ---> (a ---> b))) using BasicReasoning).
    {
      apply P2; wf_auto2.
    }
    eapply MP. 2: apply H2. apply H1.
  Defined.

  Lemma prf_weaken_conclusion_under_implication Γ a b c:
    well_formed a ->
    well_formed b ->
    well_formed c ->
    Γ ⊢i ((a ---> b) ---> ((a ---> (b ---> c)) ---> (a ---> c))) using BasicReasoning.
  Proof.
    intros wfa wfb wfc.
    assert (H1 : Γ ⊢i ((a ---> (b ---> c)) ---> (b ---> (a ---> c))) using BasicReasoning).
    {
      apply reorder; wf_auto2.
    }
    assert (H2 : Γ ⊢i (((b ---> (a ---> c)) ---> (a ---> c)) ---> ((a ---> (b ---> c)) ---> (a ---> c))) using BasicReasoning).
    {
      apply prf_strenghten_premise_meta;[wf_auto2|wf_auto2|wf_auto2|].
      apply H1.
    }
    eapply prf_weaken_conclusion_meta_meta.
    4: apply H2. 1-3: wf_auto2. clear H1 H2.

    assert (H3 : Γ ⊢i ((a ---> b) ---> ((b ---> (a ---> c)) ---> (a ---> (a ---> c)))) using BasicReasoning).
    {
      apply syllogism; wf_auto2.
    }
    assert (H4 : Γ ⊢i ((a ---> (a ---> c)) ---> (a ---> c)) using BasicReasoning).
    {
      apply prf_contraction; wf_auto2.
    }
    assert (Hiter: ((a ---> b) ---> (b ---> a ---> c) ---> a ---> c)
                   = foldr patt_imp (a ---> c) [(a ---> b); (b ---> a ---> c)]) by reflexivity.
    
    eapply (@cast_proof' _ _ _ _ _ Hiter).
    
    eapply prf_weaken_conclusion_iter_meta_meta.
    5: apply H3. 4: apply H4. all: wf_auto2.
  Defined.

  Lemma prf_weaken_conclusion_under_implication_meta Γ a b c (i : ProofInfo):
    well_formed a ->
    well_formed b ->
    well_formed c ->
    Γ ⊢i (a ---> b) using i ->
    Γ ⊢i ((a ---> (b ---> c)) ---> (a ---> c)) using i.
  Proof.
    intros wfa wfb wfc H.
    eapply MP.
    2: { useBasicReasoning. apply prf_weaken_conclusion_under_implication; wf_auto2. }
    exact H.
  Defined.

  Lemma prf_weaken_conclusion_under_implication_meta_meta Γ a b c i:
    well_formed a ->
    well_formed b ->
    well_formed c ->
    Γ ⊢i a ---> b using i ->
    Γ ⊢i a ---> b ---> c using i ->
    Γ ⊢i a ---> c using i.
  Proof.
    intros wfa wfb wfc H1 H2.
    eapply MP.
    { apply H2. }
    { apply prf_weaken_conclusion_under_implication_meta.
      4: { apply H1. }
      all: wf_auto2.
    }
  Defined.

  Lemma prf_weaken_conclusion_iter_under_implication Γ l g g':
    Pattern.wf l ->
    well_formed g ->
    well_formed g' ->
    Γ ⊢i (((g ---> g') ---> (foldr patt_imp g l)) ---> ((g ---> g') ---> (foldr patt_imp g' l)))
    using BasicReasoning.
  Proof.
    intros wfl wfg wfg'.
    pose proof (H1 := @prf_weaken_conclusion_iter Σ Γ l g g' wfl wfg wfg').
    remember ((g ---> g')) as a.
    remember (foldr patt_imp g l) as b.
    remember (foldr patt_imp g' l) as c.
    assert (well_formed a) by (subst; wf_auto2).
    assert (well_formed b) by (subst; wf_auto2).
    assert (well_formed c) by (subst; wf_auto2).
    pose proof (H2' := @prf_weaken_conclusion_under_implication Γ a b c ltac:(assumption) ltac:(assumption) ltac:(assumption)).
    apply reorder_meta in H2'. 2,3,4: subst;wf_auto2.
    eapply MP. 2: apply H2'. apply H1.
  Defined.

  Lemma prf_weaken_conclusion_iter_under_implication_meta Γ l g g' (i : ProofInfo):
    Pattern.wf l ->
    well_formed g ->
    well_formed g' ->
    Γ ⊢i ((g ---> g') ---> (foldr patt_imp g l)) using i->
    Γ ⊢i ((g ---> g') ---> (foldr patt_imp g' l)) using i.
  Proof.
    intros wfl wfg wfg' H.
    eapply MP.
    2: { useBasicReasoning. apply prf_weaken_conclusion_iter_under_implication; wf_auto2. }
    { exact H. }
  Defined.
  
  Lemma MLGoal_weakenConclusion_under_first_implication Γ l g g' i:
    @mkMLGoal Σ Γ ((g ---> g') :: l) g i ->
    @mkMLGoal Σ Γ ((g ---> g') :: l) g' i .
  Proof.
    intros H. unfold of_MLGoal in *. simpl in *.
    intros wfg' wfgg'l.
    pose proof (Htmp := wfgg'l).
    unfold Pattern.wf in Htmp. simpl in Htmp. apply andb_prop in Htmp. destruct Htmp as [wfgg' wfl].
    apply well_formed_imp_proj1 in wfgg'. specialize (H wfgg' wfgg'l).
    apply prf_weaken_conclusion_iter_under_implication_meta; assumption.
  Defined.

  Lemma prf_weaken_conclusion_iter_under_implication_iter Γ l₁ l₂ g g':
    Pattern.wf l₁ ->
    Pattern.wf l₂ ->
    well_formed g ->
    well_formed g' ->
    Γ ⊢i ((foldr patt_imp g (l₁ ++ (g ---> g') :: l₂)) --->
         (foldr patt_imp g' (l₁ ++ (g ---> g') :: l₂)))
    using BasicReasoning.
  Proof.
    intros wfl₁ wfl₂ wfg wfg'.
    induction l₁; simpl.
    - apply prf_weaken_conclusion_iter_under_implication; auto.
    - pose proof (wfal₁ := wfl₁). unfold Pattern.wf in wfl₁. simpl in wfl₁. apply andb_prop in wfl₁.
      destruct wfl₁ as [wfa wfl₁]. specialize (IHl₁ wfl₁).
      eapply prf_weaken_conclusion_meta. 4: assumption. all: wf_auto2.
  Defined.

  Lemma prf_weaken_conclusion_iter_under_implication_iter_meta Γ l₁ l₂ g g' i:
    Pattern.wf l₁ ->
    Pattern.wf l₂ ->
    well_formed g ->
    well_formed g' ->
    Γ ⊢i (foldr patt_imp g (l₁ ++ (g ---> g') :: l₂)) using i ->
    Γ ⊢i (foldr patt_imp g' (l₁ ++ (g ---> g') :: l₂)) using i.
  Proof.
    intros wfl₁ wfl₂ wfg wfg' H.
    eapply MP.
    { apply H. }
    { useBasicReasoning. apply prf_weaken_conclusion_iter_under_implication_iter; wf_auto2. }
  Defined.

  Lemma MLGoal_weakenConclusion Γ l₁ l₂ g g' i:
    @mkMLGoal Σ Γ (l₁ ++ (g ---> g') :: l₂) g i ->
    @mkMLGoal Σ Γ (l₁ ++ (g ---> g') :: l₂) g' i.
  Proof.
    unfold of_MLGoal in *. simpl in *.
    intros H wfg' wfl₁gg'l₂.
    
    apply prf_weaken_conclusion_iter_under_implication_iter_meta.
    { abstract (pose proof (wfl₁ := wf_take (length l₁) wfl₁gg'l₂); rewrite take_app in wfl₁; exact wfl₁). }
    { abstract (
        pose proof (wfgg'l₂ := wf_drop (length l₁) wfl₁gg'l₂);
        rewrite drop_app in wfgg'l₂;
        pose proof (Htmp := wfgg'l₂);
        unfold Pattern.wf in Htmp;
        simpl in Htmp;
        apply andb_prop in Htmp;
        destruct Htmp as [wfgg' wfl₂];
        exact wfl₂
      ).
    }
    {
      abstract(
        pose proof (wfgg'l₂ := wf_drop (length l₁) wfl₁gg'l₂);
        rewrite drop_app in wfgg'l₂;
        pose proof (Htmp := wfgg'l₂);
        unfold Pattern.wf in Htmp;
        simpl in Htmp;
        apply andb_prop in Htmp;
        destruct Htmp as [wfgg' wfl₂];
        pose proof (wfg := well_formed_imp_proj1 wfgg');
        exact wfg
      ).
    }
    { exact wfg'. }
    apply H.
    {
      abstract(
        pose proof (wfgg'l₂ := wf_drop (length l₁) wfl₁gg'l₂);
        rewrite drop_app in wfgg'l₂;
        pose proof (Htmp := wfgg'l₂);
        unfold Pattern.wf in Htmp;
        simpl in Htmp;
        apply andb_prop in Htmp;
        destruct Htmp as [wfgg' wfl₂];
        pose proof (wfg := well_formed_imp_proj1 wfgg');
        exact wfg
      ).
    }
    exact wfl₁gg'l₂.
  Defined.

End FOL_helpers.

Tactic Notation "mlApply" constr(n) :=
  unshelve (eapply (@cast_proof_ml_hyps _ _ _ _ _ _ _));
  [shelve|(rewrite <- (firstn_skipn n); rewrite /firstn; rewrite /skipn; reflexivity)|idtac];
  apply MLGoal_weakenConclusion;
  let hyps := fresh "hyps" in rewrite [hyps in @mkMLGoal _ _ hyps _]/app.

Local Example ex_mlApply {Σ : Signature} Γ a b:
  well_formed a ->
  well_formed b ->
  Γ ⊢i a ---> (a ---> b) ---> b using BasicReasoning.
Proof.
  intros wfa wfb.
  toMLGoal.
  { wf_auto2. }
  mlIntro. mlIntro.
  mlApply 1.
  fromMLGoal. apply P1; wf_auto2.
Defined.

Section FOL_helpers.

  Context {Σ : Signature}.
  
  Lemma Constructive_dilemma Γ p q r s:
    well_formed p ->
    well_formed q ->
    well_formed r ->
    well_formed s ->
    Γ ⊢i ((p ---> q) ---> (r ---> s) ---> (p or r) ---> (q or s)) using BasicReasoning.
  Proof.
    intros wfp wfq wfr wfs.
    unfold patt_or.

    toMLGoal.
    { wf_auto2. }

    mlIntro. mlIntro. mlIntro. mlIntro.
    mlApply 1.
    mlApply 2.
    mlIntro.
    mlApply 3.
    mlApply 0.
    mlExactn 4.
  Defined.

  Lemma prf_add_assumption Γ a b i :
    well_formed a ->
    well_formed b ->
    Γ ⊢i b using i ->
    Γ ⊢i (a ---> b) using i.
  Proof.
    intros wfa wfb H.
    eapply MP.
    { apply H. }
    { useBasicReasoning. apply P1; wf_auto2. }
  Defined.

  Lemma prf_impl_distr_meta Γ a b c i:
    well_formed a ->
    well_formed b ->
    well_formed c ->
    Γ ⊢i (a ---> (b ---> c)) using i ->
    Γ ⊢i ((a ---> b) ---> (a ---> c)) using i.
  Proof.
    intros wfa wfb wfc H.
    eapply MP.
    { apply H. }
    { useBasicReasoning. apply P2; wf_auto2. }
  Defined.

  Lemma prf_add_lemma_under_implication Γ l g h:
    Pattern.wf l ->
    well_formed g ->
    well_formed h ->
    Γ ⊢i ((foldr patt_imp h l) --->
         ((foldr patt_imp g (l ++ [h])) --->
          (foldr patt_imp g l)))
    using BasicReasoning.
  Proof.
    intros wfl wfg wfh.
    induction l; simpl.
    - apply modus_ponens; auto.
    - pose proof (wfal := wfl).
      unfold Pattern.wf in wfl. apply andb_prop in wfl. destruct wfl as [wfa wfl].
      specialize (IHl wfl).
      assert (H1: Γ ⊢i a --->
                      foldr patt_imp h l --->
                      foldr patt_imp g (l ++ [h]) --->
                      foldr patt_imp g l
              using BasicReasoning).
      { apply prf_add_assumption; wf_auto2. }

      assert (H2 : Γ ⊢i (a ---> foldr patt_imp h l) --->
                       (a ---> foldr patt_imp g (l ++ [h]) --->
                       foldr patt_imp g l)
              using BasicReasoning).
      { apply prf_impl_distr_meta;[wf_auto2|wf_auto2|wf_auto2|]. apply H1. }

      assert (H3 : Γ ⊢i ((a ---> foldr patt_imp g (l ++ [h]) ---> foldr patt_imp g l)
                          ---> ((a ---> foldr patt_imp g (l ++ [h])) ---> (a ---> foldr patt_imp g l)))
              using BasicReasoning).
      { apply P2; wf_auto2. }

      eapply prf_weaken_conclusion_meta_meta.
      4: apply H3. 4: apply H2. all: wf_auto2.
  Defined.

  Lemma prf_add_lemma_under_implication_meta Γ l g h i:
    Pattern.wf l ->
    well_formed g ->
    well_formed h ->
    Γ ⊢i (foldr patt_imp h l) using i ->
    Γ ⊢i ((foldr patt_imp g (l ++ [h])) ---> (foldr patt_imp g l)) using i.
  Proof.
    intros WFl WFg WGh H.
    eapply MP.
    { apply H. }
    { useBasicReasoning. apply prf_add_lemma_under_implication. all: wf_auto2. }
  Defined.

  Lemma prf_add_lemma_under_implication_meta_meta Γ l g h i:
    Pattern.wf l ->
    well_formed g ->
    well_formed h ->
    Γ ⊢i (foldr patt_imp h l) using i ->
    Γ ⊢i (foldr patt_imp g (l ++ [h])) using i ->
    Γ ⊢i (foldr patt_imp g l) using i.
  Proof.
    intros WFl WFg WGh H H0.
    eapply MP.
    { apply H0. }
    { apply prf_add_lemma_under_implication_meta. 4: apply H. all: wf_auto2. }
  Defined.

  Lemma myGoal_assert Γ l g h i:
    well_formed h ->
    @mkMLGoal Σ Γ l h i ->
    @mkMLGoal Σ Γ (l ++ [h]) g i ->
    @mkMLGoal Σ Γ l g i.
  Proof.
    intros wfh H1 H2.
    unfold of_MLGoal in *. simpl in *.
    intros wfg wfl.
    eapply prf_add_lemma_under_implication_meta_meta.
    4: apply H1. 6: apply H2. all: try assumption.
    { abstract (
        unfold Pattern.wf;
        rewrite map_app;
        rewrite foldr_app;
        simpl;
        rewrite wfh;
        simpl;
        exact wfl
      ).
    }
  Defined.

  Lemma prf_add_lemma_under_implication_generalized Γ l1 l2 g h:
    Pattern.wf l1 ->
    Pattern.wf l2 ->
    well_formed g ->
    well_formed h ->
    Γ ⊢i ((foldr patt_imp h l1) ---> ((foldr patt_imp g (l1 ++ [h] ++ l2)) ---> (foldr patt_imp g (l1 ++ l2))))
    using BasicReasoning.
  Proof.
    intros wfl1 wfl2 wfg wfh.
    induction l1; simpl.
    - apply modus_ponens; wf_auto2.
    - pose proof (wfal1 := wfl1).
      unfold Pattern.wf in wfl1. simpl in wfl1. apply andb_prop in wfl1. destruct wfl1 as [wfa wfl1].
      specialize (IHl1 wfl1).
      assert (H1: Γ ⊢i a ---> foldr patt_imp h l1 ---> foldr patt_imp g (l1 ++ [h] ++ l2) ---> foldr patt_imp g (l1 ++ l2) using BasicReasoning).
      { apply prf_add_assumption; wf_auto2. }
      assert (H2 : Γ ⊢i (a ---> foldr patt_imp h l1) ---> (a ---> foldr patt_imp g (l1 ++ [h] ++ l2) ---> foldr patt_imp g (l1 ++ l2)) using BasicReasoning).
      { apply prf_impl_distr_meta;[wf_auto2|wf_auto2|wf_auto2|]. exact H1. }
      assert (H3 : Γ ⊢i ((a ---> foldr patt_imp g (l1 ++ [h] ++ l2) ---> foldr patt_imp g (l1 ++ l2))
                          ---> ((a ---> foldr patt_imp g (l1 ++ [h] ++ l2)) ---> (a ---> foldr patt_imp g (l1 ++ l2)))) using BasicReasoning).
      { apply P2; wf_auto2. }

      eapply prf_weaken_conclusion_meta_meta.
      4: apply H3. 4: assumption. all: wf_auto2.
  Defined.
  
  Lemma prf_add_lemma_under_implication_generalized_meta Γ l1 l2 g h i:
    Pattern.wf l1 ->
    Pattern.wf l2 ->
    well_formed g ->
    well_formed h ->
    Γ ⊢i (foldr patt_imp h l1) using i ->
    Γ ⊢i ((foldr patt_imp g (l1 ++ [h] ++ l2)) ---> (foldr patt_imp g (l1 ++ l2))) using i.
  Proof.
    intros WFl1 WFl2 WFg WGh H.
    eapply MP.
    { apply H. }
    { useBasicReasoning.
      apply prf_add_lemma_under_implication_generalized; wf_auto2.
    }
  Defined.
  
  Lemma prf_add_lemma_under_implication_generalized_meta_meta Γ l1 l2 g h i:
    Pattern.wf l1 ->
    Pattern.wf l2 ->
    well_formed g ->
    well_formed h ->
    Γ ⊢i (foldr patt_imp h l1) using i ->
    Γ ⊢i (foldr patt_imp g (l1 ++ [h] ++ l2)) using i ->
    Γ ⊢i (foldr patt_imp g (l1 ++ l2)) using i.
  Proof.
    intros WFl1 WFl2 WFg WGh H H0.
    eapply MP.
    { apply H0. }
    { apply prf_add_lemma_under_implication_generalized_meta.
      5: apply H. all: wf_auto2.
    }
  Defined.

  Lemma myGoal_assert_generalized Γ l1 l2 g h i:
    well_formed h ->
    @mkMLGoal Σ Γ l1 h i ->
    @mkMLGoal Σ Γ (l1 ++ [h] ++ l2) g i ->
    @mkMLGoal Σ Γ (l1 ++ l2) g i.
  Proof.
    intros wfh H1 H2.
    unfold of_MLGoal in *. simpl in *.
    intros wfg wfl1l2.
    eapply prf_add_lemma_under_implication_generalized_meta_meta.
    5: apply H1. 7: apply H2. all: try assumption.
    { abstract (
          apply (wf_take (length l1)) in wfl1l2;
          rewrite take_app in wfl1l2;
          exact wfl1l2
      ).
    }
    { abstract (
          apply (wf_drop (length l1)) in wfl1l2;
          rewrite drop_app in wfl1l2;
          exact wfl1l2
      ).
    }
    { abstract (
          apply (wf_take (length l1)) in wfl1l2;
          rewrite take_app in wfl1l2;
          exact wfl1l2
      ).
    }
    {
      abstract(
        pose proof (wfl1 := wf_take (length l1) wfl1l2);
        rewrite take_app in wfl1;
        pose proof (wfl2 := wf_drop (length l1) wfl1l2);
        rewrite drop_app in wfl2;
        unfold Pattern.wf; rewrite map_app; rewrite foldr_app;
        simpl; rewrite wfh; unfold Pattern.wf in wfl2; rewrite wfl2;
        simpl; exact wfl1
      ).
    }
  Defined.

End FOL_helpers.

Tactic Notation "mlAssert" "(" constr(t) ")" :=
  match goal with
  | |- @of_MLGoal ?Sgm (@mkMLGoal ?Sgm ?Ctx ?l ?g ?i) =>
    let Hwf := fresh "Hwf" in
    assert (Hwf : well_formed t);
    [idtac|
      let H := fresh "H" in
      assert (H : @mkMLGoal Sgm Ctx l t i);
      [ | (eapply (@myGoal_assert Sgm Ctx l g t i Hwf H); rewrite [_ ++ _]/=; clear H)]
    ]
  end.

Local Example ex_mlAssert {Σ : Signature} Γ a:
  well_formed a ->
  Γ ⊢i (a ---> a ---> a) using BasicReasoning.
Proof.
  intros wfa.
  toMLGoal.
  { wf_auto2. }
  mlIntro. mlIntro.
  mlAssert (a).
  { wf_auto2. }
  { mlExactn 1. }
  { mlExactn 2. }
Qed.

Tactic Notation "mlAssert" "(" constr(t) ")" "using" "first" constr(n) :=
  lazymatch goal with
  | |- @of_MLGoal ?Sgm (@mkMLGoal ?Sgm ?Ctx ?l ?g ?i) =>
    let l1 := fresh "l1" in
    let l2 := fresh "l2" in
    let Heql1 := fresh "Heql1" in
    let Heql2 := fresh "Heql2" in
    remember (take n l) as l1 eqn:Heql1 in |-;
    remember (drop n l) as l2 eqn:Heql2 in |-;
    simpl in Heql1; simpl in Heql2;
    eapply cast_proof_ml_hyps;
    [(
      rewrite -[l](take_drop n);
      reflexivity
     )|];
    let Hwf := fresh "Hwf" in
    assert (Hwf : well_formed t);
    [idtac|
      let H := fresh "H" in
      assert (H : @mkMLGoal Sgm Ctx l1 t i) ;
      [
        (eapply cast_proof_ml_hyps; [(rewrite Heql1; reflexivity)|]);  clear l1 l2 Heql1 Heql2
      | apply (cast_proof_ml_hyps Heql1) in H;
        eapply (@myGoal_assert_generalized Sgm Ctx (take n l) (drop n l) g t i Hwf H);
        rewrite [_ ++ _]/=; clear l1 l2 Heql1 Heql2 H] 
    ]
  end.

Local Example ex_assert_using {Σ : Signature} Γ p q a b:
  well_formed a = true ->
  well_formed b = true ->
  well_formed p = true ->
  well_formed q = true ->
  Γ ⊢i a ---> p and q ---> b ---> ! ! q using BasicReasoning.
Proof.
  intros wfa wfb wfp wfq.
  toMLGoal.
  { wf_auto2. }
  do 3 mlIntro.
  mlAssert (p) using first 2.
  { wf_auto2. }
  { admit. }
  { admit. }
Abort.


Section FOL_helpers.

  Context {Σ : Signature}.
  
  Lemma P4i' (Γ : Theory) (A : Pattern) :
    well_formed A →
    Γ ⊢i ((!A ---> A) ---> A) using BasicReasoning.
  Proof.
    intros wfA.
    assert (H1: Γ ⊢i ((! A ---> ! ! A) ---> ! ! A) using BasicReasoning).
    { apply P4i. wf_auto2. }
    assert (H2: Γ ⊢i ((! A ---> A) ---> (! A ---> ! ! A)) using BasicReasoning).
    { eapply prf_weaken_conclusion_meta. 
      4: apply not_not_intro.
      all: wf_auto2.
    }
    
    eapply prf_strenghten_premise_meta_meta. 4: apply H2.
    4: eapply prf_weaken_conclusion_meta_meta. 7: apply not_not_elim.
    8: { apply H1. }
    all: wf_auto2.
  Defined.

  Lemma tofold p:
    p = fold_right patt_imp p [].
  Proof.
    reflexivity.
  Defined.

  Lemma consume p q l:
    fold_right patt_imp (p ---> q) l = fold_right patt_imp q (l ++ [p]).
  Proof.
    rewrite foldr_app. reflexivity.
  Defined.
  
  Lemma prf_disj_elim Γ p q r:
    well_formed p ->
    well_formed q ->
    well_formed r ->
    Γ ⊢i ((p ---> r) ---> (q ---> r) ---> (p or q) ---> r)
    using BasicReasoning.
  Proof.
    intros wfp wfq wfr.
    pose proof (H1 := @Constructive_dilemma Σ Γ p r q r wfp wfr wfq wfr).
    assert (Γ ⊢i ((r or r) ---> r) using BasicReasoning).
    { unfold patt_or. apply P4i'. wf_auto2. }
    eapply cast_proof' in H1.
    2: { rewrite -> tofold. do 3 rewrite -> consume. reflexivity. }
    eapply prf_weaken_conclusion_iter_meta_meta in H1. 5: apply H.
    { apply H1. }
    all: wf_auto2.
  Defined.

  Lemma prf_disj_elim_meta Γ p q r i:
    well_formed p ->
    well_formed q ->
    well_formed r ->
    Γ ⊢i (p ---> r) using i ->
    Γ ⊢i ((q ---> r) ---> (p or q) ---> r) using i.
  Proof.
    intros WFp WHq WFr H.
    eapply MP. apply H. useBasicReasoning. apply prf_disj_elim.
    all: wf_auto2.
  Defined.
  
  Lemma prf_disj_elim_meta_meta Γ p q r i:
    well_formed p ->
    well_formed q ->
    well_formed r ->
    Γ ⊢i (p ---> r) using i ->
    Γ ⊢i (q ---> r) using i ->
    Γ ⊢i ((p or q) ---> r) using i.
  Proof.
    intros WFp WHq WFr H H0.
    eapply MP. apply H0. apply prf_disj_elim_meta. 4: apply H.
    all: wf_auto2.
  Defined.

  Lemma prf_disj_elim_meta_meta_meta Γ p q r i:
    well_formed p ->
    well_formed q ->
    well_formed r ->
    Γ ⊢i (p ---> r) using i ->
    Γ ⊢i (q ---> r) using i ->
    Γ ⊢i (p or q) using i ->
    Γ ⊢i r using i.
  Proof.
    intros WFp WHq WFr H H0 H1.
    eapply MP. apply H1.
    apply prf_disj_elim_meta_meta.
    all: assumption.
  Defined.
  
  Lemma prf_add_proved_to_assumptions Γ l a g i:
    Pattern.wf l ->
    well_formed a ->
    well_formed g ->
    Γ ⊢i a using i->
    Γ ⊢i ((foldr patt_imp g (a::l)) ---> (foldr patt_imp g l)) using i.
  Proof.
    intros wfl wfa wfg Ha.
    induction l.
    - simpl.
      pose proof (@modus_ponens Σ Γ _ _ wfa wfg).
      eapply MP. apply Ha. useBasicReasoning. apply H.
    - pose proof (wfa0l := wfl).
      unfold Pattern.wf in wfl. simpl in wfl. apply andb_prop in wfl. destruct wfl as [wfa0 wfl].
      specialize (IHl wfl).
      simpl in IHl. simpl.
      (* < change a0 and a in the LHS > *)
      assert (H : Γ ⊢i (a ---> a0 ---> foldr patt_imp g l) ---> (a0 ---> a ---> foldr patt_imp g l) using BasicReasoning).
      { apply reorder; wf_auto2. }

      eapply cast_proof'.
      { rewrite -> tofold. rewrite -> consume. reflexivity. }
      pose proof (H0 := @prf_strenghten_premise_iter_meta_meta Σ Γ [] []).
      simpl in H0. simpl.
      specialize (H0 (a0 ---> a ---> foldr patt_imp g l) (a ---> a0 ---> foldr patt_imp g l)).
      specialize (H0 (a0 ---> foldr patt_imp g l)). simpl in H0. simpl.
      simpl. apply H0. all: try_wfauto2.
      { useBasicReasoning. apply H. }
      clear H0 H.
      (* </change a0 and a > *)
      assert (Γ ⊢i ((a ---> a0 ---> foldr patt_imp g l) ---> (a0 ---> foldr patt_imp g l)) using i).
      { eapply MP. 2: { useBasicReasoning. apply modus_ponens; wf_auto2. } apply Ha. }
      
      eapply prf_strenghten_premise_meta_meta. 5: apply H. all: try_wfauto2.
      useBasicReasoning.
      apply reorder; wf_auto2.
  Defined.

  Lemma prf_add_proved_to_assumptions_meta Γ l a g i:
    Pattern.wf l ->
    well_formed a ->
    well_formed g ->
    Γ ⊢i a using i ->
    Γ ⊢i (foldr patt_imp g (a::l)) using i ->
    Γ ⊢i (foldr patt_imp g l) using i.
  Proof.
    intros WFl WFa WFg H H0.
    eapply MP.
    apply H0.
    eapply prf_add_proved_to_assumptions.
    4: apply H.
    all: wf_auto2.
  Defined.
  
  Lemma MLGoal_add Γ l g h i:
    Γ ⊢i h using i ->
    @mkMLGoal Σ Γ (h::l) g i ->
    @mkMLGoal Σ Γ l g i.
  Proof.
    intros H H0.
    unfold of_MLGoal in *. simpl in *.
    intros wfg wfl.
    apply prf_add_proved_to_assumptions_meta with (a := h).
    5: apply H0.
    all: try assumption.
    { abstract (pose (tmp := proj1_sig H); apply proved_impl_wf in tmp; exact tmp). }
    { abstract (
          unfold Pattern.wf;
          simpl;
          pose (tmp := proj1_sig H);
          apply proved_impl_wf in tmp;
          rewrite tmp;
          simpl;
          exact wfl
      ).
    }
  Defined.

End FOL_helpers.

Tactic Notation "mlAdd" constr(n) :=
  match goal with
  | |- @of_MLGoal ?Sgm (@mkMLGoal ?Sgm ?Ctx ?l ?g ?i) =>
    apply (@MLGoal_add Sgm Ctx l g _ i n)
  end.

Section FOL_helpers.
  
  Context {Σ : Signature}.
  
  Local Example ex_mlAdd Γ l g h i:
    Pattern.wf l ->
    well_formed g ->
    well_formed h ->
    Γ ⊢i (h ---> g) using i ->
    Γ ⊢i h using i ->
    Γ ⊢i g using i.
  Proof.
    intros WFl WFg WFh H H0. toMLGoal.
    { wf_auto2. }
    mlAdd H0.
    mlAdd H.
    mlApply 0.    
    mlExactn 1.
  Defined.


  Lemma prf_clear_hyp Γ l1 l2 g h:
    Pattern.wf l1 ->
    Pattern.wf l2 ->
    well_formed g ->
    well_formed h ->
    Γ ⊢i (foldr patt_imp g (l1 ++ l2)) ---> (foldr patt_imp g (l1 ++ [h] ++ l2))
    using BasicReasoning.
  Proof.
    intros wfl1 wfl2 wfg wfh.
    induction l1; simpl.
    - apply P1; wf_auto2.
    - unfold Pattern.wf in wfl1. simpl in wfl1. apply andb_prop in wfl1. destruct wfl1 as [wfa wfl1].
      specialize (IHl1 wfl1).

      assert (H1: Γ ⊢i a ---> foldr patt_imp g (l1 ++ l2) ---> foldr patt_imp g (l1 ++ [h] ++ l2) using BasicReasoning).
      {
        toMLGoal.
        { wf_auto2. }
        mlAdd IHl1.
        mlIntro. mlExactn 0.
      }
      apply prf_impl_distr_meta; try_wfauto2. apply H1.
  Defined.

  Lemma prf_clear_hyp_meta Γ l1 l2 g h i:
    Pattern.wf l1 ->
    Pattern.wf l2 ->
    well_formed g ->
    well_formed h ->
    Γ ⊢i (foldr patt_imp g (l1 ++ l2)) using i ->
    Γ ⊢i (foldr patt_imp g (l1 ++ [h] ++ l2)) using i.
  Proof.
    intros. eapply MP.
    apply H3.
    useBasicReasoning.
    apply prf_clear_hyp; wf_auto2.
  Defined.  

  (* TODO move somewhere else *)
  Lemma wfapp_proj_1 l₁ l₂:
    Pattern.wf (l₁ ++ l₂) = true ->
    Pattern.wf l₁ = true.
  Proof.
    intros H.
    apply (wf_take (length l₁)) in H.
    rewrite take_app in H.
    exact H.
  Qed.

  Lemma wfapp_proj_2 l₁ l₂:
    Pattern.wf (l₁ ++ l₂) = true ->
    Pattern.wf l₂ = true.
  Proof.
    intros H.
    apply (wf_drop (length l₁)) in H.
    rewrite drop_app in H.
    exact H.
  Qed.

  Lemma wfl₁hl₂_proj_l₁ l₁ h l₂:
    Pattern.wf (l₁ ++ h :: l₂) ->
    Pattern.wf l₁.
  Proof.
    apply wfapp_proj_1.
  Qed.

  Lemma wfl₁hl₂_proj_h l₁ h l₂:
    Pattern.wf (l₁ ++ h :: l₂) ->
    well_formed h.
  Proof.
    intros H. apply wfapp_proj_2 in H. unfold Pattern.wf in H.
    simpl in H. apply andb_prop in H as [H1 H2].
    exact H1.
  Qed.

  Lemma wfl₁hl₂_proj_l₂ l₁ h l₂:
    Pattern.wf (l₁ ++ h :: l₂) ->
    Pattern.wf l₂.
  Proof.
    intros H. apply wfapp_proj_2 in H. unfold Pattern.wf in H.
    simpl in H. apply andb_prop in H as [H1 H2].
    exact H2.
  Qed.

  Lemma wfl₁hl₂_proj_l₁l₂ l₁ h l₂:
    Pattern.wf (l₁ ++ h :: l₂) ->
    Pattern.wf (l₁ ++ l₂).
  Proof.
    intros H.
    pose proof (wfl₁hl₂_proj_l₁ H).
    pose proof (wfl₁hl₂_proj_l₂ H).
    apply wf_app; assumption.
  Qed.

  Lemma myGoal_clear_hyp Γ l1 l2 g h i:
    @mkMLGoal Σ Γ (l1 ++ l2) g i ->
    @mkMLGoal Σ Γ (l1 ++ h::l2) g i.
  Proof.
    intros H1.
    unfold of_MLGoal in *. simpl in *. intros wfg wfl1hl2.
    apply prf_clear_hyp_meta.
    5: apply H1. all: try assumption.
    { apply wfl₁hl₂_proj_l₁ in wfl1hl2. exact wfl1hl2. }
    { apply wfl₁hl₂_proj_l₂ in wfl1hl2. exact wfl1hl2. }
    { apply wfl₁hl₂_proj_h in wfl1hl2. exact wfl1hl2. }
    { apply wfl₁hl₂_proj_l₁l₂ in wfl1hl2. exact wfl1hl2. }
  Defined.
  
End FOL_helpers.


Tactic Notation "mlClear" constr(n) :=
  match goal with
  | |- @of_MLGoal ?Sgm (@mkMLGoal ?Sgm ?Ctx ?l ?g ?i) =>
    let l1 := fresh "l1" in
    let l2 := fresh "l2" in
    let Heql1 := fresh "Heql1" in
    let Heql2 := fresh "Heql2" in
    eapply cast_proof_ml_hyps;
    [(rewrite -[l](take_drop n); reflexivity)|];
    remember (take n l) as l1 eqn:Heql1 in |-;
    remember (drop n l) as l2 eqn:Heql2 in |-;
    eapply cast_proof_ml_hyps;
    [(rewrite -Heql1; rewrite -Heql2; reflexivity)|];
    simpl in Heql1; simpl in Heql2;
    let a := fresh "a" in
    let Hd := fresh "Hd" in
    destruct l2 as [|a l2''] eqn:Hd in *|-;[congruence|];
    eapply cast_proof_ml_hyps;
    [(rewrite -> Hd at 1; reflexivity)|];
    let Heqa := fresh "Heqa" in
    let Heql2' := fresh "Heql2'" in
    inversion Heql2 as [[Heqa Heql2'] ]; clear Heql2;
    apply myGoal_clear_hyp;
    eapply cast_proof_ml_hyps;
    [(try(rewrite -> Heql1 at 1); try(rewrite -> Heql2' at 1); reflexivity)|];
    clear Hd Heql2' Heqa l2 l2'' a Heql1 l1;
    eapply cast_proof_ml_hyps;[rewrite {1}[_ ++ _]/=; reflexivity|]
  end.

Local Example ex_mlClear {Σ : Signature} Γ a b c:
  well_formed a ->
  well_formed b ->
  well_formed c ->
  Γ ⊢i a ---> (b ---> (c ---> b)) using BasicReasoning.
Proof.
  intros wfa wfb wfc.
  toMLGoal.
  { wf_auto2. }
  repeat mlIntro.
  mlClear 2.
  mlClear 0.
  mlExactn 0.
Defined.

Section FOL_helpers.
  
  Context {Σ : Signature}.
  
  Lemma not_concl Γ p q:
    well_formed p ->
    well_formed q ->
    Γ ⊢i (p ---> (q ---> ((p ---> ! q) ---> ⊥))) using BasicReasoning.
  Proof.
    intros wfp wfq.
    eapply cast_proof'.
    {
      rewrite [(p ---> q ---> (p ---> ! q) ---> ⊥)]tofold.
      do 3 rewrite consume.
      rewrite [(((nil ++ [p]) ++ [q]) ++ [p ---> ! q])]/=.
      replace ([p; q; p--->!q]) with ([p] ++ [q; p ---> !q] ++ []) by reflexivity.
      reflexivity.
    }
    apply prf_reorder_iter_meta; try_wfauto2.
    simpl.
    fold (! q).
    apply modus_ponens; wf_auto2.
  Defined.

  (* TODO rename or remove *)
  Lemma helper Γ p q r:
    well_formed p ->
    well_formed q ->
    well_formed r ->
    Γ ⊢i (p ---> (q ---> ((p ---> (q ---> r)) ---> r))) using BasicReasoning.
  Proof.
    intros wfp wfq wfr.
    eapply cast_proof'.
    {
      rewrite [(p ---> q ---> (p ---> q ---> r) ---> r)]tofold. repeat rewrite consume.
      replace ((([] ++ [p]) ++ [q]) ++ [p ---> (q ---> r)]) with ([p;q;p--->(q ---> r)]) by reflexivity.
      replace ([p;q;p--->(q ---> r)]) with ([p] ++ [q; p ---> (q ---> r)] ++ []) by reflexivity.
      reflexivity.
    }
    apply prf_reorder_iter_meta; try_wfauto2.
    simpl.
    apply modus_ponens; wf_auto2.
  Defined.

  Lemma reorder_last_to_head Γ g x l:
    Pattern.wf l ->
    well_formed g ->
    well_formed x ->
    Γ ⊢i ((foldr patt_imp g (x::l)) ---> (foldr patt_imp g (l ++ [x]))) using BasicReasoning.
  Proof.
    intros wfl wfg wfx.
    induction l.
    - simpl. apply A_impl_A. wf_auto2.
    - pose proof (wfal := wfl).
      unfold Pattern.wf in wfl. simpl in wfl. apply andb_prop in wfl. destruct wfl as [wfa wfl].
      specialize (IHl wfl).
      simpl. simpl in IHl.
      eapply cast_proof'.
      { rewrite -> tofold at 1. repeat rewrite -> consume. reflexivity. }
      eapply prf_weaken_conclusion_iter_meta_meta.
      4: { apply IHl. }
      all: try_wfauto2.
      eapply cast_proof'.
      {
        rewrite consume.
        replace ((([] ++ [x ---> a ---> foldr patt_imp g l]) ++ [a]) ++ [x])
          with ([x ---> a ---> foldr patt_imp g l] ++ [a;x] ++ []) by reflexivity.
        reflexivity.
      }
      apply prf_reorder_iter_meta; wf_auto2.
      simpl. apply A_impl_A. wf_auto2.
  Defined.

  Lemma reorder_last_to_head_meta Γ g x l i:
    Pattern.wf l ->
    well_formed g ->
    well_formed x ->
    Γ ⊢i (foldr patt_imp g (x::l)) using i ->
    Γ ⊢i (foldr patt_imp g (l ++ [x])) using i.
  Proof.
    intros WFl WFG WFx H.
    eapply MP.
    apply H.
    useBasicReasoning.
    apply reorder_last_to_head; wf_auto2.
  Defined.
  
  (* Iterated modus ponens.
     For l = [x₁, ..., xₙ], it says that
     Γ ⊢i ((x₁ -> ... -> xₙ -> (x₁ -> ... -> xₙ -> r)) -> r)
  *)
  Lemma modus_ponens_iter Γ l r:
    Pattern.wf l ->
    well_formed r ->
    Γ ⊢i (foldr patt_imp r (l ++ [foldr patt_imp r l])) using BasicReasoning.
  Proof.
    intros wfl wfr.
    induction l.
    - simpl. apply A_impl_A. exact wfr.
    - pose proof (wfal := wfl).
      unfold Pattern.wf in wfl. simpl in wfl. apply andb_prop in wfl. destruct wfl as [wfa wfl].
      specialize (IHl wfl).
      simpl.
      eapply cast_proof'.
      { rewrite foldr_app. simpl. rewrite consume. simpl. reflexivity. }
      eapply cast_proof' in IHl.
      2: { rewrite foldr_app. reflexivity. }
      simpl in IHl.
      eapply prf_weaken_conclusion_meta_meta.
      4: { apply reorder_last_to_head; wf_auto2. }
      all: try_wfauto2.
      simpl. apply modus_ponens; wf_auto2.
  Defined.
  
  Lemma and_impl Γ p q r:
    well_formed p ->
    well_formed q ->
    well_formed r ->
    Γ ⊢i ((p and q ---> r) ---> (p ---> (q ---> r))) using BasicReasoning.
  Proof.
    intros wfp wfq wfr.
    toMLGoal.
    { wf_auto2. }
    repeat mlIntro.
    unfold patt_and. mlApply 0.
    mlIntro. unfold patt_or at 2.
    mlAssert ((! ! p)).
    { wf_auto2. }
    {
      mlAdd (@not_not_intro Σ Γ p wfp).
      mlApply 0.
      mlExactn 2.
    }
    mlAssert ((! q)).
    { wf_auto2. }
    {
      mlApply 3. mlExactn 4.
    }
    mlApply 5. mlExactn 2.
  Defined.
  
  Lemma and_impl' Γ p q r:
    well_formed p ->
    well_formed q ->
    well_formed r ->
    Γ ⊢i ((p ---> (q ---> r)) ---> ((p and q) ---> r)) using BasicReasoning.
  Proof.
    intros wfp wfq wfr.
    toMLGoal.
    { wf_auto2. }
    repeat mlIntro.
    mlAssert (p).
    { wf_auto2. }
    {
      mlAdd (@pf_conj_elim_l Σ Γ p q wfp wfq).
      mlApply 0.
      mlExactn 2.
    }
    mlAssert (q).
    { wf_auto2. }
    {
      mlAdd (@pf_conj_elim_r Σ Γ p q wfp wfq).
      mlApply 0.
      mlExactn 2.
    }
    (* This pattern is basically an "apply ... in" *)
    mlAssert ((q ---> r)).
    { wf_auto2. }
    { mlApply 0. mlExactn 2. }
    mlApply 4. mlExactn 3.
  Defined.

  Lemma prf_disj_elim_iter Γ l p q r:
    Pattern.wf l ->
    well_formed p ->
    well_formed q ->
    well_formed r ->
    Γ ⊢i ((fold_right patt_imp r (l ++ [p]))
           --->
           ((fold_right patt_imp r (l ++ [q]))
              --->                                                                
              (fold_right patt_imp r (l ++ [p or q]))))
    using BasicReasoning.
  Proof.
    intros wfl wfp wfq wfr.
    induction l.
    - simpl. apply prf_disj_elim; wf_auto2.
    - pose proof (wfal := wfl).
      unfold Pattern.wf in wfl. simpl in wfl. apply andb_prop in wfl. destruct wfl as [wfa wfl].
      specialize (IHl wfl).
      simpl in *.
      toMLGoal.
      { wf_auto2. }
      repeat mlIntro.
      mlAdd IHl.
      mlAssert ((foldr patt_imp r (l ++ [p]))).
      { wf_auto2. }
      { mlApply 1. mlExactn 3. }
      mlAssert ((foldr patt_imp r (l ++ [q]))).
      { wf_auto2. }
      { mlApply 2. mlExactn 3. }
      mlAssert ((foldr patt_imp r (l ++ [q]) ---> foldr patt_imp r (l ++ [p or q]))).
      { wf_auto2. }
      { mlApply 0. mlExactn 4. }
      mlApply 6.
      mlExactn 5.
  Defined.
  
  Lemma prf_disj_elim_iter_2 Γ l₁ l₂ p q r:
    Pattern.wf l₁ ->
    Pattern.wf l₂ ->
    well_formed p ->
    well_formed q ->
    well_formed r ->
    Γ ⊢i ((fold_right patt_imp r (l₁ ++ [p] ++ l₂))
           --->
           ((fold_right patt_imp r (l₁ ++ [q] ++ l₂))
              --->                                                                
              (fold_right patt_imp r (l₁ ++ [p or q] ++ l₂))))
    using BasicReasoning.  
  Proof.
    intros wfl₁ wfl₂ wfp wfq wfr.
    move: l₁ wfl₁.
    induction l₂; intros l₁ wfl₁.
    - simpl. apply prf_disj_elim_iter; wf_auto2.
    - pose proof (wfal₂ := wfl₂).
      unfold Pattern.wf in wfl₂. simpl in wfl₂. apply andb_prop in wfl₂. destruct wfl₂ as [wfa wfl₂].

      simpl. (* We need to move 'a' to the beginning of l₁; then we can apply IHl₂. *)
      (* Or we can swap p and a (move a to the end of l_1) *)
      remember (foldr patt_imp r (l₁ ++ p :: a :: l₂)) as A in |-.
      remember (foldr patt_imp r (l₁ ++ q :: a :: l₂)) as B in |-.
      remember (foldr patt_imp r (l₁ ++ (p or q) :: a :: l₂)) as C in |-.
      eapply cast_proof'.
      { rewrite -HeqA. rewrite -HeqB. rewrite -HeqC. reflexivity. }
      eapply cast_proof'.
      {
        rewrite -> tofold at 1. rewrite consume. rewrite consume. rewrite [_ ++ [B] ]/=.
        rewrite -> HeqA at 1. rewrite -> HeqB at 1. rewrite -> HeqC at 1.
        reflexivity.
      }
      eapply prf_weaken_conclusion_iter_meta_meta.
      4: {
        eapply cast_proof'.
        {
          replace (l₁ ++ (p or q) :: a :: l₂) with (l₁ ++ [p or q; a] ++ l₂) by reflexivity.
          reflexivity.
        }
        apply prf_reorder_iter; wf_auto2.
      }
      all: try_wfauto2.
      simpl.

      eapply cast_proof'.
      { 
        rewrite -> tofold at 1. repeat rewrite consume. rewrite [_ ++ [_] ]/=.

      replace
        ([foldr patt_imp r (l₁ ++ p :: a :: l₂); foldr patt_imp r (l₁ ++ q :: a :: l₂)])
        with
          ([foldr patt_imp r (l₁ ++ p :: a :: l₂)] ++ (foldr patt_imp r (l₁ ++ q :: a :: l₂))::[])
        by reflexivity.
        reflexivity.
      }

      eapply prf_strenghten_premise_iter_meta_meta with (h := foldr patt_imp r (l₁ ++ a :: q :: l₂)).
      6: { apply prf_reorder_iter; wf_auto2. }
      all: try_wfauto2.

      eapply cast_proof'.
      {
        replace
          ([foldr patt_imp r (l₁ ++ p :: a :: l₂)] ++ [foldr patt_imp r (l₁ ++ a :: q :: l₂)])
          with
          ([] ++ ((foldr patt_imp r (l₁ ++ p :: a :: l₂))::[foldr patt_imp r (l₁ ++ a :: q :: l₂)]))
          by reflexivity.
        reflexivity.
     }

      eapply prf_strenghten_premise_iter_meta_meta with (h := (foldr patt_imp r (l₁ ++ a :: p :: l₂))).
      6: {  apply prf_reorder_iter; wf_auto2. }
      all: try_wfauto2.

      simpl.
      eapply cast_proof'.
      {
        replace (l₁ ++ a :: p :: l₂) with ((l₁ ++ [a]) ++ [p] ++ l₂) by (rewrite <- app_assoc; reflexivity).
        replace (l₁ ++ a :: q :: l₂) with ((l₁ ++ [a]) ++ [q] ++ l₂) by (rewrite <- app_assoc; reflexivity).
        replace (l₁ ++ a :: (p or q) :: l₂) with ((l₁ ++ [a]) ++ [p or q] ++ l₂) by (rewrite <- app_assoc; reflexivity).
        reflexivity.
      }
      apply IHl₂; wf_auto2.
  Defined.

  Lemma prf_disj_elim_iter_2_meta Γ l₁ l₂ p q r i:
    Pattern.wf l₁ ->
    Pattern.wf l₂ ->
    well_formed p ->
    well_formed q ->
    well_formed r ->
    Γ ⊢i (fold_right patt_imp r (l₁ ++ [p] ++ l₂)) using i ->
    Γ ⊢i ((fold_right patt_imp r (l₁ ++ [q] ++ l₂))
              --->                                                                
              (fold_right patt_imp r (l₁ ++ [p or q] ++ l₂))) using i.
            
  Proof.
    intros WFl1 WFl2 WFp WFq WFr H.
    eapply MP.
    apply H.
    useBasicReasoning.
    apply prf_disj_elim_iter_2; wf_auto2.
  Defined.
  
  Lemma prf_disj_elim_iter_2_meta_meta Γ l₁ l₂ p q r i:
    Pattern.wf l₁ ->
    Pattern.wf l₂ ->
    well_formed p ->
    well_formed q ->
    well_formed r ->
    Γ ⊢i (fold_right patt_imp r (l₁ ++ [p] ++ l₂)) using i ->
    Γ ⊢i (fold_right patt_imp r (l₁ ++ [q] ++ l₂)) using i ->
    Γ ⊢i (fold_right patt_imp r (l₁ ++ [p or q] ++ l₂)) using i.
  Proof.
    intros WFl1 WFl2 WFp WFq WFr H H0.
    eapply MP.
    2: { apply prf_disj_elim_iter_2_meta; try_wfauto2. apply H. }
    apply H0.
  Defined.

  Lemma MLGoal_disj_elim Γ l₁ l₂ p q r i:
    @mkMLGoal Σ Γ (l₁ ++ [p] ++ l₂) r i ->
    @mkMLGoal Σ Γ (l₁ ++ [q] ++ l₂) r i ->
    @mkMLGoal Σ Γ (l₁ ++ [p or q] ++ l₂) r i.
  Proof.
    intros H1 H2.
    unfold of_MLGoal in *. simpl in *.
    intros wfr Hwf.
    apply prf_disj_elim_iter_2_meta_meta.
    7: apply H2.
    6: apply H1.
    all: try assumption.
    { abstract (apply wfl₁hl₂_proj_l₁ in Hwf; exact Hwf). }
    { abstract (apply wfl₁hl₂_proj_l₂ in Hwf; exact Hwf). }
    { abstract (apply wfl₁hl₂_proj_h in Hwf; wf_auto2). }
    { abstract (apply wfl₁hl₂_proj_h in Hwf; wf_auto2). }
    { abstract (
        pose proof (wfl₁hl₂_proj_l₁ Hwf);
        pose proof (wfl₁hl₂_proj_h Hwf);
        pose proof (wfl₁hl₂_proj_l₂ Hwf);
        apply wf_app; [assumption|];
        unfold patt_or,patt_not in *;
        wf_auto2
      ).
    }
    { abstract (
        pose proof (wfl₁hl₂_proj_l₁ Hwf);
        pose proof (wfl₁hl₂_proj_h Hwf);
        pose proof (wfl₁hl₂_proj_l₂ Hwf);
        apply wf_app; [assumption|];
        unfold patt_or,patt_not in *;
        wf_auto2
      ).
    }
  Defined.

End FOL_helpers.

Tactic Notation "mlDestructOr" constr(n) :=
  match goal with
  | |- @of_MLGoal ?Sgm (@mkMLGoal ?Sgm ?Ctx ?l ?g ?i) =>
    let Htd := fresh "Htd" in
    eapply cast_proof_ml_hyps;
    [(
      epose proof (Htd :=take_drop);
      specialize (Htd n l);
      rewrite [take _ _]/= in Htd;
      rewrite [drop _ _]/= in Htd;
      rewrite -Htd; clear Htd;
      epose proof (Htd :=take_drop);
      specialize (Htd 1 (drop n l));
      rewrite [take _ _]/= in Htd;
      rewrite ![drop _ _]/= in Htd;
      rewrite -Htd; clear Htd; reflexivity
      )|];
    apply MLGoal_disj_elim; simpl
  end.

Section FOL_helpers.

  Context {Σ : Signature}.
  
  Local Example exd Γ a b p q c i:
    well_formed a ->
    well_formed b ->
    well_formed p ->
    well_formed q ->
    well_formed c ->
    Γ ⊢i (a ---> p ---> b ---> c) using i ->
    Γ ⊢i (a ---> q ---> b ---> c) using i->
    Γ ⊢i (a ---> (p or q) ---> b ---> c) using i.
  Proof.
    intros WFa WFb WFp WFq WFc H H0.
    toMLGoal.
    { wf_auto2. } 
    repeat mlIntro.
    mlDestructOr 1.
    - fromMLGoal. apply H.
    - fromMLGoal. apply H0.
  Defined.

  Lemma pf_iff_split Γ A B i:
    well_formed A ->
    well_formed B ->
    Γ ⊢i A ---> B using i ->
    Γ ⊢i B ---> A using i ->
    Γ ⊢i A <---> B using i.
  Proof.
    intros wfA wfB AimplB BimplA.
    unfold patt_iff.
    apply conj_intro_meta; try_wfauto2; assumption.
  Defined.
  
  Lemma pf_iff_proj1 Γ A B i:
    well_formed A ->
    well_formed B ->
    Γ ⊢i A <---> B using i ->
    Γ ⊢i A ---> B using i.
  Proof.
    intros WFA WFB H. unfold patt_iff in H.
    apply pf_conj_elim_l_meta in H; try_wfauto2; assumption.
  Defined.

  Lemma pf_iff_proj2 Γ A B i:
    well_formed A ->
    well_formed B ->
    Γ ⊢i (A <---> B) using i ->
    Γ ⊢i (B ---> A) using i.
  Proof.
    intros WFA WFB H. unfold patt_iff in H.
    apply pf_conj_elim_r_meta in H; try_wfauto2; assumption.
  Defined.

  Lemma pf_iff_iff Γ A B i:
    well_formed A ->
    well_formed B ->
    prod ((Γ ⊢i (A <---> B) using i) -> (prod (Γ ⊢i (A ---> B) using i) (Γ ⊢i (B ---> A) using i)))
    ( (prod (Γ ⊢i (A ---> B) using i)  (Γ ⊢i (B ---> A) using i)) -> (Γ ⊢i (A <---> B) using i)).
  Proof.
    intros WFA WFB.
    split; intros H.
    {
      pose proof (H1 := pf_iff_proj1 WFA WFB H).
      pose proof (H2 := pf_iff_proj2 WFA WFB H).
      split; assumption.
    }
    {
      destruct H as [H1 H2].
      apply pf_iff_split; assumption.
    }
  Defined.

  Lemma pf_iff_equiv_refl Γ A :
    well_formed A ->
    Γ ⊢i (A <---> A) using BasicReasoning.
  Proof.
    intros WFA.
    apply pf_iff_split; try_wfauto2; apply A_impl_A; assumption.
  Defined.

  Lemma pf_iff_equiv_sym Γ A B i:
    well_formed A ->
    well_formed B ->
    Γ ⊢i (A <---> B) using i ->
    Γ ⊢i (B <---> A) using i.
  Proof.
    intros wfA wfB H.
    pose proof (H2 := H).
    apply pf_iff_proj2 in H2; try_wfauto2.
    rename H into H1.
    apply pf_iff_proj1 in H1; try_wfauto2.
    apply pf_iff_split; try_wfauto2; assumption.
  Defined.

  Lemma pf_iff_equiv_trans Γ A B C i:
    well_formed A ->
    well_formed B ->
    well_formed C ->
    Γ ⊢i (A <---> B) using i ->
    Γ ⊢i (B <---> C) using i ->
    Γ ⊢i (A <---> C) using i.
  Proof.
    intros wfA wfB wfC AeqB BeqC.
    apply pf_iff_iff in AeqB; try_wfauto2. destruct AeqB as [AimpB BimpA].
    apply pf_iff_iff in BeqC; try_wfauto2. destruct BeqC as [BimpC CimpB].
    apply pf_iff_iff; try_wfauto2.
    split.
    {
      eapply syllogism_meta. 4,5: eassumption.
      1-3: wf_auto2.
    }
    {
      eapply syllogism_meta. 4,5: eassumption.
      1-3: wf_auto2.
    }
  Defined.

  Lemma prf_conclusion Γ a b i:
    well_formed a ->
    well_formed b ->
    Γ ⊢i b using i ->
    Γ ⊢i (a ---> b) using i.
  Proof.
    intros WFa WFb H. eapply MP.
    apply H.
    useBasicReasoning.
    apply P1; wf_auto2.
  Defined.
    
  Lemma prf_prop_bott_iff Γ AC:
    Γ ⊢i ((subst_ctx AC patt_bott) <---> patt_bott)
    using (
    (ExGen := ∅, SVSubst := ∅, KT := false, FP := frames_of_AC AC)).
  Proof.
    apply pf_iff_split.
    1,2: wf_auto2.
    1: apply ctx_bot_prop.
    1: apply pile_refl.
    1: wf_auto2.
    {
      useBasicReasoning.
      apply A_impl_A.
      reflexivity.
    }
    {
      useBasicReasoning.
      apply bot_elim.
      wf_auto2.
    }
  Defined.

  Lemma Prop_disj_left (Γ : Theory) (ϕ₁ ϕ₂ ψ : Pattern) :
    well_formed ϕ₁ ->
    well_formed ϕ₂ ->
    well_formed ψ ->
    Γ ⊢i (ϕ₁ or ϕ₂) $ ψ ---> (ϕ₁ $ ψ) or (ϕ₂ $ ψ) using BasicReasoning.
  Proof.
    intros wfϕ₁ wfϕ₂ wfψ.
    unshelve (eexists).
    {
      apply Prop_disj_left; assumption.
    }
    {
      abstract (
        constructor; simpl;
        [(set_solver)|(set_solver)|(reflexivity)|(set_solver)]
      ).
    }
  Defined.
  
  Lemma Prop_disj_right (Γ : Theory) (ϕ₁ ϕ₂ ψ : Pattern) :
    well_formed ϕ₁ ->
    well_formed ϕ₂ ->
    well_formed ψ ->
    Γ ⊢i ψ $ (ϕ₁ or ϕ₂)  ---> (ψ $ ϕ₁) or (ψ $ ϕ₂) using BasicReasoning.
  Proof.
    intros wfϕ₁ wfϕ₂ wfψ.
    unshelve (eexists).
    {
      apply Prop_disj_right; assumption.
    }
    {
      abstract (
        constructor; simpl;
        [(set_solver)|(set_solver)|(reflexivity)|(set_solver)]
      ).
    }
  Defined.

  End FOL_helpers.

  Tactic Notation "remember_constraint" "as" ident(i') :=
      match goal with
      | [|- (_ ⊢i _ using ?constraint)] => remember constraint as i'
      end.
  
  Tactic Notation "gapply" uconstr(pf) := eapply useGenericReasoning;[|eapply pf].

  Tactic Notation "gapply" uconstr(pf) "in" ident(H) :=
    eapply useGenericReasoning in H;[|apply pf].

  Tactic Notation "aapply" uconstr(pf)
  := gapply pf; try apply pile_any.

  Ltac try_solve_pile := try (solve [(apply pile_evs_svs_kt; auto; try set_solver)]).

  Section FOL_helpers.

  Context {Σ : Signature}.  

  Lemma prf_prop_or_iff Γ AC p q:
    well_formed p ->
    well_formed q ->
    Γ ⊢i ((subst_ctx AC (p or q)) <---> ((subst_ctx AC p) or (subst_ctx AC q)))
    using (
    (ExGen := ∅, SVSubst := ∅, KT := false, FP := frames_of_AC AC)).
  Proof.
    intros wfp wfq.
    induction AC; simpl.
    - useBasicReasoning. apply pf_iff_equiv_refl; wf_auto2.
    - apply pf_iff_iff in IHAC; try_wfauto2.
      destruct IHAC as [IH1 IH2].
      remember_constraint as i.
      apply pf_iff_split; try_wfauto2.
      + pose proof (H := IH1).
        apply useGenericReasoning with (i := i) in H.
        2: { subst i. 
          apply pile_evs_svs_kt; auto. set_solver.
        }
        rewrite Heqi in H.
        apply Framing_left with (ψ := p0) (wfψ := Prf) in H.
        2: { apply pile_evs_svs_kt; auto. set_solver. }
        eapply syllogism_meta. 4: subst i; apply H.
        all: try_wfauto2.
        remember (subst_ctx AC p) as p'.
        remember (subst_ctx AC q) as q'.
        subst i.
        eapply useGenericReasoning.
        2: eapply Prop_disj_left. all: subst; try_wfauto2.
        { apply pile_evs_svs_kt; auto. set_solver. }
      + eapply prf_disj_elim_meta_meta; try_wfauto2.
        * subst i. 
          apply Framing_left with (wfψ := Prf).
          { apply pile_evs_svs_kt; auto. set_solver. }
          eapply prf_weaken_conclusion_meta_meta.
          4: { gapply IH2. try_solve_pile. }
          1-3: wf_auto2.
          useBasicReasoning.
          apply disj_left_intro; wf_auto2.
        * subst i.
          apply Framing_left with (wfψ := Prf).
          { try_solve_pile. }
          eapply prf_weaken_conclusion_meta_meta. 4: gapply IH2; try_solve_pile. all: try_wfauto2.
          useBasicReasoning.
          apply disj_right_intro; wf_auto2.
    - apply pf_iff_iff in IHAC; try_wfauto2.
      destruct IHAC as [IH1 IH2].
      remember_constraint as i.
      apply pf_iff_split; try_wfauto2.
      + pose proof (H := IH1).
        apply useGenericReasoning with (i := i) in H.
        2: { subst i. try_solve_pile. }
        eapply Framing_right with (ψ := p0)(wfψ := Prf) in H.
        eapply syllogism_meta. 4: apply H.
        all: try_wfauto2.
        2: { subst i. try_solve_pile. }
        remember (subst_ctx AC p) as p'.
        remember (subst_ctx AC q) as q'.
        subst i; apply useBasicReasoning.
        apply Prop_disj_right. all: subst; try_wfauto2.
      + eapply prf_disj_elim_meta_meta; try_wfauto2.
        * subst i.
          apply Framing_right with (wfψ := Prf).
          { try_solve_pile. }
          eapply prf_weaken_conclusion_meta_meta.
          4: gapply IH2; try_solve_pile. all: try_wfauto2.
          useBasicReasoning.
          apply disj_left_intro; wf_auto2.
        * subst i.
          apply Framing_right with (wfψ := Prf).
          { try_solve_pile. }
          eapply prf_weaken_conclusion_meta_meta.
          4: gapply IH2; try_solve_pile.
          all: try_wfauto2.
          useBasicReasoning.
          apply disj_right_intro; wf_auto2.
  Defined.

  Lemma Ex_quan (Γ : Theory) (ϕ : Pattern) (y : evar) :
    well_formed (patt_exists ϕ) ->
    Γ ⊢i (instantiate (patt_exists ϕ) (patt_free_evar y) ---> (patt_exists ϕ))
    using BasicReasoning.
  Proof.
    intros Hwf.
    unshelve (eexists).
    {
      apply ProofSystem.Ex_quan. apply Hwf.
    }
    {
      abstract (
        constructor; simpl;
        [( set_solver )
        |( set_solver )
        |( reflexivity )
        |( set_solver )
        ]
      ).
    }
  Defined.

  Lemma hypothesis (Γ : Theory) (axiom : Pattern) :
    well_formed axiom ->
    (axiom ∈ Γ) ->
    Γ ⊢i axiom
    using BasicReasoning.
  Proof.
    intros Hwf Hin.
    unshelve (eexists).
    {
      apply ProofSystem.hypothesis. apply Hwf. apply Hin.
    }
    {
      abstract (
        constructor; simpl;
        [( set_solver )
        |( set_solver )
        |( reflexivity )
        |( set_solver )
        ]
      ).
    }
  Defined.

  Lemma Singleton_ctx (Γ : Theory) (C1 C2 : Application_context) (ϕ : Pattern) (x : evar) :
    well_formed ϕ ->
    Γ ⊢i (! ((subst_ctx C1 (patt_free_evar x and ϕ)) and
               (subst_ctx C2 (patt_free_evar x and (! ϕ)))))
    using BasicReasoning.
  Proof.
    intros Hwf.
    unshelve (eexists).
    {
      apply ProofSystem.Singleton_ctx. apply Hwf.
    }
    {
      abstract (
        constructor; simpl;
        [( set_solver )
        |( set_solver )
        |( reflexivity )
        |( set_solver )
        ]
      ).
    }
  Defined.

  Lemma Existence (Γ : Theory) :
    Γ ⊢i (ex , patt_bound_evar 0) using BasicReasoning.
  Proof.
    unshelve (eexists).
    {
      apply ProofSystem.Existence.
    }
    {
      abstract (
        constructor; simpl;
        [( set_solver )
        |( set_solver )
        |( reflexivity )
        |( set_solver )
        ]
      ).
    }
  Defined.

  Lemma pile_impl_allows_gen_x x gpi svs kt fp:
    ProofInfoLe ( (ExGen := {[x]}, SVSubst := svs, KT := kt, FP := fp)) ( gpi) ->
    x ∈ pi_generalized_evars gpi.
  Proof.
    intros [H].
    pose (H1 := @A_impl_A Σ ∅ patt_bott ltac:(wf_auto2)).
    pose (H2 := @prf_add_assumption Σ ∅ (patt_free_evar x) (patt_bott ---> patt_bott) BasicReasoning ltac:(wf_auto2) ltac:(wf_auto2) H1).
    pose (H3 := @ProofSystem.Ex_gen Σ ∅ (patt_free_evar x) (patt_bott ---> patt_bott) x ltac:(wf_auto2) ltac:(wf_auto2) (proj1_sig H2) ltac:(simpl; set_solver)).
    pose proof (H' := H ∅ _ H3).
    feed specialize H'.
    {
      constructor; simpl.
      {
        clear. set_solver.
      }
      {
        clear. set_solver.
      }
      {
        reflexivity.
      }
      {
        clear. set_solver.
      }
    }
    inversion H'. simpl in *. clear -pwi_pf_ge. set_solver.
  Qed.

  Lemma Ex_gen (Γ : Theory) (ϕ₁ ϕ₂ : Pattern) (x : evar) (i : ProofInfo)
    {pile : ProofInfoLe (
            {| pi_generalized_evars := {[x]};
               pi_substituted_svars := ∅;
               pi_uses_kt := false ;
               pi_framing_patterns := ∅ ;
            |}) i} :
    x ∉ free_evars ϕ₂ ->
    Γ ⊢i ϕ₁ ---> ϕ₂ using i ->
    Γ ⊢i (exists_quantify x ϕ₁ ---> ϕ₂) using i.
  Proof.
    intros Hfev [pf Hpf].
    unshelve (eexists).
    {
      apply ProofSystem.Ex_gen.
      { pose proof (pf' := pf). apply proved_impl_wf in pf'.  wf_auto2. }
      { pose proof (pf' := pf). apply proved_impl_wf in pf'.  wf_auto2. }
      { exact pf. }
      { exact Hfev. }
    }
    {
      simpl.
      constructor; simpl.
      {
        rewrite elem_of_subseteq. intros x0 Hx0.
        rewrite elem_of_gset_to_coGset in Hx0.
        rewrite elem_of_union in Hx0.
        destruct Hx0.
        {
          rewrite elem_of_singleton in H. subst.
          eapply pile_impl_allows_gen_x.
          apply pile.
        }
        {
          inversion Hpf.
          apply pwi_pf_ge.
          rewrite elem_of_gset_to_coGset.
          assumption.
        }
      }
      {
        inversion Hpf.
        apply pwi_pf_svs.
      }
      {
        inversion Hpf.
        apply pwi_pf_kt.
      }
      {
        inversion Hpf.
        apply pwi_pf_fp.
      }
    }
  Defined.

  Lemma pile_basic_generic eg svs kt fp:
    ProofInfoLe BasicReasoning ( (ExGen := eg, SVSubst := svs, KT := kt, FP := fp)).
  Proof.
    constructor.
    intros Γ ϕ pf Hpf.
    destruct Hpf as [Hpf2 Hpf3 Hpf4]. simpl in *.
    constructor; simpl.
    { set_solver. }
    { set_solver. }
    { unfold implb in Hpf4. case_match.
      { inversion Hpf4. }
      simpl. reflexivity.
    }
    { set_solver. }
  Qed.

  Lemma Prop_ex_left (Γ : Theory) (ϕ ψ : Pattern) :
    well_formed (ex, ϕ) ->
    well_formed ψ ->
    Γ ⊢i (ex , ϕ) $ ψ ---> ex , ϕ $ ψ
    using BasicReasoning.
  Proof.
    intros wfϕ wfψ.
    unshelve (eexists).
    {
      apply ProofSystem.Prop_ex_left.
      { exact wfϕ. }
      { exact wfψ. }
    }
    {
      constructor; simpl.
      { set_solver. }
      { set_solver. }
      { reflexivity. }
      { set_solver. }
    }
  Defined.

  Lemma Prop_ex_right (Γ : Theory) (ϕ ψ : Pattern) :
    well_formed (ex, ϕ) ->
    well_formed ψ ->
    Γ ⊢i ψ $ (ex , ϕ) ---> ex , ψ $ ϕ
    using BasicReasoning.
  Proof.
    intros wfϕ wfψ.
    unshelve (eexists).
    {
      apply ProofSystem.Prop_ex_right.
      { exact wfϕ. }
      { exact wfψ. }
    }
    {
      constructor; simpl.
      { set_solver. }
      { set_solver. }
      { reflexivity. }
      { set_solver. }
    }
  Defined.

 

  End FOL_helpers.

  Tactic Notation "change" "constraint" "in" ident(H) :=
    let i := fresh "i" in
    remember_constraint as i;
    eapply useGenericReasoning with (i := i) in H;
    subst i;
    [|(try_solve_pile)].

Section FOL_helpers.
  
  Context {Σ : Signature}.
    

  Lemma prf_prop_ex_iff Γ AC p x:
    evar_is_fresh_in x (subst_ctx AC p) ->
    well_formed (patt_exists p) = true ->
    Γ ⊢i ((subst_ctx AC (patt_exists p)) <---> (exists_quantify x (subst_ctx AC (evar_open 0 x p))))
    using (
    {| pi_generalized_evars := {[x]};
       pi_substituted_svars := ∅;
       pi_uses_kt := false ;
       pi_framing_patterns := frames_of_AC AC
    |}).
  Proof.
    intros Hx Hwf.

    induction AC; simpl.
    - simpl in Hx.
      unfold exists_quantify.
      erewrite evar_quantify_evar_open; auto. 2: now do 2 apply andb_true_iff in Hwf as [_ Hwf].
      useBasicReasoning.
      apply pf_iff_equiv_refl. exact Hwf.
    -
      assert (Hwfex: well_formed (ex , subst_ctx AC p)).
      { unfold well_formed. simpl.
        pose proof (Hwf' := Hwf).
        unfold well_formed in Hwf. simpl in Hwf.
        apply andb_prop in Hwf. destruct Hwf as [Hwfp Hwfc].
        apply (@wp_sctx _ AC p) in Hwfp. rewrite Hwfp. simpl. clear Hwfp.
        unfold well_formed_closed. unfold well_formed_closed in Hwfc. simpl in Hwfc. simpl.
        split_and!.
        + apply wcmu_sctx. destruct_and!. assumption.
        + apply wcex_sctx. destruct_and!. assumption.
      }

      assert(Hxfr1: evar_is_fresh_in x (subst_ctx AC p)).
      { simpl in Hx.
        eapply evar_is_fresh_in_richer.
        2: { apply Hx. }
        solve_free_evars_inclusion 5.
      }

      simpl in Hx.
      pose proof (Hxfr1' := Hxfr1).
      rewrite -> evar_is_fresh_in_subst_ctx in Hxfr1'.
      destruct Hxfr1' as [Hxfrp HxAC].
      
      assert(Hwf': well_formed (exists_quantify x (subst_ctx AC (evar_open 0 x p)))).
      {
        unfold exists_quantify.
        clear -HxAC Hwf.
        apply wf_ex_eq_sctx_eo.
        apply Hwf.
      }

      (* TODO automate this *)
      assert (Hwfeo: well_formed (evar_open 0 x p)).
      {
        unfold well_formed.
        unfold well_formed,well_formed_closed in Hwf. apply andb_prop in Hwf. simpl in Hwf.
        rewrite wfp_evar_open.
        { apply Hwf. }
        unfold well_formed_closed.
        destruct_and!.
        split_and!; auto.
      }
      
      
      (* TODO automate this. The problem is that [well_formed_app] and others do not have [= true];
         that is why [auto] does not work. But [auto] is not suitable for this anyway.
         A better way would be to create some `simpl_well_formed` tuple, that might use the type class
         mechanism for extension...
       *)
      assert(Hwf'p0: well_formed (exists_quantify x (subst_ctx AC (evar_open 0 x p) $ p0))).
      {
        unfold exists_quantify.
        apply wf_ex_evar_quantify.
        apply well_formed_app.
        2: { apply Prf. }
        auto.
      }
      
      apply pf_iff_iff in IHAC; auto.
           
      destruct IHAC as [IH1 IH2].
      apply pf_iff_split; auto.
      + pose proof (H := IH1).
        change constraint in IH1.
        apply Framing_left with (ψ := p0) (wfψ := Prf) in IH1.
        2: { try_solve_pile. }
        
        eapply syllogism_meta. 4: apply IH1.
        1-3: wf_auto2.
        
        remember (subst_ctx AC (evar_open 0 x p)) as p'.
        unfold exists_quantify.
        simpl. rewrite [evar_quantify x 0 p0]evar_quantify_fresh.
        { eapply evar_is_fresh_in_app_r. apply Hx. }
        useBasicReasoning.
        apply Prop_ex_left. wf_auto2. wf_auto2.
      + clear IH1.

        change constraint in IH2.
        apply Framing_left with (ψ := p0) (wfψ := Prf) in IH2.
        2: { try_solve_pile. }
        eapply syllogism_meta. 5: eapply IH2.
        1-3: wf_auto2.
        
        apply Ex_gen; auto.
        { try_solve_pile. }
        1: {
          unfold exists_quantify.
          simpl.
          rewrite free_evars_evar_quantify.
          unfold evar_is_fresh_in in Hx. simpl in Hx. clear -Hx.
          set_solver.
        }
        
        (* TODO have some nice implicit parameters *)
        gapply (@Framing_left _ _ _ _ _ _ Prf).
        2: apply pile_refl.
        1: try_solve_pile.
        unfold evar_open.
        rewrite subst_ctx_bevar_subst.
        unfold exists_quantify. simpl.
        fold (evar_open 0 x (subst_ctx AC p)).
        rewrite -> evar_quantify_evar_open; auto.
        2: now do 2 apply andb_true_iff in Hwfex as [_ Hwfex].
        useBasicReasoning.
        apply Ex_quan; auto.
    -
      assert (Hwfex: well_formed (ex , subst_ctx AC p)).
      { unfold well_formed. simpl.
        pose proof (Hwf' := Hwf).
        unfold well_formed in Hwf. simpl in Hwf.
        apply andb_prop in Hwf. destruct Hwf as [Hwfp Hwfc].
        apply (@wp_sctx _ AC p) in Hwfp. rewrite Hwfp. simpl. clear Hwfp.
        unfold well_formed_closed. unfold well_formed_closed in Hwfc. simpl in Hwfc. simpl.
        split_and!.
        + apply wcmu_sctx. destruct_and!. assumption.
        + apply wcex_sctx. destruct_and!. assumption.          
      }

      assert(Hxfr1: evar_is_fresh_in x (subst_ctx AC p)).
      { simpl in Hx.
        eapply evar_is_fresh_in_richer.
        2: { apply Hx. }
        solve_free_evars_inclusion 5.
      }

      simpl in Hx.
      pose proof (Hxfr1' := Hxfr1).
      rewrite -> evar_is_fresh_in_subst_ctx in Hxfr1'.
      destruct Hxfr1' as [Hxfrp HxAC].
      
      assert(Hwf': well_formed (exists_quantify x (subst_ctx AC (evar_open 0 x p)))).
      {
        unfold exists_quantify.
        clear -HxAC Hwf.
        apply wf_ex_eq_sctx_eo.
        apply Hwf.
      }

      (* TODO automate this *)
      assert (Hwfeo: well_formed (evar_open 0 x p)).
      {
        unfold well_formed.
        unfold well_formed,well_formed_closed in Hwf. apply andb_prop in Hwf. simpl in Hwf.
        rewrite wfp_evar_open.
        { apply Hwf. }
        unfold well_formed_closed.
        destruct_and!.
        split_and!; auto.
      }
      
      
      (* TODO automate this. The problem is that [well_formed_app] and others do not have [= true];
         that is why [auto] does not work. But [auto] is not suitable for this anyway.
         A better way would be to create some `simpl_well_formed` tuple, that might use the type class
         mechanism for extension...
       *)
      assert(Hwf'p0: well_formed (exists_quantify x (p0 $ subst_ctx AC (evar_open 0 x p)))).
      {
        unfold exists_quantify.
        apply wf_ex_evar_quantify.
        apply well_formed_app; auto.
      }
      
      apply pf_iff_iff in IHAC; auto.
           
      destruct IHAC as [IH1 IH2].
      apply pf_iff_split; auto.
      + pose proof (H := IH1).
        change constraint in IH1.
        apply (@Framing_right _ _ _ _ _ _ Prf) in IH1.
        2: try_solve_pile.
        eapply syllogism_meta. 4: apply IH1.
        1-3: wf_auto2.
        remember (subst_ctx AC (evar_open 0 x p)) as p'.
        unfold exists_quantify.
        simpl. rewrite [evar_quantify x 0 p0]evar_quantify_fresh.
        { eapply evar_is_fresh_in_app_l. apply Hx. }
        useBasicReasoning.
        apply Prop_ex_right. wf_auto2. wf_auto2.
      + clear IH1.

        change constraint in IH2.
        eapply (@Framing_right _ _ _ _ _ _ Prf) in IH2.
        eapply syllogism_meta. 5: eapply IH2.
        1-3: wf_auto2.
        2: { try_solve_pile. }

        apply Ex_gen; auto.
        { try_solve_pile. }
        1: {
          unfold exists_quantify.
          simpl.
          rewrite free_evars_evar_quantify.
          unfold evar_is_fresh_in in Hx. simpl in Hx. clear -Hx.
          set_solver.
        }
        
        eapply (@Framing_right _ _ _ _ _ _ Prf).
        { try_solve_pile. }
        {
        unfold evar_open.
        rewrite subst_ctx_bevar_subst.
        unfold exists_quantify. simpl.
        fold (evar_open 0 x (subst_ctx AC p)).
        erewrite evar_quantify_evar_open; auto.
        2: now do 2 apply andb_true_iff in Hwfex as [_ Hwfex].
        useBasicReasoning.
        apply Ex_quan; auto.
        }
  Defined.
  
  Lemma and_of_negated_iff_not_impl Γ p1 p2:
    well_formed p1 ->
    well_formed p2 ->
    Γ ⊢i (! (! p1 ---> p2) <---> ! p1 and ! p2)
    using BasicReasoning.
  Proof.
    intros wfp1 wfp2.
    apply conj_intro_meta.
    { wf_auto2. }
    { wf_auto2. }
    - toMLGoal.
      { wf_auto2. }
      mlIntro. mlIntro.
      mlApply 0.
      mlIntro.
      unfold patt_or.
      mlAdd (@not_not_elim Σ Γ p2 ltac:(wf_auto2)).
      mlApply 0.
      mlApply 2.
      mlAdd (@not_not_intro Σ Γ (! p1) ltac:(wf_auto2)).
      mlApply 0.
      mlExactn 4.
    - toMLGoal.
      { wf_auto2. }
      mlIntro. mlIntro.
      unfold patt_and.
      mlApply 0.
      unfold patt_or.
      mlIntro.
      mlAdd (@not_not_intro Σ Γ p2 ltac:(wf_auto2)).
      mlApply 0.
      mlApply 2.
      mlAdd (@not_not_elim Σ Γ (! p1) ltac:(wf_auto2)).
      mlApply 0.
      mlExactn 4.
  Defined.

  Lemma and_impl_2 Γ p1 p2:
    well_formed p1 ->
    well_formed p2 ->
    Γ ⊢i (! (p1 ---> p2) <---> p1 and ! p2)
    using BasicReasoning.
  Proof.
    intros wfp1 wfp2.
    apply conj_intro_meta.
    { wf_auto2. }
    { wf_auto2. }
    - toMLGoal.
      { wf_auto2. }
      mlIntro. mlIntro.
      mlApply 0.
      mlIntro.
      unfold patt_or.
      mlAdd (@not_not_elim Σ Γ p2 ltac:(wf_auto2)).
      mlApply 0.
      mlApply 2.
      mlAdd (@not_not_intro Σ Γ p1 ltac:(wf_auto2)).
      mlApply 0.
      mlExactn 4.
    - toMLGoal.
      { wf_auto2. }
      mlIntro. mlIntro.
      mlApply 0.
      unfold patt_or.
      mlIntro.
      mlAdd (@not_not_intro Σ Γ p2 ltac:(wf_auto2)).
      mlApply 0.
      mlApply 2.
      mlAdd (@not_not_elim Σ Γ p1 ltac:(wf_auto2)).
      mlApply 0.
      mlExactn 4.
  Defined.

  Lemma conj_intro_meta_partial (Γ : Theory) (A B : Pattern) (i : ProofInfo) :
    well_formed A → well_formed B →
    Γ ⊢i A using i →
    Γ ⊢i B ---> (A and B) using i.
  Proof.
    intros WFA WFB H.
    eapply MP.
    - exact H.
    - useBasicReasoning. apply conj_intro.
      { wf_auto2. }
      { wf_auto2. }
  Defined.

  Lemma and_impl_patt (A B C : Pattern) Γ (i : ProofInfo):
    well_formed A → well_formed B → well_formed C →
    Γ ⊢i A using i ->
    Γ ⊢i ((A and B) ---> C) using i ->
    Γ ⊢i (B ---> C) using i.
  Proof.
    intros WFA WFB WFC H H0.
    eapply syllogism_meta with (B := patt_and A B).
    { wf_auto2. }
    { wf_auto2. }
    { wf_auto2. }
    2: { exact H0. }
    apply conj_intro_meta_partial.
    { wf_auto2. }
    { wf_auto2. }
    exact H.
  Defined.

  Lemma conj_intro2 (Γ : Theory) (A B : Pattern) :
    well_formed A -> well_formed B ->
    Γ ⊢i (A ---> (B ---> (B and A)))
    using BasicReasoning.
  Proof.
    intros WFA WFB. eapply reorder_meta.
    { wf_auto2. }
    { wf_auto2. }
    { wf_auto2. }
    apply conj_intro.
    { wf_auto2. }
    { wf_auto2. }
  Defined.

  Lemma conj_intro_meta_partial2 (Γ : Theory) (A B : Pattern) (i : ProofInfo):
    well_formed A → well_formed B →
    Γ ⊢i A using i →
    Γ ⊢i B ---> (B and A) using i.
  Proof.
    intros WFA WFB H.
    eapply MP.
    - exact H.
    - useBasicReasoning. apply conj_intro2.
      { wf_auto2. }
      { wf_auto2. }
  Defined.

  Lemma and_impl_patt2  (A B C : Pattern) Γ (i : ProofInfo):
    well_formed A → well_formed B → well_formed C →
    Γ ⊢i A using i ->
    Γ ⊢i ((B and A) ---> C) using i ->
    Γ ⊢i (B ---> C) using i.
  Proof.
    intros WFA WFB WFC H H0.
    eapply syllogism_meta with (B := patt_and B A).
    { wf_auto2. }
    { wf_auto2. }
    { wf_auto2. }
    2: exact H0.
    apply conj_intro_meta_partial2.
    { wf_auto2. }
    { wf_auto2. }
    exact H.
  Defined.


  Lemma patt_and_comm_meta (A B : Pattern) (Γ : Theory) (i : ProofInfo) :
    well_formed A → well_formed B
    ->
    Γ ⊢i A and B using i ->
    Γ ⊢i B and A using i.
  Proof.
    intros WFA WFB H.
    apply pf_conj_elim_r_meta in H as P1.
    apply pf_conj_elim_l_meta in H as P2. all: try_wfauto2.
    apply conj_intro_meta; assumption.
  Defined.

  Lemma MLGoal_applyMeta Γ r r' i:
    Γ ⊢i (r' ---> r) using i ->
    forall l,
    @mkMLGoal Σ Γ l r' i ->
    @mkMLGoal Σ Γ l r i.
  Proof.
    intros Himp l H.
    unfold of_MLGoal in *. simpl in *.
    intros wfr wfl.
    eapply prf_weaken_conclusion_iter_meta_meta.
    4: apply Himp.
    4: apply H.
    all: try assumption.
    1,2: pose proof (wfrr' := proved_impl_wf _ _ (proj1_sig Himp)); wf_auto2.
  Defined.

End FOL_helpers.


Tactic Notation "mlApplyMeta" uconstr(t) :=
  eapply (@MLGoal_applyMeta _ _ _ _ _ t).

Lemma MLGoal_left {Σ : Signature} Γ l x y i:
  @mkMLGoal Σ Γ l x i ->
  @mkMLGoal Σ Γ l (patt_or x y) i.
Proof.
  intros H.
  unfold of_MLGoal in *. simpl in *.
  intros wfxy wfl.
  eapply prf_weaken_conclusion_iter_meta_meta.
  4: { useBasicReasoning. apply disj_left_intro. wf_auto2. wf_auto2. }
  { wf_auto2. }
  { wf_auto2. }
  { wf_auto2. }
  apply H.
  { wf_auto2. }
  { assumption. }
Defined.

Lemma MLGoal_right {Σ : Signature} Γ l x y i:
  @mkMLGoal Σ Γ l y i ->
  @mkMLGoal Σ Γ l (patt_or x y) i.
Proof.
  intros H.
  unfold of_MLGoal in *. simpl in *.
  intros wfxy wfl.
  eapply prf_weaken_conclusion_iter_meta_meta.
  4: { useBasicReasoning. apply disj_right_intro. wf_auto2. wf_auto2. }
  { wf_auto2. }
  { wf_auto2. }
  { wf_auto2. }
  apply H.
  { wf_auto2. }
  { assumption. }
Defined.

Ltac mlLeft := apply MLGoal_left.
Ltac mlRight := apply MLGoal_right.

Example ex_mlLeft {Σ : Signature} Γ a:
  well_formed a ->
  Γ ⊢i a ---> (a or a)
  using BasicReasoning.
Proof.
  intros wfa.
  toMLGoal.
  { wf_auto2. }
  mlIntro.
  mlLeft.
Abort.

Lemma MLGoal_applyMetaIn {Σ : Signature} Γ r r' i:
  Γ ⊢i (r ---> r') using i ->
  forall l₁ l₂ g,
    @mkMLGoal Σ Γ (l₁ ++ r'::l₂) g i ->
    @mkMLGoal Σ Γ (l₁ ++ r::l₂ ) g i.
Proof.
  intros Himp l₁ l₂ g H.
  unfold of_MLGoal in *. simpl in *.
  intros wfg Hwf.
  specialize (H wfg).
  eapply prf_strenghten_premise_iter_meta_meta.
  6: apply Himp.
  6: apply H.
  { abstract (apply wfapp_proj_1 in Hwf; exact Hwf). }
  { abstract (apply wfl₁hl₂_proj_l₂ in Hwf; exact Hwf). }
  { abstract (pose proof (Himp' := proj1_sig Himp); apply proved_impl_wf in Himp'; wf_auto2). }
  { abstract (apply wfl₁hl₂_proj_h in Hwf; exact Hwf). }
  { exact wfg. }
  { abstract(
      pose proof (wfapp_proj_1 Hwf);
      pose proof (wfl₁hl₂_proj_l₂ Hwf);
      pose proof (wfl₁hl₂_proj_h Hwf);
      unfold Pattern.wf;
      rewrite map_app;
      rewrite foldr_app;
      simpl;
      pose proof (Himp' := proj1_sig Himp);
      apply proved_impl_wf in Himp';
      apply well_formed_imp_proj2 in Himp';
      rewrite Himp';
      simpl;
      unfold Pattern.wf in H1;
      rewrite H1;
      exact H0
    ).
 }
Defined.

Tactic Notation "mlApplyMeta" uconstr(t) "in" constr(n) :=
  eapply cast_proof_ml_hyps;
  [(let hyps := fresh "hyps" in
    rewrite <- (firstn_skipn n);
    rewrite [hyps in (hyps ++ _)]/=;
    rewrite [hyps in (_ ++ hyps)]/=;
    reflexivity
   )|];
  eapply (@MLGoal_applyMetaIn _ _ _ _ _ t);
  eapply cast_proof_ml_hyps;
  [(rewrite /app; reflexivity)|].

Local Example Private_ex_mlApplyMetaIn {Σ : Signature} Γ p q:
  well_formed p ->
  well_formed q ->
  Γ ⊢i p ---> (p or q)
  using BasicReasoning.
Proof.
  intros wfp wfq.
  toMLGoal.
  { wf_auto2. }
  mlIntro.
  mlApplyMeta (@disj_left_intro Σ Γ p q ltac:(wf_auto2) ltac:(wf_auto2)) in 0.
  mlExactn 0.
Defined.

Lemma MLGoal_destructAnd {Σ : Signature} Γ g l₁ l₂ x y i:
    @mkMLGoal Σ Γ (l₁ ++ x::y::l₂ ) g i ->
    @mkMLGoal Σ Γ (l₁ ++ (x and y)::l₂) g i .
Proof.
  intros H.
  unfold of_MLGoal. intros wfg Hwf. pose proof (wfg' := wfg). pose proof (Hwf' := Hwf).
  revert wfg' Hwf'.
  cut (of_MLGoal (@mkMLGoal Σ Γ (l₁ ++ (x and y)::l₂ ) g i)).
  { auto. }
  simpl in wfg, Hwf.

  mlAssert (y) using first (length (l₁ ++ [x and y])).
  { abstract (
      apply wfapp_proj_2 in Hwf;
      unfold Pattern.wf in Hwf;
      simpl in Hwf;
      apply andb_prop in Hwf;
      destruct Hwf as [wfxy _];
      wf_auto2
    ).
  }
  {
    eapply cast_proof_ml_hyps.
    { replace (l₁ ++ (x and y) :: l₂) with ((l₁++ [x and y]) ++ l₂).
      2: { rewrite -app_assoc. reflexivity. }
      rewrite take_app.
      reflexivity.
    }
    assert (well_formed x).
    {
      abstract (
        apply wfapp_proj_2 in Hwf;
        unfold Pattern.wf in Hwf;
        simpl in Hwf;
        apply andb_prop in Hwf as [wfxy _];
        wf_auto2
      ).
    }
    useBasicReasoning.
    mlApplyMeta (@pf_conj_elim_r Σ Γ x y ltac:(assumption) ltac:(assumption)).
    apply MLGoal_exactn.
  }

  eapply cast_proof_ml_hyps.
  {  
    replace (l₁ ++ (x and y) :: l₂) with ((l₁++ [x and y]) ++ l₂).
    2: { rewrite -app_assoc. reflexivity. }
    rewrite take_app. rewrite drop_app. reflexivity.
  }

  mlAssert (x) using first (length (l₁ ++ [x and y])).
  { abstract (
      apply wfapp_proj_2 in Hwf;
      unfold Pattern.wf in Hwf;
      simpl in Hwf;
      apply andb_prop in Hwf;
      destruct Hwf as [wfxy _];
      wf_auto2
    ).
  }
  {
    eapply cast_proof_ml_hyps.
    {
      replace (l₁ ++ (x and y) :: l₂) with ((l₁++ [x and y]) ++ l₂).
      2: { rewrite -app_assoc. reflexivity. }
      rewrite take_app.
      reflexivity.
    }
    assert (well_formed x).
    {
      abstract (
        apply wfapp_proj_2 in Hwf;
        unfold Pattern.wf in Hwf;
        simpl in Hwf;
        apply andb_prop in Hwf as [wfxy _];
        wf_auto2
      ).
    }
    useBasicReasoning.
    mlApplyMeta (@pf_conj_elim_l Σ Γ x y ltac:(assumption) ltac:(assumption)).
    apply MLGoal_exactn.
  }

  eapply cast_proof_ml_hyps.
  {  
    replace (l₁ ++ (x and y) :: l₂) with ((l₁++ [x and y]) ++ l₂).
    2: { rewrite -app_assoc. reflexivity. }
    rewrite take_app. rewrite drop_app. reflexivity.
  }

  eapply cast_proof_ml_hyps.
  {
    rewrite -app_assoc. reflexivity.
  }

 apply myGoal_clear_hyp.  
 exact H.
Defined.

Tactic Notation "mlDestructAnd" constr(n) :=
  eapply cast_proof_ml_hyps;
  [(let hyps := fresh "hyps" in
    rewrite <- (firstn_skipn n);
    rewrite [hyps in (hyps ++ _)]/=;
    rewrite [hyps in (_ ++ hyps)]/=;
    reflexivity
   )|];
  apply MLGoal_destructAnd;
  eapply cast_proof_ml_hyps;
  [(rewrite /app; reflexivity)|].

Local Example ex_mlDestructAnd {Σ : Signature} Γ a b p q:
  well_formed a ->
  well_formed b ->
  well_formed p ->
  well_formed q ->
  Γ ⊢i p and q ---> a and b ---> q ---> a
  using BasicReasoning.
Proof.
  intros. toMLGoal.
  { wf_auto2. }
  do 3 mlIntro.
  mlDestructAnd 1.
  mlDestructAnd 0.
  mlExactn 2.
Defined.

Section FOL_helpers.
  
  Context {Σ : Signature}.
  
  Lemma and_of_equiv_is_equiv Γ p q p' q' i:
    well_formed p ->
    well_formed q ->
    well_formed p' ->
    well_formed q' ->
    Γ ⊢i (p <---> p') using i ->
    Γ ⊢i (q <---> q') using i ->
    Γ ⊢i ((p and q) <---> (p' and q')) using i.
  Proof.
    intros wfp wfq wfp' wfq' pep' qeq'.
    pose proof (pip' := pep'). apply pf_conj_elim_l_meta in pip'; auto.
    pose proof (p'ip := pep'). apply pf_conj_elim_r_meta in p'ip; auto.
    pose proof (qiq' := qeq'). apply pf_conj_elim_l_meta in qiq'; auto.
    pose proof (q'iq := qeq'). apply pf_conj_elim_r_meta in q'iq; auto.
    
    apply conj_intro_meta; auto.
    - toMLGoal.
      { wf_auto2. }
      mlIntro. unfold patt_and.
      mlIntro. mlApply 0.
      mlDestructOr 1.
      + apply modus_tollens in pip'; auto 10.
        mlAdd pip'.
        mlLeft.
        mlApply 0.
        mlExactn 2.
      + apply modus_tollens in qiq'; auto 10.
        mlAdd qiq'.
        mlRight.
        mlApply 0.
        mlExactn 2.
    - toMLGoal.
      { wf_auto2. }
      mlIntro. unfold patt_and.
      mlIntro. mlApply 0.
      mlDestructOr 1.
      + mlLeft.
        apply modus_tollens in p'ip; auto.
        mlAdd p'ip.
        mlApply 0.
        mlExactn 2.
      + mlRight.
        apply modus_tollens in q'iq; auto.
        mlAdd q'iq.
        mlApply 0.
        mlExactn 2.
  Defined. 

  Lemma or_of_equiv_is_equiv Γ p q p' q' i:
    well_formed p ->
    well_formed q ->
    well_formed p' ->
    well_formed q' ->
    Γ ⊢i (p <---> p') using i ->
    Γ ⊢i (q <---> q') using i ->
    Γ ⊢i ((p or q) <---> (p' or q')) using i.
  Proof with try_wfauto2.
    intros wfp wfq wfp' wfq' pep' qeq'.
    pose proof (pip' := pep'). apply pf_conj_elim_l_meta in pip'...
    pose proof (p'ip := pep'). apply pf_conj_elim_r_meta in p'ip...
    pose proof (qiq' := qeq'). apply pf_conj_elim_l_meta in qiq'...
    pose proof (q'iq := qeq'). apply pf_conj_elim_r_meta in q'iq...
    
    apply conj_intro_meta; auto.
    - toMLGoal.
      { auto. }
      mlIntro.
      mlDestructOr 0.
      + mlLeft. fromMLGoal. assumption.
      + mlRight. fromMLGoal. assumption.
    - toMLGoal.
      { auto. }
      mlIntro.
      mlDestructOr 0.
      + mlLeft. fromMLGoal. assumption.
      + mlRight. fromMLGoal. assumption.
  Defined.

End FOL_helpers.


(* TODO this should have a different name, and we should give the name [mlSplit] to a tactic
  that works with our goals *)
(*Ltac mlSplit := apply conj_intro_meta; auto.*)

Section FOL_helpers.

  Context {Σ : Signature}.

  
  Lemma impl_iff_notp_or_q Γ p q:
    well_formed p ->
    well_formed q ->
    Γ ⊢i ((p ---> q) <---> (! p or q))
    using BasicReasoning.
  Proof.
    intros wfp wfq.
    apply conj_intro_meta; auto.
    - toMLGoal.
      { wf_auto2. }
      mlIntro.
      mlAdd (@A_or_notA Σ Γ p wfp).
      mlDestructOr 0.
      + mlRight.
        mlApply 1.
        mlExactn 0.
      + mlLeft.
        mlExactn 0.
    - toMLGoal.
      { wf_auto2. }
      mlIntro. mlIntro. unfold patt_or.
      mlApply 0.
      mlApplyMeta (@not_not_intro _ _ p wfp).
      mlExactn 1.
  Defined.

  Lemma p_and_notp_is_bot Γ p:
    well_formed p ->
    Γ ⊢i (⊥ <---> p and ! p)
    using BasicReasoning.
  Proof.
    intros wfp.
    apply conj_intro_meta; auto.
    - apply bot_elim; auto.
    - unfold patt_and.
      toMLGoal.
      { wf_auto2. }
      mlIntro.
      mlApply 0.
      mlAdd (@A_or_notA Σ Γ (! p) ltac:(wf_auto2)).
      mlExactn 0.
  Defined.

  Lemma weird_lemma Γ A B L R:
    well_formed A ->
    well_formed B ->
    well_formed L ->
    well_formed R ->
    Γ ⊢i (((L and A) ---> (B or R)) ---> (L ---> ((A ---> B) or R)))
    using BasicReasoning.
  Proof.
    intros wfA wfB wfL wfR.
    toMLGoal.
    { wf_auto2. }
    mlIntro. mlIntro.
    mlAdd (@A_or_notA Σ Γ A wfA).
    mlDestructOr 0.
    - mlAssert ((B or R)).
      { wf_auto2. }
      { mlApply 1.
        unfold patt_and at 2.
        mlIntro.
        mlDestructOr 3.
        + mlApply 3. mlExactn 2.
        + mlApply 3. mlExactn 0.
      }
      mlDestructOr 3.
      + mlLeft. mlIntro. mlExactn 3.
      + mlRight. mlExactn 3.
    - mlLeft.
      mlIntro.
      mlApplyMeta (@bot_elim Σ _ B wfB).
      mlApply 0. mlExactn 3.
  Defined.

  Lemma weird_lemma_meta Γ A B L R i:
    well_formed A ->
    well_formed B ->
    well_formed L ->
    well_formed R ->
    Γ ⊢i ((L and A) ---> (B or R)) using i ->
    Γ ⊢i (L ---> ((A ---> B) or R)) using i.
  Proof.
    intros WFA WFB WFL WFR H.
    eapply MP.
    2: { useBasicReasoning. apply weird_lemma; assumption. }
    exact H.
  Defined.

  Lemma imp_trans_mixed_meta Γ A B C D i :
    well_formed A -> well_formed B -> well_formed C -> well_formed D ->
    Γ ⊢i (C ---> A) using i ->
    Γ ⊢i (B ---> D) using i ->
    Γ ⊢i ((A ---> B) ---> C ---> D) using i.
  Proof.
    intros WFA WFB WFC WFD H H0.
    epose proof (H1 := @prf_weaken_conclusion Σ Γ A B D WFA WFB WFD).
    eapply useBasicReasoning in H1.
    eapply MP in H1.
    2: { exact H0. }
    epose proof (H2 := @prf_strenghten_premise Σ Γ A C D WFA WFC WFD).
    eapply useBasicReasoning in H2.
    eapply MP in H2.
    2: { exact H. }
    epose proof (H3 := @syllogism_meta Σ Γ _ _ _ i _ _ _ H1 H2).
    exact H3.
    Unshelve. all: wf_auto2.
  Defined.

  Lemma and_weaken A B C Γ i:
    well_formed A -> well_formed B -> well_formed C ->
    Γ ⊢i (B ---> C) using i ->
    Γ ⊢i ((A and B) ---> (A and C)) using i.
  Proof.
    intros WFA WFB WFC H.
    epose proof (H0 := @and_impl' Σ Γ A B (A and C) _ _ _).
    eapply MP. 2: { useBasicReasoning. exact H0. }
    apply reorder_meta.
    1-3: wf_auto2.
    epose proof (H1 := @prf_strenghten_premise Σ Γ C B (A ---> A and C) _ _ _).
    eapply MP.
    2: eapply MP.
    3: { useBasicReasoning. exact H1. }
    2: { exact H. }
    useBasicReasoning.
    apply conj_intro2; assumption.
    Unshelve.
    all: wf_auto2.
  Defined.

  Lemma impl_and Γ A B C D i: 
    well_formed A -> well_formed B -> well_formed C -> well_formed D ->
    Γ ⊢i (A ---> B) using i ->
    Γ ⊢i (C ---> D) using i ->
    Γ ⊢i (A and C) ---> (B and D) using i.
  Proof.
    intros WFA WFB WFC WFD H H0.
    toMLGoal.
    { wf_auto2. }
    {
      mlAdd H.
      mlAdd H0.
      mlIntro.
      mlDestructAnd 2.
      mlIntro.
      mlDestructOr 4.
      {
        mlApply 4.
        mlApply 1.
        mlExactn 2.
      }
      {
        mlApply 4.
        mlApply 0.
        mlExactn 3.
      }
    }
  Defined.

  Lemma and_drop A B C Γ i:
    well_formed A -> well_formed B -> well_formed C ->
    Γ ⊢i ((A and B) ---> C) using i ->
    Γ ⊢i ((A and B) ---> (A and C)) using i.
  Proof.
    intros WFA WFB WFC H.
    toMLGoal.
    { wf_auto2. }
    mlAdd H.
    mlIntro.
    mlIntro.
    mlDestructOr 2.
    {
      mlDestructAnd 1.
      mlApply 3.
      mlExactn 1.
    }
    {
      mlApply 2.
      mlApply 0.
      mlExactn 1.
    }
  Defined.

  Lemma universal_generalization Γ ϕ x (i : ProofInfo) :
    ProofInfoLe ( (ExGen := {[x]}, SVSubst := ∅, KT := false, FP := ∅)) i ->
    well_formed ϕ ->
    Γ ⊢i ϕ using i ->
    Γ ⊢i patt_forall (evar_quantify x 0 ϕ) using i.
  Proof.
    intros pile wfϕ Hϕ.
    unfold patt_forall.
    unfold patt_not at 1.
    replace (! evar_quantify x 0 ϕ)
      with (evar_quantify x 0 (! ϕ))
      by reflexivity.
    apply Ex_gen.
    { exact pile. }
    { simpl. set_solver. }
    toMLGoal.
    { wf_auto2. }
    mlIntro. mlAdd Hϕ.
    mlApply 1. mlExactn 0.
  Defined.

  (*Hint Resolve evar_quantify_well_formed.*)

  Lemma forall_variable_substitution Γ ϕ x:
    well_formed ϕ ->
    Γ ⊢i (all, evar_quantify x 0 ϕ) ---> ϕ
    using ( (ExGen := {[x]}, SVSubst := ∅, KT := false, FP := ∅)).
  Proof.
    intros wfϕ.
   
    unfold patt_forall.
    replace (! evar_quantify x 0 ϕ)
      with (evar_quantify x 0 (! ϕ))
      by reflexivity.
    apply double_neg_elim_meta.
    { wf_auto2. }
    { wf_auto2. }
    toMLGoal.
    { wf_auto2. }
    mlIntro.
    mlIntro.
    mlApply 0.
    mlIntro.
    mlApply 2.
    pose proof (Htmp := @Ex_quan Σ Γ (evar_quantify x 0 (!ϕ)) x).
    rewrite /instantiate in Htmp.
    rewrite bevar_subst_evar_quantify_free_evar in Htmp.
    {
      simpl. split_and!. now do 2 apply andb_true_iff in wfϕ as [_ wfϕ]. reflexivity.
    }
    specialize (Htmp ltac:(wf_auto2)).
    useBasicReasoning.
    mlAdd Htmp.
    mlApply 0.
    mlIntro.
    mlApply 2.
    mlExactn 4.
  Defined.

End FOL_helpers.

Lemma pile_impl_uses_kt {Σ : Signature} gpi evs svs fp:
  ProofInfoLe ( (ExGen := evs, SVSubst := svs, KT := true, FP := fp)) ( gpi) ->
  pi_uses_kt gpi.
Proof.
  intros [H].
  specialize (H ∅).
  pose (pf1 := @A_impl_A Σ ∅ patt_bott ltac:(wf_auto2)).
  pose (pf2 := @ProofSystem.Knaster_tarski Σ ∅ (patt_bound_svar 0) patt_bott ltac:(wf_auto2) (proj1_sig pf1)).
  specialize (H _ pf2).
  feed specialize H.
  {
    constructor; simpl.
    { set_solver. }
    { set_solver. }
    reflexivity.
    { clear. set_solver. }
  }
  destruct H as [H1 H2 H3 H4].
  unfold pf2 in H3. simpl in H3. exact H3.
Qed.


Lemma Knaster_tarski {Σ : Signature}
  (Γ : Theory) (ϕ ψ : Pattern)  (i : ProofInfo)
  {pile : ProofInfoLe (
        {| pi_generalized_evars := ∅;
           pi_substituted_svars := ∅;
           pi_uses_kt := true ;
           pi_framing_patterns := ∅ ;
        |}) i} :
well_formed (mu, ϕ) ->
Γ ⊢i (instantiate (mu, ϕ) ψ) ---> ψ using i ->
Γ ⊢i mu, ϕ ---> ψ using i.
Proof.
intros Hfev [pf Hpf].
unshelve (eexists).
{
  apply ProofSystem.Knaster_tarski.
  { exact Hfev. }
  { exact pf. }
}
{
  simpl.
  constructor; simpl.
  {
    destruct Hpf as [Hpf2 Hpf3 Hpf4].
    apply Hpf2.
  }
  {
    destruct Hpf as [Hpf2 Hpf3 Hpf4].
    apply Hpf3.
  }
  {
    destruct Hpf as [Hpf2 Hpf3 Hpf4].
    pose proof (Hpile := @pile_impl_uses_kt _ _ _ _ _ pile).
    exact Hpile.
  }
  {
    destruct Hpf as [Hpf2 Hpf3 Hpf4 Hpf5].
    apply Hpf5.
  }
}
Defined.



Lemma pile_impl_allows_svsubst_X {Σ : Signature} gpi evs X kt fp:
  ProofInfoLe ( (ExGen := evs, SVSubst := {[X]}, KT := kt, FP := fp)) ( gpi) ->
  X ∈ pi_substituted_svars gpi.
Proof.
  intros [H].
  specialize (H ∅).
  pose (pf1 := @A_impl_A Σ ∅ (patt_free_svar X) ltac:(wf_auto2)).
  pose (pf2 := @ProofSystem.Svar_subst Σ ∅ (patt_free_svar X ---> patt_free_svar X) patt_bott X ltac:(wf_auto2) ltac:(wf_auto2) (proj1_sig pf1)).
  specialize (H _ pf2).
  feed specialize H.
  {
    constructor; simpl.
    { set_solver. }
    { set_solver. }
    reflexivity.
    { clear. set_solver. }
  }
  destruct H as [H1 H2 H3 H4].
  simpl in *.
  clear -H2. set_solver.
Qed.

Lemma Svar_subst {Σ : Signature}
  (Γ : Theory) (ϕ ψ : Pattern) (X : svar)  (i : ProofInfo)
  {pile : ProofInfoLe (
        {| pi_generalized_evars := ∅;
           pi_substituted_svars := {[X]};
           pi_uses_kt := false ;
           pi_framing_patterns := ∅ ;
        |}) i} :
  well_formed ψ ->
  Γ ⊢i ϕ using i ->
  Γ ⊢i (free_svar_subst ϕ ψ X) using i.
Proof.
  intros wfψ [pf Hpf].
  unshelve (eexists).
  {
   apply ProofSystem.Svar_subst.
   { pose proof (Hwf := @proved_impl_wf _ _ _ pf). exact Hwf. }
   { exact wfψ. }
   { exact pf. }
  }
{
  simpl.
  constructor; simpl.
  {
    destruct Hpf as [Hpf2 Hpf3 Hpf4].
    apply Hpf2.
  }
  {
    destruct Hpf as [Hpf2 Hpf3 Hpf4].
    pose proof (Hpile := @pile_impl_allows_svsubst_X _ _ _ _ _ _ pile).
    clear -Hpile Hpf3.
    set_solver.
  }
  {
    destruct Hpf as [Hpf2 Hpf3 Hpf4].
    exact Hpf4.
  }
  {
    destruct Hpf as [Hpf2 Hpf3 Hpf4 Hpf5].
    exact Hpf5.
  }
}
Defined.

Lemma Pre_fixp {Σ : Signature}
  (Γ : Theory) (ϕ : Pattern) :
  well_formed (patt_mu ϕ) ->
  Γ ⊢i (instantiate (patt_mu ϕ) (patt_mu ϕ) ---> (patt_mu ϕ))
  using BasicReasoning.
Proof.
  intros wfϕ.
  unshelve (eexists).
  {
    apply ProofSystem.Pre_fixp.
    { exact wfϕ. }
  }
  {
    simpl.
    constructor; simpl.
    { set_solver. }
    { set_solver. }
    { reflexivity. }
    { apply reflexivity. }
  }
Defined.

Section FOL_helpers.

  Context {Σ : Signature}.

  Lemma mu_monotone Γ ϕ₁ ϕ₂ X (i : ProofInfo):
    ProofInfoLe ( (ExGen := ∅, SVSubst := {[X]}, KT := true, FP := ∅)) i ->
    svar_has_negative_occurrence X ϕ₁ = false ->
    svar_has_negative_occurrence X ϕ₂ = false ->
    Γ ⊢i ϕ₁ ---> ϕ₂ using i->
    Γ ⊢i (patt_mu (svar_quantify X 0 ϕ₁)) ---> (patt_mu (svar_quantify X 0 ϕ₂))
    using i.
  Proof.
    intros pile nonegϕ₁ nonegϕ₂ Himp.
    pose proof (wfϕ12 := @proved_impl_wf _ _ _ (proj1_sig Himp)).
    assert(wfϕ₁ : well_formed ϕ₁) by wf_auto2.
    assert(wfϕ₂ : well_formed ϕ₂) by wf_auto2.

    apply Knaster_tarski.
    { eapply pile_trans. 2: apply pile. apply pile_svs_subseteq. set_solver. }
    { wf_auto2. }

    pose proof (Htmp := @Svar_subst Σ Γ (ϕ₁ ---> ϕ₂) (mu, svar_quantify X 0 ϕ₂) X i).
    feed specialize Htmp.
    { eapply pile_trans. 2: apply pile. apply pile_kt_impl. simpl. reflexivity. }
    { wf_auto2. }
    { exact Himp. }
    unfold free_svar_subst in Htmp.
    simpl in Htmp.
    fold free_svar_subst in Htmp.

    pose proof (Hpf := @Pre_fixp Σ Γ (svar_quantify X 0 ϕ₂)).
    simpl in Hpf.

    unshelve (eapply (@cast_proof' Σ Γ _ _) in Hpf).
    3: { 
    erewrite bound_to_free_set_variable_subst.
      5: { apply svar_quantify_not_free. }
      4: {
       apply svar_quantify_closed_mu.
       unfold well_formed, well_formed_closed in *. destruct_and!. auto.
      }
      3: {
         apply svar_quantify_closed_mu.
         unfold well_formed, well_formed_closed in *. destruct_and!. auto.
      }
      2: lia.
      reflexivity.
    }

    2: abstract (wf_auto2).

    eapply (@cast_proof' Σ Γ) in Hpf.
    2: {
      rewrite svar_open_svar_quantify.
      { unfold well_formed, well_formed_closed in *. destruct_and!. auto. }
      reflexivity.
    }


    assert(well_formed_positive (free_svar_subst ϕ₂ (mu , svar_quantify X 0 ϕ₂) X) = true).
    {
      unfold well_formed, well_formed_closed in *. destruct_and!. simpl; split_and?.
      apply wfp_free_svar_subst; auto.
      { apply svar_quantify_closed_mu. auto. }
      { simpl. split_and!.
        2: apply well_formed_positive_svar_quantify; assumption.
        apply no_negative_occurrence_svar_quantify; auto.
      }
    }

    assert(well_formed_closed_mu_aux (free_svar_subst ϕ₂ (mu , svar_quantify X 0 ϕ₂) X) 0 = true).
    {
      unfold well_formed, well_formed_closed in *. destruct_and!. simpl; split_and?; auto.
      replace 0 with (0 + 0) at 3 by lia.
      apply wfc_mu_free_svar_subst; auto.
      simpl.
      apply svar_quantify_closed_mu. assumption.
    }
    
    assert(well_formed_closed_ex_aux (free_svar_subst ϕ₂ (mu , svar_quantify X 0 ϕ₂) X) 0 = true).
    {
      unfold well_formed, well_formed_closed in *. destruct_and!. simpl; split_and?; auto.
      replace 0 with (0 + 0) at 3 by lia.
      apply wfc_ex_free_svar_subst; auto.
      simpl.
      apply svar_quantify_closed_ex. assumption.
    }

    assert(well_formed_positive (free_svar_subst ϕ₁ (mu , svar_quantify X 0 ϕ₂) X) = true).
    {
      unfold well_formed, well_formed_closed in *. destruct_and!. simpl; split_and?.
      apply wfp_free_svar_subst; auto.
      { apply svar_quantify_closed_mu. auto. }
      { simpl. split_and!.
        2: apply well_formed_positive_svar_quantify; assumption.
        apply no_negative_occurrence_svar_quantify; auto.
      }
    }

    assert(well_formed_closed_mu_aux (free_svar_subst ϕ₁ (mu , svar_quantify X 0 ϕ₂) X) 0 = true).
    {
      unfold well_formed, well_formed_closed in *. destruct_and!. simpl; split_and?; auto.
      replace 0 with (0 + 0) at 3 by lia.
      apply wfc_mu_free_svar_subst; auto.
      simpl.
      apply svar_quantify_closed_mu. assumption.
    }
    
    assert(well_formed_closed_ex_aux (free_svar_subst ϕ₁ (mu , svar_quantify X 0 ϕ₂) X) 0 = true).
    {
      unfold well_formed, well_formed_closed in *. destruct_and!. simpl; split_and?; auto.
      replace 0 with (0 + 0) at 3 by lia.
      apply wfc_ex_free_svar_subst; auto.
      simpl.
      apply svar_quantify_closed_ex. assumption.
    }
    
    apply useBasicReasoning with (i := i) in Hpf.
    epose proof (Hsi := @syllogism_meta Σ _ _ _ _ _ _ _ _ Htmp Hpf).
    simpl.

    eapply (@cast_proof' Σ Γ).
    1: {
      erewrite bound_to_free_set_variable_subst with (X := X).
      5: { apply svar_quantify_not_free. }
      4: {
           apply svar_quantify_closed_mu.
           unfold well_formed, well_formed_closed in *. destruct_and!. auto.
      }
      3: {
           apply svar_quantify_closed_mu.
           unfold well_formed, well_formed_closed in *. destruct_and!. auto.
      }
      2: lia.
      reflexivity.
    }

    eapply (@cast_proof' Σ Γ).
    1: {
      rewrite svar_open_svar_quantify.
      { unfold well_formed, well_formed_closed in *. destruct_and!. auto. }
      reflexivity.
    }
    apply Hsi.
    Unshelve.
    all: abstract(wf_auto2).
  Defined.

  Lemma prf_equiv_of_impl_of_equiv Γ a b a' b' i:
    well_formed a = true ->
    well_formed b = true ->
    well_formed a' = true ->
    well_formed b' = true ->
    Γ ⊢i (a <---> a') using i ->
    Γ ⊢i (b <---> b') using i ->
    Γ ⊢i (a ---> b) <---> (a' ---> b') using i
  .
  Proof.
    intros wfa wfb wfa' wfb' Haa' Hbb'.
    unshelve(epose proof (Haa'1 := @pf_conj_elim_l_meta _ _ _ _ _ _ _ Haa')).
    { wf_auto2. }
    { wf_auto2. }
    unshelve(epose proof (Haa'2 := @pf_conj_elim_r_meta _ _ _ _ _ _ _ Haa')).
    { wf_auto2. }
    { wf_auto2. }
    unshelve(epose proof (Hbb'1 := @pf_conj_elim_l_meta _ _ _ _ _ _ _ Hbb')).
    { wf_auto2. }
    { wf_auto2. }
    unshelve(epose proof (Hbb'2 := @pf_conj_elim_r_meta _ _ _ _ _ _ _ Hbb')).
    { wf_auto2. }
    { wf_auto2. }

    apply pf_iff_equiv_trans with (B := (a ---> b')).
    1-3: wf_auto2.
      + apply conj_intro_meta.
        1-2: wf_auto2.
        * toMLGoal.
          { wf_auto2. }
          mlIntro. mlIntro.
          mlAdd Hbb'1.
          mlApply 0.
          mlApply 1.
          mlExactn 2.
        * toMLGoal.
          { wf_auto2. }
          mlIntro. mlIntro.
          mlAdd Hbb'2.
          mlApply 0.
          mlApply 1.
          mlExactn 2.
      + apply conj_intro_meta.
        1-2: wf_auto2.
        * toMLGoal.
          { wf_auto2. }
          mlIntro. mlIntro.
          mlAdd Haa'2.
          mlApply 1.
          mlApply 0.
          mlExactn 2.
        * toMLGoal.
          { wf_auto2. }
          mlIntro. mlIntro.
          mlAdd Haa'1.
          mlApply 1.
          mlApply 0.
          mlExactn 2.
  Defined.

  Lemma pf_evar_open_free_evar_subst_equiv_sides Γ x n ϕ p q E i:
    x <> E ->
    well_formed p = true ->
    well_formed q = true ->
    Γ ⊢i free_evar_subst (evar_open n x ϕ) p E <---> free_evar_subst (evar_open n x ϕ) q E using i ->
    Γ ⊢i evar_open n x (free_evar_subst ϕ p E) <---> evar_open n x (free_evar_subst ϕ q E) using i.
  Proof.
    intros Hx wfp wfq H.
    unshelve (eapply (@cast_proof' Σ Γ _ _ _ _ H)).
    rewrite -> evar_open_free_evar_subst_swap by assumption.
    rewrite -> evar_open_free_evar_subst_swap by assumption.
    reflexivity.
  Defined.

  Lemma strip_exists_quantify_l Γ x P Q i :
    x ∉ free_evars P ->
    well_formed_closed_ex_aux P 1 ->
    Γ ⊢i (exists_quantify x (evar_open 0 x P) ---> Q) using i ->
    Γ ⊢i ex , P ---> Q using i.
  Proof.
    intros Hx HwfcP H.
    unshelve (eapply (@cast_proof' Σ Γ _ _ _ _ H)).
    abstract (
      unfold exists_quantify;
      rewrite -> evar_quantify_evar_open by assumption;
      reflexivity
    ).
  Defined.

  Lemma strip_exists_quantify_r Γ x P Q i :
    x ∉ free_evars Q ->
    well_formed_closed_ex_aux Q 1 ->
    Γ ⊢i P ---> (exists_quantify x (evar_open 0 x Q)) using i ->
    Γ ⊢i P ---> ex, Q using i.
  Proof.
    intros Hx HwfcP H.
    unshelve (eapply (@cast_proof' Σ Γ _ _ _ _ H)).
    abstract (
      unfold exists_quantify;
      rewrite -> evar_quantify_evar_open by assumption;
      reflexivity
    ).
  Defined.

  Lemma pf_iff_free_evar_subst_svar_open_to_bsvar_subst_free_evar_subst Γ ϕ p q E X i:
    well_formed_closed_mu_aux p 0 = true ->
    well_formed_closed_mu_aux q 0 = true ->
    Γ ⊢i free_evar_subst (svar_open 0 X ϕ) p E <---> free_evar_subst (svar_open 0 X ϕ) q E using i ->
    Γ ⊢i bsvar_subst (free_evar_subst ϕ p E) (patt_free_svar X) 0 <--->
        bsvar_subst (free_evar_subst ϕ q E) (patt_free_svar X) 0 using i.
  Proof.
    intros wfp wfq H.
    unshelve (eapply (@cast_proof' _ _ _ _ _ _ H)).

    abstract (
      unfold svar_open in H;
      rewrite <- free_evar_subst_bsvar_subst;
      [idtac|wf_auto| unfold evar_is_fresh_in; simpl; clear; set_solver];
      rewrite <- free_evar_subst_bsvar_subst;
      [idtac|wf_auto|unfold evar_is_fresh_in; simpl; clear; set_solver];
      reflexivity
   ).
  Defined.

  Lemma pf_iff_mu_remove_svar_quantify_svar_open Γ ϕ p q E X i :
    well_formed_closed_mu_aux (free_evar_subst ϕ p E) 1 ->
    well_formed_closed_mu_aux (free_evar_subst ϕ q E) 1 ->
    X ∉ free_svars (free_evar_subst ϕ p E) ->
    X ∉ free_svars (free_evar_subst ϕ q E) ->
    Γ ⊢i mu , svar_quantify X 0 (svar_open 0 X (free_evar_subst ϕ p E)) <--->
        mu , svar_quantify X 0 (svar_open 0 X (free_evar_subst ϕ q E)) using i ->
    Γ ⊢i mu , free_evar_subst ϕ p E <---> mu , free_evar_subst ϕ q E using i.
  Proof.
    intros wfp' wfq' Xfrp Xfrq H.
    unshelve (eapply (@cast_proof' _ _ _ _ _ _ H)).
    abstract (
      rewrite -{1}[free_evar_subst ϕ p E](@svar_quantify_svar_open _ X 0); [assumption| auto | auto];
      rewrite -{1}[free_evar_subst ϕ q E](@svar_quantify_svar_open _ X 0); [assumption| auto | auto];
      reflexivity
    ).
  Defined.


End FOL_helpers.

  Add Search Blacklist "_elim".
  Add Search Blacklist "_graph_rect".
  Add Search Blacklist "_graph_mut".
  Add Search Blacklist "FunctionalElimination_".


Section FOL_helpers.

  Context {Σ : Signature}.

  Fixpoint maximal_exists_depth_of_evar_in_pattern' (depth : nat) (E : evar) (ψ : Pattern) : nat :=
    match ψ with
    | patt_bott => 0
    | patt_sym _ => 0
    | patt_bound_evar _ => 0
    | patt_bound_svar _ => 0
    | patt_free_svar _ => 0
    | patt_free_evar E' =>
      match (decide (E' = E)) with
      | left _ => depth
      | right _ => 0
      end
    | patt_imp ψ₁ ψ₂
      => Nat.max
        (maximal_exists_depth_of_evar_in_pattern' depth E ψ₁)
        (maximal_exists_depth_of_evar_in_pattern' depth E ψ₂)
    | patt_app ψ₁ ψ₂
      => Nat.max
        (maximal_exists_depth_of_evar_in_pattern' depth E ψ₁)
        (maximal_exists_depth_of_evar_in_pattern' depth E ψ₂)
    | patt_exists ψ' =>
      maximal_exists_depth_of_evar_in_pattern' (S depth) E ψ'
    | patt_mu ψ' =>
      maximal_exists_depth_of_evar_in_pattern' depth E ψ'
    end.

  Definition maximal_exists_depth_of_evar_in_pattern (E : evar) (ψ : Pattern) : nat :=
    maximal_exists_depth_of_evar_in_pattern' 0 E ψ.

  Definition pf_ite {P : Prop} (i : ProofInfo) (dec: {P} + {~P}) (Γ : Theory) (ϕ : Pattern)
    (pf1: P -> Γ ⊢i ϕ using i)
    (pf2: (~P) -> Γ ⊢i ϕ using i) :
    Γ ⊢i ϕ using i :=
    match dec with
    | left pf => pf1 pf
    | right pf => pf2 pf
    end.

  Lemma evar_fresh_seq_max (EvS : EVarSet) (n1 n2 : nat) :
    (@list_to_set evar EVarSet _ _ _ (evar_fresh_seq EvS n1)) ⊆ (list_to_set (evar_fresh_seq EvS (n1 `max` n2))).
  Proof.
    move: EvS n2.
    induction n1; intros EvS n2.
    {
      simpl. set_solver.
    }
    {
      simpl.
      destruct n2.
      {
        simpl. set_solver.
      }
      {
        simpl.
        cut (@list_to_set evar EVarSet _ _ _ (evar_fresh_seq ({[evar_fresh_s EvS]} ∪ EvS) n1)
        ⊆ list_to_set (evar_fresh_seq ({[evar_fresh_s EvS]} ∪ EvS) (n1 `max` n2))).
        {
          set_solver.
        }
        specialize (IHn1 ({[evar_fresh_s EvS]} ∪ EvS) n2).
        apply IHn1.
      }
    }
  Qed.

  Lemma medoeip_evar_open depth E n x ψ:
    E <> x ->
    maximal_exists_depth_of_evar_in_pattern' depth E (evar_open n x ψ)
    = maximal_exists_depth_of_evar_in_pattern' depth E ψ.
  Proof.
    intros HEnex.
    unfold evar_open.
    move: depth n.
    induction ψ; intros depth n'; simpl; try reflexivity.
    {
      case_match; simpl; try reflexivity.
      case_match; try reflexivity. subst. contradiction.
    }
    {
      rewrite IHψ1. rewrite IHψ2. reflexivity.
    }
    {
      rewrite IHψ1. rewrite IHψ2. reflexivity.
    }
    {
      rewrite IHψ. reflexivity.
    }
    {
      rewrite IHψ. reflexivity.
    }
  Qed.

  Lemma medoeip_svar_open depth E n X ψ:
    maximal_exists_depth_of_evar_in_pattern' depth E (svar_open n X ψ)
    = maximal_exists_depth_of_evar_in_pattern' depth E ψ.
  Proof.
    unfold svar_open.
    move: depth n.
    induction ψ; intros depth n'; simpl; try reflexivity.
    {
      case_match; simpl; try reflexivity.
    }
    {
      rewrite IHψ1. rewrite IHψ2. reflexivity.
    }
    {
      rewrite IHψ1. rewrite IHψ2. reflexivity.
    }
    {
      rewrite IHψ. reflexivity.
    }
    {
      rewrite IHψ. reflexivity.
    }
  Qed.

  Lemma medoeip_notin E ψ depth:
    E ∉ free_evars ψ ->
    maximal_exists_depth_of_evar_in_pattern' depth E ψ = 0.
  Proof.
    intros Hnotin.
    move: E depth Hnotin.
    induction ψ; intros E depth Hnotin; simpl in *; try reflexivity.
    { case_match. set_solver. reflexivity. }
    { rewrite IHψ1. set_solver. rewrite IHψ2. set_solver. reflexivity. }
    { rewrite IHψ1. set_solver. rewrite IHψ2. set_solver. reflexivity. }
    { rewrite IHψ. exact Hnotin. reflexivity. }
    { rewrite IHψ. exact Hnotin. reflexivity. }
  Qed.

  Lemma medoeip_S_in E ψ depth:
    E ∈ free_evars ψ ->
    maximal_exists_depth_of_evar_in_pattern' (S depth) E ψ
    = S (maximal_exists_depth_of_evar_in_pattern' depth E ψ).
  Proof.
    intros Hin.
    move: E depth Hin.
    induction ψ; intros E depth Hin; simpl in *.
    { case_match. reflexivity. set_solver. }
    { set_solver. }
    { set_solver. }
    { set_solver. }
    { set_solver. }
    {
      destruct (decide (E ∈ free_evars ψ1)),(decide (E ∈ free_evars ψ2)).
      {
        rewrite IHψ1. assumption. rewrite IHψ2. assumption. simpl. reflexivity.
      }
      {
        rewrite IHψ1. assumption.
        rewrite [maximal_exists_depth_of_evar_in_pattern' _ _ ψ2]medoeip_notin.
        { assumption. }
        rewrite [maximal_exists_depth_of_evar_in_pattern' _ _ ψ2]medoeip_notin.
        { assumption. }
        simpl.
        rewrite Nat.max_comm.
        simpl.
        reflexivity.
      }
      {
        rewrite IHψ2. assumption.
        rewrite [maximal_exists_depth_of_evar_in_pattern' _ _ ψ1]medoeip_notin.
        { assumption. }
        rewrite [maximal_exists_depth_of_evar_in_pattern' _ _ ψ1]medoeip_notin.
        { assumption. }
        simpl.
        reflexivity.
      }
      {
        exfalso. set_solver.
      }
    }
    { set_solver. }
    {
      destruct (decide (E ∈ free_evars ψ1)),(decide (E ∈ free_evars ψ2)).
      {
        rewrite IHψ1. assumption. rewrite IHψ2. assumption. simpl. reflexivity.
      }
      {
        rewrite IHψ1. assumption.
        rewrite [maximal_exists_depth_of_evar_in_pattern' _ _ ψ2]medoeip_notin.
        { assumption. }
        rewrite [maximal_exists_depth_of_evar_in_pattern' _ _ ψ2]medoeip_notin.
        { assumption. }
        simpl.
        rewrite Nat.max_comm.
        simpl.
        reflexivity.
      }
      {
        rewrite IHψ2. assumption.
        rewrite [maximal_exists_depth_of_evar_in_pattern' _ _ ψ1]medoeip_notin.
        { assumption. }
        rewrite [maximal_exists_depth_of_evar_in_pattern' _ _ ψ1]medoeip_notin.
        { assumption. }
        simpl.
        reflexivity.
      }
      {
        exfalso. set_solver.
      }     
    }
    {
      rewrite IHψ. assumption. reflexivity.
    }
    {
      rewrite IHψ. assumption. reflexivity.
    }
  Qed.


  Fixpoint maximal_mu_depth_of_evar_in_pattern' (depth : nat) (E : evar) (ψ : Pattern) : nat :=
    match ψ with
    | patt_bott => 0
    | patt_sym _ => 0
    | patt_bound_evar _ => 0
    | patt_bound_svar _ => 0
    | patt_free_svar _ => 0
    | patt_free_evar E' =>
      match (decide (E' = E)) with
      | left _ => depth
      | right _ => 0
      end
    | patt_imp ψ₁ ψ₂
      => Nat.max
        (maximal_mu_depth_of_evar_in_pattern' depth E ψ₁)
        (maximal_mu_depth_of_evar_in_pattern' depth E ψ₂)
    | patt_app ψ₁ ψ₂
      => Nat.max
        (maximal_mu_depth_of_evar_in_pattern' depth E ψ₁)
        (maximal_mu_depth_of_evar_in_pattern' depth E ψ₂)
    | patt_exists ψ' =>
      maximal_mu_depth_of_evar_in_pattern' depth E ψ'
    | patt_mu ψ' =>
      maximal_mu_depth_of_evar_in_pattern' (S depth) E ψ'
    end.

  Definition maximal_mu_depth_of_evar_in_pattern (E : evar) (ψ : Pattern) : nat :=
    maximal_mu_depth_of_evar_in_pattern' 0 E ψ.



  Lemma svar_fresh_seq_max (SvS : SVarSet) (n1 n2 : nat) :
    (@list_to_set svar SVarSet _ _ _ (svar_fresh_seq SvS n1)) ⊆ (list_to_set (svar_fresh_seq SvS (n1 `max` n2))).
  Proof.
    move: SvS n2.
    induction n1; intros SvS n2.
    {
      simpl. set_solver.
    }
    {
      simpl.
      destruct n2.
      {
        simpl. set_solver.
      }
      {
        simpl.
        cut (@list_to_set svar SVarSet _ _ _ (svar_fresh_seq ({[svar_fresh_s SvS]} ∪ SvS) n1)
        ⊆ list_to_set (svar_fresh_seq ({[svar_fresh_s SvS]} ∪ SvS) (n1 `max` n2))).
        {
          set_solver.
        }
        specialize (IHn1 ({[svar_fresh_s SvS]} ∪ SvS) n2).
        apply IHn1.
      }
    }
  Qed.

  Lemma mmdoeip_svar_open depth E n X ψ:
    maximal_mu_depth_of_evar_in_pattern' depth E (svar_open n X ψ)
    = maximal_mu_depth_of_evar_in_pattern' depth E ψ.
  Proof.
    unfold svar_open.
    move: depth n.
    induction ψ; intros depth n'; simpl; try reflexivity.
    {
      case_match; simpl; try reflexivity.
    }
    {
      rewrite IHψ1. rewrite IHψ2. reflexivity.
    }
    {
      rewrite IHψ1. rewrite IHψ2. reflexivity.
    }
    {
      rewrite IHψ. reflexivity.
    }
    {
      rewrite IHψ. reflexivity.
    }
  Qed.

  Lemma mmdoeip_evar_open depth E n x ψ:
  E <> x ->
  maximal_mu_depth_of_evar_in_pattern' depth E (evar_open n x ψ)
  = maximal_mu_depth_of_evar_in_pattern' depth E ψ.
Proof.
  intros Hne.
  unfold evar_open.
  move: depth n.
  induction ψ; intros depth n'; simpl; try reflexivity.
  {
    case_match; simpl; try reflexivity.
    case_match; simpl; try reflexivity.
    subst. contradiction.
  }
  {
    rewrite IHψ1. rewrite IHψ2. reflexivity.
  }
  {
    rewrite IHψ1. rewrite IHψ2. reflexivity.
  }
  {
    rewrite IHψ. reflexivity.
  }
  {
    rewrite IHψ. reflexivity.
  }
Qed.


  Lemma mmdoeip_notin E ψ depth:
    E ∉ free_evars ψ ->
    maximal_mu_depth_of_evar_in_pattern' depth E ψ = 0.
  Proof.
    intros Hnotin.
    move: E depth Hnotin.
    induction ψ; intros E depth Hnotin; simpl in *; try reflexivity.
    { case_match. set_solver. reflexivity. }
    { rewrite IHψ1. set_solver. rewrite IHψ2. set_solver. reflexivity. }
    { rewrite IHψ1. set_solver. rewrite IHψ2. set_solver. reflexivity. }
    { rewrite IHψ. exact Hnotin. reflexivity. }
    { rewrite IHψ. exact Hnotin. reflexivity. }
  Qed.

  Lemma mmdoeip_S_in E ψ depth:
    E ∈ free_evars ψ ->
    maximal_mu_depth_of_evar_in_pattern' (S depth) E ψ
    = S (maximal_mu_depth_of_evar_in_pattern' depth E ψ).
  Proof.
    intros Hin.
    move: E depth Hin.
    induction ψ; intros E depth Hin; simpl in *.
    { case_match. reflexivity. set_solver. }
    { set_solver. }
    { set_solver. }
    { set_solver. }
    { set_solver. }
    {
      destruct (decide (E ∈ free_evars ψ1)),(decide (E ∈ free_evars ψ2)).
      {
        rewrite IHψ1. assumption. rewrite IHψ2. assumption. simpl. reflexivity.
      }
      {
      rewrite IHψ1. assumption.
      rewrite [maximal_mu_depth_of_evar_in_pattern' _ _ ψ2]mmdoeip_notin.
      { assumption. }
      rewrite [maximal_mu_depth_of_evar_in_pattern' _ _ ψ2]mmdoeip_notin.
      { assumption. }
      simpl.
      rewrite Nat.max_comm.
      simpl.
      reflexivity.
    }
    {
      rewrite IHψ2. assumption.
      rewrite [maximal_mu_depth_of_evar_in_pattern' _ _ ψ1]mmdoeip_notin.
      { assumption. }
      rewrite [maximal_mu_depth_of_evar_in_pattern' _ _ ψ1]mmdoeip_notin.
      { assumption. }
      simpl.
      reflexivity.
    }
    {
      exfalso. set_solver.
    }
  }
  { set_solver. }
  {
    destruct (decide (E ∈ free_evars ψ1)),(decide (E ∈ free_evars ψ2)).
    {
      rewrite IHψ1. assumption. rewrite IHψ2. assumption. simpl. reflexivity.
    }
    {
    rewrite IHψ1. assumption.
    rewrite [maximal_mu_depth_of_evar_in_pattern' _ _ ψ2]mmdoeip_notin.
    { assumption. }
    rewrite [maximal_mu_depth_of_evar_in_pattern' _ _ ψ2]mmdoeip_notin.
    { assumption. }
    simpl.
    rewrite Nat.max_comm.
    simpl.
    reflexivity.
  }
  {
    rewrite IHψ2. assumption.
    rewrite [maximal_mu_depth_of_evar_in_pattern' _ _ ψ1]mmdoeip_notin.
    { assumption. }
    rewrite [maximal_mu_depth_of_evar_in_pattern' _ _ ψ1]mmdoeip_notin.
    { assumption. }
    simpl.
    reflexivity.
  }
  {
    exfalso. set_solver.
  }
}
{
  rewrite IHψ. assumption. reflexivity.
}
{
  rewrite IHψ. assumption. reflexivity.
}
Qed.


  Lemma congruence_ex_helper Γ E ψ x p q gpi exdepth mudepth EvS SvS
  (HxneqE : x ≠ E)
  (wfψ : well_formed (ex , ψ))
  (wfp : well_formed p)
  (wfq : well_formed q)
  (Heqx : x = evar_fresh (elements EvS))
  (HEinψ: E ∈ free_evars ψ)
  (i': ProofInfo)
  (p_sub_EvS: free_evars p ⊆ EvS)
  (q_sub_EvS: free_evars q ⊆ EvS)
  (ψ_sub_EvS : free_evars ψ ⊆ EvS)
  (Heqi': i' =
        
          (ExGen := list_to_set
                      (evar_fresh_seq EvS
                         (maximal_exists_depth_of_evar_in_pattern' exdepth E
                            (ex , ψ))),
           SVSubst := list_to_set
                        (svar_fresh_seq SvS
                           (maximal_mu_depth_of_evar_in_pattern' mudepth E
                              (ex , ψ))),
           KT := (if
                   decide
                     (0 =
                      maximal_mu_depth_of_evar_in_pattern' mudepth E (ex , ψ))
                  is left _ then false
                  else true),
           FP := ∅
          ))
  (pile: ProofInfoLe i' ( gpi))
  (IH: Γ ⊢i (free_evar_subst (evar_open 0 x ψ) p E) <---> (free_evar_subst (evar_open 0 x ψ) q E)
     using  gpi) :
  (Γ ⊢i ex , (free_evar_subst ψ p E) <---> ex , (free_evar_subst ψ q E) using  gpi).
  Proof.
    apply pf_evar_open_free_evar_subst_equiv_sides in IH.
    2: { exact HxneqE. }
    2: { exact wfp. }
    2: { exact wfq. }
    unshelve (epose proof (IH1 := @pf_iff_proj1 Σ Γ _ _ _ _ _ IH)).
    { abstract (wf_auto2). }
    { abstract (wf_auto2). }
    unshelve (epose proof (IH2 := @pf_iff_proj2 Σ Γ _ _ _ _ _ IH)).
    { abstract (wf_auto2). }
    { abstract (wf_auto2). }

    (* TODO: remove the well-formedness constraints on this lemma*)
    apply pf_iff_split.
    { abstract (wf_auto2). }
    { abstract (wf_auto2). }
    {
      eapply strip_exists_quantify_l.
      3: {
        apply Ex_gen.
        3: {
          eapply syllogism_meta.
          5: {
            useBasicReasoning.
            apply Ex_quan.
            abstract (wf_auto2).
          }
          4: {
              apply IH1.
            }
          { abstract (wf_auto2). }
          { abstract (simpl; wf_auto2; apply wfc_ex_aux_bevar_subst; wf_auto2). }
          { abstract (wf_auto2). }
        }
        {
          abstract (
            subst i';
            eapply pile_trans;
            [|apply pile];
            apply pile_evs_svs_kt;
            [(
            simpl;
            rewrite medoeip_S_in;
            [assumption|];
            simpl;
            unfold evar_fresh_s;
            rewrite -Heqx;
            clear;
            set_solver
            )|(clear; set_solver)
            |reflexivity|(clear; set_solver)]
          ).
        }
        {
          abstract (
            simpl;
            pose proof (Htmp1 := @set_evar_fresh_is_fresh' _ EvS);
            pose proof (Htmp2 := @free_evars_free_evar_subst Σ ψ q E);   
            set_solver
          ).
        }
      }
      {
        abstract (
          simpl;
          pose proof (Htmp1 := @set_evar_fresh_is_fresh' _ EvS);
          pose proof (Htmp := @free_evars_free_evar_subst Σ ψ p E);
          set_solver
        ).
      }
      {
        abstract (wf_auto2).
      }
    }
    (* this block is a symmetric version of the previous block*)
    {
      eapply strip_exists_quantify_l.
      3: {
        apply Ex_gen.
        3: {
          eapply syllogism_meta.
          5: {
            useBasicReasoning.
            apply Ex_quan.
            abstract (wf_auto2).
          }
          4: {
              apply IH2.
            }
          { abstract (wf_auto2). }
          { abstract (simpl; wf_auto2; apply wfc_ex_aux_bevar_subst; wf_auto2). }
          { abstract (wf_auto2). }
        }
        {
          abstract (
            subst i';
            eapply pile_trans;
            [|apply pile];
            apply pile_evs_svs_kt;
            [(
              simpl;
              rewrite medoeip_S_in;
              [assumption|];
              simpl;
              unfold evar_fresh_s;
              rewrite -Heqx;
              clear;
              set_solver
            )
           |(clear; set_solver)
           |(reflexivity)|(clear; set_solver)
            ]).
        }
        {
          abstract (
            simpl;
            pose proof (Htmp1 := @set_evar_fresh_is_fresh' _ EvS);
            pose proof (Htmp := @free_evars_free_evar_subst Σ ψ p E);
            set_solver
          ).
        }
      }
      {
        abstract (
          simpl;
          pose proof (Htmp1 := @set_evar_fresh_is_fresh' _ EvS);
          pose proof (Htmp := @free_evars_free_evar_subst Σ ψ q E);
          set_solver
        ).
      }
      {
        abstract (wf_auto2).
      }
    }
  Defined.

  Equations? frames_on_the_way_to_hole'
  (EvS : EVarSet)
  (SvS : SVarSet)
  (E : evar)
  (ψ p q : Pattern)
  (wfψ : well_formed ψ = true)
  (wfp : well_formed p = true)
  (wfq : well_formed q = true)
  : gset wfPattern
  by wf (size' ψ) lt :=
  @frames_on_the_way_to_hole' EvS SvS E (patt_free_evar _) _ _ _ _ _ := ∅ ;
  
  @frames_on_the_way_to_hole' EvS SvS E (patt_free_svar _) _ _ _ _ _ := ∅ ;
  
  @frames_on_the_way_to_hole' EvS SvS E (patt_bound_evar _) _ _ _ _ _ := ∅ ;
  
  @frames_on_the_way_to_hole' EvS SvS E (patt_bound_svar _) _ _ _ _ _ := ∅ ;
  
  @frames_on_the_way_to_hole' EvS SvS E (patt_sym _) _ _ _ _ _ := ∅ ;
  
  @frames_on_the_way_to_hole' EvS SvS E (patt_bott) _ _ _ _ _ := ∅ ;
  
  @frames_on_the_way_to_hole' EvS SvS E (patt_app ψ1 ψ2) p q _ _ _
    :=
      (@singleton _ _ gset_singleton (exist _ (free_evar_subst ψ1 p E) _))
      ∪ {[(exist _ (free_evar_subst ψ2 p E) _)]}
      ∪ {[(exist _ (free_evar_subst ψ1 q E) _)]}
      ∪ {[(exist _ (free_evar_subst ψ2 q E) _)]}
      ∪ (@frames_on_the_way_to_hole' EvS SvS E ψ1 p q _ _ _)
      ∪ (@frames_on_the_way_to_hole' EvS SvS E ψ2 p q _ _ _) ;

  @frames_on_the_way_to_hole' EvS SvS E (patt_imp ψ1 ψ2) p q _ _ _
  := @union _ gset_union (@frames_on_the_way_to_hole' EvS SvS E ψ1 p q _ _ _)
     (@frames_on_the_way_to_hole' EvS SvS E ψ2 p q _ _ _) ;
  
  @frames_on_the_way_to_hole' EvS SvS E (patt_exists ψ') p q _ _ _
   := (@frames_on_the_way_to_hole' ({[(evar_fresh (elements EvS))]} ∪ EvS) SvS E (evar_open 0 ((evar_fresh (elements EvS))) ψ') p q _ _ _) ;
  
  @frames_on_the_way_to_hole' EvS SvS E (patt_mu ψ') _ _ _ _ _
   := (@frames_on_the_way_to_hole' EvS ({[(svar_fresh (elements SvS))]} ∪ SvS) E (svar_open 0 ((svar_fresh (elements SvS))) ψ') p q _ _ _)
  .
  Proof.
    all: try (abstract (solve [try_wfauto2])).
    all: simpl in *.
    all: try abstract(lia).
    { rewrite evar_open_size'. abstract(lia). }
    { rewrite svar_open_size'. abstract(lia). }
  Defined.

End FOL_helpers.

  Ltac pi_exact H := 
    lazymatch type of H with
    | ?H' =>
      lazymatch goal with
      | [|- ?g] =>
        (cut (H' = g);
        [(let H0 := fresh "H0" in intros H0; rewrite -H0; exact H)|
         (repeat f_equal; try reflexivity; try apply proof_irrel)])
      end
    end.

  Ltac pi_assumption :=
    match goal with
    | [H : _ |- _] => pi_exact H
    end.

  Ltac pi_set_solver := set_solver by (try pi_assumption).

  Section FOL_helpers.

  Context {Σ : Signature}.

  Lemma frames_on_the_way_to_hole'_app_1 EvS SvS E ψ1 ψ2 p q wfψ1 wfψ wfp wfq :
  (@frames_on_the_way_to_hole' Σ EvS SvS E ψ1 p q wfψ1 wfp wfq)
  ⊆
  (@frames_on_the_way_to_hole' Σ EvS SvS E (ψ1 $ ψ2) p q wfψ wfp wfq).
  Proof.
    simp frames_on_the_way_to_hole'.
    pi_set_solver.
  Qed.

  Lemma frames_on_the_way_to_hole'_app_2 EvS SvS E ψ1 ψ2 p q wfψ2 wfψ wfp wfq:
  (@frames_on_the_way_to_hole' Σ EvS SvS E ψ2 p q wfψ2 wfp wfq)
  ⊆
  (@frames_on_the_way_to_hole' Σ EvS SvS E (ψ1 $ ψ2) p q wfψ wfp wfq).
  Proof.
    simp frames_on_the_way_to_hole'.
    pi_set_solver.
  Qed.

  Lemma frames_on_the_way_to_hole'_imp_1 EvS SvS E ψ1 ψ2 p q wfψ1 wfψ wfp wfq :
  (@frames_on_the_way_to_hole' Σ EvS SvS E ψ1 p q wfψ1 wfp wfq)
  ⊆
  (@frames_on_the_way_to_hole' Σ EvS SvS E (ψ1 ---> ψ2) p q wfψ wfp wfq).
  Proof.
    simp frames_on_the_way_to_hole'.
    (*unfold frames_on_the_way_to_hole'_unfold_clause_7.*)
    pi_set_solver.
  Qed.

  Lemma frames_on_the_way_to_hole'_imp_2 EvS SvS E ψ1 ψ2 p q wfψ2 wfψ wfp wfq:
  (@frames_on_the_way_to_hole' Σ EvS SvS E ψ2 p q wfψ2 wfp wfq)
  ⊆
  (@frames_on_the_way_to_hole' Σ EvS SvS E (ψ1 ---> ψ2) p q wfψ wfp wfq).
  Proof.
    simp frames_on_the_way_to_hole'.
    pi_set_solver.
  Qed.
  
  Lemma helper_app_lemma Γ ψ1 ψ2 p q E i
  (wfψ1: well_formed ψ1)
  (wfψ2: well_formed ψ2)
  (wfp: well_formed p)
  (wfq: well_formed q)
  (pile: ProofInfoLe ( (
    ExGen := ∅, 
    SVSubst := ∅, 
    KT := false, 
    FP := {[(exist _ (free_evar_subst ψ1 p E) (well_formed_free_evar_subst_0 E wfp wfψ1))
          ;(exist _ (free_evar_subst ψ1 q E) (well_formed_free_evar_subst_0 E wfq wfψ1))
          ;(exist _ (free_evar_subst ψ2 p E) (well_formed_free_evar_subst_0 E wfp wfψ2))
          ;(exist _ (free_evar_subst ψ2 q E) (well_formed_free_evar_subst_0 E wfq wfψ2))
          ]} )) i )
  (pf₁: Γ ⊢i free_evar_subst ψ1 p E <---> free_evar_subst ψ1 q E using i)
  (pf₂: Γ ⊢i free_evar_subst ψ2 p E <---> free_evar_subst ψ2 q E using i)
  :
  (Γ ⊢i (free_evar_subst ψ1 p E) $ (free_evar_subst ψ2 p E) <---> (free_evar_subst ψ1 q E) $ (free_evar_subst ψ2 q E) using i).
  Proof.
    remember (well_formed_free_evar_subst_0 E wfp wfψ1) as Hwf1.
    remember (well_formed_free_evar_subst_0 E wfq wfψ1) as Hwf2.
    remember (well_formed_free_evar_subst_0 E wfp wfψ2) as Hwf3.
    remember (well_formed_free_evar_subst_0 E wfq wfψ2) as Hwf4.

    eapply pf_iff_equiv_trans.
    5: { 
      apply conj_intro_meta.
      4: {
        eapply Framing_right with (ψ := free_evar_subst ψ1 q E) (wfψ := Hwf2).
        1: { eapply pile_trans. 2: apply pile. try_solve_pile. }
        {
          eapply pf_conj_elim_r_meta in pf₂.
          apply pf₂.
          { abstract (wf_auto2). }
          { abstract (wf_auto2). }
        }
      }
      3: {
        eapply Framing_right with (ψ := free_evar_subst ψ1 q E) (wfψ := Hwf2).
        1: { eapply pile_trans. 2: apply pile. try_solve_pile. }
        {
          eapply pf_conj_elim_l_meta in pf₂.
          apply pf₂.
          { abstract (wf_auto2). }
          { abstract (wf_auto2). }
        }
      }
      {
        abstract (wf_auto2).
      }
      {
        abstract (wf_auto2).
      }
     }
     4: {
      apply conj_intro_meta.
      4: {
        apply Framing_left with (ψ := free_evar_subst ψ2 p E) (wfψ := Hwf3).
        { eapply pile_trans. 2: apply pile. try_solve_pile. }
        {
          eapply pf_conj_elim_r_meta in pf₁.
          apply pf₁.
          { abstract (wf_auto2). }
          { abstract (wf_auto2). }
        }
      }
      3: {
        apply Framing_left with (ψ := free_evar_subst ψ2 p E) (wfψ := Hwf3).
        { eapply pile_trans. 2: apply pile. try_solve_pile. }
        {
          eapply pf_conj_elim_l_meta in pf₁.
          apply pf₁.
          { abstract (wf_auto2). }
          { abstract (wf_auto2). }
        }
      }
      {
        abstract (wf_auto2).
      }
      {
        abstract (wf_auto2).
      }         
     }
     { abstract (wf_auto2). }
     { abstract (wf_auto2). }
     { abstract (wf_auto2). }
  Defined.

  Lemma eq_prf_equiv_congruence
  (sz : nat)
  Γ p q
  (wfp : well_formed p)
  (wfq : well_formed q)
  (EvS : EVarSet)
  (SvS : SVarSet)
  E ψ
  (Hsz: size' ψ <= sz)
  (wfψ : well_formed ψ)
  (p_sub_EvS : (free_evars p) ⊆ EvS)
  (q_sub_EvS : (free_evars q) ⊆ EvS)
  (ψ_sub_EvS : (free_evars ψ) ⊆ EvS)
  (E_in_EvS : E ∈ EvS)
  (p_sub_SvS : (free_svars p) ⊆ SvS)
  (q_sub_SvS : (free_svars q) ⊆ SvS)
  (ψ_sub_SvS : (free_svars ψ) ⊆ SvS)
  (exdepth : nat)
  (mudepth : nat)
  (gpi : ProofInfo)
  (pile : ProofInfoLe
   (
     (ExGen := list_to_set (evar_fresh_seq EvS (maximal_exists_depth_of_evar_in_pattern' exdepth E ψ)),
     SVSubst := list_to_set (svar_fresh_seq SvS (maximal_mu_depth_of_evar_in_pattern' mudepth E ψ)),
     KT := if decide (0 = (maximal_mu_depth_of_evar_in_pattern' mudepth E ψ)) is left _ then false else true,
     FP :=  gset_to_coGset (@frames_on_the_way_to_hole' Σ EvS SvS E ψ p q wfψ wfp wfq)
    )
   )
   ( gpi)
  )
  (pf : Γ ⊢i (p <---> q) using ( gpi)) :
      Γ ⊢i (((free_evar_subst ψ p E) <---> (free_evar_subst ψ q E))) using ( gpi).
  Proof.

    move: ψ wfψ Hsz EvS SvS pile
      p_sub_EvS q_sub_EvS E_in_EvS ψ_sub_EvS
      p_sub_SvS q_sub_SvS ψ_sub_SvS
    .
    induction sz; intros ψ wfψ Hsz EvS SvS pile
      p_sub_EvS q_sub_EvS E_in_EvS ψ_sub_EvS p_sub_SvS q_sub_SvS ψ_sub_SvS.
    abstract (destruct ψ; simpl in Hsz; lia).  

    lazymatch type of pile with
    | ProofInfoLe ?st _ => set (i' := st) in *
    end.
  
    destruct (decide (E ∈ free_evars ψ)) as [HEinψ|HEnotinψ].
    2: {
      eapply cast_proof'.
      {
        rewrite free_evar_subst_no_occurrence.
        {
          apply count_evar_occurrences_0.
          assumption.
        }
        rewrite free_evar_subst_no_occurrence.
        {
          apply count_evar_occurrences_0.
          assumption.
        }
        reflexivity.
      }
      useBasicReasoning.
      apply pf_iff_equiv_refl.
      { abstract (wf_auto2). }
    }

    destruct ψ; simpl in Hsz; simpl.
    {
      destruct (decide (E = x)).
      {
        exact pf.
      }
      {
        useBasicReasoning.
        apply pf_iff_equiv_refl.
        abstract (wf_auto2).
      }
    }
    {
      useBasicReasoning.
      apply pf_iff_equiv_refl.
      abstract (wf_auto2).
    }
    {
      useBasicReasoning.
      apply pf_iff_equiv_refl.
      abstract (wf_auto2).
    }
    {
      useBasicReasoning.
      apply pf_iff_equiv_refl.
      abstract (wf_auto2).
    }
    {
      useBasicReasoning.
      apply pf_iff_equiv_refl.
      abstract (wf_auto2).
    }
    {
      assert (wfψ1 : well_formed ψ1 = true).
      { clear -wfψ. abstract (wf_auto2). }
      assert (size' ψ1 <= sz) by abstract(lia).
      assert (wfψ2 : well_formed ψ2 = true).
      { clear -wfψ. abstract (wf_auto2). }
      assert (size' ψ2 <= sz) by abstract(lia).
      
      pose proof (pf₁ := (IHsz ψ1) ltac:(assumption) ltac:(assumption)).
      specialize (pf₁ EvS SvS).
      feed specialize pf₁.
      {
        abstract (
          eapply pile_trans;[|apply pile];
          subst i';
        apply pile_evs_svs_kt;
        [
        (
          simpl; clear; pose proof (Htmp := evar_fresh_seq_max); set_solver
        )|
        (
          simpl; clear; pose proof (Htmp := svar_fresh_seq_max); set_solver
        )|
        (
          simpl; clear pf₁;
          repeat case_match; simpl; try reflexivity; lia
        )|(simpl; apply frames_on_the_way_to_hole'_app_1)
        ]).
      }
      { exact p_sub_EvS. }
      { exact q_sub_EvS. }
      { exact E_in_EvS. }
      { abstract(
          simpl in ψ_sub_EvS;
          clear -ψ_sub_EvS;
          set_solver
        ).
      }
      { exact p_sub_SvS. }
      { exact q_sub_SvS. }
      { abstract(
          simpl in ψ_sub_SvS;
          clear -ψ_sub_SvS;
          set_solver
        ).
      }
      pose proof (pf₂ := (IHsz ψ2) ltac:(assumption) ltac:(assumption)).
      specialize (pf₂ EvS SvS).
      feed specialize pf₂.
      {
        abstract (subst i';
          eapply pile_trans;[|(apply pile)];
          simpl;
          apply pile_evs_svs_kt;
          [(simpl; rewrite Nat.max_comm; pose proof (Htmp := evar_fresh_seq_max); set_solver)
          |(rewrite Nat.max_comm; pose proof (Htmp := svar_fresh_seq_max); set_solver)
          |(clear pf₂; repeat case_match; simpl; try reflexivity; try lia)
          |(apply frames_on_the_way_to_hole'_app_2)
          ]
        ).
      }
      { exact p_sub_EvS. }
      { exact q_sub_EvS. }
      { exact E_in_EvS. }
      {
        abstract (
          simpl in ψ_sub_EvS;
          clear -ψ_sub_EvS;
          set_solver
        ).
      }
      { exact p_sub_SvS. }
      { exact q_sub_SvS. }
      { 
        abstract (
          simpl in ψ_sub_SvS;
          clear -ψ_sub_SvS;
          set_solver
        ).
      }

      unshelve (eapply helper_app_lemma); try assumption.
      eapply pile_trans;[|apply pile].
      unfold i'.
      apply pile_evs_svs_kt.
      { clear; set_solver. }
      { clear; set_solver. }
      { reflexivity. }
      {
        simp frames_on_the_way_to_hole'.
        (* This should be automatable! *)
        remember (well_formed_free_evar_subst_0 E wfp wfψ1) as wf1.
        remember (well_formed_free_evar_subst_0 E wfp wfψ2) as wf2.
        remember (well_formed_free_evar_subst_0 E wfq wfψ1) as wf3.
        remember (well_formed_free_evar_subst_0 E wfq wfψ2) as wf4.
        remember (frames_on_the_way_to_hole' EvS SvS E
        (frames_on_the_way_to_hole'_obligation_5 wfψ)
        (frames_on_the_way_to_hole'_obligation_6 wfp)
        (frames_on_the_way_to_hole'_obligation_7 wfq) ∪
      frames_on_the_way_to_hole' EvS SvS E
        (frames_on_the_way_to_hole'_obligation_9 wfψ)
        (frames_on_the_way_to_hole'_obligation_10 wfp)
        (frames_on_the_way_to_hole'_obligation_11 wfq))
        as rest.
        remember (frames_on_the_way_to_hole'_obligation_1 E wfψ wfp) as wf1'.
        remember (frames_on_the_way_to_hole'_obligation_2 E wfψ wfp) as wf2'.
        remember (frames_on_the_way_to_hole'_obligation_3 E wfψ wfq) as wf3'.
        remember (frames_on_the_way_to_hole'_obligation_4 E wfψ wfq) as wf4'.
        clear.
        remember (free_evar_subst ψ1 p E) as A.
        remember (free_evar_subst ψ1 q E) as B.
        remember (free_evar_subst ψ2 p E) as C.
        remember (free_evar_subst ψ2 q E) as D.
        clear.
        set_unfold.
        intros.
        destruct_or!.
        { left. left. left. left. left. pi_assumption. }
        { left. left. left. right. pi_assumption. }
        { left. left. left. left. right. pi_assumption. }
        { left. left. right. pi_assumption. }
      }
    }
    {
      useBasicReasoning.
      apply pf_iff_equiv_refl.
      abstract (wf_auto2).
    }
    {
      assert (wfψ1 : well_formed ψ1 = true).
      { clear -wfψ. abstract (wf_auto2). }
      assert (size' ψ1 <= sz) by abstract(lia).
      assert (wfψ2 : well_formed ψ2 = true).
      { clear -wfψ. abstract (wf_auto2). }
      assert (size' ψ2 <= sz) by abstract(lia).

      pose proof (pf₁ := (IHsz ψ1) ltac:(assumption) ltac:(assumption)).
      specialize (pf₁ EvS SvS).
      feed specialize pf₁.
      {
        abstract (
          subst i';
          eapply pile_trans;
          [|apply pile];
          apply pile_evs_svs_kt;
          [(simpl; pose proof evar_fresh_seq_max; set_solver)
          |(simpl; pose proof svar_fresh_seq_max; set_solver)
          |(clear pf₁;repeat case_match; simpl; try reflexivity; simpl in *; lia)
          |(apply frames_on_the_way_to_hole'_imp_1)
          ]
        ).
        
      }
      { exact p_sub_EvS. }
      { exact q_sub_EvS. }
      { exact E_in_EvS. }
      {
        abstract (
          simpl in ψ_sub_EvS;
          clear -ψ_sub_EvS;
          set_solver
        ).
      }
      { exact p_sub_SvS. }
      { exact q_sub_SvS. }
      { abstract (
          simpl in ψ_sub_SvS;
          clear -ψ_sub_SvS;
          set_solver
        ).
      }

      pose proof (pf₂ := (IHsz ψ2) ltac:(assumption) ltac:(assumption)).

      specialize (pf₂ EvS SvS).
      feed specialize pf₂.
      {
        abstract (
          subst i';
          eapply pile_trans;
          [|apply pile];
          apply pile_evs_svs_kt;
          [(simpl; rewrite Nat.max_comm; clear; pose proof evar_fresh_seq_max; set_solver)
          |(simpl; rewrite Nat.max_comm; clear; pose proof svar_fresh_seq_max; set_solver)
          |(clear pf₂; repeat case_match; simpl in *; try reflexivity; lia)
          |(apply frames_on_the_way_to_hole'_imp_2)
          ]
        ).
      }
      { exact p_sub_EvS. }
      { exact q_sub_EvS. }
      { exact E_in_EvS. }
      {
        abstract (
          simpl in ψ_sub_EvS;
          clear -ψ_sub_EvS;
          set_solver
        ).
      }
      { exact p_sub_SvS. }
      { exact q_sub_SvS. }
      { 
        abstract (
          simpl in ψ_sub_SvS;
          clear -ψ_sub_SvS;
          set_solver
        ).
      }

      apply prf_equiv_of_impl_of_equiv.
      { abstract (wf_auto2). }
      { abstract (wf_auto2). }
      { abstract (wf_auto2). }
      { abstract (wf_auto2). }
      { apply pf₁. }
      { apply pf₂. }
    }
    {
      pose proof (frx := @set_evar_fresh_is_fresh' Σ EvS).
      remember (evar_fresh (elements EvS)) as x.

      (* there used to be a destruct on whether E is in psi *)

      assert (well_formed (evar_open 0 x ψ)) by abstract(wf_auto2).
      assert (size' (evar_open 0 x ψ) <= sz) by abstract(rewrite evar_open_size'; lia).

      pose proof (IH := IHsz (evar_open 0 x ψ) ltac:(assumption) ltac:(assumption)).
      specialize (IH ({[x]} ∪ EvS) SvS).
      feed specialize IH.
      {
        abstract(
          subst i';
          simpl;
          eapply pile_trans;
          [|apply pile];
          assert (HxneE: x <> E);
          [(clear -frx E_in_EvS; set_solver)|];
          apply pile_evs_svs_kt;
          [(
            simpl;
            rewrite medoeip_evar_open;
            [(apply not_eq_sym; exact HxneE)
            |(simpl;
              rewrite medoeip_S_in;
              [(assumption)
              |(remember (maximal_exists_depth_of_evar_in_pattern' exdepth E ψ) as n;
                simpl;
                unfold evar_fresh_s;
                rewrite -Heqx;
                clear;
                set_solver)
              ]
            )]
          )
         |(
            simpl;
            rewrite mmdoeip_evar_open;
            [(apply not_eq_sym; exact HxneE)
            |(apply reflexivity)
            ]
          )
        |(
            clear IH;
            repeat case_match; simpl in *; try reflexivity;
            pose proof (Htmp := n);
            rewrite mmdoeip_evar_open in Htmp;
            [(apply not_eq_sym; exact HxneE)|(lia)]
          )
          |(simp frames_on_the_way_to_hole'; subst x; clear; pi_set_solver)
        ]).
      }
      { clear -p_sub_EvS. abstract (set_solver). }
      { clear -q_sub_EvS. abstract (set_solver). }
      { clear -E_in_EvS. abstract (set_solver). }
      { clear -ψ_sub_EvS.
        abstract (
          rewrite elem_of_subseteq;
          intros x0;
          rewrite free_evars_evar_open'';
          intros [[H1 H2]| H2];
          [
            (subst; clear; set_solver)
            |(simpl in ψ_sub_EvS; set_solver)
          ]
        ).
      }
      { exact p_sub_SvS. }
      { exact q_sub_SvS. }
      { abstract (
          simpl in ψ_sub_SvS;
          clear -ψ_sub_SvS;
          rewrite free_svars_evar_open;
          exact ψ_sub_SvS
        ).
      }
      eapply congruence_ex_helper with (x := x)(EvS := EvS)(SvS := SvS)(exdepth := exdepth)(mudepth := mudepth); try assumption.
      { set_solver. }
      { reflexivity. }
      { eapply pile_trans;[|apply pile].
        unfold i'.
        apply pile_evs_svs_kt.
        { apply reflexivity. }
        { apply reflexivity. }
        { case_match; reflexivity. }
        { clear. set_solver. }
      }
    }
    {
      pose proof (frX := @set_svar_fresh_is_fresh' Σ SvS).
      remember (svar_fresh (elements SvS)) as X.

      simpl in HEinψ.

      assert (well_formed (svar_open 0 X ψ) = true) by (abstract(clear -wfψ;wf_auto2)).
      assert (size' (svar_open 0 X ψ) <= sz) by abstract(rewrite svar_open_size'; lia).
      pose proof (IH := IHsz (svar_open 0 X ψ) ltac:(assumption) ltac:(assumption)).
      specialize (IH EvS ({[X]} ∪ SvS)).
      feed specialize IH.
      {
        abstract (
          subst i';
          eapply pile_trans;
          [|apply pile];
          apply pile_evs_svs_kt;
          [
            (
            simpl;
            rewrite medoeip_svar_open;
            apply reflexivity
            )
          |(
            simpl;
            rewrite mmdoeip_svar_open;
            rewrite mmdoeip_S_in;[exact HEinψ|];
            simpl;
            unfold svar_fresh_s;
            rewrite -HeqX;
            clear;
            set_solver
          )
          |(
            clear IH;
            repeat case_match; simpl in *; try reflexivity;
            pose proof (Htmp := n);
            rewrite mmdoeip_svar_open in Htmp;
            pose proof (Htmp2 := e);
            rewrite mmdoeip_S_in in Htmp2;
            [exact HEinψ|];
            inversion Htmp2
          )
          |(simp frames_on_the_way_to_hole'; subst X; clear; pi_set_solver)]).
      }
      {
        exact p_sub_EvS.
      }
      {
        exact q_sub_EvS.
      }
      {
        exact E_in_EvS.
      }
      {
        abstract (
          rewrite free_evars_svar_open;
          simpl in ψ_sub_EvS;
          apply ψ_sub_EvS
        ).
      }
      {
        clear -p_sub_SvS.
        abstract (set_solver).
      }
      {
        clear -q_sub_SvS.
        abstract (set_solver).
      }
      {
        rewrite elem_of_subseteq.
        intros X'.
        rewrite free_svars_svar_open''.
        intros [[H1 H2]|H1].
        {
          abstract (subst X'; clear; set_solver).
        }
        {
          abstract (
            simpl in ψ_sub_SvS;
            clear -H1 ψ_sub_SvS;
            set_solver
          ).
        }
      }

      apply pf_iff_free_evar_subst_svar_open_to_bsvar_subst_free_evar_subst in IH.
      3: { clear -wfq. abstract (wf_auto2). }
      2: { clear -wfp. abstract (wf_auto2). }

      unshelve (epose proof (IH1 := @pf_iff_proj1 _ _ _ _ _ _ _ IH)).
      { clear -wfψ wfp. abstract (wf_auto2). }
      { clear -wfψ wfq. abstract (wf_auto2). }
      unshelve (epose proof (IH2 := @pf_iff_proj2 _ _ _ _ _ _ _ IH)).
      { clear -wfψ wfp. abstract (wf_auto2). }
      { clear -wfψ wfq. abstract (wf_auto2). }

      eapply pf_iff_mu_remove_svar_quantify_svar_open.
      5: {
        apply pf_iff_split.
        4: {
          apply mu_monotone.
          4: {
            unfold svar_open.
            apply IH2.
          }
          3: {
            abstract (
              clear -ψ_sub_SvS p_sub_SvS frX wfψ wfp;
              wf_auto2;
              simpl in *;
              pose proof (Htmp := @free_svars_free_evar_subst Σ ψ E p);
              clear -Htmp ψ_sub_SvS p_sub_SvS frX;
              set_solver
            ).
          }
          2: {
            abstract (
              clear -ψ_sub_SvS q_sub_SvS frX wfψ wfq;
              wf_auto2;
              simpl in *;
              pose proof (Htmp := @free_svars_free_evar_subst Σ ψ E q);
              clear -Htmp ψ_sub_SvS q_sub_SvS frX;
              set_solver
            ).
          }
          {
            abstract (
              subst i';
              eapply pile_trans;[|apply pile];
              apply pile_evs_svs_kt;
              [(clear; set_solver)
              |(simpl;
                rewrite mmdoeip_S_in;
                [(exact HEinψ)|];
                simpl;
                unfold svar_fresh_s;
                rewrite -HeqX;
                clear;
                set_solver
            )|(repeat case_match; simpl in *; try reflexivity;
            pose proof (Htmp := e);
            rewrite mmdoeip_S_in in Htmp;
            [exact HEinψ|];
            inversion Htmp)|(clear; set_solver)]
            ).
          }
        }
        3: {
          apply mu_monotone.
          4: {
            unfold svar_open.
            apply IH1.
          }
          3: {
            abstract (
              clear -ψ_sub_SvS q_sub_SvS frX wfψ wfq;
              wf_auto2; simpl in *;
              pose proof (Htmp := @free_svars_free_evar_subst Σ ψ E q);
              clear -Htmp ψ_sub_SvS q_sub_SvS frX;
              set_solver
            ).
          }
          2: {
            abstract (
              clear -ψ_sub_SvS p_sub_SvS frX wfψ wfp;
              wf_auto2; simpl in *;
              pose proof (Htmp := @free_svars_free_evar_subst Σ ψ E p);
              clear -Htmp ψ_sub_SvS p_sub_SvS frX;
              set_solver
            ).
          }
          {
            abstract (
              subst i';
              eapply pile_trans;[|apply pile];
              apply pile_evs_svs_kt;
              [(clear; set_solver)
              |(simpl;
                rewrite mmdoeip_S_in;
                [(exact HEinψ)|];
                simpl;
                unfold svar_fresh_s;
                rewrite -HeqX;
                clear;
                set_solver
              )|(repeat case_match; simpl in *; try reflexivity;
              pose proof (Htmp := e);
              rewrite mmdoeip_S_in in Htmp;
              [exact HEinψ|];
              inversion Htmp)|(clear; set_solver)]
            ).
          }          
        }
        {
          cut (X ∉ free_svars ψ.[[evar:E↦p]]).
          {
            clear -wfψ wfp.
            abstract (wf_auto2).
          }
          abstract (
            pose proof (Htmp := @free_svars_free_evar_subst Σ ψ E p);
            clear -H Htmp frX ψ_sub_SvS p_sub_SvS;
            set_solver
          ).
        }
        {
          cut (X ∉ free_svars ψ.[[evar:E↦q]]).
          {
            clear -wfψ wfq.
            abstract (wf_auto2).
          }
          abstract (
            pose proof (Htmp := @free_svars_free_evar_subst Σ ψ E q);
            clear -H Htmp frX ψ_sub_SvS q_sub_SvS;
            set_solver
          ).
        }
      }
      {
        clear -wfψ wfp.
        abstract (wf_auto2).
      }
      {
        clear -wfψ wfq.
        abstract (wf_auto2).
      }
      {
        abstract (
          pose proof (Htmp := @free_svars_free_evar_subst Σ ψ E p);
          clear -H Htmp frX ψ_sub_SvS p_sub_SvS;
          set_solver
        ).
      }
      {
        abstract (
          pose proof (Htmp := @free_svars_free_evar_subst Σ ψ E q);
          clear -H Htmp frX ψ_sub_SvS q_sub_SvS;
          set_solver
        ).
      }
    }
  Defined.

  Lemma prf_equiv_congruence Γ p q C
  (gpi : ProofInfo)
  (wfp : well_formed p = true)
  (wfq : well_formed q = true)
  (wfC: PC_wf C)
  (pile : ProofInfoLe
   (
     (ExGen := list_to_set (evar_fresh_seq (free_evars (pcPattern C) ∪ free_evars p ∪ free_evars q ∪ {[pcEvar C]}) (maximal_exists_depth_of_evar_in_pattern (pcEvar C) (pcPattern C))),
     SVSubst := list_to_set (svar_fresh_seq (free_svars (pcPattern C) ∪ free_svars p ∪ free_svars q) (maximal_mu_depth_of_evar_in_pattern (pcEvar C) (pcPattern C))),
     KT := if decide (0 = (maximal_mu_depth_of_evar_in_pattern (pcEvar C) (pcPattern C))) is left _ then false else true,
     FP := gset_to_coGset (@frames_on_the_way_to_hole' Σ (free_evars (pcPattern C) ∪ free_evars p ∪ free_evars q ∪ {[pcEvar C]}) (free_svars (pcPattern C) ∪ free_svars p ∪ free_svars q) (pcEvar C) (pcPattern C) p q wfC wfp wfq))
    )
   ( gpi)
  ):
    Γ ⊢i (p <---> q) using ( gpi) ->
    Γ ⊢i (((emplace C p) <---> (emplace C q))) using ( gpi).
  Proof.
    intros Hiff.
    assert (well_formed (p <---> q)).
    { abstract (
        pose proof (proved_impl_wf _ _ (proj1_sig Hiff));
        assumption
      ).
    }
    assert (well_formed p) by (abstract (wf_auto2)).
    assert (well_formed q) by (abstract (wf_auto2)).
    destruct C as [E ψ]. simpl in *.
    unfold emplace. simpl.
    eapply @eq_prf_equiv_congruence
    with (EvS := (free_evars ψ ∪ free_evars p ∪ free_evars q ∪ {[E]}))
         (SvS := (free_svars ψ ∪ free_svars p ∪ free_svars q))
         (exdepth := 0)
         (mudepth := 0)
         (sz := size' ψ)
    .
    { apply reflexivity. }
    { abstract (clear; set_solver). }
    { abstract (clear; set_solver). }
    { abstract (clear; set_solver). }
    { abstract (clear; set_solver). }
    { abstract (clear; set_solver). }
    { abstract (clear; set_solver). }
    { abstract (clear; set_solver). }
    { eapply pile_trans;[|apply pile]. apply pile_refl. }
    { exact Hiff. }
  Defined.

End FOL_helpers.

Lemma ex_quan_monotone {Σ : Signature} Γ x ϕ₁ ϕ₂ (i : ProofInfo)
  (pile : ProofInfoLe ( (ExGen := {[x]}, SVSubst := ∅, KT := false, FP := ∅)) i) :
  Γ ⊢i ϕ₁ ---> ϕ₂ using i ->
  Γ ⊢i (exists_quantify x ϕ₁) ---> (exists_quantify x ϕ₂) using i.
Proof.
  intros H.
  pose proof (Hwf := @proved_impl_wf Σ Γ _ (proj1_sig H)).
  assert (wfϕ₁: well_formed ϕ₁ = true) by wf_auto2.
  assert (wfϕ₂: well_formed ϕ₂ = true) by wf_auto2.
  apply Ex_gen.
  { exact pile. }
  { simpl. rewrite free_evars_evar_quantify. clear. set_solver. }

  unfold exists_quantify.
  eapply syllogism_meta. 4: apply H.
  { wf_auto2. }
  { wf_auto2. }
  { wf_auto2. }
  clear H wfϕ₁ ϕ₁ Hwf.

  (* We no longer need to use [cast_proof] to avoid to ugly eq_sym terms;
     however, without [cast_proof'] the [replace] tactics does not work,
     maybe because of implicit parameters.
   *)
  eapply (cast_proof').
  {
    replace ϕ₂ with (instantiate (ex, evar_quantify x 0 ϕ₂) (patt_free_evar x)) at 1.
    2: { unfold instantiate.
       rewrite bevar_subst_evar_quantify_free_evar.
       now do 2 apply andb_true_iff in wfϕ₂ as [_ wfϕ₂].
       reflexivity.
    }
    reflexivity.
  }
        (* i =  gpi *)
  useBasicReasoning.
  apply Ex_quan.
  abstract (wf_auto2).
Defined.

Lemma ex_quan_and_proj1 {Σ : Signature} Γ x ϕ₁ ϕ₂:
  well_formed ϕ₁ = true ->
  well_formed ϕ₂ = true ->
  Γ ⊢i (exists_quantify x (ϕ₁ and ϕ₂)) ---> (exists_quantify x ϕ₁)
  using ( (ExGen := {[x]}, SVSubst := ∅, KT := false, FP := ∅)).
Proof.
  intros wfϕ₁ wfϕ₂.
  apply ex_quan_monotone.
  { apply pile_refl. }
  toMLGoal.
  { wf_auto2. }
  mlIntro.
  mlDestructAnd 0. mlExactn 0.
Defined.

Lemma ex_quan_and_proj2 {Σ : Signature} Γ x ϕ₁ ϕ₂:
  well_formed ϕ₁ = true ->
  well_formed ϕ₂ = true ->
  Γ ⊢i (exists_quantify x (ϕ₁ and ϕ₂)) ---> (exists_quantify x ϕ₂)
  using ( (ExGen := {[x]}, SVSubst := ∅, KT := false, FP := ∅)).
Proof.
  intros wfϕ₁ wfϕ₂.
  apply ex_quan_monotone.
  { apply pile_refl. }
  toMLGoal.
  { wf_auto2. }
  mlIntro.
  mlDestructAnd 0.
  mlExactn 1.
Defined.

Lemma lhs_to_and {Σ : Signature} Γ a b c i:
  well_formed a ->
  well_formed b ->
  well_formed c ->
  Γ ⊢i (a and b) ---> c using i ->
  Γ ⊢i a ---> b ---> c using i.
Proof.
  intros wfa wfb wfc H.
  toMLGoal.
  { wf_auto2. }
  do 2 mlIntro. mlApplyMeta H.
  fromMLGoal.
  useBasicReasoning.
  apply conj_intro.
  { wf_auto2. }
  { wf_auto2. }
Defined.

Lemma lhs_from_and {Σ : Signature} Γ a b c i:
  well_formed a ->
  well_formed b ->
  well_formed c ->
  Γ ⊢i a ---> b ---> c using i ->
  Γ ⊢i (a and b) ---> c using i.
Proof.
  intros wfa wfb wfc H.
  toMLGoal.
  { wf_auto2. }
  mlIntro.
  mlAssert (b).
  { wf_auto2. }
  { fromMLGoal. useBasicReasoning. apply pf_conj_elim_r.
    wf_auto2. wf_auto2.
  }
  mlAssert (a) using first 1.
  { wf_auto2. }
  { fromMLGoal. useBasicReasoning. apply pf_conj_elim_l; wf_auto2. }
  mlAdd H.
  mlAssert ((b ---> c)).
  { wf_auto2. }
  { mlApply 0. mlExactn 2. }
  mlApply 4.
  mlExactn 3.
Defined.

Lemma prf_conj_split {Σ : Signature} Γ a b l:
  well_formed a ->
  well_formed b ->
  Pattern.wf l ->
  Γ ⊢i (foldr patt_imp a l) ---> (foldr patt_imp b l) ---> (foldr patt_imp (a and b) l)
  using BasicReasoning.
Proof.
  intros wfa wfb wfl.
  induction l.
  - simpl. apply conj_intro; assumption.
  - simpl. pose proof (wfl' := wfl). unfold Pattern.wf in wfl'. simpl in wfl'. apply andb_prop in wfl' as [wfa0 wfl'].
    specialize (IHl wfl').
    toMLGoal.
    { wf_auto2. }
    do 3 mlIntro.
    mlAssert ((foldr patt_imp a l)).
    { wf_auto2. }
    { mlApply 0. mlExactn 2. }
    mlAssert ((foldr patt_imp b l)).
    { wf_auto2. }
    { mlApply 1. mlExactn 2. }
    mlClear 2. mlClear 1. mlClear 0.
    fromMLGoal. apply IHl.
Defined.

Lemma prf_conj_split_meta {Σ : Signature} Γ a b l (i : ProofInfo):
  well_formed a ->
  well_formed b ->
  Pattern.wf l ->
  Γ ⊢i (foldr patt_imp a l) using i -> 
  Γ ⊢i (foldr patt_imp b l) ---> (foldr patt_imp (a and b) l) using i.
Proof.
  intros. eapply MP. 2: { useBasicReasoning. apply prf_conj_split; assumption. }
  exact H2.
Defined.

Lemma prf_conj_split_meta_meta {Σ : Signature} Γ a b l (i : ProofInfo):
  well_formed a ->
  well_formed b ->
  Pattern.wf l ->
  Γ ⊢i (foldr patt_imp a l) using i -> 
  Γ ⊢i (foldr patt_imp b l) using i ->
  Γ ⊢i (foldr patt_imp (a and b) l) using i.
Proof.
  intros. eapply MP.
  2: {
    apply prf_conj_split_meta; assumption.
  }
  exact H3.
Defined.

Lemma MLGoal_splitAnd {Σ : Signature} Γ a b l i:
  @mkMLGoal Σ Γ l a i ->
  @mkMLGoal Σ Γ l b i ->
  @mkMLGoal Σ Γ l (a and b) i.
Proof.
  intros Ha Hb.
  unfold of_MLGoal in *. simpl in *.
  intros wfab wfl.
  feed specialize Ha.
  { abstract(wf_auto2). }
  { exact wfl. }
  feed specialize Hb.
  { abstract(wf_auto2). }
  { exact wfl. }
  apply prf_conj_split_meta_meta; auto.
  { abstract (wf_auto2). }
  { abstract (wf_auto2). }
Defined.

Ltac mlSplitAnd := apply MLGoal_splitAnd.

Local Lemma ex_mlSplitAnd {Σ : Signature} Γ a b c:
  well_formed a ->
  well_formed b ->
  well_formed c ->
  Γ ⊢i a ---> b ---> c ---> (a and b)
  using BasicReasoning.
Proof.
  intros wfa wfb wfc.
  toMLGoal.
  { wf_auto2. }
  mlIntro. mlIntro. mlIntro.
  mlSplitAnd.
  - mlExactn 0.
  - mlExactn 1.
Defined.

Lemma prf_local_goals_equiv_impl_full_equiv {Σ : Signature} Γ g₁ g₂ l:
  well_formed g₁ ->
  well_formed g₂ ->
  Pattern.wf l ->
  Γ ⊢i (foldr patt_imp (g₁ <---> g₂) l) --->
      ((foldr patt_imp g₁ l) <---> (foldr patt_imp g₂ l))
  using BasicReasoning.
Proof.
  intros wfg₁ wfg₂ wfl.
  induction l; simpl.
  - apply A_impl_A; wf_auto2.
  - pose proof (wfl' := wfl). unfold Pattern.wf in wfl'. simpl in wfl'. apply andb_prop in wfl' as [wfa wfl'].
    specialize (IHl wfl').
    toMLGoal.
    { wf_auto2. }
    mlIntro. mlSplitAnd.
    + unshelve (mlApplyMeta (@P2 _ _ _ _ _ _ _ _)).
      1-3: wf_auto2.
      (* TODO we need some [mlRevert] tactic *)
      fromMLGoal. toMLGoal.
      { wf_auto2. }
      unshelve(mlApplyMeta (@P2 _ _ _ _ _ _ _ _)).
      1-3: wf_auto2.
      mlIntro. mlClear 0. mlIntro.
      mlApplyMeta IHl in 0. unfold patt_iff at 1. mlDestructAnd 0.
      mlExactn 0.
    + unshelve (mlApplyMeta (@P2 _ _ _ _ _ _ _ _)).
      1-3: wf_auto2.
      fromMLGoal. toMLGoal.
      { wf_auto2. }
      unshelve (mlApplyMeta (@P2 _ _ _ _ _ _ _ _)).
      1-3: wf_auto2.
      mlIntro. mlClear 0. mlIntro.
      mlApplyMeta IHl in 0. unfold patt_iff at 1. mlDestructAnd 0.
      mlExactn 1.
Defined.

Lemma prf_local_goals_equiv_impl_full_equiv_meta {Σ : Signature} Γ g₁ g₂ l i:
  well_formed g₁ ->
  well_formed g₂ ->
  Pattern.wf l ->
  Γ ⊢i (foldr patt_imp (g₁ <---> g₂) l) using i ->
  Γ ⊢i ((foldr patt_imp g₁ l) <---> (foldr patt_imp g₂ l)) using i.
Proof.
  intros wfg₁ wfg₂ wfl H.
  eapply MP.
  2: { useBasicReasoning. apply prf_local_goals_equiv_impl_full_equiv; assumption. }
  exact H.
Defined.

Lemma prf_local_goals_equiv_impl_full_equiv_meta_proj1 {Σ : Signature} Γ g₁ g₂ l i:
  well_formed g₁ ->
  well_formed g₂ ->
  Pattern.wf l ->
  Γ ⊢i (foldr patt_imp (g₁ <---> g₂) l) using i ->
  Γ ⊢i (foldr patt_imp g₁ l) using i ->
  Γ ⊢i (foldr patt_imp g₂ l) using i.
Proof.
  intros wfg₁ wfg₂ wfl H1 H2.
  eapply MP.
  2: eapply pf_iff_proj1.
  4: apply prf_local_goals_equiv_impl_full_equiv_meta.
  7: apply H1.
  1: exact H2.
  all: wf_auto2.
Defined.

Lemma prf_local_goals_equiv_impl_full_equiv_meta_proj2 {Σ : Signature} Γ g₁ g₂ l i:
  well_formed g₁ ->
  well_formed g₂ ->
  Pattern.wf l ->
  Γ ⊢i (foldr patt_imp (g₁ <---> g₂) l) using i ->
  Γ ⊢i (foldr patt_imp g₂ l) using i ->
  Γ ⊢i (foldr patt_imp g₁ l) using i.
Proof.
  intros wfg₁ wfg₂ wfl H1 H2.
  eapply MP.
  2: eapply pf_iff_proj2.
  4: apply prf_local_goals_equiv_impl_full_equiv_meta.
  7: apply H1.
  1: exact H2.
  all: wf_auto2.
Defined.

Lemma prf_equiv_congruence_iter {Σ : Signature} (Γ : Theory) (p q : Pattern) (C : PatternCtx) l
  (wfp : well_formed p)
  (wfq : well_formed q)
  (wfC : PC_wf C)
  (gpi : ProofInfo)
  (pile : ProofInfoLe
  (
    (ExGen := list_to_set (evar_fresh_seq (free_evars (pcPattern C) ∪ free_evars p ∪ free_evars q ∪ {[pcEvar C]}) (maximal_exists_depth_of_evar_in_pattern (pcEvar C) (pcPattern C))),
      SVSubst := list_to_set (svar_fresh_seq (free_svars (pcPattern C) ∪ free_svars p ∪ free_svars q) (maximal_mu_depth_of_evar_in_pattern (pcEvar C) (pcPattern C))),
      KT := if decide (0 = (maximal_mu_depth_of_evar_in_pattern (pcEvar C) (pcPattern C))) is left _ then false else true,
      FP := gset_to_coGset (@frames_on_the_way_to_hole' Σ (free_evars (pcPattern C) ∪ free_evars p ∪ free_evars q ∪ {[pcEvar C]}) (free_svars (pcPattern C) ∪ free_svars p ∪ free_svars q) (pcEvar C) (pcPattern C) p q wfC wfp wfq))  
    )
    ( gpi)
  ):
  Pattern.wf l ->
  Γ ⊢i p <---> q using ( gpi) ->
  Γ ⊢i (foldr patt_imp (emplace C p) l) <---> (foldr patt_imp (emplace C q) l) using ( gpi).
Proof.
  intros wfl Himp.
  induction l; simpl in *.
  - unshelve(eapply prf_equiv_congruence); assumption.
  - pose proof (wfal := wfl).
    unfold Pattern.wf in wfl. simpl in wfl. apply andb_prop in wfl as [wfa wfl].
    specialize (IHl wfl).
    pose proof (Hwf1 := proved_impl_wf _ _ (proj1_sig IHl)).
    pose proof (Hwf2 := proved_impl_wf _ _ (proj1_sig Himp)).
    assert (well_formed (emplace C p)).
    {
      unfold emplace.
      wf_auto2.
    }
    assert (well_formed (emplace C q)).
    {
      unfold emplace.
      wf_auto2.
    }
    toMLGoal.
    { unfold emplace. wf_auto2. }
    unfold patt_iff.
    mlSplitAnd.
    + mlIntro. mlIntro.
      mlAssert ((foldr patt_imp (emplace C p) l)).
      { wf_auto2. }
      { mlApply 0. mlExactn 1. }
      apply pf_iff_proj1 in IHl.
      2,3: wf_auto2.
      mlApplyMeta IHl.
      mlExactn 2.
    + mlIntro. mlIntro.
      mlAssert ((foldr patt_imp (emplace C q) l)).
      { wf_auto2. }
      { mlApply 0. mlExactn 1. }
      apply pf_iff_proj2 in IHl.
      2,3: wf_auto2.
      mlApplyMeta IHl.
      mlExactn 2.
Defined.

Lemma extract_wfp {Σ : Signature} (Γ : Theory) (p q : Pattern) (i : ProofInfo):
  Γ ⊢i p <---> q using i ->
  well_formed p.
Proof.
  intros H.
  pose proof (H' := proj1_sig H).
  apply proved_impl_wf in H'.
  wf_auto2.
Qed.

Lemma extract_wfq {Σ : Signature} (Γ : Theory) (p q : Pattern) (i : ProofInfo):
  Γ ⊢i p <---> q using i ->
  well_formed q.
Proof.
  intros H.
  pose proof (H' := proj1_sig H).
  apply proved_impl_wf in H'.
  wf_auto2.
Qed.

Lemma MLGoal_rewriteIff
  {Σ : Signature} (Γ : Theory) (p q : Pattern) (C : PatternCtx) l (gpi : ProofInfo)
  (wfC : PC_wf C)
  (pf : Γ ⊢i p <---> q using ( gpi)) :
  @mkMLGoal Σ Γ l (emplace C q) ( gpi) ->
  (ProofInfoLe
  (
     (ExGen := list_to_set
                 (evar_fresh_seq
                    (free_evars (pcPattern C) ∪ free_evars p ∪ free_evars q
                     ∪ {[pcEvar C]})
                    (maximal_exists_depth_of_evar_in_pattern 
                       (pcEvar C) (pcPattern C))),
      SVSubst := list_to_set
                   (svar_fresh_seq
                      (free_svars (pcPattern C) ∪ free_svars p
                       ∪ free_svars q)
                      (maximal_mu_depth_of_evar_in_pattern 
                         (pcEvar C) (pcPattern C))),
      KT := (if
              decide
                (0 =
                 maximal_mu_depth_of_evar_in_pattern (pcEvar C) (pcPattern C))
             is left _
             then false
             else true
             ),
      FP := gset_to_coGset (@frames_on_the_way_to_hole' Σ (free_evars (pcPattern C) ∪ free_evars p ∪ free_evars q ∪ {[pcEvar C]}) (free_svars (pcPattern C) ∪ free_svars p ∪ free_svars q) (pcEvar C) (pcPattern C) p q wfC (@extract_wfp Σ Γ p q ( gpi) pf) (@extract_wfq Σ Γ p q ( gpi) pf))
      ))
      ( gpi)) ->
  @mkMLGoal Σ Γ l (emplace C p) ( gpi).
Proof.
  rename pf into Hpiffq.
  intros H pile.
  unfold of_MLGoal in *. simpl in *.
  intros wfcp wfl.
  feed specialize H.
  { abstract (
      pose proof (Hwfiff := proved_impl_wf _ _ (proj1_sig Hpiffq));
      unfold emplace;
      apply well_formed_free_evar_subst_0;[wf_auto2|];
      fold (PC_wf C);
      eapply wf_emplaced_impl_wf_context;
      apply wfcp
    ).
  }
  { exact wfl. }

  eapply MP.
  2: apply pf_iff_proj2.
  2: abstract (wf_auto2).
  3: eapply prf_equiv_congruence_iter.
  5: apply Hpiffq.
  4: assumption.
  1: apply H.
  1: {
    pose proof (@proved_impl_wf _ _ _ (proj1_sig H)).
    wf_auto2.  
  }
  exact pile.
Defined.




Ltac2 mutable ml_debug_rewrite := false.

(* Calls [cont] for every subpattern [a] of pattern [phi], giving the match context as an argument *)
Ltac2 for_each_match := fun (a : constr) (phi : constr) (cont : Pattern.context -> unit) =>
  try (
      if ml_debug_rewrite then
           Message.print (
               Message.concat
                 (Message.of_string "Trying to match ")
                 (Message.of_constr a)
             )
        else ();
      match! phi with
      | context ctx [ ?x ]
        => if ml_debug_rewrite then
             Message.print (
                 Message.concat
                   (Message.of_string " against ")
                   (Message.of_constr x)
               )
           else ();
           (if Constr.equal x a then
              if ml_debug_rewrite then
                Message.print (Message.of_string "Success.")
              else () ;
              cont ctx
            else ());
           fail (* backtrack *)
      end
    ); ().

(* Calls [cont] for [n]th subpatern [a] of pattern [phi]. *)
Ltac2 for_nth_match :=
  fun (n : int) (a : constr) (phi : constr) (cont : Pattern.context -> unit) =>
    if ml_debug_rewrite then
      Message.print (Message.of_string "for_nth_match")
    else () ;
    let curr : int ref := {contents := 0} in
    let found : bool ref := {contents := false} in
    for_each_match a phi
    (fun ctx =>
      if (found.(contents))
      then ()
      else
        curr.(contents) := Int.add 1 (curr.(contents)) ;
        if (Int.equal (curr.(contents)) n) then
          cont ctx
        else ()
    )
.

Local Ltac reduce_free_evar_subst_step_2 star :=
      lazymatch goal with
      | [ |- context ctx [free_evar_subst ?p ?q star] ]
        =>
          progress rewrite -> (@free_evar_subst_no_occurrence _ star p q) by (
            apply count_evar_occurrences_0;
            subst star;
            eapply evar_is_fresh_in_richer';
            [|apply set_evar_fresh_is_fresh'];
            simpl; clear; set_solver
          )
      end.

Local Ltac reduce_free_evar_subst_2 star :=
  (* unfold free_evar_subst; *)
  repeat (reduce_free_evar_subst_step_2 star).

Local Tactic Notation "solve_fresh_contradictions_2'" constr(star) constr(x) constr(h) :=
  let hcontra := fresh "Hcontra" in
  assert (hcontra: x <> star) by (subst star; unfold fresh_evar,evar_fresh_s; try clear h; simpl; solve_fresh_neq);
  rewrite -> h in hcontra;
  contradiction.

Local Ltac solve_fresh_contradictions_2 star :=
  unfold fresh_evar; simpl;
  match goal with
  | h: ?x = star |- _ =>
    let hprime := fresh "hprime" in
    pose proof (hprime := eq_sym h);
    solve_fresh_contradictions_2' star x hprime
  | h: star = ?x |- _
    => solve_fresh_contradictions_2' star x h
  end.

Local Ltac clear_obvious_equalities_2 :=
  repeat (
      match goal with
      | [ h: ?x = ?x |- _ ] => clear h
      end
    ).


Ltac simplify_emplace_2 star :=
  unfold emplace;
  simpl;
  (* unfold free_evar_subst; *)
  simpl;
  repeat break_match_goal;
  clear_obvious_equalities_2; try contradiction;
  try (solve_fresh_contradictions_2 star);
  (* repeat (rewrite nest_ex_aux_0); *)
  reduce_free_evar_subst_2 star.

(* Returns [n]th matching logic context [C] (of type [PatternCtx]) such that
   [emplace C a = phi].
 *)

 
 Ltac simplify_pile_side_condition_helper star :=
  subst star;
  unfold fresh_evar,evar_fresh_s;
  eapply evar_is_fresh_in_richer';
  [|apply set_evar_fresh_is_fresh'];
  clear; simpl; set_solver.

 Ltac simplify_pile_side_condition star :=
  try apply pile_any;
  cbn;
  simplify_emplace_2 star;
  repeat (rewrite (mmdoeip_notin, medoeip_notin);
  [(simplify_pile_side_condition_helper star)|]);
  simpl;
  repeat (
    lazymatch goal with
    | [H: context [maximal_mu_depth_of_evar_in_pattern' _ _ _] |- _ ]
      => rewrite mmdoeip_notin in H;
         [(simplify_pile_side_condition_helper star)|]
    | [H: context [maximal_exists_depth_of_evar_in_pattern' _ _ _] |- _ ]
      => rewrite medoeip_notin in H;
         [(simplify_pile_side_condition_helper star)|]
    end
  );
  simpl in *;
  try lia;
  try apply pile_any.

Ltac2 Type HeatResult := {
  star_ident : ident ;
  star_eq : ident ;
  pc : constr ;
  ctx : Pattern.context ;
  ctx_pat : constr ;
  equality : ident ;
}.

Ltac2 heat :=
  fun (n : int) (a : constr) (phi : constr) : HeatResult =>
    let found : (Pattern.context option) ref := { contents := None } in
     for_nth_match n a phi
     (fun ctx =>
        found.(contents) := Some ctx; ()
     );
    match found.(contents) with
    | None => Control.backtrack_tactic_failure "Cannot heat"
    | Some ctx
      => (
         let fr := constr:(fresh_evar $phi) in
         let star_ident := Fresh.in_goal ident:(star) in
         let star_eq := Fresh.in_goal ident:(star_eq) in
         (*set ($star_ident := $fr);*)
         remember $fr as $star_ident eqn:star_eq;
         let star_hyp := Control.hyp star_ident in
         let ctxpat := Pattern.instantiate ctx constr:(patt_free_evar $star_hyp) in
         let pc := constr:((@Build_PatternCtx _ $star_hyp $ctxpat)) in
         let heq1 := Fresh.in_goal ident:(heq1) in
         assert(heq1 : ($phi = (@emplace _ $pc $a))) 
         > [ abstract(
             (ltac1:(star |- simplify_emplace_2 star) (Ltac1.of_ident star_ident);
             reflexivity
             ))
           | ()
           ];
         { star_ident := star_ident; star_eq := star_eq; pc := pc; ctx := ctx; ctx_pat := ctxpat; equality := heq1 }
         )
    end
.

Ltac2 mlRewrite (hiff : constr) (atn : int) :=
  let thiff := Constr.type hiff in
  (* we have to unfold [derives] otherwise this might not match *)
  lazy_match! (eval unfold ProofSystem.derives in $thiff) with
  | _ ⊢i (?a <---> ?a') using _
    =>
    unfold AnyReasoning;
    lazy_match! goal with
    | [ |- of_MLGoal (@mkMLGoal ?sgm ?g ?l ?p ( ?gpi))]
      => let hr : HeatResult := heat atn a p in
         if ml_debug_rewrite then
           Message.print (Message.of_constr (hr.(ctx_pat)))
         else () ;
         let heq := Control.hyp (hr.(equality)) in
         let pc := (hr.(pc)) in
         eapply (@cast_proof_ml_goal _ $g) >
           [ rewrite $heq; reflexivity | ()];
         Std.clear [hr.(equality)];
         let wfC := Fresh.in_goal ident:(wfC) in
         assert (wfC : PC_wf $pc = true) > [ ltac1:(unfold PC_wf; simpl; wf_auto2); Control.shelve () | ()] ;
         let wfCpf := Control.hyp wfC in
         apply (@MLGoal_rewriteIff $sgm $g _ _ $pc $l $gpi $wfCpf $hiff)  >
         [
         (lazy_match! goal with
         | [ |- of_MLGoal (@mkMLGoal ?sgm ?g ?l ?p _)]
           =>
             let heq2 := Fresh.in_goal ident:(heq2) in
             let plugged := Pattern.instantiate (hr.(ctx)) a' in
             assert(heq2: ($p = $plugged))
             > [
                 abstract (ltac1:(star |- simplify_emplace_2 star) (Ltac1.of_ident (hr.(star_ident)));
                 reflexivity
                 )
               | ()
               ];
             let heq2_pf := Control.hyp heq2 in
             eapply (@cast_proof_ml_goal _ $g) >
               [ rewrite $heq2_pf; reflexivity | ()];
             Std.clear [wfC; heq2 ; (hr.(star_ident)); (hr.(star_eq))]
         end)
         | (ltac1:(star |- simplify_pile_side_condition star) (Ltac1.of_ident (hr.(star_ident))))
         ]
    end
  end.

Ltac2 rec constr_to_int (x : constr) : int :=
  match! x with
  | 0 => 0
  | (S ?x') => Int.add 1 (constr_to_int x')
  end.


Tactic Notation "mlRewrite" constr(Hiff) "at" constr(atn) :=
  (let ff := ltac2:(hiff atn |-
                      mlRewrite
                        (Option.get (Ltac1.to_constr(hiff)))
                        (constr_to_int (Option.get (Ltac1.to_constr(atn))))
                   ) in
   ff Hiff atn).

Lemma pf_iff_equiv_sym_nowf {Σ : Signature} Γ A B i :
  Γ ⊢i (A <---> B) using i ->
  Γ ⊢i (B <---> A) using i.
Proof.
  intros H.
  pose proof (wfp := proved_impl_wf _ _ (proj1_sig H)).
  assert (well_formed A) by wf_auto2.
  assert (well_formed B) by wf_auto2.
  apply pf_iff_equiv_sym; assumption.
Defined.

Tactic Notation "mlRewrite" "->" constr(Hiff) "at" constr(atn) :=
  mlRewrite Hiff at atn.

Tactic Notation "mlRewrite" "<-" constr(Hiff) "at" constr(atn) :=
  mlRewrite (@pf_iff_equiv_sym_nowf _ _ _ _ _ Hiff) at atn.


Local Example ex_prf_rewrite_equiv_2 {Σ : Signature} Γ a a' b x:
  well_formed a ->
  well_formed a' ->
  well_formed b ->
  Γ ⊢ a <---> a' ->
  Γ ⊢i (a $ a $ b $ a ---> (patt_free_evar x)) <---> (a $ a' $ b $ a' ---> (patt_free_evar x))
  using AnyReasoning.
Proof.
  intros wfa wfa' wfb Hiff.
  toMLGoal.
  { abstract(wf_auto2). }
  mlRewrite Hiff at 2.
  mlRewrite <- Hiff at 3.
  fromMLGoal.
  useBasicReasoning.
  apply pf_iff_equiv_refl. abstract(wf_auto2).
Defined.

Lemma top_holds {Σ : Signature} Γ:
  Γ ⊢i Top using BasicReasoning.
Proof.
  apply false_implies_everything.
  { wf_auto2. }
Defined.

Lemma phi_iff_phi_top {Σ : Signature} Γ ϕ :
  well_formed ϕ ->
  Γ ⊢i ϕ <---> (ϕ <---> Top)
  using BasicReasoning.
Proof.
  intros wfϕ.
  toMLGoal.
  { wf_auto2. }
  mlSplitAnd; mlIntro.
  - mlSplitAnd.
    + mlIntro. mlClear 0. mlClear 0.
      fromMLGoal.
      apply top_holds. (* TODO: we need something like [mlExactMeta top_holds] *)
    + fromMLGoal.
      apply P1; wf_auto2.
  - mlDestructAnd 0.
    mlApply 1.
    mlClear 0.
    mlClear 0.
    fromMLGoal.
    apply top_holds.
Defined.

Lemma not_phi_iff_phi_bott {Σ : Signature} Γ ϕ :
  well_formed ϕ ->
  Γ ⊢i (! ϕ ) <---> (ϕ <---> ⊥)
  using BasicReasoning.
Proof.
  intros wfϕ.
  toMLGoal.
  { wf_auto2. }
  mlSplitAnd; mlIntro.
  - mlSplitAnd.
    + mlExactn 0.
    + mlClear 0. fromMLGoal.
      apply false_implies_everything.
      { wf_auto2. }
  - mlDestructAnd 0.
    mlExactn 0.
Defined.

Lemma not_not_iff {Σ : Signature} (Γ : Theory) (A : Pattern) :
  well_formed A ->
  Γ ⊢i A <---> ! ! A
  using BasicReasoning.
Proof.
  intros wfA.
  apply pf_iff_split.
  { wf_auto2. }
  { wf_auto2. }
  - apply not_not_intro.
    { wf_auto2. }
  - apply not_not_elim.
    { wf_auto2. }
Defined.

(* prenex-exists-and-left *)
Lemma prenex_exists_and_1 {Σ : Signature} (Γ : Theory) ϕ₁ ϕ₂:
  well_formed (ex, ϕ₁) ->
  well_formed ϕ₂ ->
  Γ ⊢i ((ex, ϕ₁) and ϕ₂) ---> (ex, (ϕ₁ and ϕ₂))
  using ( (ExGen := {[fresh_evar (ϕ₂ ---> ex , (ϕ₁ and ϕ₂))]}, SVSubst := ∅, KT := false, FP := ∅)).
Proof.
  intros wfϕ₁ wfϕ₂.
  toMLGoal.
  { wf_auto2. }
  mlIntro. mlDestructAnd 0.
  fromMLGoal.

  remember (fresh_evar (ϕ₂ ---> (ex, (ϕ₁ and ϕ₂)))) as x.
  apply strip_exists_quantify_l with (x := x).
  { subst x. eapply evar_is_fresh_in_richer'.
    2: { apply set_evar_fresh_is_fresh'. }
    simpl. clear. set_solver.
  }
  { wf_auto2. }
  apply Ex_gen.
  { apply pile_refl. }
  { wf_auto2. }
  
  apply lhs_to_and.
  { wf_auto2. }
  { wf_auto2. }
  { wf_auto2. }

  eapply cast_proof'.
  {
    replace (evar_open 0 x ϕ₁ and ϕ₂)
            with (evar_open 0 x (ϕ₁ and ϕ₂)).
    2: {
      unfold evar_open. simpl_bevar_subst.
      rewrite [bevar_subst ϕ₂ _ _]bevar_subst_not_occur.
      {
        wf_auto2.
      }
      reflexivity.
    }
    reflexivity.
  }
  useBasicReasoning.
  apply Ex_quan.
  wf_auto2.
Defined.

(* prenex-exists-and-right *)
Lemma prenex_exists_and_2 {Σ : Signature} (Γ : Theory) ϕ₁ ϕ₂:
  well_formed (ex, ϕ₁) ->
  well_formed ϕ₂ ->
  Γ ⊢i (ex, (ϕ₁ and ϕ₂)) ---> ((ex, ϕ₁) and ϕ₂)
  using ( (ExGen := {[fresh_evar ((ϕ₁ and ϕ₂))]}, SVSubst := ∅, KT := false, FP := ∅)).
Proof.
  intros wfϕ₁ wfϕ₂.
  toMLGoal.
  { wf_auto2. }
  mlIntro.
  mlSplitAnd.
  - fromMLGoal.
    remember (fresh_evar (ϕ₁ and ϕ₂)) as x.
    apply strip_exists_quantify_l with (x := x).
    { subst x. apply set_evar_fresh_is_fresh. }
    (* TODO: make wf_auto2 solve this *)
    { simpl. rewrite !andbT. split_and!.
      + wf_auto2.
      + wf_auto2.
    }
    apply strip_exists_quantify_r with (x := x).
    { subst x. eapply evar_is_fresh_in_richer'.
      2: { apply set_evar_fresh_is_fresh'. }
      simpl. clear. set_solver.
    }
    { wf_auto2. }
    apply ex_quan_monotone.
    { apply pile_refl. }

    unfold evar_open. simpl_bevar_subst.
    rewrite [bevar_subst ϕ₂ _ _]bevar_subst_not_occur.
    {
      wf_auto2.
    }
    toMLGoal.
    { wf_auto2. }
    mlIntro. mlDestructAnd 0. mlExactn 0.
  - fromMLGoal.
    remember (fresh_evar (ϕ₁ and ϕ₂)) as x.
    eapply cast_proof'.
    {
      rewrite -[ϕ₁ and ϕ₂](@evar_quantify_evar_open Σ x 0).
      { subst x. apply set_evar_fresh_is_fresh. }
      { cbn. split_and!; auto. wf_auto. wf_auto2. }
      reflexivity.
    }
    apply Ex_gen.
    { apply pile_refl. }
    { eapply evar_is_fresh_in_richer. 2: { subst x. apply set_evar_fresh_is_fresh'. }
      simpl. clear. set_solver.
    }

    unfold evar_open.
    simpl_bevar_subst.
    rewrite [bevar_subst ϕ₂ _ _]bevar_subst_not_occur.
    {
      wf_auto2.
    }
    toMLGoal.
    { wf_auto2. }
    mlIntro.
    mlDestructAnd 0.
    mlExactn 1.
Defined.

Lemma prenex_exists_and_iff {Σ : Signature} (Γ : Theory) ϕ₁ ϕ₂:
  well_formed (ex, ϕ₁) ->
  well_formed ϕ₂ ->
  Γ ⊢i (ex, (ϕ₁ and ϕ₂)) <---> ((ex, ϕ₁) and ϕ₂)
  using ( (ExGen := {[fresh_evar ((ϕ₁ and ϕ₂))]}, SVSubst := ∅, KT := false, FP := ∅)).
Proof.
  intros wfϕ₁ wfϕ₂.
  apply conj_intro_meta.
  { wf_auto2. }
  { wf_auto2. }
  - apply prenex_exists_and_2; assumption.
  - (* TODO we need a tactic to automate this change *)
    replace (fresh_evar (ϕ₁ and ϕ₂))
    with (fresh_evar (ϕ₂ ---> ex , (ϕ₁ and ϕ₂))).
    2: { cbn. unfold fresh_evar. apply f_equal. simpl. set_solver. }
   apply prenex_exists_and_1; assumption.
Defined.

Lemma patt_and_comm {Σ : Signature} Γ p q:
  well_formed p ->
  well_formed q ->
  Γ ⊢i (p and q) <---> (q and p)
  using BasicReasoning.
Proof.
  intros wfp wfq.
  toMLGoal.
  { wf_auto2. }
  mlSplitAnd; mlIntro; mlDestructAnd 0; mlSplitAnd.
  - mlExactn 1.
  - mlExactn 0.
  - mlExactn 1.
  - mlExactn 0.
Defined.

(* We need to come up with tactics that make this easier. *)
Local Example ex_mt {Σ : Signature} Γ ϕ₁ ϕ₂:
  well_formed ϕ₁ ->
  well_formed ϕ₂ ->
  Γ ⊢i (! ϕ₁ ---> ! ϕ₂) ---> (ϕ₂ ---> ϕ₁)
  using BasicReasoning.
Proof.
  intros wfϕ₁ wfϕ₂.
  toMLGoal.
  { wf_auto2. }
  mlIntro. mlIntro.
  unfold patt_not.
  mlAssert (((ϕ₁ ---> ⊥) ---> ⊥)).
  { wf_auto2. }
  { mlIntro.
    mlAssert ((ϕ₂ ---> ⊥)).
    { wf_auto2. }
    { mlApply 0. mlExactn 2. }
    mlApply 3.
    mlExactn 1.
  }
  mlApplyMeta (@not_not_elim Σ Γ ϕ₁ ltac:(wf_auto2)).
  mlExactn 2.
Defined.

Lemma well_formed_foldr_and {Σ : Signature} (x : Pattern) (xs : list Pattern):
  well_formed x ->
  Pattern.wf xs ->
  well_formed (foldr patt_and x xs).
Proof.
  intros wfx wfxs.
  induction xs; simpl.
  - assumption.
  - feed specialize IHxs.
    { unfold Pattern.wf in wfxs. simpl in wfxs. destruct_and!. assumption. }
    apply well_formed_and.
    { unfold Pattern.wf in wfxs. simpl in wfxs. destruct_and!. assumption. }
    assumption.
Qed.


Lemma lhs_and_to_imp {Σ : Signature} Γ (g x : Pattern) (xs : list Pattern):
  well_formed g ->
  well_formed x ->
  Pattern.wf xs ->
  Γ ⊢i (foldr patt_and x xs ---> g) ---> (foldr patt_imp g (x :: xs))
  using BasicReasoning.
Proof.
  intros wfg wfx wfxs.
  induction xs; simpl.
  - apply A_impl_A.
    { wf_auto2. }
  - pose proof (wfaxs := wfxs).
    unfold Pattern.wf in wfxs.
    simpl in wfxs.
    apply andb_prop in wfxs as [wfa wfxs].
    fold (Pattern.wf xs) in wfxs.
    specialize (IHxs wfxs).
    simpl in IHxs.
    assert (Hwffa: well_formed (foldr patt_and x xs)).
    { apply well_formed_foldr_and; assumption. }
    toMLGoal.
    { wf_auto2. }
    do 3 mlIntro.
    mlAdd IHxs.
    mlAssert (((foldr patt_and x xs ---> g) ---> foldr patt_imp g xs)).
    { wf_auto2. }
    { mlIntro.
      mlAssert ((x ---> foldr patt_imp g xs)).
      { wf_auto2. }
      { mlApply 0. mlExactn 4. }
      mlClear 0.
      mlApply 4.
      mlExactn 1.
    }
    mlClear 0.
    mlApply 3.
    mlClear 3.
    mlIntro.
    mlApply 0.
    mlSplitAnd.
    + mlExactn 2.
    + mlExactn 3.
Defined.

Lemma lhs_and_to_imp_meta {Σ : Signature} Γ (g x : Pattern) (xs : list Pattern) i:
  well_formed g ->
  well_formed x ->
  Pattern.wf xs ->
  Γ ⊢i (foldr patt_and x xs ---> g) using i ->
  Γ ⊢i (foldr patt_imp g (x :: xs)) using i.
Proof.
  intros wfg wfx wfxs H.
  eapply MP.
  2: { useBasicReasoning. apply lhs_and_to_imp; assumption. }
  exact H.
Defined.


(* TODO move this reshaper somewhere *)
Lemma lhs_and_to_imp_r {Σ : Signature} Γ (g x : Pattern) (xs : list Pattern) i :
  well_formed g ->
  well_formed x ->
  Pattern.wf xs ->
  forall (r : ImpReshapeS g (x::xs)),
     Γ ⊢i ((foldr (patt_and) x xs) ---> g) using i ->
     Γ ⊢i untagPattern (irs_flattened r) using i .
Proof.
  intros wfg wfx wfxs r H.
  eapply cast_proof'.
  { rewrite irs_pf; reflexivity. }
  clear r.
  apply lhs_and_to_imp_meta; assumption.
Defined.


Local Example ex_match {Σ : Signature} Γ a b c d:
  well_formed a ->
  well_formed b ->
  well_formed c ->
  well_formed d ->
  Γ ⊢i a ---> (b ---> (c ---> d)) using BasicReasoning.
Proof.
  intros wfa wfb wfc wfd.
  apply lhs_and_to_imp_r.
Abort.

Lemma forall_gen {Σ : Signature} Γ ϕ₁ ϕ₂ x (i : ProofInfo):
  evar_is_fresh_in x ϕ₁ ->
  ProofInfoLe ( (ExGen := {[x]}, SVSubst := ∅, KT := false, FP := ∅)) i ->
  Γ ⊢i ϕ₁ ---> ϕ₂ using i ->
  Γ ⊢i ϕ₁ ---> all, (evar_quantify x 0 ϕ₂) using i.
Proof.
  intros Hfr pile Himp.
  pose proof (Hwf := proved_impl_wf _ _ (proj1_sig Himp)).
  pose proof (wfϕ₁ := well_formed_imp_proj1 Hwf).
  pose proof (wfϕ₂ := well_formed_imp_proj2 Hwf).
  toMLGoal.
  { wf_auto2. }
  mlIntro.
  mlApplyMeta (@useBasicReasoning Σ Γ _ _ (@not_not_intro Σ Γ ϕ₁ ltac:(wf_auto2))) in 0.
  fromMLGoal.
  apply modus_tollens.

  eapply cast_proof'.
  {
    replace (! evar_quantify x 0 ϕ₂)
            with (evar_quantify x 0 (! ϕ₂))
                 by reflexivity.
    reflexivity.
  }
  apply Ex_gen.
  { exact pile. }
  { simpl. unfold evar_is_fresh_in in Hfr. clear -Hfr. set_solver. }
  apply modus_tollens; assumption.
Defined.



Lemma forall_variable_substitution' {Σ : Signature} Γ ϕ x (i : ProofInfo):
  well_formed ϕ ->
  (ProofInfoLe ( (ExGen := {[x]}, SVSubst := ∅, KT := false, FP := ∅)) i) ->
  Γ ⊢i (all, evar_quantify x 0 ϕ) ---> ϕ using i.
Proof.
  intros wfϕ pile.
  pose proof (Htmp := @forall_variable_substitution Σ Γ ϕ x wfϕ).
  eapply useGenericReasoning. apply pile. apply Htmp.
Defined.

Lemma forall_elim {Σ : Signature} Γ ϕ x (i : ProofInfo):
  well_formed (ex, ϕ) ->
  evar_is_fresh_in x ϕ ->
  ProofInfoLe ( (ExGen := {[x]}, SVSubst := ∅, KT := false, FP := ∅)) i ->
  Γ ⊢i (all, ϕ) using i ->
  Γ ⊢i (evar_open 0 x ϕ) using i.
Proof.
  intros wfϕ frϕ pile H.
  destruct i.
  eapply MP.
  2: eapply forall_variable_substitution'.
  2: wf_auto2.
  2: apply pile.
  eapply cast_proof'.
  {
    rewrite evar_quantify_evar_open.
    { apply frϕ. }
    { wf_auto2. }
    reflexivity.
  }
  apply H.
Defined.

Lemma prenex_forall_imp {Σ : Signature} Γ ϕ₁ ϕ₂ i:
  well_formed (ex, ϕ₁) ->
  well_formed ϕ₂ ->
  ProofInfoLe ( (ExGen := {[fresh_evar (ϕ₁ ---> ϕ₂)]}, SVSubst := ∅, KT := false, FP := ∅)) i ->
  Γ ⊢i (all, (ϕ₁ ---> ϕ₂)) using i ->
  Γ ⊢i (ex, ϕ₁) ---> (ϕ₂) using i.
Proof.
  intros wfϕ₁ wfϕ₂ pile H.
  remember (fresh_evar (ϕ₁ ---> ϕ₂)) as x.
  apply (@strip_exists_quantify_l Σ Γ x).
  { subst x.
    eapply evar_is_fresh_in_richer'.
    2: { apply set_evar_fresh_is_fresh'. }
    simpl. set_solver.
  }
  { wf_auto2. }
  apply Ex_gen.
  { apply pile. }
  1: {
    subst x.
    eapply evar_is_fresh_in_richer'.
    2: { apply set_evar_fresh_is_fresh'. }
    simpl. set_solver.
  }

  eapply cast_proof'.
  {
    rewrite -[HERE in evar_open _ _ _ ---> HERE](@evar_open_not_occur Σ 0 x ϕ₂).
    {
      wf_auto2.
    }
    reflexivity.
  }
  eapply forall_elim with (x := x) in H.
  4: { apply pile. }
  2: wf_auto2.
  2: { subst x. apply set_evar_fresh_is_fresh. }
  unfold evar_open in *. simpl in *. exact H.
Defined.

Lemma evar_fresh_in_foldr {Σ : Signature} x g l:
  evar_is_fresh_in x (foldr patt_imp g l) <-> evar_is_fresh_in x g /\ evar_is_fresh_in_list x l.
Proof.
  induction l; simpl; split; intros H.
  - split;[assumption|]. unfold evar_is_fresh_in_list. apply Forall_nil. exact I.
  - destruct H as [H _]. exact H.
  - unfold evar_is_fresh_in_list,evar_is_fresh_in in *. simpl in *.
    split;[set_solver|].
    apply Forall_cons.
    destruct IHl as [IHl1 IHl2].
    split;[set_solver|].
    apply IHl1. set_solver.
  - unfold evar_is_fresh_in_list,evar_is_fresh_in in *. simpl in *.
    destruct IHl as [IHl1 IHl2].
    destruct H as [H1 H2].
    inversion H2; subst.
    specialize (IHl2 (conj H1 H4)).
    set_solver.
Qed.

Lemma Ex_gen_lifted {Σ : Signature} (Γ : Theory) (ϕ₁ : Pattern) (l : list Pattern) (g : Pattern) (x : evar)
  (i : ProofInfo) :
  evar_is_fresh_in x g ->
  evar_is_fresh_in_list x l ->
  ProofInfoLe ( (ExGen := {[x]}, SVSubst := ∅, KT := false, FP := ∅)) i ->
  bevar_occur ϕ₁ 0 = false ->
  @mkMLGoal Σ Γ (ϕ₁::l) g i -> 
 @mkMLGoal Σ Γ ((exists_quantify x ϕ₁)::l) g i.
Proof.
  intros xfrg xfrl pile Hno0 H.
  mlExtractWF H1 H2.
  fromMLGoal.
  pose proof (H1' := H1).
  unfold Pattern.wf in H1. simpl in H1. apply andb_prop in H1. destruct H1 as [H11 H12].
  apply wf_ex_quan_impl_wf in H11. 2: assumption.
  unfold of_MLGoal in H. simpl in H.
  specialize (H H2).
  feed specialize H.
  {
    unfold Pattern.wf. simpl. rewrite H11 H12. reflexivity.
  }
  apply Ex_gen.
  { apply pile. }
  2: { assumption. }
  simpl.
  apply evar_fresh_in_foldr.
  split; assumption.
Defined.

(* Weakening under existential *)
Local Example ex_exists {Σ : Signature} Γ ϕ₁ ϕ₂ ϕ₃ i:
  well_formed (ex, ϕ₁) ->
  well_formed (ex, ϕ₂) ->
  well_formed ϕ₃ ->
  ProofInfoLe ( (ExGen := {[(evar_fresh (elements (free_evars ϕ₁ ∪ free_evars ϕ₂ ∪ free_evars (ex, ϕ₃))))]}, SVSubst := ∅, KT := false, FP := ∅)) i ->
  Γ ⊢i (all, (ϕ₁ and ϕ₃ ---> ϕ₂)) using i ->
  Γ ⊢i (ex, ϕ₁) ---> ϕ₃ ---> (ex, ϕ₂) using i.
Proof.
  intros wfϕ₁ wfϕ₂ wfϕ₃ pile H.
  toMLGoal.
  { wf_auto2. }
  mlIntro.
  remember (evar_fresh (elements (free_evars ϕ₁ ∪ free_evars ϕ₂ ∪ free_evars (ex, ϕ₃)))) as x.
  rewrite -[ϕ₁](@evar_quantify_evar_open Σ x 0).
  { subst x.
    eapply evar_is_fresh_in_richer'. 2: apply set_evar_fresh_is_fresh'. clear. set_solver.
  }
  wf_auto2.
  mlIntro.
  apply Ex_gen_lifted.
  { subst x. eapply evar_is_fresh_in_richer'. 2: apply set_evar_fresh_is_fresh'. clear. set_solver. }
  { constructor. 2: apply Forall_nil; exact I.
    subst x.
    eapply evar_is_fresh_in_richer'. 2: apply set_evar_fresh_is_fresh'. clear. set_solver.
  }
  { wf_auto. }

Abort.

(* This is an example and belongs to the end of this file.
   Its only purpose is only to show as many tactics as possible.\
 *)
   Lemma ex_and_of_equiv_is_equiv_2 {Σ : Signature} Γ p q p' q' i:
    well_formed p ->
    well_formed q ->
    well_formed p' ->
    well_formed q' ->
    Γ ⊢i (p <---> p') using i ->
    Γ ⊢i (q <---> q') using i ->
    Γ ⊢i ((p and q) <---> (p' and q')) using i.
  Proof.
    intros wfp wfq wfp' wfq' pep' qeq'.
    pose proof (pip' := pep'). apply pf_conj_elim_l_meta in pip'; auto.
    pose proof (p'ip := pep'). apply pf_conj_elim_r_meta in p'ip; auto.
    pose proof (qiq' := qeq'). apply pf_conj_elim_l_meta in qiq'; auto.
    pose proof (q'iq := qeq'). apply pf_conj_elim_r_meta in q'iq; auto.

    toMLGoal.
    { wf_auto2. }
    unfold patt_iff.
    mlSplitAnd.
    - mlIntro.
      mlDestructAnd 0.
      mlSplitAnd.
      + mlApplyMeta pip'.
        mlExactn 0.
      + mlApplyMeta qiq' in 1.
        mlExactn 1.
    - mlIntro.
      unfold patt_and at 2.
      unfold patt_not at 1.
      mlIntro.
      mlDestructOr 1.
      + mlDestructAnd 0.
        unfold patt_not.
        mlApply 2.
        mlClear 2.
        mlClear 1.
        fromMLGoal.
        exact p'ip.
      + mlAdd q'iq.
        mlDestructAnd 1.
        mlAssert (q).
        { wf_auto2. }
        { mlApply 0. mlExactn 2. }
        unfold patt_not at 1.
        mlApply 3.
        mlExactn 4.
  Defined.

#[local]
Ltac tryExact l idx :=
  match l with
    | nil => idtac
    | (?a :: ?m) => try mlExactn idx; tryExact m (idx + 1)
  end.

#[global]
Ltac mlAssumption :=
  match goal with
    | [ |- @of_MLGoal ?Sgm (@mkMLGoal ?Sgm ?Ctx ?l ?g ?i) ] 
      =>
        tryExact l 0
  end.

Section FOL_helpers.

  Context {Σ : Signature}.

  Lemma MLGoal_revert (Γ : Theory) (l : list Pattern) (x g : Pattern) i :
      @mkMLGoal Σ Γ l (x ---> g) i ->
      @mkMLGoal Σ Γ (l ++ [x]) g i.
    Proof.
      intros H.
      unfold of_MLGoal in H. simpl in H.
      unfold of_MLGoal. simpl. intros wfxig wfl.

      feed specialize H.
      {
        abstract (
            apply wfapp_proj_2 in wfl;
            unfold Pattern.wf in wfl;
            simpl in wfl;
            rewrite andbT in wfl;
            wf_auto2
          ).
      }
      {
        abstract (apply wfapp_proj_1 in wfl; exact wfl).
      }

      eapply cast_proof'.
      { rewrite foldr_app. simpl. reflexivity. }
      exact H.
    Defined.

End FOL_helpers.

#[global]
  Ltac mlRevert :=
    match goal with
    | |- @of_MLGoal ?Sgm (@mkMLGoal ?Sgm ?Ctx ?l ?g ?i)
      => eapply cast_proof_ml_hyps;
         [(rewrite -[l](take_drop (length l - 1)); rewrite [take _ _]/=; rewrite [drop _ _]/=; reflexivity)|];
         apply MLGoal_revert
    end.

#[local]
  Lemma ex_or_of_equiv_is_equiv_2 {Σ : Signature} Γ p q p' q' i:
    well_formed p ->
    well_formed q ->
    well_formed p' ->
    well_formed q' ->
    Γ ⊢i (p <---> p') using i ->
    Γ ⊢i (q <---> q') using i ->
    Γ ⊢i ((p or q) <---> (p' or q')) using i.
  Proof.
    intros wfp wfq wfp' wfq' pep' qeq'.

    pose proof (pip' := pep'). apply pf_conj_elim_l_meta in pip'; auto.
    pose proof (p'ip := pep'). apply pf_conj_elim_r_meta in p'ip; auto.
    pose proof (qiq' := qeq'). apply pf_conj_elim_l_meta in qiq'; auto.
    pose proof (q'iq := qeq'). apply pf_conj_elim_r_meta in q'iq; auto.

    toMLGoal.
    { wf_auto2. }
    unfold patt_iff.
    mlSplitAnd.
    - mlIntro.
      mlDestructOr 0.
      mlLeft.
      + mlApplyMeta pip'.
        mlExactn 0.
      + mlRight.
        mlApplyMeta qiq'.
        mlExactn 0.
    - mlIntro.
      mlDestructOr 0.
      mlLeft.
      + mlApplyMeta p'ip.
        mlExactn 0.
      + mlRight.
        mlApplyMeta q'iq.
        mlExactn 0. 
  Defined.


Lemma impl_eq_or {Σ : Signature} Γ a b:
  well_formed a ->
  well_formed b ->
  Γ ⊢i ( (a ---> b) <---> ((! a) or b) )
  using BasicReasoning.
Proof.
  intros wfa wfb.
  toMLGoal.
  { wf_auto2. }
  repeat mlIntro.
  mlDestructOr 0.
  - mlApply 0. mlIntro. mlClear 0. mlIntro.
    mlApplyMeta (@not_not_elim _ _ _ _) in 1.
    mlApply 0. mlAssumption.
  - mlApply 0. mlIntro. mlClear 0. mlIntro.
    mlDestructOr 0.
    + mlApplyMeta (@false_implies_everything _ _ _ _).
      mlApply 0. mlAssumption.
    + mlAssumption.
  Unshelve. all: assumption.
Qed.


Lemma nimpl_eq_and {Σ : Signature} Γ a b:
  well_formed a ->
  well_formed b ->
  Γ ⊢i ( ! (a ---> b) <---> (a and !b) )
  using BasicReasoning.
Proof.
  intros wfa wfb.
  toMLGoal.
  { wf_auto2. }
  repeat mlIntro.
  mlDestructOr 0.
  - mlApply 0. repeat mlIntro.
    mlApply 1. mlIntro.
    mlDestructOr 2.
    + mlApplyMeta (false_implies_everything _ _).
      mlApply 2. mlAssumption.
    + mlApplyMeta (@not_not_elim _ _ _ _) in 2.
      mlAssumption.
  - mlApply 0. repeat mlIntro.
    mlDestructAnd 1. mlApply 2. mlApply 3.
    mlAssumption.
  Unshelve. all: assumption.
Qed.


Lemma deMorgan_nand {Σ : Signature} Γ a b:
    well_formed a ->
    well_formed b ->
    Γ ⊢i ( !(a and b) <---> (!a or !b) )
    using BasicReasoning.
  Proof.
    intros wfa wfb.
    toMLGoal.
    { wf_auto2. }
    repeat mlIntro.
    mlDestructOr 0.
    - mlRevert. mlApplyMeta (@not_not_intro _ _ _ _). repeat mlIntro.
      mlApplyMeta (@not_not_elim _ _ _ _) in 1.
      mlApply 0. mlIntro.
      mlDestructOr 3.
      all: mlApply 3; mlAssumption.
    - mlRevert. mlApplyMeta (@not_not_intro _ _ _ _). repeat mlIntro.
      mlDestructAnd 1.
      mlDestructOr 0.
      all: mlApply 0; mlAssumption.
    Unshelve. all: auto.
  Qed.

Lemma deMorgan_nor {Σ : Signature} Γ a b:
    well_formed a ->
    well_formed b ->
    Γ ⊢i ( !(a or b) <---> (!a and !b))
    using BasicReasoning.
  Proof.
    intros wfa wfb.
    toMLGoal.
    { wf_auto2. }
    repeat mlIntro.
    mlDestructOr 0.
    - mlRevert. mlApplyMeta (@not_not_intro _ _ _ _). repeat mlIntro.
      mlApply 0.
      mlDestructOr 1.
      + mlApplyMeta (@not_not_elim _ _ _ _) in 1.
        mlLeft. mlAssumption.
      + mlApplyMeta (@not_not_elim _ _ _ _) in 1.
        mlRight. mlAssumption.
    - mlRevert. mlApplyMeta (@not_not_intro _ _ _ _). repeat mlIntro.
      mlDestructAnd 0.
      mlDestructOr 2.
      + mlApply 0. mlAssumption.
      + mlApply 1. mlAssumption.
    Unshelve. all: wf_auto2.
  Qed.

Lemma not_not_eq {Σ : Signature} (Γ : Theory) (a : Pattern) :
  well_formed a ->
  Γ ⊢i (!(!a) <---> a)
  using BasicReasoning.
Proof.
  intros wfa.
  toMLGoal.
  { wf_auto2. }
  mlIntro.
  mlDestructOr 0.
  - mlApply 0. mlIntro.
    mlApplyMeta (@not_not_elim _ _ _ _) in 1.
    mlAssumption.
  - unfold patt_not. mlApply 0. repeat mlIntro.
    mlApply 2. mlAssumption.
  Unshelve.
  all: assumption.
Defined.
(* TODO: de-duplicate the code *)
#[local]
Ltac convertToNNF_rewrite_pat Ctx p i :=
  lazymatch p with
    | (! ! ?x) =>
        let H' := fresh "H" in
        pose proof (@not_not_eq _ Ctx x ltac:(wf_auto2)) as H';
        apply (@useBasicReasoning _ _ _ i) in H';
        repeat (mlRewrite H' at 1);
        try clear H';
        convertToNNF_rewrite_pat Ctx x i
    | patt_not (patt_and ?x ?y) =>
        let H' := fresh "H" in
        pose proof (@deMorgan_nand _ Ctx x y ltac:(wf_auto2) ltac:(wf_auto2)) as H';
        apply (@useBasicReasoning _ _ _ i) in H';
        repeat (mlRewrite H' at 1);
        try clear H';
        convertToNNF_rewrite_pat Ctx (!x or !y) i
    | patt_not (patt_or ?x ?y) =>
        let H' := fresh "H" in
        pose proof (@deMorgan_nor _ Ctx x y ltac:(wf_auto2) ltac:(wf_auto2)) as H';
        apply (@useBasicReasoning _ _ _ i) in H';
        repeat (mlRewrite H' at 1);
        try clear H';
        convertToNNF_rewrite_pat Ctx (!x and !y) i
    | patt_not (?x ---> ?y) =>
        let H' := fresh "H" in
        pose proof (@nimpl_eq_and _ Ctx x y ltac:(wf_auto2) ltac:(wf_auto2)) as H';
        apply (@useBasicReasoning _ _ _ i) in H';
        repeat (mlRewrite H' at 1);
        try clear H';
        convertToNNF_rewrite_pat Ctx (x and !y) i
    | (?x ---> ?y) =>
        let H' := fresh "H" in
        pose proof (@impl_eq_or _ Ctx x y ltac:(wf_auto2) ltac:(wf_auto2)) as H';
        apply (@useBasicReasoning _ _ _ i) in H';
        repeat (mlRewrite H' at 1);
        try clear H';
        convertToNNF_rewrite_pat Ctx (!x or y) i
    | patt_and ?x ?y => convertToNNF_rewrite_pat Ctx x i; convertToNNF_rewrite_pat Ctx y i
    | patt_or ?x ?y => convertToNNF_rewrite_pat Ctx x i; convertToNNF_rewrite_pat Ctx y i
    | _ => idtac
  end.

#[local]
Ltac toNNF := 
  repeat mlRevert;
  match goal with
    | [ |- @of_MLGoal ?Sgm (@mkMLGoal ?Sgm ?Ctx ?ll ?g ?i) ] 
      =>
        mlApplyMeta (@useBasicReasoning _ _ _ i (@not_not_elim Sgm Ctx g ltac:(wf_auto2)));
        convertToNNF_rewrite_pat Ctx (!g) i
  end.

#[local] Example test_toNNF {Σ : Signature} Γ a b :
  well_formed a ->
  well_formed b ->
  Γ ⊢i ( (b and (a or b) and !b and ( a or a) and a) ---> ⊥)
  using BasicReasoning.
Proof.
  intros wfa wfb.
  toMLGoal.
  { wf_auto2. }
  toNNF.
Abort.

#[local]
Ltac rfindContradictionTo a ll k n:=
  match ll with
    | ((! a) :: ?m) =>
        mlApply n; mlExactn k
    | (?b :: ?m) => 
        let nn := eval compute in ( n + 1 ) in
         (rfindContradictionTo a m k nn)
    | _ => fail
  end.

#[local]
Ltac findContradiction l k:=
    match l with
       | (?a :: ?m) => 
             match goal with
                | [ |- @of_MLGoal ?Sgm (@mkMLGoal ?Sgm ?Ctx ?ll ?g ?i) ] 
                  =>
                     try rfindContradictionTo a ll k 0;
                     let kk := eval compute in ( k + 1 ) in
                     (findContradiction m kk)
             end
       | _ => fail
    end.

#[local]
Ltac findContradiction_start :=
  match goal with
    | [ |- @of_MLGoal ?Sgm (@mkMLGoal ?Sgm ?Ctx ?l ?g ?i) ] 
      =>
        match goal with
          | [ |- @of_MLGoal ?Sgm (@mkMLGoal ?Sgm ?Ctx ?l ?g ?i) ] 
            =>
              findContradiction l 0
        end
  end.

#[local]
Ltac breakHyps l n:=
  let nn := eval compute in ( n + 1)
  in
  (
    match l with
    | ((?x and ?y) :: ?m) => 
        mlDestructAnd n
    | ((?x or ?y) :: ?m) => 
        mlDestructOr n
    | (?x :: ?m)  =>
        breakHyps m nn
    end
  )
.
#[local]
Ltac mlTautoBreak := repeat match goal with
| [ |- @of_MLGoal ?Sgm (@mkMLGoal ?Sgm ?Ctx ?l ?g ?i) ] 
  =>
    lazymatch g with
      | (⊥) =>
              breakHyps l 0
      | _ => mlApplyMeta (@useBasicReasoning _ _ _ i (@false_implies_everything _ _ g _))
    end
end.

Ltac try_solve_pile2 fallthrough :=
  lazymatch goal with
  | [ |- ProofInfoLe _ _] => try apply pile_refl; try_solve_pile; fallthrough
  | _ => idtac
  end.

#[global]
Ltac mlTauto :=
  unshelve(
    try (
      toNNF; (try_solve_pile2 shelve);
      repeat mlIntro;
      mlTautoBreak;
      findContradiction_start
    )
  )
.

#[local]
Example conj_right {Σ : Signature} Γ a b:
  well_formed a ->
  well_formed b ->
  Γ ⊢i ( (b and (a or b) and !b and ( a or a) and a) ---> ⊥)
  using AnyReasoning.
Proof.
  intros wfa wfb.
  toMLGoal.
  { wf_auto2. }
  (* TODO: fail loudly if there is something else than AnyReasoning *)
  mlTauto.
Defined.

#[local]
Example condtradict_taut_2 {Σ : Signature} Γ a b:
  well_formed a ->
  well_formed b ->
  Γ ⊢i (a ---> ((! a) ---> b))
  using AnyReasoning.
Proof.
  intros wfa wfb.
  toMLGoal.
  { wf_auto2. }
  mlTauto.
Qed.

#[local]
Example taut {Σ : Signature} Γ a b c:
  well_formed a ->
  well_formed b ->
  well_formed c ->
  Γ ⊢i ((a ---> b) ---> ((b ---> c) ---> ((a or b)---> c)))
  using AnyReasoning.
Proof.
  intros wfa wfb wfc.
  toMLGoal.
  { wf_auto2. }
  mlTauto. (* Slow *)
Qed.

#[local]
Example condtradict_taut_1 {Σ : Signature} Γ a:
  well_formed a ->
  Γ ⊢i !(a and !a)
  using AnyReasoning.
Proof.
  intros wfa.
  toMLGoal.
  { wf_auto2. }
  mlTauto.
Qed.

#[local]
Example notnot_taut_1 {Σ : Signature} Γ a:
  well_formed a ->
  Γ ⊢i (! ! a ---> a)
  using AnyReasoning.
Proof.
  intros wfa.
  toMLGoal.
  { wf_auto2. }
  mlTauto.
Qed.

#[local]
Lemma Peirce_taut {Σ : Signature} Γ a b:
  well_formed a ->
  well_formed b ->
  Γ ⊢i ((((a ---> b) ---> a) ---> a))
  using AnyReasoning.
Proof.
  intros wfa wfb.
  toMLGoal.
  { wf_auto2. }
  mlTauto.
Qed.
