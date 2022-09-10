From Coq Require Import ssreflect ssrfun ssrbool.

From Ltac2 Require Import Ltac2.

From Coq Require Import Ensembles Bool String.
From Coq.Logic Require Import FunctionalExtensionality Eqdep_dec.
From Equations Require Import Equations.

Require Import Coq.Program.Tactics.

From MatchingLogic Require Import Syntax
                                  ProofSystem
                                  wftactics
                                  ProofMode_base.

From stdpp Require Import list tactics fin_sets coGset gmap sets.

From MatchingLogic.Utils Require Import stdpp_ext.

Import extralibrary.

Import
  MatchingLogic.Syntax.Notations
  MatchingLogic.DerivedOperators_Syntax.Notations
  MatchingLogic.ProofSystem.Notations
.

Set Default Proof Mode "Classic".

Open Scope ml_scope.

Ltac solve_pim_simple := constructor; simpl;[(set_solver)|(set_solver)|(reflexivity)|(apply reflexivity)].


Lemma useBasicReasoning {Σ : Signature} {Γ : Theory} {ϕ : Pattern} (i : ProofInfo) :
  Γ ⊢i ϕ using BasicReasoning ->
  Γ ⊢i ϕ using i.
Proof.
  intros H.
  pose proof (Hpf := proj2_sig H).
  remember (proj1_sig H) as _H.
  exists (_H).
  clear Heq_H.
  abstract (
    destruct Hpf as [Hpf1 Hpf2 Hpf3 Hpf4];
  destruct i; constructor; simpl in *;
  [set_solver|set_solver|idtac|set_solver];
  (destruct (uses_kt _H); simpl in *; try congruence)).
Defined.


Lemma mlUseBasicReasoning
  {Σ : Signature} (Γ : Theory) (l : hypotheses) (g : Pattern) (i : ProofInfo) :
  mkMLGoal Σ Γ l g BasicReasoning ->
  mkMLGoal Σ Γ l g i.
Proof.
  intros H wf1 wf2.
  specialize (H wf1 wf2).
  apply useBasicReasoning.
  exact H.
Defined.


Ltac useBasicReasoning :=
  unfold ProofSystem.derives;
  lazymatch goal with
  | [ |- of_MLGoal (mkMLGoal _ _ _ _ _) ] => apply mlUseBasicReasoning
  | [ |- _ ⊢i _ using _ ] => apply useBasicReasoning
  end.


Tactic Notation "remember_constraint" "as" ident(i') :=
    match goal with
    | [|- (_ ⊢i _ using ?constraint)] => remember constraint as i'
    end.

Lemma MP {Σ : Signature} {Γ : Theory} {ϕ₁ ϕ₂ : Pattern} {i : ProofInfo} :
  Γ ⊢i ϕ₁ using i ->
  Γ ⊢i (ϕ₁ ---> ϕ₂) using i ->
  Γ ⊢i ϕ₂ using i.
Proof.
  intros H1 H2.
  unshelve (eexists).
  {
    eapply (ProofSystem.Modus_ponens _ _ _).
    { apply H1. }
    { apply H2. }
  }
  {
    abstract(
      simpl;
      destruct H1 as [pf1 Hpf1];
      destruct H2 as [pf2 Hpf2];
      destruct Hpf1,Hpf2;
      constructor; simpl;
      [set_solver|set_solver|(destruct (uses_kt pf1),(uses_kt pf2); simpl in *; congruence)|set_solver]
    ).
  }
Defined.

Lemma P1 {Σ : Signature} (Γ : Theory) (ϕ ψ : Pattern) :
  well_formed ϕ ->
  well_formed ψ ->
  Γ ⊢i ϕ ---> ψ ---> ϕ 
  using BasicReasoning.
Proof.
  intros wfϕ wfψ.
  unshelve (eexists).
  { apply ProofSystem.P1. exact wfϕ. exact wfψ. }
  { abstract(solve_pim_simple). }
Defined.

Lemma P2 {Σ : Signature} (Γ : Theory) (ϕ ψ ξ : Pattern) :
  well_formed ϕ ->
  well_formed ψ ->
  well_formed ξ ->
  Γ ⊢i (ϕ ---> ψ ---> ξ) ---> (ϕ ---> ψ) ---> (ϕ ---> ξ)
  using BasicReasoning.
Proof.
  intros wfϕ wfψ wfξ.
  unshelve (eexists).
  { apply ProofSystem.P2. exact wfϕ. exact wfψ. exact wfξ. }
  { abstract (solve_pim_simple). }
Defined.

Lemma P3 {Σ : Signature} (Γ : Theory) (ϕ : Pattern) :
  well_formed ϕ ->
  Γ ⊢i (((ϕ ---> ⊥) ---> ⊥) ---> ϕ)
  using BasicReasoning.
Proof.
  intros wfϕ.
  unshelve (eexists).
  { apply ProofSystem.P3. exact wfϕ. }
  { abstract ( solve_pim_simple ). }
Defined.

  Lemma A_impl_A {Σ : Signature} (Γ : Theory) (A : Pattern)  :
    (well_formed A) ->
    Γ ⊢i (A ---> A)
    using BasicReasoning.
  Proof. 
    intros WFA.
    pose proof (_1 := P2 Γ A (A ---> A) A ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2)).
    pose proof (_2 := P1 Γ A (A ---> A) ltac:(wf_auto2) ltac:(wf_auto2)).
    pose proof (_3 := MP _2 _1).
    pose proof (_4 := P1 Γ A A ltac:(wf_auto2) ltac:(wf_auto2)).
    pose proof (_5 := MP _4 _3).
    exact _5.
  Defined.

  Lemma pile_evs_svs_kt_back {Σ : Signature} evs1 evs2 svs1 svs2 kt1 kt2 fp1 fp2:
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
      pose (pf1 := A_impl_A ∅ (patt_free_evar y) ltac:(wf_auto2)).
      pose (pf2 := ProofSystem.Ex_gen ∅ (patt_free_evar y) (patt_free_evar y) x ltac:(wf_auto2) ltac:(wf_auto2) (proj1_sig pf1) ltac:(simpl; rewrite elem_of_singleton; solve_fresh_neq)).
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
      pose (pf1 := A_impl_A ∅ (patt_free_svar X) ltac:(wf_auto2)).
      pose (pf2 := ProofSystem.Svar_subst ∅ (patt_free_svar X ---> patt_free_svar X) patt_bott X ltac:(wf_auto2) ltac:(wf_auto2) (proj1_sig pf1)).
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
      pose (pf1 := A_impl_A ∅ patt_bott ltac:(wf_auto2)).
      pose (pf2 := ProofSystem.Knaster_tarski ∅ (patt_bound_svar 0) patt_bott ltac:(wf_auto2) (proj1_sig pf1)).
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
      pose (pf1 := A_impl_A ∅ patt_bott ltac:(wf_auto2)).
      pose (pf2 := Framing_left ∅ patt_bott patt_bott p wfp (proj1_sig pf1)).
      pose (pf3 := Framing_right ∅ patt_bott patt_bott p wfp (proj1_sig pf1)).
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

Lemma useGenericReasoning  {Σ : Signature} (Γ : Theory) (ϕ : Pattern) evs svs kt fp i:
  (ProofInfoLe ((ExGen := evs, SVSubst := svs, KT := kt, FP := fp)) i) ->
  Γ ⊢i ϕ using ((ExGen := evs, SVSubst := svs, KT := kt, FP := fp)) ->
  Γ ⊢i ϕ using i.
Proof.
  intros pile [pf Hpf].
  exists pf.
  destruct Hpf as [Hpf2 Hpf3 Hpf4 Hpf5].
  simpl in *.
  destruct i.
  pose proof (Htmp := pile_evs_svs_kt_back).
  specialize (Htmp evs pi_generalized_evars svs pi_substituted_svars kt pi_uses_kt fp pi_framing_patterns pile).
  destruct Htmp as [Hevs [Hsvs [Hkt Hfp] ] ].
  constructor; simpl.
  { clear -Hpf2 Hevs. set_solver. }
  { clear -Hpf3 Hsvs. set_solver. }
  { unfold implb in *. repeat case_match; try reflexivity; try assumption. inversion Hpf4. }
  { clear -Hpf5 Hfp. set_solver.  }
Defined.

Lemma useGenericReasoning'  {Σ : Signature} (Γ : Theory) (ϕ : Pattern) i' i:
  (ProofInfoLe i' i) ->
  Γ ⊢i ϕ using i' ->
  Γ ⊢i ϕ using i.
Proof.
  intros H.
  destruct i'.
  apply useGenericReasoning.
  exact H.
Qed.

Lemma mlUseGenericReasoning
  {Σ : Signature} (Γ : Theory) (l : hypotheses) (g : Pattern) (i i' : ProofInfo) :
  ProofInfoLe i i' ->
  mkMLGoal Σ Γ l g i ->
  mkMLGoal Σ Γ l g i'.
Proof.
  intros pile H wf1 wf2.
  specialize (H wf1 wf2).
  simpl in *.
  destruct i.
  eapply useGenericReasoning.
  { apply pile. }
  exact H.
Defined.

Tactic Notation "gapply" uconstr(pf) := eapply useGenericReasoning;[|eapply pf].

Tactic Notation "gapply" uconstr(pf) "in" ident(H) :=
  eapply useGenericReasoning in H;[|apply pf].


(* Extracts well-formedness assumptions about (local) goal and (local) hypotheses. *)
Tactic Notation "mlExtractWF" ident(wfl) ident(wfg) :=
match goal with
| [ |- ?g ] =>
  let wfl' := fresh "wfl'" in
  let wfg' := fresh "wfg'" in
  intros wfg' wfl';
  pose proof (wfl := wfl');
  pose proof (wfg := wfg');
  revert wfg' wfl';
  fold g;
  rewrite /mlConclusion in wfg;
  rewrite /mlHypotheses in wfl
end.

Local Example ex_extractWfAssumptions {Σ : Signature} Γ (p : Pattern) :
  well_formed p ->
  Γ ⊢i p ---> p using BasicReasoning.
Proof.
  intros wfp.
  toMLGoal.
  { auto. }
  mlExtractWF wfl wfg.
  (* These two asserts by assumption only test presence of the two hypotheses *)
  assert (Pattern.wf []) by assumption.
  assert (well_formed (p ---> p)) by assumption.
Abort.

Lemma pile_evs_subseteq {Σ : Signature} evs1 evs2 svs kt fp:
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

Lemma pile_svs_subseteq {Σ : Signature} evs svs1 svs2 kt fp:
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

Lemma pile_kt_impl {Σ : Signature} evs svs kt1 kt2 fp:
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

Lemma pile_fp_subseteq  {Σ : Signature} evs svs kt fp1 fp2:
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


Lemma pile_evs_svs_kt {Σ : Signature} evs1 evs2 svs1 svs2 kt1 kt2 fp1 fp2:
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

Lemma pile_any {Σ : Signature} i:
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

Tactic Notation "aapply" uconstr(pf)
:= gapply pf; try apply pile_any.

Ltac try_solve_pile := try (solve [(apply pile_evs_svs_kt; auto; try set_solver)]).


Lemma pile_basic_generic {Σ : Signature} eg svs kt fp:
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

Lemma pile_basic_generic' {Σ : Signature} i:
ProofInfoLe BasicReasoning i.
Proof.
  destruct i.
  apply pile_basic_generic.
Qed.


Tactic Notation "_mlReshapeHypsByIdx" constr(n) :=
  unshelve (eapply (@cast_proof_ml_hyps _ _ _ _ _ _ _));
  [shelve|(apply f_equal; rewrite <- (firstn_skipn n); rewrite /firstn; rewrite /skipn; reflexivity)|idtac]
.

Tactic Notation "_mlReshapeHypsByName" constr(n) :=
  unshelve (eapply (@cast_proof_ml_hyps _ _ _ _ _ _ _));
  [shelve|(
    apply f_equal;
    lazymatch goal with
    | [|- _ = ?l] =>
      lazymatch (eval cbv in (find_hyp n l)) with
      | Some (?n, _) =>
        rewrite <- (firstn_skipn n);
        rewrite /firstn;
        rewrite /skipn;
        reflexivity
      end
    end
    )
  |idtac]
.

Ltac2 _mlReshapeHypsByName (name' : constr) :=
  ltac1:(name'' |- _mlReshapeHypsByName name'') (Ltac1.of_constr name')
.

Tactic Notation "_mlReshapeHypsBack" :=
  let hyps := fresh "hyps" in rewrite [hyps in mkMLGoal _ _ hyps _]/app
.

Ltac2 _mlReshapeHypsBack () :=
  ltac1:(_mlReshapeHypsBack)
.

Lemma prf_add_assumption {Σ : Signature} Γ a b i :
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

Lemma pile_impl_allows_gen_x {Σ : Signature} x gpi svs kt fp:
  ProofInfoLe ( (ExGen := {[x]}, SVSubst := svs, KT := kt, FP := fp)) ( gpi) ->
  x ∈ pi_generalized_evars gpi.
Proof.
  intros [H].
  pose (H1 := A_impl_A ∅ patt_bott ltac:(wf_auto2)).
  pose (H2 := prf_add_assumption ∅ (patt_free_evar x) (patt_bott ---> patt_bott) BasicReasoning ltac:(wf_auto2) ltac:(wf_auto2) H1).
  pose (H3 := ProofSystem.Ex_gen ∅ (patt_free_evar x) (patt_bott ---> patt_bott) x ltac:(wf_auto2) ltac:(wf_auto2) (proj1_sig H2) ltac:(simpl; set_solver)).
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

Lemma pile_impl_uses_kt {Σ : Signature} gpi evs svs fp:
  ProofInfoLe ( (ExGen := evs, SVSubst := svs, KT := true, FP := fp)) ( gpi) ->
  pi_uses_kt gpi.
Proof.
  intros [H].
  specialize (H ∅).
  pose (pf1 := A_impl_A ∅ patt_bott ltac:(wf_auto2)).
  pose (pf2 := ProofSystem.Knaster_tarski ∅ (patt_bound_svar 0) patt_bott ltac:(wf_auto2) (proj1_sig pf1)).
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

Lemma pile_impl_allows_svsubst_X {Σ : Signature} gpi evs X kt fp:
  ProofInfoLe ( (ExGen := evs, SVSubst := {[X]}, KT := kt, FP := fp)) ( gpi) ->
  X ∈ pi_substituted_svars gpi.
Proof.
  intros [H].
  specialize (H ∅).
  pose (pf1 := A_impl_A ∅ (patt_free_svar X) ltac:(wf_auto2)).
  pose (pf2 := ProofSystem.Svar_subst ∅ (patt_free_svar X ---> patt_free_svar X) patt_bott X ltac:(wf_auto2) ltac:(wf_auto2) (proj1_sig pf1)).
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

Lemma liftPi {Σ : Signature} (Γ : Theory) (ϕ : Pattern) (i₁ i₂ : ProofInfo)
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

  Lemma useAnyReasoning {Σ : Signature} {Γ ϕ i}:
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

Close Scope ml_scope.