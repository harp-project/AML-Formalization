From Coq Require Import ssreflect ssrfun ssrbool.

From Ltac2 Require Import Ltac2.

From Coq Require Import Ensembles Bool String Btauto.
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

(** For goals shaped like ProoInforMeeaning _ _ _ BasicReasoning *)
Ltac solve_pim_simple := constructor; simpl;[(set_solver)|(set_solver)|(reflexivity)|(reflexivity)].


Lemma useBasicReasoning {Σ : Signature} {Γ : Theory} {ϕ : Pattern} (i : ProofInfo) :
  Γ ⊢i ϕ using BasicReasoning ->
  Γ ⊢i ϕ using i.
Proof.
  intros H.
  pose proof (Hpf := proj2_sig H).
  remember (proj1_sig H) as _H.
  exists (_H).
  clear Heq_H.
  destruct Hpf as [Hpf1 Hpf2 Hpf3 Hpf4].
  destruct i; constructor; simpl in *;
  [set_solver|set_solver|idtac|idtac].
  {
    (destruct (uses_kt _H); simpl in *; try congruence).
  }
  {
    (destruct (uses_kt_unreasonably _H); simpl in *; try congruence).
  }
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
    
      simpl;
      destruct H1 as [pf1 Hpf1];
      destruct H2 as [pf2 Hpf2];
      destruct Hpf1,Hpf2;
      constructor; simpl;
      [set_solver
      |set_solver
      |(destruct (uses_kt pf1),(uses_kt pf2); simpl in *; congruence)
      |idtac]
    .
    unfold is_true in pwi_pf_kt.
    rewrite implb_true_iff in pwi_pf_kt.
    unfold is_true in pwi_pf_kta.
    rewrite implb_true_iff in pwi_pf_kta.
    unfold is_true in pwi_pf_kt0.
    rewrite implb_true_iff in pwi_pf_kt0.
    unfold is_true in pwi_pf_kta0.
    rewrite implb_true_iff in pwi_pf_kta0.
    unfold is_true.
    rewrite implb_true_iff.
    intro H.
    rewrite orb_true_iff in H.
    destruct H as [H|H].
    {
      specialize (pwi_pf_kta H).
      rewrite andb_true_iff in pwi_pf_kta.
      destruct pwi_pf_kta as [H1 H2].
      rewrite H1 H2. reflexivity.
    }
    {
      specialize (pwi_pf_kta0 H).
      rewrite andb_true_iff in pwi_pf_kta0.
      destruct pwi_pf_kta0 as [H1 H2].
      rewrite H1 H2.
      rewrite orb_true_r.
      reflexivity.
    }
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

Lemma useGenericReasoning  {Σ : Signature} (Γ : Theory) (ϕ : Pattern) i' i:
  (ProofInfoLe i' i) ->
  Γ ⊢i ϕ using i' ->
  Γ ⊢i ϕ using i.
Proof.
  intros pile [pf Hpf].
  exists pf.

  destruct Hpf as [Hpf2 Hpf3 Hpf4 Hpf5].
  destruct i, i'; cbn in *.
  destruct pile as [H [H0 H1] ].
  constructor; simpl.
  { set_solver. }
  { set_solver. }
  { simpl in *. apply implb_true_iff.
    unfold is_true in *. rewrite implb_true_iff in Hpf4 H1.
    set_solver.
  }
  {
    simpl in *. apply implb_true_iff.
    unfold is_true in *. rewrite implb_true_iff in Hpf5 H1.
    destruct H1 as [H11 H12].
    rewrite implb_true_iff in H11.
    rewrite implb_true_iff in H12.
    intros H'.
    naive_solver.
  }
Defined.

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

Lemma pile_any {Σ : Signature} i:
  ProofInfoLe i AnyReasoning.
Proof.
  try_solve_pile.
Qed.

Tactic Notation "aapply" uconstr(pf)
:= gapply pf; try apply pile_any.

Lemma pile_basic_generic {Σ : Signature} i:
  ProofInfoLe BasicReasoning i.
Proof.
  try_solve_pile.
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

Lemma pile_impl_allows_gen_x {Σ : Signature} x gpi svs kt:
  ProofInfoLe ( (ExGen := {[x]}, SVSubst := svs, KT := kt, AKT := false)) ( gpi) ->
  x ∈ pi_generalized_evars gpi.
Proof.
  destruct gpi. intro H.
  destruct_pile. set_solver.
Qed.

Lemma pile_impl_uses_kt {Σ : Signature} gpi evs svs:
  ProofInfoLe ( (ExGen := evs, SVSubst := svs, KT := true, AKT := false)) ( gpi) ->
  pi_uses_kt gpi.
Proof.
  destruct gpi. intro H.
  destruct_pile. set_solver.
Qed.

Lemma pile_impl_allows_svsubst_X {Σ : Signature} gpi evs X kt:
  ProofInfoLe ( (ExGen := evs, SVSubst := {[X]}, KT := kt, AKT := false)) ( gpi) ->
  X ∈ pi_substituted_svars gpi.
Proof.
  destruct gpi. intro H.
  destruct_pile. set_solver.
Qed.

Lemma liftProofLe {Σ : Signature} (Γ : Theory) (ϕ : Pattern) (i₁ i₂ : ProofInfo)
  {pile : ProofLe i₁ i₂}
  :
  Γ ⊢i ϕ using i₁ ->
  Γ ⊢i ϕ using i₂.
Proof.
    intros [pf Hpf].
    apply pile in Hpf.
    exists pf.
    exact Hpf.
Qed.

Lemma liftProofInfoLe {Σ : Signature} (Γ : Theory) (ϕ : Pattern) (i₁ i₂ : ProofInfo)
  {pile : ProofInfoLe i₁ i₂}
  :
  Γ ⊢i ϕ using i₁ ->
  Γ ⊢i ϕ using i₂.
Proof.
    intros H.
    eapply liftProofLe.
    apply ProofInfoLe_ProofLe.
    all: eassumption.
Qed.

Tactic Notation "use" constr(i) "in" ident(H) :=
  apply liftProofInfoLe with (i₂ := i) in H; [|try_solve_pile].

Close Scope ml_scope.