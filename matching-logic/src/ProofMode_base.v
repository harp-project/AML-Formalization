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

Open Scope ml_scope.



Record MLGoal {Σ : Signature} : Type := mkMLGoal
  { mlTheory : Theory;
    mlHypotheses: list Pattern;
    mlConclusion : Pattern ;
    mlInfo : ProofSystem.ProofInfo ;
  }.

Definition MLGoal_from_goal
  {Σ : Signature} (Γ : Theory) (goal : Pattern) (pi : ProofInfo)
  :
  MLGoal
  := @mkMLGoal Σ Γ nil goal pi.

Coercion of_MLGoal {Σ : Signature} (MG : MLGoal) : Type :=
  well_formed (mlConclusion MG) ->
  Pattern.wf (mlHypotheses MG) ->
  (mlTheory MG) ⊢i (fold_right patt_imp (mlConclusion MG) (mlHypotheses MG))
  using (mlInfo MG).

  (* This is useful only for printing. *)
  Notation "[ S , G ⊢ l ==> g ]  'using' pi "
  := (@mkMLGoal S G l g pi) (at level 95, no associativity, only printing).


Ltac toMLGoal :=
  unfold ProofSystem.derives;
  lazymatch goal with
  | [ |- ?G ⊢i ?phi using ?pi]
    => cut (of_MLGoal (MLGoal_from_goal G phi pi));
       unfold MLGoal_from_goal;
       [(unfold of_MLGoal; simpl; let H := fresh "H" in intros H; apply H; clear H; [|reflexivity])|]
  end.

Ltac fromMLGoal := unfold of_MLGoal; simpl; intros _ _.

Ltac solve_pim_simple := constructor; simpl;[(set_solver)|(set_solver)|(reflexivity)|(apply reflexivity)].


Lemma useBasicReasoning {Σ : Signature} (Γ : Theory) (ϕ : Pattern) (i : ProofInfo) :
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
  {Σ : Signature} (Γ : Theory) (l : list Pattern) (g : Pattern) (i : ProofInfo) :
  @mkMLGoal Σ Γ l g BasicReasoning ->
  @mkMLGoal Σ Γ l g i.
Proof.
  intros H wf1 wf2.
  specialize (H wf1 wf2).
  apply useBasicReasoning.
  exact H.
Defined.


Ltac useBasicReasoning :=
  unfold ProofSystem.derives;
  lazymatch goal with
  | [ |- of_MLGoal (@mkMLGoal _ _ _ _ _) ] => apply mlUseBasicReasoning
  | [ |- _ ⊢i _ using _ ] => apply useBasicReasoning
  end.


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

Lemma cast_proof' {Σ : Signature} (Γ : Theory) (ϕ ψ : Pattern) (i : ProofInfo) (e : ψ = ϕ) :
  Γ ⊢i ϕ using i ->
  Γ ⊢i ψ using i.
Proof.
  intros [pf Hpf].
  unshelve (eexists).
  {
    apply (cast_proof e).
    exact pf.
  }
  { abstract(
    destruct Hpf as [Hpf2 Hpf3 Hpf4];
    constructor; [
    (
      rewrite elem_of_subseteq in Hpf2;
      rewrite elem_of_subseteq;
      intros x Hx;
      specialize (Hpf2 x);
      apply Hpf2; clear Hpf2;
      rewrite elem_of_gset_to_coGset in Hx;
      rewrite uses_of_ex_gen_correct in Hx;
      rewrite elem_of_gset_to_coGset;
      rewrite uses_of_ex_gen_correct;
      rewrite indifferent_to_cast_uses_ex_gen in Hx;
      exact Hx
    )|
    (
      rewrite elem_of_subseteq in Hpf3;
      rewrite elem_of_subseteq;
      intros x Hx;
      specialize (Hpf3 x);
      apply Hpf3; clear Hpf3;
      rewrite elem_of_gset_to_coGset in Hx;
      rewrite uses_of_svar_subst_correct in Hx;
      rewrite elem_of_gset_to_coGset;
      rewrite uses_of_svar_subst_correct;
      rewrite indifferent_to_cast_uses_svar_subst in Hx;
      exact Hx
    )|
    (
      rewrite indifferent_to_cast_uses_kt;
      apply Hpf4
    )|
    (
      rewrite framing_patterns_cast_proof;
      destruct i; assumption
    )
    ]).
  }
Defined.

Lemma cast_proof_ml_hyps {Σ : Signature} Γ hyps hyps' (e : hyps = hyps') goal (i : ProofInfo) :
  @mkMLGoal Σ Γ hyps goal i ->
  @mkMLGoal Σ Γ hyps' goal i.
Proof.
  unfold of_MLGoal. simpl. intros H.
  intros wfg wfhyps'.
  feed specialize H.
  { exact wfg. }
  { rewrite e. exact wfhyps'. }
  unshelve (eapply (@cast_proof' Σ Γ _ _ i _ H)).
  rewrite e.
  reflexivity.
Defined.

Lemma cast_proof_ml_goal {Σ : Signature} Γ hyps goal goal' (e : goal = goal') (i : ProofInfo):
  @mkMLGoal Σ Γ hyps goal i ->
  @mkMLGoal Σ Γ hyps goal' i .
Proof.
  unfold of_MLGoal. simpl. intros H.
  intros wfgoal' wfhyps.
  feed specialize H.
  { rewrite e. exact wfgoal'. }
  { exact wfhyps. }
  unshelve (eapply (@cast_proof' Σ Γ _ _ i _ H)).
  rewrite e.
  reflexivity.
Defined.

Lemma cast_proof_ml_hyps_indifferent'
      Σ P Γ hyps hyps' (e : hyps = hyps') goal (i : ProofInfo)
      (pf : @mkMLGoal Σ Γ hyps goal i) wf1 wf2 wf3 wf4:
  indifferent_to_cast P ->
  P _ _ (proj1_sig (@cast_proof_ml_hyps Σ Γ hyps hyps' e goal i pf wf1 wf2)) = P _ _ (proj1_sig (pf wf3 wf4)).
Proof.
  intros Hp. simpl. unfold cast_proof_ml_hyps.
  unfold proj1_sig. unfold cast_proof'. destruct pf as [pf' Hpf'] eqn:Heqpf.
  rewrite Hp.
  apply f_equal. simpl in *.
  case_match. simpl in *.
  remember (pf wf1
  (eq_ind_r (λ pv : list Pattern, Pattern.wf pv)
     wf2 e)).
  simpl in *.
  apply proj1_sig_eq in Heqpf. simpl in Heqpf. rewrite -Heqpf.
  apply proj1_sig_eq in Heqd0. rewrite Heqd0.
  apply proj1_sig_eq in Heqd. simpl in Heqd. rewrite -Heqd.
  f_equal. f_equal.
  { apply UIP_dec; apply bool_eqdec. }
  { apply UIP_dec. apply bool_eqdec. }
Qed.

Lemma cast_proof_ml_goal_indifferent
      Σ P Γ hyps goal goal' (e : goal = goal') (i : ProofInfo)
      (pf : @mkMLGoal Σ Γ hyps goal i) wf1 wf2 wf3 wf4:
  indifferent_to_cast P ->
  P _ _ (proj1_sig (@cast_proof_ml_goal Σ Γ hyps goal goal' e i pf wf1 wf2)) = P _ _ (proj1_sig (pf wf3 wf4)).
Proof.
  intros Hp. simpl. unfold cast_proof_ml_goal.
  unfold proj1_sig. unfold cast_proof'. destruct pf as [pf' Hpf'] eqn:Heqpf.
  rewrite Hp.
  apply f_equal. f_equal.
  apply proj1_sig_eq in Heqpf. simpl in Heqpf. rewrite -Heqpf. clear Heqpf. simpl.
  case_match. simpl in *.
  apply proj1_sig_eq in Heqd. simpl in Heqd. rewrite -Heqd.
  f_equal. f_equal.
  { apply UIP_dec; apply bool_eqdec. }
  { apply UIP_dec. apply bool_eqdec. }
Qed.

Lemma MLGoal_intro {Σ : Signature} (Γ : Theory) (l : list Pattern) (x g : Pattern)
  (i : ProofInfo) :
  @mkMLGoal Σ Γ (l ++ [x]) g i ->
  @mkMLGoal Σ Γ l (x ---> g) i.
Proof.
  intros H.
  unfold of_MLGoal in H. simpl in H.
  unfold of_MLGoal. simpl. intros wfxig wfl.

  feed specialize H.
  { abstract (apply well_formed_imp_proj2 in wfxig; exact wfxig). }
  { abstract (unfold Pattern.wf; unfold Pattern.wf in wfl; rewrite map_app foldr_app; simpl;
              apply well_formed_imp_proj1 in wfxig; rewrite wfxig; simpl; exact wfl).
  }
  unshelve (eapply (cast_proof' _ H)).
  { rewrite foldr_app. reflexivity. }
Defined.

Ltac simplLocalContext :=
  match goal with
    | [ |- @of_MLGoal ?Sgm (@mkMLGoal ?Sgm ?Ctx ?l ?g ?i) ]
      => eapply cast_proof_ml_hyps;[(rewrite {1}[l]/app; reflexivity)|]
  end.

#[global]
 Ltac mlIntro := apply MLGoal_intro; simplLocalContext.


Local Example ex_toMLGoal {Σ : Signature} Γ (p : Pattern) :
well_formed p ->
Γ ⊢i p ---> p using BasicReasoning.
Proof.
intros wfp.
toMLGoal.
{ wf_auto2. }
Set Printing All.
match goal with
| [ |- of_MLGoal (@mkMLGoal Σ Γ [] (p ---> p) BasicReasoning) ] => idtac
| _ => fail
end.
fromMLGoal.
Abort.


Local Example ex_mlIntro {Σ : Signature} Γ a (i : ProofInfo) :
well_formed a ->
Γ ⊢i a ---> a using i.
Proof.
intros wfa.
toMLGoal.
{ wf_auto2. }
mlIntro.
match goal with
| [ |- of_MLGoal (@mkMLGoal Σ Γ [a] a i) ] => idtac
| _ => fail
end.
Abort.