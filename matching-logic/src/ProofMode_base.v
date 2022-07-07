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