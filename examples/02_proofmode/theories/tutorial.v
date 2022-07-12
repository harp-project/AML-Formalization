
(* What follows is a minimal example of how to use the ProofMode. *)

From MatchingLogic Require Import
    Syntax
    ProofSystem
    ProofMode
.

Import MatchingLogic.Syntax.Notations.
Import MatchingLogic.ProofSystem.Notations.

(* Below we prove that in matching logic, ϕ -> ϕ for any pattern ϕ. *)
Example phi_implies_phi
    (* Formulas are formed over a particular signature *)
    {Σ : Signature}
    (Γ : Theory)
    (ϕ : Pattern) :
    (* we have to assume that [ϕ] is well_formed *)
    well_formed ϕ = true ->
    (* The goal *)
    Γ ⊢ ϕ ---> ϕ
.
Proof.
    intros wfϕ.
    (* The tactic [toMLGoal] enters the matching logic proof mode.
       However, it first has to check that the pattern to prove is well-formed.
    *)
    toMLGoal.
    {
        (* the [wf_auto2] tactic is used to discharge well-formedness obligations. *)
        wf_auto2.
    }
    (* the [mlTauto] tactic tries to solve a propositional tautology. *)
    mlTauto.
Qed.

(* Of course, we could prove the same thing using an empty theory.
   However, to be able to denote empty set, we have to import part of the [stdpp] library. 
*)

From stdpp Require Import base.

Example phi_implies_phi_from_empty_theory {Σ : Signature} (ϕ : Pattern) :
    well_formed ϕ = true ->
    ∅ ⊢ ϕ ---> ϕ
.
Proof.
    intros wfϕ.
    toMLGoal;[wf_auto2|].
    mlTauto.
Qed.

(* But how would we prove the goal manually? *)
From Coq Require Import String.
Open Scope string_scope.


Example phi_implies_phi_manual {Σ : Signature} (Γ : Theory) (ϕ : Pattern) :
    well_formed ϕ = true ->
    Γ ⊢ ϕ ---> ϕ
.
Proof.
    intros wfϕ.
    toMLGoal;[wf_auto2|].

    (* Ok, lets assume that ϕ holds. We assign this hypothesis a name "H".
       We say that the tactic [mlIntro] moves a left-side of an implication
       into so-called "local context".
    *)
    mlIntro "H".
    (* Now we have to prove ϕ, and we have a hypothesis "H" saying that ϕ holds.
       Then the goal can be proven <i>exact</i>ly from the hypothesis.
     *)
    mlExact "H".

    (* Another way of proving the goal would be to use the [mlAssumption] tactic,
       which searches for a hypothesis that matches the goal.
    *)
    Undo.
    mlAssumption.

    (* Of course, we could also use [mlTauto]. *)
    Undo.
    mlTauto.
Qed.

(* We can also work with conjunction and disjunction. *)
Import MatchingLogic.DerivedOperators_Syntax.Notations.

Example and_or {Σ : Signature} (Γ : Theory) (ϕ₁ ϕ₂ : Pattern) :
    well_formed ϕ₁ = true ->
    well_formed ϕ₂ = true ->
    Γ ⊢ ϕ₁ and ϕ₂ ---> ϕ₁ or ϕ₂
.
Proof.
    intros wfϕ1 wfϕ2.
    toMLGoal;[wf_auto2|].

    mlIntro "H".
    (* we have tactics like:
        * [mlDestructAnd]
        * [mlDestructOr]
        * [mlLeft]
        * [mlRight]
        * [mlSplitAnd]
       which work similarly to their Coq counterparts
     *)

    mlDestructAnd "H" as "H1" "H2".
    mlLeft.
    mlExact "H1".
Qed.

(* Propositional reasoning is easy.
*)

Open Scope ml_scope.

Example use_rewrite {Σ : Signature} (Γ : Theory) (ϕ₁ ϕ₂ ϕ₃ ϕ₄ : Pattern) :
    well_formed ϕ₁ = true ->
    well_formed ϕ₂ = true ->
    well_formed ϕ₃ = true ->
    well_formed ϕ₄ = true ->
    Γ ⊢ ϕ₁ <---> ϕ₂ ->
    (* The [$] operator is an application. *)
    Γ ⊢ (ϕ₃ $ ϕ₁ $ ϕ₄) <---> (ϕ₃ $ ϕ₂ $ ϕ₄)
.
Proof.
    intros wfϕ₁ wfϕ₂ wfϕ₃ wfϕ₄ H. toMLGoal;[wf_auto2|].

    (* Notice that now we have a meta-level assumption [H]. *)

    (* Obviously, mlTauto can't solve this goal. *)
    Fail solve [mlTauto].

    (* However, we can use [H] to rewrite the first occurrence of [ϕ₁] to [ϕ₂]. *)
    mlRewrite H at 1.
    (* Now the goal is provable by propositional reasoning. *)
    (* However, mlTauto cannot solve it. That is a bug. *)
    Fail solve[mlTauto].
    (* Never mind, we prove it manually. *)
    mlSplitAnd; mlIntro "H"; mlExact "H".
    
    (* We could also rewrite in the other direction *)
    Restart.
    intros wfϕ₁ wfϕ₂ wfϕ₃ wfϕ₄ H. toMLGoal;[wf_auto2|].
    mlRewrite <- H at 1.
    mlSplitAnd; mlIntro "H"; mlExact "H".
Qed.


