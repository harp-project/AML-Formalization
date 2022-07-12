
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
    (* The tactic [toMLGoal] enters the matching logic proof mode. *)
    toMLGoal.
    {
        (* the [wf_auto2] tactic is used to discharge well-formedness obligations. *)
        wf_auto2.
    }
    (* the [mlTauto] tactic tries to solve a propositional tautology. *)
    mlTauto.
Qed.
