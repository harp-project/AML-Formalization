
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

    (* Unfortunately, we do not have [mlRewrite _ in _] yet.*)
Qed.

(* We can also use definedness and equality.
   To do so, we have to assume that the signature contains a definedness symbol,
   and the theory a definedness axiom.
   Otherwise, the signature and axiom can be arbitrary.
*)

From MatchingLogic Require Import
    Theories.Definedness_Syntax
    Theories.Definedness_ProofSystem
.
Import Theories.Definedness_Syntax.Notations.

(* Obviously, without the definedness symbol, we cannot use equality. *)
Fail Example use_rewriteBy {Σ : Signature} (Γ : Theory) (ϕ₁ ϕ₂ ϕ₃ ϕ₄ : Pattern) :
    well_formed ϕ₁ = true ->
    well_formed ϕ₂ = true ->
    well_formed ϕ₃ = true ->
    well_formed ϕ₄ = true ->
    Γ ⊢ (ϕ₁ $ ϕ₄ =ml ϕ₂ $ ϕ₄ ) ---> (ϕ₁ =ml ϕ₂) ---> ((ϕ₃ $ ϕ₁ $ ϕ₄) <---> (ϕ₃ $ ϕ₂ $ ϕ₄))
.

Example use_rewriteBy {Σ : Signature} {syntax : Definedness_Syntax.Syntax}
    (Γ : Theory) (ϕ₁ ϕ₂ ϕ₃ ϕ₄ : Pattern) :
    well_formed ϕ₁ = true ->
    well_formed ϕ₂ = true ->
    well_formed ϕ₃ = true ->
    well_formed ϕ₄ = true ->
    Γ ⊢ (ϕ₁ $ ϕ₄ =ml ϕ₂ $ ϕ₄ ) ---> (ϕ₁ =ml ϕ₂) ---> ((ϕ₃ $ ϕ₁ $ ϕ₄) <---> (ϕ₃ $ ϕ₂ $ ϕ₄))
.
Proof.
    intros wfϕ₁ wfϕ₂ wfϕ₃ wfϕ₄. toMLGoal;[wf_auto2|].
    mlIntro "H1". mlIntro "H2".

    (* We can rewrite using an equality from the local context. *)
    mlRewriteBy "H1" at 1.
    {
        (* Oops, there is a obligation we do not know how to solve. What does that mean? *)
        unfold theory, named_axioms, NamedAxioms.theory_of_NamedAxioms, axiom. simpl.
        (* Aha, we are missing a Definedness axiom. *)
        admit.
    }
Abort.


Example use_rewriteBy {Σ : Signature} {syntax : Definedness_Syntax.Syntax}
    (Γ : Theory) (ϕ₁ ϕ₂ ϕ₃ ϕ₄ : Pattern) :
    (* This makes the difference. *)
    Definedness_Syntax.theory ⊆ Γ ->
    well_formed ϕ₁ = true ->
    well_formed ϕ₂ = true ->
    well_formed ϕ₃ = true ->
    well_formed ϕ₄ = true ->
    Γ ⊢ (ϕ₁ $ ϕ₄ =ml ϕ₂ $ ϕ₄ ) ---> (ϕ₁ =ml ϕ₂) ---> ((ϕ₃ $ ϕ₁ $ ϕ₄) <---> (ϕ₃ $ ϕ₂ $ ϕ₄))
.
Proof.
    intros HΓ wfϕ₁ wfϕ₂ wfϕ₃ wfϕ₄. toMLGoal;[wf_auto2|].
    mlIntro "H1". mlIntro "H2".

    (* We can rewrite using an equality from the local context. *)
    mlRewriteBy "H1" at 1.
    { 
        (* Now we have the appropriate assumption. *)
        assumption.
    }
    {
        (* Another constraint. Under the hood, the rewrite uses the equality elimination lemma,
           which in turn uses deduction theorem.
           Our deduction theorem does not support working with μ patterns yet,
           so we have to check that the context in which we want to rewrite
           is μ-free.
        *)
        simpl.
        (* Oh.. we do not know anything about the [ϕᵢ]s. *)
        admit.
    }
Abort.

(* A solver for boolean tautologies. *)
From Coq Require Import btauto.Btauto.
(* Some helper tactics. *)
From MatchingLogic Require Import
    Utils.extralibrary
    Utils.stdpp_ext
.

Open Scope ml_scope.

Example use_rewriteBy {Σ : Signature} {syntax : Definedness_Syntax.Syntax}
    (Γ : Theory) (ϕ₁ ϕ₂ ϕ₃ ϕ₄ : Pattern) :
    Definedness_Syntax.theory ⊆ Γ ->
    (* This makes the difference. *)
    ((mu_free ϕ₁) && (mu_free ϕ₂) && (mu_free ϕ₃) && (mu_free ϕ₄)) = true ->
    well_formed ϕ₁ = true ->
    well_formed ϕ₂ = true ->
    well_formed ϕ₃ = true ->
    well_formed ϕ₄ = true ->
    Γ ⊢ (ϕ₁ $ ϕ₄ =ml ϕ₂ $ ϕ₄ ) ---> (ϕ₁ =ml ϕ₂) ---> ((ϕ₃ $ ϕ₁ $ ϕ₄) <---> (ϕ₃ $ ϕ₂ $ ϕ₄))
.
Proof.
    intros HΓ Hmf wfϕ₁ wfϕ₂ wfϕ₃ wfϕ₄. toMLGoal;[wf_auto2|].
    mlIntro "H1". mlIntro "H2".

    (* We can rewrite using an equality from the local context. *)
    mlRewriteBy "H1" at 1.
    { assumption. }
    { simpl. destruct_and!. unfold is_true. rewrite H0, H2, H3. reflexivity. }

    (* We could also rewrite by H2 *)
    Restart.

    intros HΓ Hmf wfϕ₁ wfϕ₂ wfϕ₃ wfϕ₄. toMLGoal;[wf_auto2|].
    mlIntro "H1". mlIntro "H2".

    mlRewriteBy "H2" at 1.
    { assumption. }
    { simpl. destruct_and!. unfold is_true. rewrite H0, H2, H3. reflexivity. }

    mlSplitAnd; mlIntro "Hyp"; mlExact "Hyp".
Defined.

Example use_mlApply {Σ : Signature} (Γ : Theory) (a b c : Pattern) :
    well_formed a = true ->
    well_formed b = true ->
    well_formed c = true ->
    Γ ⊢ (a ---> b $ c) ---> (b $ c ---> c) ---> (a ---> c).
Proof.
    intros wfa wfb wfc. toMLGoal;[wf_auto2|].
    mlIntro "H1". mlIntro "H2". mlIntro "H3".
    (* strenghtens the concusion using H2 *)
    mlApply "H2".
    (* Would weaken the hypothesis H3 using H1
       if we had it.
     *)
    (* (mlApply "H1" in "H3"). *)
    mlApply "H1".
    mlExact "H3".
Defined.

Example use_mlApplyMeta {Σ : Signature} (Γ : Theory) (a b c d : Pattern) :
    well_formed a = true ->
    well_formed b = true ->
    well_formed (ex, c) = true ->
    well_formed d = true ->
    Γ ⊢ a ---> ((ex, c) $ d) ---> b ---> (ex, (c $ d)).
Proof.
    intros wfa wfb wfc wfd. toMLGoal;[wf_auto2|].
    mlIntro "H1". mlIntro "H2". mlIntro "H3".

    Check Prop_ex_left.
    mlApplyMeta Prop_ex_left.
    mlExact "H2".
Defined.


