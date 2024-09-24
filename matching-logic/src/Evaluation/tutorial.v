
(* What follows is a minimal example of how to use the ProofMode. *)

From MatchingLogic Require Import
    Syntax
    ProofSystem
    ProofMode.MLPM
.

Import MatchingLogic.Syntax.Notations.

From stdpp Require Import base.
From Coq Require Import String.

Section tutorial.

Context {Σ : Signature}
        {Γ : Theory}
        (ϕ : Pattern)
        (wfϕ : well_formed ϕ).

Open Scope string_scope.

Open Scope string_scope.
Open Scope ml_scope.

(* Below we prove that in matching logic, ϕ -> ϕ for any pattern ϕ. *)
Example phi_implies_phi :
    Γ ⊢ ϕ ---> ϕ.
Proof.
  mlIntro "H".
  mlExact "H".
Qed.

(* We can also work with conjunction and disjunction. *)
Import MatchingLogic.DerivedOperators_Syntax.Notations.

Context (ϕ₁ : Pattern)
        (wfϕ₁ : well_formed ϕ₁)
        (ϕ₂ : Pattern)
        (wfϕ₂ : well_formed ϕ₂).

Example and_or :
    Γ ⊢ ϕ₁ and ϕ₂ ---> ϕ₁ or ϕ₂
.
Proof.
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

Context (ϕ₃ : Pattern)
        (wfϕ₃ : well_formed ϕ₃)
        (ϕ₄ : Pattern)
        (wfϕ₄ : well_formed ϕ₄).

Example use_rewrite :
    Γ ⊢ ϕ₁ <---> ϕ₂ ->
    (* The [$] operator is an application. *)
    Γ ⊢ (ϕ₃ $ ϕ₁ $ ϕ₄) <---> (ϕ₃ $ ϕ₂ $ ϕ₄)
.
Proof.
    intros H.
    (* Notice that now we have a meta-level assumption [H]. *)

    (* We can use [H] to rewrite the first occurrence of [ϕ₁] to [ϕ₂]. *)
    mlRewrite H at 1.
    (* Now the goal is provable by propositional reasoning. *)
    mlSplitAnd.
    * mlIntro "H". mlExact "H".
    * mlIntro "H". mlExact "H".
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
Open Scope ml_scope.
Open Scope string_scope.

(* Obviously, without the definedness symbol, we cannot use equality. *)
Fail Example use_rewriteBy :
    Γ ⊢ (ϕ₁ $ ϕ₄ =ml ϕ₂ $ ϕ₄ ) ---> (ϕ₁ =ml ϕ₂) ---> ((ϕ₃ $ ϕ₁ $ ϕ₄) <---> (ϕ₃ $ ϕ₂ $ ϕ₄))
.

(* The typeclass [Definedness_Syntax.Syntax] ensures the presence of the definedness symbol
   in the (implicit) signature Σ.
 *)
Context {syntax : Definedness_Syntax.Syntax}.

Example use_rewriteBy :
    Γ ⊢ (ϕ₁ $ ϕ₄ =ml ϕ₂ $ ϕ₄) ---> (ϕ₁ =ml ϕ₂) ---> ((ϕ₃ $ ϕ₁ $ ϕ₄) <---> (ϕ₃ $ ϕ₂ $ ϕ₄))
.
Proof.
    mlIntro "H1". mlIntro "H2".

    (* We can rewrite using an equality from the local context. *)
    mlRewriteBy "H1" at 1.
    {
        (* There is an obligation we do not know how to solve. What does that mean? *)
        unfold theory, named_axioms, NamedAxioms.theory_of_NamedAxioms, axiom. simpl.
        (* We are missing a Definedness axiom. *)
        admit.
    }
Abort.

Context {HΓ : Definedness_Syntax.theory ⊆ Γ}.

Example use_rewriteBy :
    Γ ⊢ (ϕ₁ $ ϕ₄ =ml ϕ₂ $ ϕ₄ ) ---> (ϕ₁ =ml ϕ₂) ---> ((ϕ₃ $ ϕ₁ $ ϕ₄) <---> (ϕ₃ $ ϕ₂ $ ϕ₄))
.
Proof.
    mlIntro "H1". mlIntro "H2".

    (* We can rewrite using an equality from the local context. *)
    mlRewriteBy "H1" at 1.
    (* Now the obligation was solved automatically *)

    mlSplitAnd; mlIntro "H"; mlExact "H".
Defined.


(*
   We now demonstrate how to use local hypotheses that are implications.
*)
Example use_mlApply :
    Γ ⊢ (ϕ₁ ---> ϕ₂ $ ϕ₃) ---> (ϕ₂ $ ϕ₃ ---> ϕ₃) ---> (ϕ₁ ---> ϕ₃).
Proof.
    mlIntro "H1". mlIntro "H2". mlIntro "H3".
    (* replace the goal with the premise of "H2", since the goal is exactly
       the conclusion of "H2" *)
    mlApply "H2".
    (* Alternatively: replace "H3" with the conclusion of "H1", since "H3" is
                      the premise of "H1". *)
    (* mlApply "H1" in "H3". *)

    mlApply "H1".
    mlExact "H3".
Defined.

Context (ψ : Pattern)
        (wfψ : well_formed (ex, ψ)).

(*
   What if we have a matching logic implication in a Coq hypothesis
   or in a lemma? There is `mlApplyMeta` for that.
*)
Example use_mlApplyMeta :
    Γ ⊢ ϕ₁ ---> ((ex, ψ) $ ϕ₂) ---> ϕ₃ ---> (ex, (ψ $ ϕ₂)).
Proof.
    mlIntro "H1". mlIntro "H2". mlIntro "H3".

    Check Prop_ex_left.
    (*
        Prop_ex_left
        : ∀ (Γ : Theory) (ϕ ψ : Pattern),
            well_formed (ex , ϕ)
            → well_formed ψ
            → Γ ⊢i (ex , ϕ) $ ψ ---> (ex , ϕ $ ψ) using BasicReasoning
    *)
    mlApplyMeta Prop_ex_left.
    (* Did you notice that [mlApplyMeta] automatically instantiated
       all the preconditions of the lemma?
       That is, without some magic happening on the background,
       one would need to manualy specify them,
       and solve the well-formedness subgoals.
    *)
    mlExact "H2".
Defined.

Close Scope ml_scope.
Close Scope string_scope.
Close Scope list_scope.
