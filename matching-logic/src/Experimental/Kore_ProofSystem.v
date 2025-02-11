From MatchingLogic.Experimental Require Export Kore.

Import MatchingLogic.Logic.Notations.
Import MatchingLogic.Theories.Definedness_Syntax.Notations.
Import MatchingLogic.Theories.Sorts_Syntax.Notations.
Import MatchingLogic.Theories.Nat_Syntax.Notations.
Import MatchingLogic.Experimental.Kore.Notations.

Set Default Proof Mode "Classic".

(* For the well-formedness tactics, we forbid simplifications *)
Arguments well_formed_positive : simpl never.
Arguments well_formed_closed_mu_aux : simpl never.
Arguments well_formed_closed_ex_aux : simpl never.

Section DerivedRules.

  Context {Σ : Signature}
          {syntax : Kore.Syntax}
          (Γ: Theory)
          (HΓ : KoreTheory ⊆ Γ).

  Theorem kore_equals_trans s s₂ φ₁ φ₂ φ₃:
    well_formed s ->
    well_formed s₂ ->
    well_formed φ₁ ->
    well_formed φ₂ ->
    well_formed φ₃ ->
    Γ ⊢ φ₁ =ml(s, s₂) φ₂ ---> φ₂ =ml(s, s₂) φ₃ --->
        φ₁ =ml(s, s₂) φ₃.
  Proof.
    intros.
    mlIntro "H".
    mlIntro "H0".
    mlApplyMeta equals_equiv_1 in "H". 2: assumption.
    mlApplyMeta equals_equiv_1 in "H0". 2: assumption.
    mlDestructAnd "H" as "H_1" "H_2".
    mlDestructAnd "H0" as "H0_1" "H0_2".
    mlApplyMeta equals_equiv_2. 2: assumption.
    mlSplitAnd. 2: mlAssumption.
    mlRewriteBy "H_1" at 1. 1: unfold KoreTheory in HΓ; set_solver.
    mlAssumption.
  Defined.


End DerivedRules.