From MatchingLogic Require Export Sorts_ProofSystem.

Import Definedness_Syntax.Notations.
Import Sorts_Syntax.Notations.
Import Sorts_Syntax.Notations.
Import Logic.Notations.

Set Default Proof Mode "Classic".

Inductive Symbols := sym_next.

Global Instance Symbols_eqdec : EqDecision Symbols.
Proof. solve_decision. Defined.

#[global]
Program Instance Symbols_finite : finite.Finite Symbols.
Next Obligation.
  exact [sym_next].
Defined.
Next Obligation.
  unfold Symbols_finite_obligation_1.
  compute_done.
Defined.
Next Obligation.
  destruct x; compute_done.
Defined.

Global Instance Symbols_countable : countable.Countable Symbols.
Proof. apply finite.finite_countable. Defined.

Section Syntax.

  Context {Σ : Signature}.

  Class Syntax :=
  { sym_inj : Symbols -> symbols;
    imported_sorts : Sorts_Syntax.Syntax;
  }.

  #[global] Existing Instance imported_definedness.
  #[global] Existing Instance imported_sorts.

  Context {self : Syntax}.

  Definition patt_next (φ : Pattern) := patt_sym (sym_inj sym_next) ⋅ φ.
  Local Notation "• p" := (patt_next p) (at level 71) : ml_scope.

  Definition patt_all_path_next (φ : Pattern) := ! (• (! φ)).
  Local Notation "◯ p" := (patt_all_path_next p) (at level 71) : ml_scope.

  Definition patt_eventually (φ : Pattern) := mu , (nest_mu φ) or • B0.
  Local Notation "⋄ p" := (patt_eventually p) (at level 71) : ml_scope.

  Definition patt_weak_eventually (φ : Pattern) := ! mu , ! ((nest_mu φ) or • (! B0)).
  Local Notation "⋄ʷ p" := (patt_weak_eventually p) (at level 71) : ml_scope.

  Definition patt_always (φ : Pattern) := ! mu , ! ((nest_mu φ) and ◯ (! B0)).
  Local Notation "⊞ p" := (patt_always p) (at level 71) : ml_scope. (* □ is taken by application contexts *)

  (* well_foundedness is about types/sorts *)
  (* Definition patt_well_founded (φ : Pattern) := mu , nest_mu φ *)

  Definition patt_rewrites (φ₁ φ₂ : Pattern) := φ₁ ---> • φ₂.
  Local Notation "p ⇒ q" := (patt_rewrites p q) (at level 81) : ml_scope.

  Definition patt_rewrites_star (φ₁ φ₂ : Pattern) := φ₁ ---> ⋄ φ₂.
  Local Notation "p ⇒* q" := (patt_rewrites_star p q) (at level 81) : ml_scope.

  Definition patt_rewrites_plus (φ₁ φ₂ : Pattern) := φ₁ ---> • (⋄ φ₂).
  Local Notation "p ⇒⁺ q" := (patt_rewrites_star p q) (at level 81) : ml_scope.

  Definition patt_circularity (φ : Pattern) := ◯ (⊞ φ).

  (*
    TODO:
    https://github.com/runtimeverification/proof-generation/blob/main/theory/kore.mm
    - well_foundedness
    - one-path-reachability
    - non-termination
    - all-path-reachability
  *)

  Definition is_final (φ : Pattern) := φ ---> ! (• Top).

  #[global]
  Program Instance Unary_next : Unary patt_next := {}.
  Next Obligation.
    intros A f m φ a. repeat rewrite pm_correctness.
    simpl. reflexivity.
  Defined.
  Next Obligation.
    intros. simpl. reflexivity.
  Qed.
  Next Obligation.
    intros. simpl. reflexivity.
  Qed.
  Next Obligation.
    intros. simpl. reflexivity.
  Qed.

  #[global]
  Program Instance Binary_rewrites : Binary patt_rewrites := {}.
  Next Obligation.
    intros A f m φ1 φ2 a. repeat rewrite pm_correctness.
    simpl. reflexivity.
  Defined.
  Next Obligation.
    intros. simpl. reflexivity.
  Qed.
  Next Obligation.
    intros. simpl. reflexivity.
  Qed.
  Next Obligation.
    intros. simpl. reflexivity.
  Qed.
End Syntax.


Module Notations.

  Notation "∙ p" := (patt_next p) (at level 30) : ml_scope.
  Notation "◯ p" := (patt_all_path_next p) (at level 71) : ml_scope.
  Notation "⋄ p" := (patt_eventually p) (at level 71) : ml_scope.
  Notation "⋄ʷ p" := (patt_weak_eventually p) (at level 71) : ml_scope.
  Notation "⊞ p" := (patt_always p) (at level 71) : ml_scope. (* □ is taken by application contexts *)
  Notation "p ⇒ q" := (patt_rewrites p q) (at level 81) : ml_scope.
  Notation "p ⇒* q" := (patt_rewrites_star p q) (at level 81) : ml_scope.
  Notation "p ⇒⁺ q" := (patt_rewrites_star p q) (at level 81) : ml_scope.
End Notations.

From MatchingLogic.Experimental Require Import Nat_ProofSystem.
Set Default Proof Mode "Classic".
(* From MatchingLogic.Experimental Require Import Nat_ProofSystem.
 *)

Section Lemmas.
  Import Next.Notations.
  Import Nat_Syntax.Notations.
  Context {Σ : Signature}
          {syntax1 : Next.Syntax}
          {syntax2 : Nat_Syntax.Syntax}.
  Definition One : Pattern := Succ ⋅ Zero.

  (*
    x != 1 /\ x => x + 1
  *)
  Definition rule : Pattern :=
    all Nat , ((! (b0 =ml One) and b0) ⇒ b0 +ml One).

  (*
    x = 0 ∧ x ⇒ 1
  *)
  Goal
    forall Γ (x : evar), rule ∈ Γ ->
    Nat_Syntax.theory ⊆ Γ ->
    Γ ⊢ patt_free_evar x ∈ml 〚 Nat 〛 --->
        ((patt_free_evar x =ml Zero and patt_free_evar x) ⇒ (One and patt_free_evar x =ml Zero)).
  Proof.
    intros.
    pose proof (BasicProofSystemLemmas.hypothesis) Γ rule ltac:(wf_auto2) H as Hyp.
    unfold rule in Hyp.
    use AnyReasoning in Hyp.
    (* First, we introduce the rewrite rule into the proof mode:
       ∀x:Nat, x != 1 ∧ x ⇒ x + 1
    *)
    mlAdd Hyp as "Hyp".
    mlSpecialize "Hyp" with x. mlSimpl.
    (**)
    (* Next, we specialize the rewrite rule for x
       x != 1 ∧ x ⇒ x + 1
    *)
    mlIntro "H".
    mlApply "Hyp" in "H". mlClear "Hyp".
    unfold patt_rewrites.
    (*
      We know that x = 0, we rewrite in the rule with it:
      0 != 1 ∧ 0 ⇒ 0 + 1
    *)
    mlIntro "H0".
    mlDestructAnd "H0" as "E" "Hx".
    mlRevert "Hx". mlRewriteBy "E" at 1. 1: unfold theory in H0; set_solver.
    mlIntro "Hx".
    (* mlDestructAnd "0". *)
    mlRevert "H".
    mlRewriteBy "E" at 1. 1: unfold theory in H0; set_solver.
    mlRewriteBy "E" at 1. 1: unfold theory in H0; set_solver.
    mlRewriteBy "E" at 1. 1: unfold theory in H0; set_solver.
    mlRewriteBy "E" at 1. 1: unfold theory in H0; set_solver.
    mlClear "E".
    clear -H0.
    (* Next, we manually simplify 0 + 1 to 1:
       0 != 1 ∧ 0 ⇒ 1
       The proof for it is technical, because we lack tactics for reasoning
       about sorts, sorted quantification, and functional patterns.
    *)
    assert (HZ : Γ ⊢ (is_functional Zero)). {
      mlApplyMeta ex_sort_impl_ex.
      2: unfold theory in H0; set_solver.
      pose proof use_nat_axiom AxFun1 Γ H0;simpl in H.
      mlAdd H as "f"; mlAssumption.
    }

    assert (HIn : Γ ⊢ (Zero ∈ml 〚 Nat 〛)). {
      (* manual fixpoint reasoning needed: *)
      pose proof use_nat_axiom AxInductiveDomain Γ H0;simpl in H.
      mlAdd H as "R".
      mlRewriteBy "R" at 1. 1: unfold theory in H0; set_solver.
      epose proof membership_monotone_functional Γ 
       ( (mu , Zero or Succ ⋅ B0)^[mu , Zero or Succ ⋅ B0] ) 
       (mu , Zero or Succ ⋅ B0) (Zero) (AnyReasoning) ltac:(unfold theory in H0;set_solver) ltac:(wf_auto2) 
        ltac:(wf_auto2) ltac:(wf_auto2) _ .
      pose proof BasicProofSystemLemmas.Pre_fixp Γ (Zero or Succ ⋅ B0) ltac:(wf_auto2).
      use AnyReasoning in H2.
      specialize (H1 H2).
      unfold instantiate in H1. mlSimpl in H1. simpl in H1.
      mlApplyMeta H1.
      mlApplyMeta membership_or_2_functional_meta.
      2:{ 
          mlApplyMeta ex_sort_impl_ex.
          2: unfold theory in H0;set_solver.
          pose proof use_nat_axiom AxFun1 Γ H0 as H4; simpl in H4; mlAdd H4 as "f";mlExact "f".
        }
      2: unfold theory in H0;set_solver.
       
      mlLeft.
      mlApplyMeta membership_refl.
      2: unfold theory in H0;set_solver.
      mlApplyMeta ex_sort_impl_ex.
      2: unfold theory in H0;set_solver.
      pose proof use_nat_axiom AxFun1 Γ H0 as H4; simpl in H4; mlAdd H4 as "f";mlExact "f".
    }
    (*End of boiler-plate*)
    mlIntro "H".
    mlAssert ("E2" : ((Zero +ml (Succ ⋅ Zero)) =ml One)). wf_auto2.
    {
      mlClear "H".
      pose proof (use_nat_axiom AxDefAdd Γ H0) as H. cbn in H.
      mlAdd H as "EQ1".
      pose proof (use_nat_axiom AxDefAddId Γ H0) as H1. cbn in H1.
      mlAdd H1 as "EQ2".
      (** This is a repeating scheme in reasoning: *)
      epose proof forall_functional_subst _ _ Γ ltac:(unfold theory in H0; set_solver)
         _ _ _ _ as H2.
      mlAdd HZ as "HZ". mlAdd HIn as "HIn".
      mlConj "EQ1" "HZ" as "H".  mlClear "EQ1". mlClear "HZ".
      mlApplyMeta H2 in "H". mlSimpl.
      mlApply "H" in "HIn". mlClear "H". clear H2.
      (***)
      epose proof forall_functional_subst _ _ Γ ltac:(unfold theory in H0; set_solver)
         _ _ _ _ as H2.
      mlAdd HZ as "HZ". mlAdd HIn as "HIn2".
      mlConj "HIn" "HZ" as "H". mlClear "HIn". mlClear "HZ".
      mlApplyMeta H2 in "H". mlSimpl.
      mlApply "H" in "HIn2". mlClear "H". clear H2.
      mlRewriteBy "HIn2" at 1. 1: unfold theory in H0; set_solver.
      epose proof forall_functional_subst _ _ Γ ltac:(unfold theory in H0; set_solver)
         _ _ _ _ as H2.
      mlAdd HZ as "HZ". mlAdd HIn as "HIn3".
      mlConj "EQ2" "HZ" as "H".
      mlApplyMeta H2 in "H". mlSimpl.
      mlApply "H" in "HIn3". mlClear "H". clear H2.
      mlRewriteBy "HIn3" at 1. 1: unfold theory in H0; set_solver.
      unfold One.
      mlReflexivity.
    }
    mlRevert "H".
    mlRewriteBy "E2" at 1. 1: unfold theory in H0; set_solver.
    (* We separate the condition of 0 = 0 in the RHS: *)
    epose proof predicate_propagate_right_2_meta Γ One (Zero =ml Zero) (patt_sym (Next.sym_inj sym_next)) _ _ _ _.
    assert (Γ ⊢ is_predicate_pattern (Zero =ml Zero)). {
      mlFreshEvar as x.
      mlFreshEvar as y.
      mlFreshEvar as z.
      apply floor_is_predicate with (x := x) (y := y) (z := z); try by wf_auto2.
      1: unfold theory in H0; set_solver.
      1: fm_solve.
      1: fm_solve.
    }
    apply H in H1.
    fold (patt_next One) in H1.
    fold (patt_next (Zero =ml Zero and One)) in H1.
    epose proof patt_and_comm Γ (Zero =ml Zero) One _ _.
    use AnyReasoning in H2.
    mlRewrite <- H2 at 1.
    mlRewrite <- H1 at 1.
    clear H H1 H2.
    mlIntro "H".
    mlSplitAnd. 1: mlReflexivity.
    (* finally, we prove that we reached One indeed by applying the rewrite rule
       which we specialized *)
    mlApply "H".
    mlSplitAnd.
    { (* We prove the premise of the rule: 0 != 1 *)
      mlIntro.
      pose proof (use_nat_axiom AxNoConfusion1 Γ H0) as H1. cbn in H1.
      mlClear "Hx". mlClear "H". mlClear "E2".
      mlAdd H1 as "X".
      epose proof forall_functional_subst _ _ Γ ltac:(unfold theory in H0; set_solver)
         _ _ _ _ as H2.
      mlAdd HZ as "HZ". mlAdd HIn as "HIn".
      mlConj "X" "HZ" as "H".
      mlApplyMeta H2 in "H". mlSimpl.
      mlApply "H" in "HIn".
      mlApply "HIn".
      mlAssumption.
    }
    {
      mlAssumption.
    }
    Unshelve.
      all: wf_auto2.
      1: unfold theory in H0; set_solver.
  Defined.

  (* One is final *)
  Goal
    forall Γ, rule ∈ Γ ->
    Nat_Syntax.theory ⊆ Γ ->
    Γ ⊢ is_final One.
  Proof.
    intros.
    mlIntro "H".
    mlIntro "H0".
    pose proof (BasicProofSystemLemmas.hypothesis) Γ rule ltac:(wf_auto2) H as Hyp.
    unfold rule in Hyp.
    use AnyReasoning in Hyp.
    (* First, we introduce the rewrite rule into the proof mode:
       ∀x:Nat, x != 1 ∧ x ⇒ x + 1
    *)
    mlAdd Hyp as "Hyp".
    unfold patt_top, patt_next.
    Print Application_context.
    (* No idea, how to prove "finality" *)
    epose proof Misc.Singleton_ctx Γ (patt_sym (Next.sym_inj sym_next) $ᵣ box).
  Defined.

End Lemmas.

