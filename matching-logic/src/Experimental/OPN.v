From Coq Require Import ssreflect ssrfun ssrbool.

(* From Ltac2 Require Import Ltac2. *)

Require Import Equations.Prop.Equations.

From Coq Require Import String Setoid.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.Classical_Prop.
From Coq.Logic Require Import FunctionalExtensionality Eqdep_dec.
From Coq.Classes Require Import Morphisms_Prop.
From Coq.Unicode Require Import Utf8.
From Coq.micromega Require Import Lia.

From MatchingLogic Require Import Logic ProofMode.MLPM Substitution.
From MatchingLogic.Theories Require Import Definedness_Syntax Definedness_ProofSystem FOEquality_ProofSystem DeductionTheorem.
From MatchingLogic.Utils Require Import stdpp_ext.

Require Import MatchingLogic.wftactics.

From stdpp Require Import base fin_sets sets propset proof_irrel option list.

Import extralibrary.

Import MatchingLogic.Logic.Notations.
Import MatchingLogic.Theories.Definedness_Syntax.Notations.

Set Default Proof Mode "Classic".

Close Scope equations_scope. (* Because of [!] *)

Open Scope ml_scope.
Open Scope string_scope.
Open Scope list_scope.

(* FOEquality.v vagy Definedness *)
Section OPN.
  Context {Σ : Signature} {syntax : Syntax}.
  Context (next_sym : symbols).

  Definition next (φ : Pattern) : Pattern := patt_sym next_sym ⋅ φ.

  Context (Γ : Theory).
  Hypothesis (HΓ : theory ⊆ Γ).

  Goal forall φ1 φ2 φ3,
    well_formed φ1 ->
    well_formed φ2 ->
    well_formed φ3 ->
    Γ ⊢ is_predicate_pattern φ3 ->
    Γ ⊢ (φ1 ---> (next φ2)) ---> (φ1 and φ3) ---> (next (φ2 and φ3)).
  Proof with try solve [auto | wf_auto2 | try_solve_pile].
    intros * wfφ1 wfφ2 wfφ3 ppφ3.
    opose proof* (predicate_propagate_right_2 Γ φ2 φ3 (patt_sym next_sym))...
    opose proof* pf_iff_proj1; only 3: exact H...
    clear H. mlAdd H0. clear H0.
    do 2 mlIntro. mlDestructAnd "2".
    mlApply "3" in "1". mlClear "1".
    mlConj "4" "3" as "1". mlClear "3". mlClear "4". unfold next.
    mlApply "0" in "1". mlClear "0". fromMLGoal.
    apply Framing_right...
    aapply patt_and_comm_basic...
  Defined.
End OPN.
