From Coq Require Import ssreflect ssrfun ssrbool.

From Ltac2 Require Import Ltac2.

From Coq Require Import String Ensembles Setoid.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.Classical_Prop.
From Coq.Logic Require Import FunctionalExtensionality Eqdep_dec.
From Coq.Classes Require Import Morphisms_Prop.
From Coq.Unicode Require Import Utf8.
From Coq.micromega Require Import Lia.

From MatchingLogic Require Export Logic ProofMode.MLPM.
From MatchingLogic.Theories Require Export Definedness_Syntax Definedness_ProofSystem Sorts_Syntax FOEquality_ProofSystem.
From MatchingLogic.Utils Require Export stdpp_ext.

Require Export MatchingLogic.wftactics.

From stdpp Require Import base fin_sets sets propset proof_irrel option list.
Import FreshnessManager.
Import extralibrary.

Import MatchingLogic.Logic.Notations.
Import MatchingLogic.Theories.Definedness_Syntax.Notations.

Set Default Proof Mode "Classic".

Require Import MatchingLogic.Theories.DeductionTheorem.

Require MatchingLogic.Theories.Sorts_Syntax.
Export MatchingLogic.Theories.Sorts_Syntax.Notations.

Open Scope ml_scope.
Open Scope string_scope.
Open Scope list_scope.

Set Printing All.

Local Lemma simplTest
  {Σ : Signature}
  {syntax : Sorts_Syntax.Syntax}
  (Γ : Theory)
  (φ ψ τ: Pattern)
  (s : symbols) x:
  well_formed (ex , φ) ->
  well_formed ψ ->
  well_formed τ ->
  Definedness_Syntax.theory ⊆ Γ ->
  Γ ⊢ ((all ψ , φ) ---> ex ψ ,  φ)^[[evar:x↦τ]].
Proof.
  intros. mlSimpl. mlSortedSimpl. mlSortedSimpl. mlSimpl.
  remember (fresh_evar (ψ $ φ $ τ)) as y.
  mlIntro.
  mlSpecialize "0" with x.
  mlExists x.
Abort.

Lemma ex_sort_impl_ex
  {Σ : Signature}
  {syntax : Sorts_Syntax.Syntax}
  (Γ : Theory)
  (ϕ : Pattern)
  (s : symbols)
  :
  well_formed (ex , ϕ) ->
  Definedness_Syntax.theory ⊆ Γ ->
  Γ ⊢ (ex (patt_sym s) , ϕ) ---> (ex , ϕ).
Proof.
  intros wfϕ HΓ.

  unfold "ex _ , _".

  unfold nest_ex; simpl.

  remember (fresh_evar (b0 ∈ml 〚 patt_sym s 〛 and ϕ)) as x.
  rewrite <- evar_quantify_evar_open with (n := 0) (x := x) (phi := b0 ∈ml 〚 patt_sym s 〛 and ϕ).
  2: {
    subst x. eapply evar_is_fresh_in_richer'.
    2: apply set_evar_fresh_is_fresh'.
    clear. set_solver.
  }
  2: {
    wf_auto2.
  }

  gapply BasicProofSystemLemmas.Ex_gen.
  { apply pile_any. }
  { apply pile_any. }
  {
    subst x. eapply evar_is_fresh_in_richer'.
    2: { apply set_evar_fresh_is_fresh'. }
    clear. set_solver.
  }

  mlSimpl. unfold evar_open. simpl.

  toMLGoal.
  { wf_auto2. }
  mlIntro "H".
  mlDestructAnd "H" as "H0" "H1".
  mlClear "H0".

  mlApplyMeta BasicProofSystemLemmas.Ex_quan. simpl.
  mlExact "H1".
Defined.

Theorem top_includes_everything {Σ : Signature} {syntax : Sorts_Syntax.Syntax}:
  ∀ (Γ : Theory) (x : evar),
  Definedness_Syntax.theory ⊆ Γ -> 
  Γ ⊢i patt_free_evar x  ∈ml patt_top using AnyReasoning.
Proof.
  intros.
  pose proof proved_membership_functional Γ (patt_top) (patt_free_evar x) ltac:(set_solver) ltac:(wf_auto2) ltac:(wf_auto2).
  mlApplyMeta H0.
  * unfold  is_functional.
    mlExists x.
    mlSimpl. cbn.
    mlReflexivity.
  * pose proof top_holds Γ.
    use AnyReasoning in H1.
    mlExactMeta H1.
Defined.

Close Scope ml_scope.
Close Scope string_scope.
Close Scope list_scope.