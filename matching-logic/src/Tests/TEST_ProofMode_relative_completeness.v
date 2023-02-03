From MatchingLogic Require Import Logic ProofMode.

From Coq Require Import String.

Import
  MatchingLogic.Logic.Notations
  MatchingLogic.DerivedOperators_Syntax.Notations
.

Set Default Proof Mode "Classic".


Open Scope ml_scope.
Open Scope string_scope.
Open Scope list_scope.

Section with_signature.

Context {Σ : Signature}.

Local Lemma P1_complete (Γ : Theory) (ϕ ψ : Pattern):
  well_formed ϕ -> well_formed ψ ->
  mkMLGoal _ Γ [] (ϕ ---> ψ ---> ϕ) BasicReasoning.
Proof.
  intros.
  do 2 mlIntro. mlAssumption.
Qed.

Local Lemma P2_complete (Γ : Theory) (ϕ ψ ξ : Pattern):
  well_formed ϕ -> well_formed ψ -> well_formed ξ ->
  mkMLGoal _ Γ [] ((ϕ ---> ψ ---> ξ) ---> (ϕ ---> ψ) ---> ϕ ---> ξ) BasicReasoning.
Proof.
  intros.
  do 3 mlIntro.
  mlApply "0". mlSplitAnd.
  * mlAssumption.
  * mlApply "1". mlAssumption.
Qed.

Local Lemma P3_complete Γ ϕ :
  well_formed ϕ ->
  mkMLGoal _ Γ [] (! ! ϕ ---> ϕ) BasicReasoning.
Proof.
  intros.
  mlIntro.
  mlAssert ("H" : (ϕ or ! ϕ)). wf_auto2.
  { mlIntro. mlAssumption. }
  mlDestructOr "H".
  * mlAssumption.
  * mlExFalso. mlApply "0". mlAssumption.
Qed.

Local Lemma MP_complete Γ ϕ ψ i:
  well_formed ϕ -> well_formed ψ ->
  mkMLGoal _ Γ [] ϕ i -> mkMLGoal _ Γ [] (ϕ ---> ψ) i  ->
  mkMLGoal _ Γ [] ψ i.
Proof.
  intros.
  mlAssert ("H" : (ϕ and (ϕ ---> ψ))). wf_auto2.
  { mlSplitAnd; assumption. }
  mlDestructAnd "H".
  mlApply "1". mlAssumption.
Qed.

Local Lemma Ex_quan_complete (Γ : Theory) (ϕ : Pattern) (y : evar):
  well_formed (ex , ϕ) -> 
  mkMLGoal _ Γ [] ((ex , ϕ) ^ [patt_free_evar y] ---> (ex , ϕ)) BasicReasoning.
Proof.
  intros. mlIntro "H".
  unfold instantiate.
  mlExists y. mlAssumption.
Qed.

Local Lemma Ex_gen_complete (Γ : Theory) (ϕ₁ ϕ₂ : Pattern) (x : evar) (i : ProofInfo):
  well_formed ϕ₁ -> well_formed ϕ₂ ->
  ProofInfoLe (ExGen := {[x]}, SVSubst := ∅, KT := false) i ->
  x ∉ free_evars ϕ₂ ->
  mkMLGoal _ Γ [] (ϕ₁ ---> ϕ₂) i ->
  mkMLGoal _ Γ [] (exists_quantify x ϕ₁ ---> ϕ₂) i.
Proof.
  unfold exists_quantify. intros.
  mlIntro "H0".
  mlDestructEx "H0" as x.
  1: by apply evar_quantify_no_occurrence.
  rewrite evar_open_evar_quantify. 2: wf_auto2.
  mlRevertLast. assumption.
Qed.

End with_signature.