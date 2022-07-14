From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Ltac2 Require Import Ltac2.

From Coq Require Import Ensembles Bool String.
From Coq.Logic Require Import FunctionalExtensionality Eqdep_dec.
From Equations Require Import Equations.

Require Import Coq.Program.Tactics.

From MatchingLogic Require Import
    Syntax
    DerivedOperators_Syntax
    ProofSystem
    IndexManipulation
    wftactics
    ProofMode_base
    ProofMode_propositional
.

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



Lemma pile_impl_allows_gen_x {Σ : Signature} x gpi svs kt fp:
ProofInfoLe ( (ExGen := {[x]}, SVSubst := svs, KT := kt, FP := fp)) ( gpi) ->
x ∈ pi_generalized_evars gpi.
Proof.
intros [H].
pose (H1 := @A_impl_A Σ ∅ patt_bott ltac:(wf_auto2)).
pose (H2 := @prf_add_assumption Σ ∅ (patt_free_evar x) (patt_bott ---> patt_bott) BasicReasoning ltac:(wf_auto2) ltac:(wf_auto2) H1).
pose (H3 := @ProofSystem.Ex_gen Σ ∅ (patt_free_evar x) (patt_bott ---> patt_bott) x ltac:(wf_auto2) ltac:(wf_auto2) (proj1_sig H2) ltac:(simpl; set_solver)).
pose proof (H' := H ∅ _ H3).
feed specialize H'.
{
  constructor; simpl.
  {
    clear. set_solver.
  }
  {
    clear. set_solver.
  }
  {
    reflexivity.
  }
  {
    clear. set_solver.
  }
}
inversion H'. simpl in *. clear -pwi_pf_ge. set_solver.
Qed.

Lemma Ex_gen {Σ : Signature} (Γ : Theory) (ϕ₁ ϕ₂ : Pattern) (x : evar) (i : ProofInfo)
{pile : ProofInfoLe (
        {| pi_generalized_evars := {[x]};
           pi_substituted_svars := ∅;
           pi_uses_kt := false ;
           pi_framing_patterns := ∅ ;
        |}) i} :
x ∉ free_evars ϕ₂ ->
Γ ⊢i ϕ₁ ---> ϕ₂ using i ->
Γ ⊢i (exists_quantify x ϕ₁ ---> ϕ₂) using i.
Proof.
intros Hfev [pf Hpf].
unshelve (eexists).
{
  apply ProofSystem.Ex_gen.
  { pose proof (pf' := pf). apply proved_impl_wf in pf'.  wf_auto2. }
  { pose proof (pf' := pf). apply proved_impl_wf in pf'.  wf_auto2. }
  { exact pf. }
  { exact Hfev. }
}
{
  simpl.
  constructor; simpl.
  {
    rewrite elem_of_subseteq. intros x0 Hx0.
    rewrite elem_of_gset_to_coGset in Hx0.
    rewrite elem_of_union in Hx0.
    destruct Hx0.
    {
      rewrite elem_of_singleton in H. subst.
      eapply pile_impl_allows_gen_x.
      apply pile.
    }
    {
      inversion Hpf.
      apply pwi_pf_ge.
      rewrite elem_of_gset_to_coGset.
      assumption.
    }
  }
  {
    inversion Hpf.
    apply pwi_pf_svs.
  }
  {
    inversion Hpf.
    apply pwi_pf_kt.
  }
  {
    inversion Hpf.
    apply pwi_pf_fp.
  }
}
Defined.


Lemma Ex_quan {Σ : Signature} (Γ : Theory) (ϕ : Pattern) (y : evar) :
well_formed (patt_exists ϕ) ->
Γ ⊢i (instantiate (patt_exists ϕ) (patt_free_evar y) ---> (patt_exists ϕ))
using BasicReasoning.
Proof.
intros Hwf.
unshelve (eexists).
{
  apply ProofSystem.Ex_quan. apply Hwf.
}
{
  abstract (
    constructor; simpl;
    [( set_solver )
    |( set_solver )
    |( reflexivity )
    |( set_solver )
    ]
  ).
}
Defined.

Lemma universal_generalization {Σ : Signature} Γ ϕ x (i : ProofInfo) :
ProofInfoLe ( (ExGen := {[x]}, SVSubst := ∅, KT := false, FP := ∅)) i ->
well_formed ϕ ->
Γ ⊢i ϕ using i ->
Γ ⊢i patt_forall (evar_quantify x 0 ϕ) using i.
Proof.
intros pile wfϕ Hϕ.
unfold patt_forall.
unfold patt_not at 1.
replace (! evar_quantify x 0 ϕ)
  with (evar_quantify x 0 (! ϕ))
  by reflexivity.
apply Ex_gen.
{ exact pile. }
{ simpl. set_solver. }
toMLGoal.
{ wf_auto2. }
mlIntro. mlAdd Hϕ.
mlApply "0". mlExactn 0.
Defined.

(*Hint Resolve evar_quantify_well_formed.*)

Lemma forall_variable_substitution {Σ : Signature} Γ ϕ x:
well_formed ϕ ->
Γ ⊢i (all, evar_quantify x 0 ϕ) ---> ϕ
using ( (ExGen := {[x]}, SVSubst := ∅, KT := false, FP := ∅)).
Proof.
intros wfϕ.

unfold patt_forall.
replace (! evar_quantify x 0 ϕ)
  with (evar_quantify x 0 (! ϕ))
  by reflexivity.
apply double_neg_elim_meta.
{ wf_auto2. }
{ wf_auto2. }
toMLGoal.
{ wf_auto2. }
mlIntro.
mlIntro.
mlApply "0".
mlIntro.
mlApply "2".
pose proof (Htmp := @Ex_quan Σ Γ (evar_quantify x 0 (!ϕ)) x).
rewrite /instantiate in Htmp.
rewrite bevar_subst_evar_quantify_free_evar in Htmp.
{
  simpl. split_and!. now do 2 apply andb_true_iff in wfϕ as [_ wfϕ]. reflexivity.
}
specialize (Htmp ltac:(wf_auto2)).
useBasicReasoning.
mlAdd Htmp.
mlApply "3".
mlIntro.
mlApply "1".
mlExactn 4.
Defined.


Lemma ex_quan_monotone {Σ : Signature} Γ x ϕ₁ ϕ₂ (i : ProofInfo)
  (pile : ProofInfoLe ( (ExGen := {[x]}, SVSubst := ∅, KT := false, FP := ∅)) i) :
  Γ ⊢i ϕ₁ ---> ϕ₂ using i ->
  Γ ⊢i (exists_quantify x ϕ₁) ---> (exists_quantify x ϕ₂) using i.
Proof.
  intros H.
  pose proof (Hwf := @proved_impl_wf Σ Γ _ (proj1_sig H)).
  assert (wfϕ₁: well_formed ϕ₁ = true) by wf_auto2.
  assert (wfϕ₂: well_formed ϕ₂ = true) by wf_auto2.
  apply Ex_gen.
  { exact pile. }
  { simpl. rewrite free_evars_evar_quantify. clear. set_solver. }

  unfold exists_quantify.
  eapply syllogism_meta. 4: apply H.
  { wf_auto2. }
  { wf_auto2. }
  { wf_auto2. }
  clear H wfϕ₁ ϕ₁ Hwf.

  (* We no longer need to use [cast_proof] to avoid to ugly eq_sym terms;
     however, without [cast_proof'] the [replace] tactics does not work,
     maybe because of implicit parameters.
   *)
  eapply (cast_proof').
  {
    replace ϕ₂ with (instantiate (ex, evar_quantify x 0 ϕ₂) (patt_free_evar x)) at 1.
    2: { unfold instantiate.
       rewrite bevar_subst_evar_quantify_free_evar.
       now do 2 apply andb_true_iff in wfϕ₂ as [_ wfϕ₂].
       reflexivity.
    }
    reflexivity.
  }
        (* i =  gpi *)
  useBasicReasoning.
  apply Ex_quan.
  abstract (wf_auto2).
Defined.

Lemma ex_quan_and_proj1 {Σ : Signature} Γ x ϕ₁ ϕ₂:
  well_formed ϕ₁ = true ->
  well_formed ϕ₂ = true ->
  Γ ⊢i (exists_quantify x (ϕ₁ and ϕ₂)) ---> (exists_quantify x ϕ₁)
  using ( (ExGen := {[x]}, SVSubst := ∅, KT := false, FP := ∅)).
Proof.
  intros wfϕ₁ wfϕ₂.
  apply ex_quan_monotone.
  { apply pile_refl. }
  toMLGoal.
  { wf_auto2. }
  mlIntro.
  mlDestructAnd "0". mlExactn 0.
Defined.

Lemma ex_quan_and_proj2 {Σ : Signature} Γ x ϕ₁ ϕ₂:
  well_formed ϕ₁ = true ->
  well_formed ϕ₂ = true ->
  Γ ⊢i (exists_quantify x (ϕ₁ and ϕ₂)) ---> (exists_quantify x ϕ₂)
  using ( (ExGen := {[x]}, SVSubst := ∅, KT := false, FP := ∅)).
Proof.
  intros wfϕ₁ wfϕ₂.
  apply ex_quan_monotone.
  { apply pile_refl. }
  toMLGoal.
  { wf_auto2. }
  mlIntro.
  mlDestructAnd "0".
  mlExactn 1.
Defined.


Lemma strip_exists_quantify_l {Σ : Signature} Γ x P Q i :
x ∉ free_evars P ->
well_formed_closed_ex_aux P 1 ->
Γ ⊢i (exists_quantify x (evar_open 0 x P) ---> Q) using i ->
Γ ⊢i ex , P ---> Q using i.
Proof.
intros Hx HwfcP H.
unshelve (eapply (@cast_proof' Σ Γ _ _ _ _ H)).
abstract (
  unfold exists_quantify;
  rewrite -> evar_quantify_evar_open by assumption;
  reflexivity
).
Defined.

Lemma strip_exists_quantify_r {Σ : Signature} Γ x P Q i :
x ∉ free_evars Q ->
well_formed_closed_ex_aux Q 1 ->
Γ ⊢i P ---> (exists_quantify x (evar_open 0 x Q)) using i ->
Γ ⊢i P ---> ex, Q using i.
Proof.
intros Hx HwfcP H.
unshelve (eapply (@cast_proof' Σ Γ _ _ _ _ H)).
abstract (
  unfold exists_quantify;
  rewrite -> evar_quantify_evar_open by assumption;
  reflexivity
).
Defined.


(* prenex-exists-and-left *)
Lemma prenex_exists_and_1 {Σ : Signature} (Γ : Theory) ϕ₁ ϕ₂:
  well_formed (ex, ϕ₁) ->
  well_formed ϕ₂ ->
  Γ ⊢i ((ex, ϕ₁) and ϕ₂) ---> (ex, (ϕ₁ and ϕ₂))
  using ( (ExGen := {[fresh_evar (ϕ₂ ---> ex , (ϕ₁ and ϕ₂))]}, SVSubst := ∅, KT := false, FP := ∅)).
Proof.
  intros wfϕ₁ wfϕ₂.
  toMLGoal.
  { wf_auto2. }
  mlIntro. mlDestructAnd "0".
  fromMLGoal.

  remember (fresh_evar (ϕ₂ ---> (ex, (ϕ₁ and ϕ₂)))) as x.
  apply strip_exists_quantify_l with (x := x).
  { subst x. eapply evar_is_fresh_in_richer'.
    2: { apply set_evar_fresh_is_fresh'. }
    simpl. clear. set_solver.
  }
  { wf_auto2. }
  apply Ex_gen.
  { apply pile_refl. }
  { wf_auto2. }
  
  apply lhs_to_and.
  { wf_auto2. }
  { wf_auto2. }
  { wf_auto2. }

  eapply cast_proof'.
  {
    replace (evar_open 0 x ϕ₁ and ϕ₂)
            with (evar_open 0 x (ϕ₁ and ϕ₂)).
    2: {
      unfold evar_open. simpl_bevar_subst.
      rewrite [bevar_subst ϕ₂ _ _]bevar_subst_not_occur.
      {
        wf_auto2.
      }
      reflexivity.
    }
    reflexivity.
  }
  useBasicReasoning.
  apply Ex_quan.
  wf_auto2.
Defined.

(* prenex-exists-and-right *)
Lemma prenex_exists_and_2 {Σ : Signature} (Γ : Theory) ϕ₁ ϕ₂:
  well_formed (ex, ϕ₁) ->
  well_formed ϕ₂ ->
  Γ ⊢i (ex, (ϕ₁ and ϕ₂)) ---> ((ex, ϕ₁) and ϕ₂)
  using ( (ExGen := {[fresh_evar ((ϕ₁ and ϕ₂))]}, SVSubst := ∅, KT := false, FP := ∅)).
Proof.
  intros wfϕ₁ wfϕ₂.
  toMLGoal.
  { wf_auto2. }
  mlIntro.
  mlSplitAnd.
  - fromMLGoal.
    remember (fresh_evar (ϕ₁ and ϕ₂)) as x.
    apply strip_exists_quantify_l with (x := x).
    { subst x. apply set_evar_fresh_is_fresh. }
    (* TODO: make wf_auto2 solve this *)
    { simpl. rewrite !andbT. split_and!.
      + wf_auto2.
      + wf_auto2.
    }
    apply strip_exists_quantify_r with (x := x).
    { subst x. eapply evar_is_fresh_in_richer'.
      2: { apply set_evar_fresh_is_fresh'. }
      simpl. clear. set_solver.
    }
    { wf_auto2. }
    apply ex_quan_monotone.
    { apply pile_refl. }

    unfold evar_open. simpl_bevar_subst.
    rewrite [bevar_subst ϕ₂ _ _]bevar_subst_not_occur.
    {
      wf_auto2.
    }
    toMLGoal.
    { wf_auto2. }
    mlIntro. mlDestructAnd "0". mlExactn 0.
  - fromMLGoal.
    remember (fresh_evar (ϕ₁ and ϕ₂)) as x.
    eapply cast_proof'.
    {
      rewrite -[ϕ₁ and ϕ₂](@evar_quantify_evar_open Σ x 0).
      { subst x. apply set_evar_fresh_is_fresh. }
      { cbn. split_and!; auto. wf_auto. wf_auto2. }
      reflexivity.
    }
    apply Ex_gen.
    { apply pile_refl. }
    { eapply evar_is_fresh_in_richer. 2: { subst x. apply set_evar_fresh_is_fresh'. }
      simpl. clear. set_solver.
    }

    unfold evar_open.
    simpl_bevar_subst.
    rewrite [bevar_subst ϕ₂ _ _]bevar_subst_not_occur.
    {
      wf_auto2.
    }
    toMLGoal.
    { wf_auto2. }
    mlIntro.
    mlDestructAnd "0".
    mlExactn 1.
Defined.

Lemma prenex_exists_and_iff {Σ : Signature} (Γ : Theory) ϕ₁ ϕ₂:
  well_formed (ex, ϕ₁) ->
  well_formed ϕ₂ ->
  Γ ⊢i (ex, (ϕ₁ and ϕ₂)) <---> ((ex, ϕ₁) and ϕ₂)
  using ( (ExGen := {[fresh_evar ((ϕ₁ and ϕ₂))]}, SVSubst := ∅, KT := false, FP := ∅)).
Proof.
  intros wfϕ₁ wfϕ₂.
  apply conj_intro_meta.
  { wf_auto2. }
  { wf_auto2. }
  - apply prenex_exists_and_2; assumption.
  - (* TODO we need a tactic to automate this change *)
    replace (fresh_evar (ϕ₁ and ϕ₂))
    with (fresh_evar (ϕ₂ ---> ex , (ϕ₁ and ϕ₂))).
    2: { cbn. unfold fresh_evar. apply f_equal. simpl. set_solver. }
   apply prenex_exists_and_1; assumption.
Defined.


Lemma forall_gen {Σ : Signature} Γ ϕ₁ ϕ₂ x (i : ProofInfo):
  evar_is_fresh_in x ϕ₁ ->
  ProofInfoLe ( (ExGen := {[x]}, SVSubst := ∅, KT := false, FP := ∅)) i ->
  Γ ⊢i ϕ₁ ---> ϕ₂ using i ->
  Γ ⊢i ϕ₁ ---> all, (evar_quantify x 0 ϕ₂) using i.
Proof.
  intros Hfr pile Himp.
  pose proof (Hwf := proved_impl_wf _ _ (proj1_sig Himp)).
  pose proof (wfϕ₁ := well_formed_imp_proj1 Hwf).
  pose proof (wfϕ₂ := well_formed_imp_proj2 Hwf).
  toMLGoal.
  { wf_auto2. }
  mlIntro.
  mlApplyMetaRaw (@useBasicReasoning Σ Γ _ _ (@not_not_intro Σ Γ ϕ₁ ltac:(wf_auto2))) in "0".
  fromMLGoal.
  apply modus_tollens.

  eapply cast_proof'.
  {
    replace (! evar_quantify x 0 ϕ₂)
            with (evar_quantify x 0 (! ϕ₂))
                 by reflexivity.
    reflexivity.
  }
  apply Ex_gen.
  { exact pile. }
  { simpl. unfold evar_is_fresh_in in Hfr. clear -Hfr. set_solver. }
  apply modus_tollens; assumption.
Defined.

Lemma forall_variable_substitution' {Σ : Signature} Γ ϕ x (i : ProofInfo):
  well_formed ϕ ->
  (ProofInfoLe ( (ExGen := {[x]}, SVSubst := ∅, KT := false, FP := ∅)) i) ->
  Γ ⊢i (all, evar_quantify x 0 ϕ) ---> ϕ using i.
Proof.
  intros wfϕ pile.
  pose proof (Htmp := @forall_variable_substitution Σ Γ ϕ x wfϕ).
  eapply useGenericReasoning. apply pile. apply Htmp.
Defined.

Lemma forall_elim {Σ : Signature} Γ ϕ x (i : ProofInfo):
  well_formed (ex, ϕ) ->
  evar_is_fresh_in x ϕ ->
  ProofInfoLe ( (ExGen := {[x]}, SVSubst := ∅, KT := false, FP := ∅)) i ->
  Γ ⊢i (all, ϕ) using i ->
  Γ ⊢i (evar_open 0 x ϕ) using i.
Proof.
  intros wfϕ frϕ pile H.
  destruct i.
  eapply MP.
  2: eapply forall_variable_substitution'.
  2: wf_auto2.
  2: apply pile.
  eapply cast_proof'.
  {
    rewrite evar_quantify_evar_open.
    { apply frϕ. }
    { wf_auto2. }
    reflexivity.
  }
  apply H.
Defined.

Lemma prenex_forall_imp {Σ : Signature} Γ ϕ₁ ϕ₂ i:
  well_formed (ex, ϕ₁) ->
  well_formed ϕ₂ ->
  ProofInfoLe ( (ExGen := {[fresh_evar (ϕ₁ ---> ϕ₂)]}, SVSubst := ∅, KT := false, FP := ∅)) i ->
  Γ ⊢i (all, (ϕ₁ ---> ϕ₂)) using i ->
  Γ ⊢i (ex, ϕ₁) ---> (ϕ₂) using i.
Proof.
  intros wfϕ₁ wfϕ₂ pile H.
  remember (fresh_evar (ϕ₁ ---> ϕ₂)) as x.
  apply (@strip_exists_quantify_l Σ Γ x).
  { subst x.
    eapply evar_is_fresh_in_richer'.
    2: { apply set_evar_fresh_is_fresh'. }
    simpl. set_solver.
  }
  { wf_auto2. }
  apply Ex_gen.
  { apply pile. }
  1: {
    subst x.
    eapply evar_is_fresh_in_richer'.
    2: { apply set_evar_fresh_is_fresh'. }
    simpl. set_solver.
  }

  eapply cast_proof'.
  {
    rewrite -[HERE in evar_open _ _ _ ---> HERE](@evar_open_not_occur Σ 0 x ϕ₂).
    {
      wf_auto2.
    }
    reflexivity.
  }
  eapply forall_elim with (x := x) in H.
  4: { apply pile. }
  2: wf_auto2.
  2: { subst x. apply set_evar_fresh_is_fresh. }
  unfold evar_open in *. simpl in *. exact H.
Defined.


Lemma evar_fresh_in_foldr {Σ : Signature} x g l:
  evar_is_fresh_in x (foldr patt_imp g l) <-> evar_is_fresh_in x g /\ evar_is_fresh_in_list x l.
Proof.
  induction l; simpl; split; intros H.
  - split;[assumption|]. unfold evar_is_fresh_in_list. apply Forall_nil. exact I.
  - destruct H as [H _]. exact H.
  - unfold evar_is_fresh_in_list,evar_is_fresh_in in *. simpl in *.
    split;[set_solver|].
    apply Forall_cons.
    destruct IHl as [IHl1 IHl2].
    split;[set_solver|].
    apply IHl1. set_solver.
  - unfold evar_is_fresh_in_list,evar_is_fresh_in in *. simpl in *.
    destruct IHl as [IHl1 IHl2].
    destruct H as [H1 H2].
    inversion H2; subst.
    specialize (IHl2 (conj H1 H4)).
    set_solver.
Qed.

Lemma Ex_gen_lifted {Σ : Signature} (Γ : Theory) (ϕ₁ : Pattern) (l : hypotheses) (n : string) (g : Pattern) (x : evar)
  (i : ProofInfo) :
  evar_is_fresh_in x g ->
  evar_is_fresh_in_list x (patterns_of l) ->
  ProofInfoLe ( (ExGen := {[x]}, SVSubst := ∅, KT := false, FP := ∅)) i ->
  bevar_occur ϕ₁ 0 = false ->
  @mkMLGoal Σ Γ (mkNH n ϕ₁::l) g i -> 
  @mkMLGoal Σ Γ (mkNH n (exists_quantify x ϕ₁)::l) g i.
Proof.
  intros xfrg xfrl pile Hno0 H.
  mlExtractWF H1 H2.
  fromMLGoal.
  pose proof (H1' := H1).
  unfold Pattern.wf in H1. simpl in H1. apply andb_prop in H1. destruct H1 as [H11 H12].
  apply wf_ex_quan_impl_wf in H11. 2: assumption.
  unfold of_MLGoal in H. simpl in H.
  specialize (H H2).
  feed specialize H.
  {
    unfold Pattern.wf. simpl. rewrite H11 H12. reflexivity.
  }
  apply Ex_gen.
  { apply pile. }
  2: { assumption. }
  simpl.
  apply evar_fresh_in_foldr.
  split; assumption.
Defined.



(* Weakening under existential *)
Local Example ex_exists {Σ : Signature} Γ ϕ₁ ϕ₂ ϕ₃ i:
  well_formed (ex, ϕ₁) ->
  well_formed (ex, ϕ₂) ->
  well_formed ϕ₃ ->
  ProofInfoLe ( (ExGen := {[(evar_fresh (elements (free_evars ϕ₁ ∪ free_evars ϕ₂ ∪ free_evars (ex, ϕ₃))))]}, SVSubst := ∅, KT := false, FP := ∅)) i ->
  Γ ⊢i (all, (ϕ₁ and ϕ₃ ---> ϕ₂)) using i ->
  Γ ⊢i (ex, ϕ₁) ---> ϕ₃ ---> (ex, ϕ₂) using i.
Proof.
  intros wfϕ₁ wfϕ₂ wfϕ₃ pile H.
  toMLGoal.
  { wf_auto2. }
  mlIntro.
  remember (evar_fresh (elements (free_evars ϕ₁ ∪ free_evars ϕ₂ ∪ free_evars (ex, ϕ₃)))) as x.
  rewrite -[ϕ₁](@evar_quantify_evar_open Σ x 0).
  { subst x.
    eapply evar_is_fresh_in_richer'. 2: apply set_evar_fresh_is_fresh'. clear. set_solver.
  }
  wf_auto2.
  mlIntro.
  apply Ex_gen_lifted.
  { subst x. eapply evar_is_fresh_in_richer'. 2: apply set_evar_fresh_is_fresh'. clear. set_solver. }
  { constructor. 2: apply Forall_nil; exact I.
    subst x.
    eapply evar_is_fresh_in_richer'. 2: apply set_evar_fresh_is_fresh'. clear. set_solver.
  }
  { wf_auto. }

Abort.
