From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From stdpp Require Import base tactics sets.

From MatchingLogic.Utils
Require Import
    extralibrary
.

From MatchingLogic
Require Import
    Signature
    Pattern
.

Section with_signature.
    Context {Σ : Signature}.

    (* TODO make Set ? *)
  Inductive Application_context : Type :=
  | box
  | ctx_app_l (cc : Application_context) (p : Pattern) (Prf : well_formed p)
  | ctx_app_r (p : Pattern) (cc : Application_context) (Prf : well_formed p)
  .

  Fixpoint AC_free_evars (AC : Application_context) : EVarSet :=
    match AC with
    | box => ∅
    | @ctx_app_l cc p _ => free_evars p ∪ AC_free_evars cc
    | @ctx_app_r p cc _ => free_evars p ∪ AC_free_evars cc
    end.

  Fixpoint subst_ctx (C : Application_context) (p : Pattern)
    : Pattern :=
    match C with
    | box => p
    | @ctx_app_l C' p' prf => patt_app (subst_ctx C' p) p'
    | @ctx_app_r p' C' prf => patt_app p' (subst_ctx C' p)
    end.

  (* TODO rewrite using wc_sctx *)
  Lemma wf_sctx (C : Application_context) (A : Pattern) :
    well_formed A = true -> well_formed (subst_ctx C A) = true.
  Proof.
    intros H.
    unfold well_formed in H.
    apply andb_true_iff in H. destruct H as [Hwfp Hwfc].
    unfold well_formed_closed in Hwfc.
    induction C; simpl.
    - unfold well_formed. rewrite Hwfp. unfold well_formed_closed. rewrite Hwfc. reflexivity.
    - unfold well_formed. simpl.
      unfold well_formed in IHC. apply andb_true_iff in IHC. destruct IHC as [IHC1 IHC2].
      rewrite IHC1. simpl.
      unfold well_formed in Prf. apply andb_true_iff in Prf. destruct Prf as [Prf1 Prf2].
      rewrite Prf1. simpl.
      unfold well_formed_closed in *. simpl.
      destruct_and!. split_and!; auto.
    - unfold well_formed,well_formed_closed in *. simpl in *.
      destruct_and!. split_and!; auto.
  Qed.

  Lemma wp_sctx (C : Application_context) (A : Pattern) :
    well_formed_positive A = true -> well_formed_positive (subst_ctx C A) = true.
  Proof.
    intros H.
    induction C.
    - auto.
    - simpl. rewrite IHC. simpl.
      unfold well_formed in Prf. apply andb_true_iff in Prf. destruct Prf. exact H0.
    - simpl. unfold well_formed in Prf. apply andb_true_iff in Prf.
      destruct Prf. rewrite H0. rewrite IHC. reflexivity.
  Qed.

  Lemma wcex_sctx (C : Application_context) (A : Pattern) idx1 :
    well_formed_closed_ex_aux A idx1 = true -> well_formed_closed_ex_aux (subst_ctx C A) idx1 = true.
  Proof.
    intros H.
    induction C.
    - auto.
    - simpl. rewrite IHC. simpl.
      unfold well_formed,well_formed_closed in *.
      destruct_and!.
      eapply well_formed_closed_ex_aux_ind. 2: eassumption. lia.
    - simpl. rewrite IHC.
      unfold well_formed,well_formed_closed in *.
      destruct_and!. split_and!; auto.
      eapply well_formed_closed_ex_aux_ind. 2: eassumption. lia.
  Qed.

  Lemma wcmu_sctx (C : Application_context) (A : Pattern) idx1 :
    well_formed_closed_mu_aux A idx1 = true -> well_formed_closed_mu_aux (subst_ctx C A) idx1 = true.
  Proof.
    intros H.
    induction C.
    - auto.
    - simpl. rewrite IHC. simpl.
      unfold well_formed,well_formed_closed in *.
      destruct_and!.
      eapply well_formed_closed_mu_aux_ind. 2: eassumption. lia.
    - simpl. rewrite IHC.
      unfold well_formed,well_formed_closed in *.
      destruct_and!. split_and!; auto.
      eapply well_formed_closed_mu_aux_ind. 2: eassumption. lia.
  Qed.
  
  Fixpoint free_evars_ctx (C : Application_context)
    : (EVarSet) :=
    match C with
    | box => empty
    | @ctx_app_l cc p prf => union (free_evars_ctx cc) (free_evars p)
    | @ctx_app_r p cc prf => union (free_evars p) (free_evars_ctx cc)
    end.


  Definition ApplicationContext2Pattern (boxvar : evar) (AC : Application_context) :=
    subst_ctx AC (patt_free_evar boxvar).

  Lemma ApplicationContext2Pattern_one_occ (AC : Application_context) (boxvar : evar):
    boxvar ∉ free_evars_ctx AC ->
    count_evar_occurrences boxvar (ApplicationContext2Pattern boxvar AC) = 1.
  Proof.
    intros H.
    induction AC; simpl.
    - destruct (decide (boxvar = boxvar)). reflexivity. contradiction.
    - simpl in H. apply not_elem_of_union in H. 
      rewrite IHAC.
      { exact (proj1 H). }
      simpl in H.
      rewrite count_evar_occurrences_0. 2: lia.
      exact (proj2 H).
    - simpl in H. apply not_elem_of_union in H. 
      rewrite IHAC.
      { exact (proj2 H). }
      simpl in H.
      rewrite count_evar_occurrences_0. 2: lia.
      exact (proj1 H).
  Qed.

  End with_signature.


Lemma free_evars_subst_ctx {Σ : Signature} AC ϕ:
free_evars (subst_ctx AC ϕ) = AC_free_evars AC ∪ free_evars ϕ.
Proof.
induction AC; simpl.
- set_solver.
- rewrite IHAC. clear. set_solver.
- rewrite IHAC. clear. set_solver.
Qed.