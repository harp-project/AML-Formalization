From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Coq.Logic Require Import FunctionalExtensionality PropExtensionality Classical_Pred_Type Classical_Prop.
From Coq.micromega Require Import Lia.
From Coq.Program Require Import Wf.

From stdpp Require Import base fin_sets.
From stdpp Require Import pmap gmap mapset fin_sets sets propset list_numbers.

From MatchingLogic.Utils Require Import Lattice stdpp_ext extralibrary.
From MatchingLogic Require Import
  Syntax
  Freshness
  NamedAxioms
  IndexManipulation
  Semantics
.

Import MatchingLogic.Syntax.Notations.


Inductive closure_increasing {Σ : Signature} : (list (prod db_index evar)) -> Prop :=
| ci_nil : closure_increasing []
| ci_cons
  (k0 k1 : db_index)
  (x0 x1 : evar)
  (l : list (prod db_index evar)) :
  k0 <= k1 ->
  closure_increasing ((k1,x1)::l) ->
  closure_increasing ((k0,x0)::(k1,x1)::l)
.

Definition M_pre_predicate {Σ : Signature} (k : db_index) (M : Model) (ϕ : Pattern) : Prop :=
    forall (l : list (prod db_index evar)),
      Forall (λ p, p.1 <= k) l ->
      closure_increasing l ->
      well_formed_closed_ex_aux (bcmcloseex l ϕ) 0 ->
      M_predicate M (bcmcloseex l ϕ).

Lemma pre_predicate_S {Σ : Signature} (k : db_index) (M : Model) (ϕ : Pattern) :
  M_pre_predicate (S k) M ϕ ->
  M_pre_predicate k M ϕ.
Proof.
  unfold M_pre_predicate.
  intros H l Hl Hci Hwf.
  apply H.
  { clear -Hl. induction l. apply Forall_nil. exact I. inversion Hl. subst.
    apply Forall_cons. split;[lia|]. apply IHl. assumption.
  }
  { exact Hci. }
  { exact Hwf. }
Qed.

Definition closing_list_weight {Σ : Signature} (l : list (prod db_index evar)) : nat :=
  sum_list_with fst l.

Definition lower_closing_list {Σ : Signature} (x : evar) (l : list (prod db_index evar))
:= (0,x)::(map (λ p, (Nat.pred p.1, p.2)) l).

(*
Lemma lower_closing_list_app {Σ : Signature} (x : evar) (l1 l2 : list (prod db_index evar))
: lower_closing_list x (l1 ++ l2) = (map (λ p, (Nat.pred p.1, p.2)) l1) ++ (lower_closing_list x l2).
Proof.
  unfold lower_closing_list.
  rewrite map_app. rewrite app_assoc. reflexivity.
Qed.
*)
Lemma lower_closing_list_same
  {Σ : Signature}
  (x : evar)
  (l : list (prod db_index evar))
  (ϕ : Pattern)
  :
  bevar_occur ϕ 0 = false ->
  Forall (λ p, p.1 > 0) l ->
  well_formed_closed_ex_aux (bcmcloseex l ϕ) 0 ->
  bcmcloseex (lower_closing_list x l) ϕ = bcmcloseex l ϕ.
Proof.
  intros Hocc Hagt0 Hwfc.
  move: ϕ Hocc Hwfc.
  induction l; intros ϕ Hocc Hwfc.
  { simpl in *. apply evar_open_closed. apply Hwfc. }
  {
    destruct a as [dbi y].
    simpl in *.
    inversion Hagt0. subst. simpl in *.
    rewrite -IHl.
    { assumption. }
    { 
      apply bevar_occur_evar_open.
      { exact Hocc. }
      { lia. }
    }
    { exact Hwfc. }
    f_equal.

    destruct dbi.
    { lia. }
    destruct dbi.
    { simpl. apply evar_open_twice_not_occur. apply Hocc. }
    apply evar_open_comm_lower.
    lia.
  }
Qed.


(*
Fixpoint lower_closing_list_iter {Σ : Signature} (k : nat) (x : evar) (l : list (prod db_index evar))
:=
match k with
| 0 => l
| (S k') => lower_closing_list_iter k' x (lower_closing_list x l)
end.

Lemma lower_closing_list_iter_same
  {Σ : Signature}
  (k : nat)
  (x : evar)
  (l : list (prod db_index evar))
  (ϕ : Pattern)
:
  bcmcloseex (lower_closing_list_iter k x l) ϕ = bcmcloseex l ϕ.
Proof. Abort.
*)

Lemma pre_predicate_0 {Σ : Signature} (k : db_index) (M : Model) (ϕ : Pattern) :
  M_pre_predicate 0 M ϕ ->
  M_pre_predicate k M ϕ.
Proof.
  unfold M_pre_predicate.
  intros H l Hl Hcd Hwf.
  Search list_find.
  (* we want to give [H] a list [l'] such that [bcmcloseex l' ϕ = bcmcloseex l ϕ]
     containing only zeros as indices
  *)

Qed.

Lemma closed_M_pre_predicate_is_M_predicate {Σ : Signature} (k : db_index) (M : Model) (ϕ : Pattern) :
  well_formed_closed_ex_aux ϕ 0 ->
  M_pre_predicate k M ϕ ->
  M_predicate M ϕ.
Proof.
  intros Hwfcex Hpp.
  unfold M_pre_predicate in Hpp.
  specialize (Hpp []). simpl in Hpp.
  apply Hpp.
  apply Forall_nil. exact I.
  apply Hwfcex.
Qed.

Lemma M_pre_predicate_bott {Σ : Signature} (k : db_index) (M : Model) :
  M_pre_predicate k M patt_bott.
Proof.
  intros l Hk H.
  rewrite bcmcloseex_bott.
  apply M_predicate_bott.
Qed.

Lemma M_pre_predicate_imp
  {Σ : Signature} (k : db_index) (M : Model) (p q : Pattern) :
  M_pre_predicate k M p ->
  M_pre_predicate k M q ->
  M_pre_predicate k M (patt_imp p q).
Proof.
  intros Hp Hq.
  intros l Hk H.
  rewrite bcmcloseex_imp.
  rewrite bcmcloseex_imp in H.
  simpl in H.
  destruct_and!.
  apply M_predicate_impl.
  { apply Hp. assumption. assumption. }
  { apply Hq. assumption. assumption. }
Qed.

Lemma M_pre_predicate_exists {Σ : Signature} (k : db_index) M ϕ :
  M_pre_predicate (S k) M ϕ ->
  M_pre_predicate k M (patt_exists ϕ).
Proof.
  simpl. unfold M_pre_predicate. intros H.
  intros l Hk Hwfc.
  rewrite bcmcloseex_ex.
  apply M_predicate_exists.
  remember (evar_fresh
  (elements (free_evars (bcmcloseex (map (λ p : nat * evar, (S p.1, p.2)) l) ϕ)))) as x.
  replace (evar_open 0 x (bcmcloseex (map (λ p : nat * evar, (S p.1, p.2)) l) ϕ))
  with (bcmcloseex ((pair 0 x)::(map (λ p : nat * evar, (S p.1, p.2)) l)) ϕ)
  by reflexivity.
  apply H.
  {
    apply Forall_cons. split.
    {
      simpl. lia.
    }
    {
      clear -Hk. induction l.
      { apply Forall_nil. exact I. }
      { simpl. inversion Hk. subst. apply Forall_cons. simpl. split. lia. apply IHl. apply H2. }
    }
  }
  simpl.
  unfold evar_open.
  
  apply wfc_ex_aux_bevar_subst.
  2: { simpl. reflexivity. }
  apply wfc_ex_aux_bcmcloseex.
  { clear. induction l. apply Forall_nil. exact I. apply Forall_cons. split.   }
  { assumption. }
Qed.


Definition T_pre_predicate {Σ : Signature} Γ ϕ :=
  forall M, satisfies_theory M Γ -> M_pre_predicate M ϕ.
