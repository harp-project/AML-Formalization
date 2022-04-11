From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Coq.Logic Require Import FunctionalExtensionality PropExtensionality Classical_Pred_Type Classical_Prop.
From Coq.micromega Require Import Lia.
From Coq.Program Require Import Wf.

From Equations Require Import Equations.

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

Lemma drop_weight {Σ : Signature} (dummy_x : evar) (idx : nat) (l : list (prod db_index evar)) :
    closing_list_weight l >= closing_list_weight (drop idx l).
Proof.
    unfold closing_list_weight.
    move: l.
    induction idx; intros l.
    {
        rewrite drop_0. lia.
    }
    {
        destruct l; simpl.
        {
            lia.
        }
        {
            specialize (IHidx l). lia.
        }
    }
Qed.

Definition lower_closing_list {Σ : Signature} (x : evar) (l : list (prod db_index evar))
:= (0,x)::(map (λ p, (Nat.pred p.1, p.2)) l).

Lemma lower_closing_list_weight {Σ : Signature} (x : evar) (l : list (prod db_index evar)) :
    closing_list_weight l >= closing_list_weight (lower_closing_list x l).
Proof.
    unfold closing_list_weight.
    unfold lower_closing_list.
    simpl.
    Search sum_list_with map.
    induction l.
    { simpl. unfold sum_list_with. lia. }
    { simpl. lia. }
Qed.

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

Lemma list_find_dep {A} P `{∀ x, Decision (P x)} (l : list A) :
    ({p : (nat*A)%type & (l !! p.1 = Some p.2 ∧ P p.2 ∧ ∀ j y, l !! j = Some y → j < p.1 → ¬P y) }
    + (Forall (λ x, ¬P x) l))%type.
Proof.
    remember (list_find P l) as f.
    symmetry in Heqf.
    destruct f.
    {
        left.
        destruct p as [n a].
        apply list_find_Some in Heqf.
        exists (n,a). apply Heqf.
    }
    {
        right. 
        apply list_find_None in Heqf.
        exact Heqf.
    }
Defined.

Equations? make_zero_list
    {Σ : Signature}
    (dummy_x : evar)
    (l : list (prod db_index evar))
    : (list (prod db_index evar))
    by wf (closing_list_weight l) lt
:=
    make_zero_list dummy_x l
        with (@list_find_dep _ (λ p, p.1 <> 0) _ l) => {
        | inr _ => l
        | inl (existT p pf) =>
            let idx := p.1 in
            (firstn idx l) ++ (make_zero_list dummy_x (lower_closing_list dummy_x (skipn idx l)))
        }.
Proof.
    destruct_and!. destruct p. simpl in *. unfold idx. clear idx.
    destruct p as [dbi x]. simpl in *.
    destruct dbi.
    { contradiction. }
    rewrite <- (take_drop_middle l n (S dbi, x) H) at 2.
    unfold closing_list_weight.
    rewrite sum_list_with_app.
    rewrite -> (drop_S l (S dbi, x) n H) at 1.
    simpl. clear H1 make_zero_list.
    pose proof (Htmp1 := lower_closing_list_weight dummy_x (drop (S n) l)).
    unfold closing_list_weight, lower_closing_list in Htmp1. simpl in Htmp1.
    lia.
Defined.


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
