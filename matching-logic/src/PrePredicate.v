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
| ci_single
  (k0 : db_index)
  (x0 : evar) :
  closure_increasing [(k0,x0)]
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

Lemma make_zero_list_zeroes {Σ : Signature} (dummy_x : evar) (l : list (prod db_index evar)) :
    (Forall (λ p, p.1 = 0) (make_zero_list dummy_x l)).
Proof.
    eapply make_zero_list_elim.
    {
        clear. intros. destruct p as [dbi x]. simpl in *.
        destruct_and!.
        apply Forall_app. split.
        {
            apply Forall_forall.
            intros.
            clear Heq.
            apply elem_of_take in H1.
            destruct H1 as [i Hi].
            destruct Hi as [Hi1 Hi2].
            specialize (H3 i x0 Hi1 Hi2).
            tauto.
         }
         apply H.
    }
    {
        clear. intros. clear Heq.
        rewrite Forall_forall in f.
        rewrite Forall_forall.
        intros. specialize (f x H). tauto.
    }
Qed.

Lemma closure_increasing_lower_closing_list
  {Σ : Signature}
  (dummy_x : evar)
  (l : list (prod db_index evar))
  :
  closure_increasing l ->
  closure_increasing (lower_closing_list dummy_x l).
Proof.
  unfold lower_closing_list.
  intros H.

  induction H.
  {
    simpl. constructor.
  }
  {
    simpl. constructor.
    { lia. }
    { constructor. }
  }
  {
    simpl in *.
    constructor.
    { lia. }
    constructor.
    { lia. }
    inversion IHclosure_increasing; subst.
    assumption.
  }
Qed.

Lemma closure_increasing_app_proj1
  {Σ : Signature}
  (l₁ l₂ : list (prod db_index evar))
  :
  closure_increasing (l₁ ++ l₂) ->
  closure_increasing l₁.
Proof.
  intros H.
  induction l₁.
  {
    apply ci_nil.
  }
  {
    simpl in H.
    destruct l₁.
    {
      destruct a.
      apply ci_single.
    }
    {
      inversion H. subst. simpl in IHl₁.
      specialize (IHl₁ ltac:(assumption)).
      constructor.
      { assumption. }
      { exact IHl₁. }
    }
  }
Qed.

Lemma closure_increasing_app_proj2
  {Σ : Signature}
  (l₁ l₂ : list (prod db_index evar))
  :
  closure_increasing (l₁ ++ l₂) ->
  closure_increasing l₂.
Proof.
  intros H.
  induction l₁.
  {
    simpl in H. exact H.
  }
  {
    apply IHl₁. clear IHl₁.
    inversion H; subst.
    {
      apply ci_nil.
    }
    {
      assumption.
    }
  }
Qed.

Lemma wfc_ex_aux_evar_open_change_evar {Σ : Signature} x x' dbi ϕ:
  well_formed_closed_ex_aux (evar_open dbi x ϕ) dbi =
  well_formed_closed_ex_aux (evar_open dbi x' ϕ) dbi.
Proof.
  unfold evar_open. simpl.
  move: dbi.
  induction ϕ; intros dbi; simpl; auto; try congruence.
  {
    repeat case_match; simpl; auto.
  }
Qed.

Lemma wfcexaux_bcmcloseex_evar_open_change_evar {Σ : Signature} l x x' dbi dbi' ϕ:
  well_formed_closed_ex_aux (bcmcloseex l (evar_open dbi x ϕ)) dbi'
  = well_formed_closed_ex_aux (bcmcloseex l (evar_open dbi x' ϕ)) dbi'.
Proof.
  move: dbi dbi' x x' l.
  induction ϕ; intros dbi dbi' x' x'' l; unfold evar_open; simpl; try reflexivity.
  {
    repeat case_match; auto.
    clear.
    induction l.
    {
      reflexivity.
    }
    {
      simpl. unfold evar_open. simpl. apply IHl.
    }
  }
  {
    unfold evar_open in *.
    do 2 rewrite bcmcloseex_app. simpl.
    erewrite IHϕ1, IHϕ2. reflexivity.
  }
  {
    unfold evar_open in *.
    do 2 rewrite bcmcloseex_imp. simpl.
    erewrite IHϕ1, IHϕ2. reflexivity.
  }
  {
    unfold evar_open in *.
    do 2 rewrite bcmcloseex_ex. simpl.
    erewrite IHϕ. reflexivity.
  }
  {
    unfold evar_open in *.
    do 2 rewrite bcmcloseex_mu. simpl.
    erewrite IHϕ. reflexivity.
  }
Qed.

Lemma wfcexaux_bcmcloseex_lower_closing_list
  {Σ : Signature}
  (dummy_x : evar)
  (l : list (prod db_index evar))
  (ϕ : Pattern)
  :
  well_formed_closed_ex_aux (bcmcloseex l ϕ) 0 = true ->
  well_formed_closed_ex_aux (bcmcloseex (lower_closing_list dummy_x l) ϕ) 0 = true.
Proof.
  move: ϕ dummy_x.
  induction l; intros ϕ dummy_x H.
  {
    simpl in *.
    apply wfc_mu_aux_body_ex_imp3.
    { lia. }
    apply well_formed_closed_ex_aux_ind with (ind_evar1 := 0).
    { lia. }
    exact H.
  }
  {
    destruct a as [dbi x].
    simpl in *.
    destruct dbi.
    {
      simpl in *. apply IHl.
      erewrite wfcexaux_bcmcloseex_evar_open_change_evar. apply H.
    }
    rewrite -evar_open_comm_higher.
    { lia. }
    apply IHl. exact H.
  }
Qed.

Lemma wfcexaux_bcmcloseex_evar_open_change_evar_2
  {Σ : Signature}
  l ϕ dbi (f : prod db_index evar -> evar):
  well_formed_closed_ex_aux (bcmcloseex (map (λ p, (p.1, (f p))) l) ϕ) dbi
  = well_formed_closed_ex_aux (bcmcloseex l ϕ) dbi.
Proof.
  move: ϕ.
  induction l; intros ϕ.
  {
    simpl. reflexivity.
  }
  {
    simpl. rewrite IHl. clear IHl.
    apply wfcexaux_bcmcloseex_evar_open_change_evar.
  }
Qed.

  Lemma wfcex_and_increasing_first_not_k_impl_wfcex
    {Σ : Signature}
    (l : list (prod db_index evar))
    (k : db_index)
    (ϕ : Pattern)
    :
    closure_increasing l ->
    (forall p, l !! 0 = Some p -> p.1 > k) ->
    well_formed_closed_ex_aux (bcmcloseex l ϕ) k = true ->
    bevar_occur ϕ k = false.
  Proof.
    intros Hci Hnk Hwfc.

    destruct l.
    {
      simpl in *.
      apply wfc_ex_aux_implies_not_bevar_occur.
      exact Hwfc.
    }
    specialize (Hnk p erefl).

    move: p k l Hnk Hwfc Hci.
    induction ϕ; intros p k l Hnk Hwfc Hci; simpl in *; auto.
    {
      unfold evar_open in Hwfc. simpl in Hwfc.
      repeat case_match; simpl in *; auto; inversion Hci; subst; simpl in *; try lia;
        repeat case_match; try lia.
      unfold evar_open in Hwfc. simpl in Hwfc. case_match; try lia.
      exfalso. clear Heqc Heqs Hci Heqc0.
      induction l1; simpl in Hwfc.
      {
        case_match. lia. congruence.
      }
      {
        destruct a. inversion H2; subst.
        unfold evar_open in Hwfc. simpl in Hwfc. case_match; subst; auto; try lia.
        apply IHl1. apply Hwfc.
        destruct l1.
        {
          constructor.
        }
        {
          destruct p.
          inversion H7. subst.
          apply ci_cons. lia. assumption.
        }
      }
    }
    {
      unfold evar_open in *. simpl in Hwfc. rewrite bcmcloseex_app in Hwfc.
      simpl in Hwfc. destruct_and!.
      specialize (IHϕ1 p k l Hnk ltac:(assumption) Hci).
      specialize (IHϕ2 p k l Hnk ltac:(assumption) Hci).
      rewrite IHϕ1.
      rewrite IHϕ2.
      reflexivity.
    }
    {
      unfold evar_open in *. simpl in Hwfc. rewrite bcmcloseex_imp in Hwfc.
      simpl in Hwfc. destruct_and!.
      specialize (IHϕ1 p k l Hnk ltac:(assumption) Hci).
      specialize (IHϕ2 p k l Hnk ltac:(assumption) Hci).
      rewrite IHϕ1.
      rewrite IHϕ2.
      reflexivity.
    }
    {
      unfold evar_open in *. simpl in Hwfc. rewrite bcmcloseex_ex in Hwfc.
      simpl in Hwfc.
      destruct p as [dbi x]. simpl in *.
      specialize (IHϕ (S dbi,x) (S k) ((map (λ p : nat * evar, (S p.1, p.2)) l)) ltac:(simpl;lia) Hwfc).
      feed specialize IHϕ.
      {
        clear -Hci. induction l.
        {
          simpl. apply ci_single.
        }
        {
          simpl in *. inversion Hci. subst. apply ci_cons.
          { simpl. lia. }
          {
            inversion H4; subst.
            {
              simpl. apply ci_single.
            }
            {
              simpl in *. apply ci_cons. lia.
              feed specialize IHl.
              {
                apply ci_cons. lia. assumption.
              }
              inversion IHl. subst. assumption.
            }
          }
        }
      }
      {
        apply IHϕ.
      }
    }
    {
      unfold evar_open in *. simpl in Hwfc. rewrite bcmcloseex_mu in Hwfc.
      simpl in *.
      specialize (IHϕ p k l Hnk Hwfc Hci).
      exact IHϕ.
    }
  Qed.

Lemma make_zero_list_equiv {Σ : Signature} (dummy_x : evar) (l : list (prod db_index evar)) ϕ:
    closure_increasing l ->
    well_formed_closed_ex_aux (bcmcloseex l ϕ) 0 ->
    bcmcloseex (make_zero_list dummy_x l) ϕ = bcmcloseex l ϕ.
Proof.
    intros Hci Hwfc.
    funelim (make_zero_list dummy_x l).
    {
        rewrite -Heqcall. clear Heqcall.
        destruct_and!. clear Heq.
        rewrite bcmcloseex_append.
        rewrite H.
        {
            simpl. apply closure_increasing_lower_closing_list.
            rewrite -(firstn_skipn p.1 l) in Hci.
            apply closure_increasing_app_proj2 in Hci.
            exact Hci.
        }
        {
          rewrite -bcmcloseex_append.
          destruct p as [idx x]. simpl in *.
          clear -Hwfc H3.
          induction idx.
          {
            rewrite take_0. rewrite drop_0.
            rewrite [_ ++ _]/=.
            apply wfcexaux_bcmcloseex_lower_closing_list.
            exact Hwfc.
          }
          {
            feed specialize IHidx.
            {
              intros.
              eapply H3. apply H. lia.
            }
            
            clear Hwfc.
            move: idx ϕ H3 IHidx.
            induction l; intros idx ϕ H3 IHidx.
            {
              simpl in *. rewrite take_nil in IHidx. rewrite drop_nil in IHidx.
              simpl in IHidx.
              exact IHidx.
            }
            {
              simpl in *.
              destruct a as [dbi x].
              destruct dbi.
              2: {
                specialize (H3 0 (S dbi, x) erefl ltac:(lia)).
                simpl in H3.
                lia.
              }
              simpl in *.
              replace (bcmcloseex (take idx l ++ lower_closing_list dummy_x (drop idx l))
              (evar_open 0 x ϕ))
              with (bcmcloseex ((0,x)::(take idx l ++ lower_closing_list dummy_x (drop idx l))) ϕ)
              by reflexivity.
              
              rename IHidx into IHidx'.
              destruct idx.
              {
                rewrite take_0 in IHidx'. rewrite take_0.
                rewrite drop_0 in IHidx'. rewrite drop_0.
                rewrite [[] ++ _]/= in IHidx'. rewrite [[] ++ _]/=.
                simpl in *.
                replace (bcmcloseex (map (λ p : nat * evar, (Nat.pred p.1, p.2)) l)
                (evar_open 0 dummy_x (evar_open 0 x ϕ)))
                with (bcmcloseex ((0,x)::(0,dummy_x)::(map (λ p : nat * evar, (Nat.pred p.1, p.2)) l)) ϕ)
                by reflexivity.
                replace (bcmcloseex (map (λ p : nat * evar, (Nat.pred p.1, p.2)) l)
                (evar_open 0 x (evar_open 0 dummy_x ϕ)))
                with (bcmcloseex ((0,dummy_x)::(0,x)::(map (λ p : nat * evar, (Nat.pred p.1, p.2)) l)) ϕ)
                in IHidx'
                by reflexivity.
                rewrite <- wfcexaux_bcmcloseex_evar_open_change_evar_2
                with (f := (λ p, x)).
                rewrite <- wfcexaux_bcmcloseex_evar_open_change_evar_2
                with (f := (λ p, x)) in IHidx'.
                simpl. simpl in IHidx'.
                apply IHidx'.
              }
              {
                simpl in *.
                destruct l.
                {
                  simpl in *. rewrite take_nil in IHidx'. rewrite drop_nil in IHidx'.
                  simpl in IHidx'. apply IHidx'.
                }
                {
                  simpl in *.
                  apply IHl.
                  {
                    intros.
                    apply H3 with (j := (S j)).
                    {
                      simpl. assumption.
                    }
                    { lia. }
                  }
                  {
                    apply IHidx'.
                  }
                }
              }
            }
          }
        }
        {
          clear H.
          rewrite -bcmcloseex_append.
          destruct p as [idx x]. simpl in *.
          clear -H0 H2 H3 Hci.
          induction idx.
          {
            rewrite take_0. rewrite drop_0.
            rewrite [_ ++ _]/=.
            apply lower_closing_list_same.
            {
              eapply wfcex_and_increasing_first_not_k_impl_wfcex.
              { apply Hci. }
              {
                intros.
                rewrite H in H0. inversion H0. subst. lia.
              }
            }
            {
              admit.
            }
            {
              
            }
              apply wfc_ex_aux_implies_not_bevar_occur.
              apply wfcex_and_increasing_first_not_k_impl_wfcex.
            }
            Search bcmcloseex lower_closing_list.

            admit.
          }
          {
            destruct l.
            {
              simpl in *. rewrite take_nil in IHidx.
              rewrite drop_nil in IHidx.
              simpl in IHidx.
              exact IHidx.
            }
          }
          
        }
        clear H.
        destruct p as [idx [dbi x] ]. simpl in *|-.
        rewrite lower_closing_list_same.
        {
            simpl.
            destruct idx.
            {
                simpl.
            }

        }
    }


Qed.

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

Abort.

Lemma closed_M_pre_predicate_is_M_predicate {Σ : Signature} (k : db_index) (M : Model) (ϕ : Pattern) :
  well_formed_closed_ex_aux ϕ 0 ->
  M_pre_predicate k M ϕ ->
  M_predicate M ϕ.
Proof.
  intros Hwfcex Hpp.
  unfold M_pre_predicate in Hpp.
  specialize (Hpp []). simpl in Hpp.
  apply Hpp.
  { apply Forall_nil. exact I. }
  { apply ci_nil. }
  apply Hwfcex.
Qed.

Lemma M_pre_predicate_bott {Σ : Signature} (k : db_index) (M : Model) :
  M_pre_predicate k M patt_bott.
Proof.
  intros l Hk Hci H.
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
  intros l Hk Hci H.
  rewrite bcmcloseex_imp.
  rewrite bcmcloseex_imp in H.
  simpl in H.
  destruct_and!.
  apply M_predicate_impl.
  { apply Hp. assumption. assumption. assumption. }
  { apply Hq. assumption. assumption. assumption. }
Qed.

Lemma M_pre_predicate_exists {Σ : Signature} (k : db_index) M ϕ :
  M_pre_predicate (S k) M ϕ ->
  M_pre_predicate k M (patt_exists ϕ).
Proof.
  simpl. unfold M_pre_predicate. intros H.
  intros l Hk Hci Hwfc.
  rewrite bcmcloseex_ex.
  apply M_predicate_exists.
  remember (evar_fresh
  (elements (free_evars (bcmcloseex (map (λ p : nat * evar, (S p.1, p.2)) l) ϕ)))) as x.

  replace (evar_open 0 x (bcmcloseex (map (λ p : nat * evar, (S p.1, p.2)) l) ϕ))
  with (bcmcloseex ((map (λ p : nat * evar, (S p.1, p.2)) l)++[(pair 0 x)]) ϕ).
  2: {
      simpl. unfold bcmcloseex. rewrite fold_left_app. simpl. reflexivity.
  }
  apply H.
  {
    apply Forall_app. split.
    {
      clear -Hk. induction l.
      { apply Forall_nil. exact I. }
      { simpl. inversion Hk. subst. apply Forall_cons. simpl. split. lia. apply IHl. apply H2. }
    }
    {
        apply Forall_cons. simpl. split.
        { lia. }
        { apply Forall_nil. exact I. }
    }
  }
  {
      admit.
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
