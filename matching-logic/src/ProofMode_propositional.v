From Coq Require Import ssreflect ssrfun ssrbool.

From Ltac2 Require Import Ltac2 Control.

From Coq Require Import Ensembles Bool String.
From Coq.Logic Require Import FunctionalExtensionality Eqdep_dec.
From Equations Require Import Equations.

Require Import Coq.Program.Tactics.

From MatchingLogic Require Import
    Utils.extralibrary
    Logic
    DerivedOperators_Syntax
    ProofMode_base
    ProofInfo
    BasicProofSystemLemmas
.

From stdpp Require Import list tactics fin_sets coGset gmap sets.

From MatchingLogic.Utils Require Import stdpp_ext.

Import extralibrary.

Import
  MatchingLogic.Logic.Notations
  MatchingLogic.DerivedOperators_Syntax.Notations
.

Set Default Proof Mode "Classic".

Open Scope string_scope.
Open Scope list_scope.
Open Scope ml_scope.

Definition is_variable {Σ : Signature} (pme: ProofModeEntry) : Prop :=
  pme = pme_variable
.

#[global]
Instance is_variable_dec {Σ : Signature} (pme: ProofModeEntry)
: Decision (is_variable pme).
Proof. unfold is_variable. solve_decision. Defined.

Definition foralls_count
  {Σ : Signature} (pmes : list ProofModeEntry) : nat
  := length (filter is_variable pmes).

Fixpoint evar_fresh_nth {Σ : Signature} (avoid : EVarSet) (n : nat) : evar :=
  match n with
  | 0 => evar_fresh_s avoid
  | (S n') => evar_fresh_nth (avoid ∪ {[(evar_fresh_s avoid)]}) n'
  end.

Fixpoint evar_open_fresh_iter_base
  {Σ : Signature} (avoid : EVarSet) (base : nat) (n : nat) (p : Pattern) : Pattern
:= match n with
   | 0 => p
   | (S n') =>
     let x := (evar_fresh_s avoid) in
     let p' := (evar_open x (base + n') p) in
    (evar_open_fresh_iter_base (avoid ∪ {[x]}) base n' p')
   end
.

Definition evar_open_fresh_iter
  {Σ : Signature} (avoid : EVarSet) (n : nat) (p : Pattern) : Pattern
  := evar_open_fresh_iter_base avoid 0 n p.

Fixpoint evar_open_pmes {Σ : Signature}
  (idx : nat) (x : evar) (pmes : list ProofModeEntry)
  : list ProofModeEntry
  :=
  match pmes with
  | [] => pmes
  | (pme_pattern p)::pmes'
    => (pme_pattern (evar_open x idx p))::(evar_open_pmes idx x pmes')
  | (pme_variable)::pmes'
    => (pme_variable)::(evar_open_pmes (S idx) x pmes')
  end.

Lemma foralls_count_evar_open_pmes {Σ : Signature}
  (idx : nat) (x : evar) (pmes : list ProofModeEntry)
  :
  foralls_count (evar_open_pmes idx x pmes) = foralls_count pmes
.
Proof.
  move: idx.
  induction pmes; intros idx; simpl.
  {
    reflexivity.
  }
  {
    destruct a as [p|]; cbn; unfold decide; simpl.
    {
      unfold foralls_count in IHpmes.
      rewrite IHpmes.
      reflexivity.
    }
    {
      unfold foralls_count in IHpmes.
      rewrite IHpmes.
      reflexivity.
    }
  }
Qed.

Lemma length_evar_open_pmes {Σ : Signature}
  (idx : nat) (x : evar) (pmes : list ProofModeEntry)
  : length (evar_open_pmes idx x pmes) = length pmes
.
Proof.
  move: idx.
  induction pmes; simpl; intros idx.
  { reflexivity. }
  {
    destruct a; simpl.
    {
      rewrite IHpmes. reflexivity.
    }
    {
      rewrite IHpmes. reflexivity.
    }
  }
Qed.


Lemma evar_open_foldr_connect
  {Σ : Signature} (g : Pattern) (pmes : list ProofModeEntry)
  (x : evar) (idx : nat)
  :
  (foldr connect g pmes)^{evar:idx↦x}
  = foldr connect
          (g^{evar:(idx + foralls_count pmes)↦x})
          (evar_open_pmes idx x pmes)
.
Proof.
  move: idx.
  induction pmes; intros idx; cbn.
  {
    f_equal. lia.
  }
  {
    destruct a as [p|]; simpl.
    {
      unfold evar_open in *.
      rewrite IHpmes. clear IHpmes.
      reflexivity.
    }
    {
      unfold evar_open in *.
      rewrite IHpmes.
      unfold patt_forall,patt_not.
      simpl. rewrite Nat.add_succ_r.
      reflexivity.
    }
  }
Qed.

Lemma evar_open_pmes_comm_higher {Σ : Signature} m x pmes :
  evar_open_pmes m x (evar_open_pmes (S m) x pmes)
  = evar_open_pmes m x (evar_open_pmes m x pmes)
.
Proof.
  move: m.
  induction pmes; simpl; intros m.
  { reflexivity. }
  {
    destruct a as [p|]; cbn.
    {
      unfold evar_open.
      rewrite bevar_subst_comm_higher.
      { lia. }
      { reflexivity. }
      { reflexivity. }
      simpl.
      f_equal.
      apply IHpmes.
    }
    {
      rewrite IHpmes.
      reflexivity.
    }
  }
Qed.

Lemma wf_all_MLGoal_to_pattern' {Σ : Signature} (g : Pattern)
  (pmes : list ProofModeEntry) (x : evar) (m n : nat)
  :
  well_formed_xy m n (all , MLGoal_to_pattern' g pmes) ->
  well_formed_xy m n (MLGoal_to_pattern' g^[evar:m + (foralls_count pmes)↦patt_free_evar x]
    (evar_open_pmes m x pmes)
  )
.
Proof.
  remember (S(length pmes)) as pml.
  assert (Hpml : S(length pmes) <= pml) by lia.
  clear Heqpml.

  move: pmes Hpml m n g.
  induction pml; simpl; intros pmes Hpml m n g H.
  {
    lia.
  }
  destruct pmes.
  {
    cbn. rewrite Nat.add_0_r.
    wf_auto2.
  }
  {
    destruct p as [p|]; simpl in *.
    {
      specialize (IHpml pmes ltac:(lia) m n g).
      feed specialize IHpml.
      {
        wf_auto2.
      }
      wf_auto2.
    }
    {
      unfold MLGoal_to_pattern' in *.
      cut (well_formed_xy m n
      (evar_open x m (
       foldr connect g^[evar:m + (foralls_count (pme_variable :: pmes))↦patt_free_evar x] (evar_open_pmes (S m) x pmes))) = true).
      {
        clear IHpml.
        intros H'.
        wf_auto2.
      }

      rewrite evar_open_foldr_connect.
      unfold evar_open.
      cbn. unfold decide. cbn.
      rewrite evar_open_pmes_comm_higher.
      rewrite foralls_count_evar_open_pmes.
      rewrite -[foralls_count pmes](foralls_count_evar_open_pmes m x).

      apply IHpml.
      {
        rewrite length_evar_open_pmes. lia.
      }
      clear IHpml.

      assert (H' : well_formed_xy m n (evar_open x m (evar_open x (S m) (foldr connect g pmes))) = true).
      {
        wf_auto2.
      }
      clear H.
      rewrite evar_open_foldr_connect in H'.
      cbn in H'.
      rewrite evar_open_foldr_connect in H'.
      cbn in H'.
      rewrite foralls_count_evar_open_pmes in H'.

      cut (well_formed_xy m n (evar_open x m
      (
       foldr connect
         g^[evar:m + S (length (filter is_variable pmes))↦
         patt_free_evar x] (evar_open_pmes m x pmes))) = true
      ).
      {
        intros H''. wf_auto2.
      }
      fold (foralls_count pmes).
      rewrite -plus_Snm_nSm. simpl.
      unfold evar_open in *.

      rewrite evar_open_pmes_comm_higher in H'.
      remember (m + foralls_count pmes) as m'.
      remember (evar_open_pmes m x pmes) as pmes'.
      remember (g^[evar: S m' ↦ patt_free_evar x]) as g'.
      fold (evar_open x m (foldr connect g' pmes')).
      rewrite evar_open_foldr_connect.
      simpl.
      subst.
      unfold evar_open.
      rewrite foralls_count_evar_open_pmes.
      exact H'.
    }
  }
Qed.

Lemma bevar_occur_Sn_bevar_occur_bsvar_subst_n
  {Σ : Signature} (n : nat) (p q : Pattern)
  :
  bevar_occur p (S n) = true ->
  bevar_occur (bevar_subst q n p) n = true
.
Proof.
  move: n.
  induction p; simpl; intros m Hocc; try congruence.
  {
    repeat case_match; try reflexivity; try lia.
    destruct n; simpl; case_match; try reflexivity; try lia.
  }
  {
    apply orb_true_iff.
    apply orb_true_iff in Hocc.
    destruct Hocc as [Hocc|Hocc].
    {
      left. auto with nocore.
    }
    {
      right. auto with nocore.
    }
  }
  {
    apply orb_true_iff.
    apply orb_true_iff in Hocc.
    destruct Hocc as [Hocc|Hocc].
    {
      left. auto with nocore.
    }
    {
      right. auto with nocore.
    }
  }
  {
    auto with nocore.
  }
  {
    auto with nocore.
  }
Qed.

Lemma bevar_occur_foldr_connect
  {Σ : Signature} (g : Pattern) (pmes : list ProofModeEntry) (k : nat) :
  well_formed_closed_ex_aux (MLGoal_to_pattern' g pmes) k ->
  bevar_occur (foldr connect g pmes) k
  = bevar_occur g (k + (foralls_count pmes))
.
Proof.
  move: g k.
  induction pmes; cbn; intros g k Hwf.
  {
    rewrite plus_0_r. reflexivity.
  }
  {
    destruct a as [p|]; unfold decide; simpl.
    {
      assert (Hbopk : bevar_occur p k = false).
      {
        simpl in Hwf.
        apply wfc_ex_aux_implies_not_bevar_occur.
        wf_auto2.
      }
      rewrite Hbopk. simpl.
      rewrite IHpmes.
      {
        simpl in Hwf. unfold MLGoal_to_pattern'.
        wf_auto2.
      }
      reflexivity.
    }
    {
      rewrite 2!orb_false_r.
      rewrite IHpmes.
      {
        wf_auto2.
      }
      rewrite Nat.add_succ_r. simpl.
      reflexivity.
    }
  }
Qed.


Lemma bevar_occur_foldr_connect'
  {Σ : Signature} (g : Pattern) (pmes : list ProofModeEntry) (k : nat) :
  bevar_occur (MLGoal_to_pattern' patt_bott pmes) k = false ->
  bevar_occur (foldr connect g pmes) k
  = bevar_occur g (k + (foralls_count pmes))
.
Proof.
  move: g k.
  induction pmes; cbn; intros g k Hwf.
  {
    rewrite plus_0_r. reflexivity.
  }
  {
    destruct a as [p|]; unfold decide; simpl.
    {
      simpl in Hwf.
      apply orb_false_iff in Hwf.
      destruct Hwf as [Hwf1 Hwf2].
      rewrite Hwf1. simpl.
      rewrite IHpmes.
      { exact Hwf2. }
      reflexivity.
    }
    {
      rewrite 2!orb_false_r.
      simpl in Hwf.
      rewrite 2!orb_false_r in Hwf.
      rewrite IHpmes.
      { exact Hwf. }
      rewrite Nat.add_succ_r. simpl.
      reflexivity.
    }
  }
Qed.


Lemma bevar_occur_foldr_connect''
  {Σ : Signature} (g : Pattern) (pmes : list ProofModeEntry) (k : nat) :
  bevar_occur g (k + (foralls_count pmes)) = true ->
  bevar_occur (foldr connect g pmes) k = true
.
Proof.
  move: g k.
  induction pmes; cbn; intros g k H.
  {
    rewrite plus_0_r in H. exact H.
  }
  {
    destruct a as [p|]; unfold decide in *; simpl in *.
    {
      simpl.
      rewrite IHpmes.
      { exact H. }
      rewrite orb_true_r. reflexivity.
    }
    {
      rewrite 2!orb_false_r.
      rewrite IHpmes;[|reflexivity].
      rewrite Nat.add_succ_r in H. simpl in H.
      exact H.
    }
  }
Qed.

Lemma wfc_ex_aux_foldr_connect {Σ : Signature} g pmes k :
  well_formed_closed_ex_aux (foldr connect g pmes) k = true ->
  well_formed_closed_ex_aux g (k + (foralls_count pmes)) = true
.
Proof.
  move: k g.
  induction pmes; cbn; intros k g H.
  {
    rewrite plus_0_r. exact H.
  }
  {
    destruct a; unfold decide; simpl in *.
    {
      destruct_and!.
      rewrite IHpmes;[assumption|reflexivity].
    }
    {
      destruct_and!.
      rewrite -plus_Snm_nSm.
      rewrite IHpmes;[assumption|reflexivity].
    }
  }
Qed.

Lemma lift_to_mixed_context' {Σ : Signature} (Γ : Theory)
  (concl₁ concl₂: Pattern) (pmes : list ProofModeEntry)
  (i : ProofInfo)
  (* TODO relax ExGen *)
  (pile : ProofInfoLe (ExGen := ⊤, SVSubst := ∅, KT := false, FP := ∅) i)
  :
  well_formed (MLGoal_to_pattern' concl₁ pmes) ->
  well_formed (MLGoal_to_pattern' concl₂ pmes) ->
  forall (avoid : EVarSet),
  free_evars (MLGoal_to_pattern' concl₁ pmes) ⊆ avoid ->
  free_evars (MLGoal_to_pattern' concl₂ pmes) ⊆ avoid ->
  Γ ⊢i (evar_open_fresh_iter
         (avoid)
         (foralls_count pmes)
         (concl₂ ---> concl₁)
       ) using i ->
  Γ ⊢i ((fold_right connect concl₂ pmes) --->
        (fold_right connect concl₁ pmes)) using i
.
Proof.
  remember (length pmes) as pml.
  assert (Hpml : length pmes <= pml) by lia.
  clear Heqpml.

  move: concl₁ concl₂.
  move: pmes Hpml.
  unfold evar_open_fresh_iter.
  induction pml; simpl;
    intros pmes Hpml concl₁ concl₂ Hwf1 Hwf2 avoid Havoid1 Havoid2 Heo.
  {
    destruct pmes; simpl in *. exact Heo. lia.
  }
  {
    destruct pmes.
    { exact Heo. }
    
    destruct p as [p|]; simpl in *.
    {
      cbn in Heo. unfold decide in Heo.
      specialize (IHpml pmes ltac:(lia) concl₁ concl₂ ltac:(wf_auto2) ltac:(wf_auto2)).
      specialize (IHpml avoid ltac:(set_solver) ltac:(set_solver)).
      specialize (IHpml Heo).
      clear Heo.
      apply prf_weaken_conclusion_meta.
      { wf_auto2. }
      { wf_auto2. }
      { wf_auto2. }
      exact IHpml.
    }
    {
      cbn in Heo.
      remember (evar_fresh_s (avoid)) as x.


      apply forall_monotone with (x := x).
      { eapply pile_trans. 2: apply pile. try_solve_pile. }
      {
        subst x.
        eapply evar_is_fresh_in_richer'.
        2: apply set_evar_fresh_is_fresh'.
        { unfold MLGoal_to_pattern' in Havoid1,Havoid2.
          clear -Havoid1 Havoid2.
          set_solver.
        }
      }
      {
        subst x.
        eapply evar_is_fresh_in_richer'.
        2: apply set_evar_fresh_is_fresh'.
        { unfold MLGoal_to_pattern' in Havoid1,Havoid2.
          clear -Havoid1 Havoid2.
          set_solver.
        }
      }
      rewrite 2!evar_open_foldr_connect.
      simpl.

      apply IHpml with (avoid := (avoid ∪ {[x]})).
      {
        rewrite length_evar_open_pmes.
        lia.
      }
      {
        simpl.
        apply wf_wfxy00_compose.
        apply wf_wfxy00_decompose in Hwf1.
        apply wf_all_MLGoal_to_pattern' with (x := x) in Hwf1.
        apply Hwf1.
      }
      {
        simpl.
        apply wf_wfxy00_compose.
        apply wf_wfxy00_decompose in Hwf2.
        apply wf_all_MLGoal_to_pattern' with (x := x) in Hwf2.
        apply Hwf2.
      }
      {
        unfold MLGoal_to_pattern'.
        replace (foralls_count pmes)
          with (0 + (foralls_count pmes))
          by reflexivity
        .
        rewrite -evar_open_foldr_connect.
        pose proof (Hfeeo := free_evars_evar_open (foldr connect concl₁ pmes) x 0).
        unfold MLGoal_to_pattern' in Havoid1.
        eapply transitivity.
        { apply Hfeeo. }
        clear -Havoid1.
        set_solver.
      }
      {
        unfold MLGoal_to_pattern'.
        replace (foralls_count pmes)
          with (0 + (foralls_count pmes))
          by reflexivity
        .
        rewrite -evar_open_foldr_connect.
        pose proof (Hfeeo := free_evars_evar_open (foldr connect concl₂ pmes) x 0).
        unfold MLGoal_to_pattern' in Havoid2.
        eapply transitivity.
        { apply Hfeeo. }
        clear -Havoid2.
        set_solver.
      }
      {
        clear IHpml.
        simpl.
        rewrite foralls_count_evar_open_pmes.
        fold (foralls_count pmes) in Heo.
        unfold decide in Heo.
        apply Heo.
      }
    }
  }
Defined.


Lemma lift_to_mixed_context {Σ : Signature} (Γ : Theory)
  (concl₁ concl₂: Pattern) (pmes : list ProofModeEntry)
  (i : ProofInfo)
  (* TODO relax ExGen *)
  (pile : ProofInfoLe (ExGen := ⊤, SVSubst := ∅, KT := false, FP := ∅) i)
  :
  well_formed (MLGoal_to_pattern' concl₁ pmes) ->
  well_formed (MLGoal_to_pattern' concl₂ pmes) ->
  Γ ⊢i (evar_open_fresh_iter
         (free_evars (MLGoal_to_pattern' concl₁ pmes) ∪ free_evars (MLGoal_to_pattern' concl₂ pmes))
         (foralls_count pmes)
         (concl₂ ---> concl₁)
       ) using i ->
  Γ ⊢i ((fold_right connect concl₂ pmes) --->
        (fold_right connect concl₁ pmes)) using i
.
Proof.
  intros wf1 wf2 H.
  eapply lift_to_mixed_context'.
  6: apply H.
  1,2,3: assumption.
  1,2: clear; set_solver.
Defined.

Lemma wf_lift_helper' {Σ : Signature} hyps concl₁ concl₂ x y:
  well_formed_xy (x + foralls_count (pmes_of hyps)) y concl₂ ->
  well_formed_xy (x) y (foldr connect concl₁ (map nh_pme hyps)) ->
  well_formed_xy (x) y (foldr connect concl₂ (map nh_pme hyps))
.
Proof.
  move: x y.
  induction hyps; cbn; intros x y wf1 wf2.
  {
    rewrite Nat.add_0_r in wf1.
    wf_auto2.
  }
  {
    destruct a as [name h].
    destruct h as [p|]; unfold decide in *; simpl in *.
    {
      specialize (IHhyps x y).
      feed specialize IHhyps.
      { wf_auto2. }
      { wf_auto2. }
      wf_auto2.
    }
    {
      specialize (IHhyps (S x) y).
      rewrite Nat.add_succ_r in wf1.
      feed specialize IHhyps.
      { simpl. wf_auto2. }
      { wf_auto2. }
      wf_auto2.
    }
  }
Qed.

Lemma wf_lift_helper {Σ : Signature} hyps concl₁ concl₂ :
  well_formed_xy (foralls_count (pmes_of hyps)) 0 concl₂ ->
  well_formed (foldr connect concl₁ (map nh_pme hyps)) ->
  well_formed (foldr connect concl₂ (map nh_pme hyps))
.
Proof.
  intros wf1 wf2.
  rewrite wf_wfxy00.
  rewrite wf_wfxy00 in wf2.
  apply wf_lift_helper' with (concl₁ := concl₁); simpl; try assumption.
Qed.

Lemma MLGoal_lift_to_mixed_context {Σ : Signature} (Γ : Theory)
  (concl₁ concl₂: Pattern) (hyps : hypotheses)
  (i : ProofInfo)
  (* TODO relax ExGen *)
  (pile : ProofInfoLe (ExGen := ⊤, SVSubst := ∅, KT := false, FP := ∅) i)
  :
  well_formed_xy (foralls_count (pmes_of hyps)) 0 concl₂ ->
  Γ ⊢i (evar_open_fresh_iter
         (free_evars (MLGoal_to_pattern' concl₁ (pmes_of hyps)) ∪ free_evars (MLGoal_to_pattern' concl₂ (pmes_of hyps)))
         (foralls_count (pmes_of hyps))
         (concl₂ ---> concl₁)
       ) using i ->
  (mkMLGoal Σ Γ hyps concl₂ i) ->
  (mkMLGoal Σ Γ hyps concl₁ i)
.
Proof.
  intros wfxy Himpl H.
  mlExtractWF wf'.
  (*intros wf1 wf2 Himpl H.*)
  feed specialize H.
  {
    cbn.
    apply wf_lift_helper with (concl₁ := concl₁).
    wf_auto2.
    wf_auto2.
  }
  unfold of_MLGoal. intros _. cbn.
  cbn in *.
  pose proof (Htmp := lift_to_mixed_context Γ concl₁ concl₂).
  specialize (Htmp (map nh_pme hyps) _ pile).
  eapply MP.
  2: apply Htmp.
  1,4: assumption.
  1,2: wf_auto2.
Defined.


Ltac _mlCut g' :=
  lazymatch goal with
  | [ |- @of_MLGoal ?S (mkMLGoal ?S ?T ?l ?g ?i)] =>
    cut (@of_MLGoal S (mkMLGoal S T l g' i));
    [(
      let H := fresh "H" in
      intros H;
      apply MLGoal_lift_to_mixed_context with (concl₂ := g');
      [
        (try_solve_pile)|
        (cbn; unfold decide; cbn)|
        (cbn; unfold decide; cbn)|
        (exact H)
      ]
       (*;
      unshelve (eapply (MLGoal_lift_to_mixed_context _ _ _ _ _ _ _ H)) *)
    )|]
  end
.

Tactic Notation "mlCut" constr(g') :=
  _mlCut g'
.

#[local]
Example ex_mlCut {Σ : Signature}
  (Γ : Theory) (a b c : Pattern) (s1 s2 : symbols)
  :
  well_formed a ->
  well_formed b ->
  well_formed c ->
  Γ ⊢ (patt_sym s1 ---> patt_sym s2) ->
  Γ ⊢ all, (a $ b0 ---> all, (b0 $ b $ b1 ---> all, (patt_sym s1))) ->
  Γ ⊢ all, (a $ b0 ---> all, (b0 $ b $ b1 ---> all, (patt_sym s2)))
.
Proof.
  intros wfa wfb wfc Himpl H.
  toMLGoal.
  { wf_auto2. }
  mlIntroForall "x".
  mlIntro "H1".
  mlIntroForall "y".
  mlIntro "H2".
  mlIntroForall "z".
  mlCut (patt_sym s1).
  { wf_auto2. }
  { apply Himpl. }
  (* now the conclusion is [patt_sym s1] *)
  fromMLGoal.
  apply H.
Qed.


#[local]
Example ex_mlCut2 {Σ : Signature}
  (Γ : Theory) (a b c : Pattern) (s1 s2 : symbols)
  :
  well_formed a ->
  well_formed b ->
  well_formed c ->
  Γ ⊢ (patt_sym s1 ---> patt_sym s2) ->
  Γ ⊢ all, (a $ b0 ---> all, (b0 $ b $ b1 ---> all, (patt_sym s1 $ b1))) ->
  Γ ⊢ all, (a $ b0 ---> all, (b0 $ b $ b1 ---> all, (patt_sym s2 $ b1)))
.
Proof.
  intros wfa wfb wfc Himpl H.
  toMLGoal.
  { wf_auto2. }
  mlIntroForall "x".
  mlIntro "H1".
  mlIntroForall "y".
  mlIntro "H2".
  mlIntroForall "z".
  mlCut (patt_sym s1 $ b1).
  { wf_auto2. }
  { 
    (* TODO have Framing available there. *)
    admit.
  }
Abort.

Lemma evar_open_fresh_iter_impl {Σ : Signature} avoid m a b base :
  evar_open_fresh_iter_base avoid base m  (a ---> b)
  = (evar_open_fresh_iter_base avoid base m a ---> evar_open_fresh_iter_base avoid base m b)
.
Proof.
  move: a b avoid.
  induction m; intros a b avoid; simpl.
  { 
    reflexivity.
  }
  {
    rewrite IHm.
    reflexivity.
  }
Qed.

Lemma evar_open_fresh_iter_wfc_aux:
  ∀ {Σ : Signature} (db2 : nat) (phi : Pattern) avoid,
	well_formed_closed_ex_aux phi 0 →
  evar_open_fresh_iter avoid db2 phi = phi
.
Proof.
  intros.
  move: avoid phi H.
  induction db2; intros avoid phi Hwf.
  {
    simpl. reflexivity.
  }
  {
    simpl.
    unfold evar_open_fresh_iter.
    simpl.
    rewrite (evar_open_wfc_aux db2).
    { lia. }
    { eapply well_formed_closed_ex_aux_ind;[|apply Hwf]. lia. }
    apply IHdb2.
    apply Hwf.
  }
Qed.

Lemma well_formed_evar_open_fresh_iter {Σ : Signature} avoid m p:
  well_formed_xy m 0 p ->
  well_formed (evar_open_fresh_iter avoid m p)
.
Proof.
  move: p avoid.
  induction m; simpl; intros p avoid H.
  {
    wf_auto2.
  }
  {
    apply IHm.
    wf_auto2.
  }
Qed.

Lemma evar_open_fresh_iter_base_forall {Σ : Signature} avoid base m p l:
  evar_open_fresh_iter_base avoid base m (all , foldr connect p l)
  = all, (evar_open_fresh_iter_base avoid (S base) m (foldr connect p l))
.
Proof.
  move: l p avoid base.
  induction m; simpl; intros l p avoid base.
  {
    reflexivity.
  }
  {
    mlSimpl.
    rewrite evar_open_foldr_connect. simpl.
    rewrite IHm. simpl. reflexivity.
  }
Qed.

Lemma forall_quantify_evar_open {Σ : Signature} x' p :
  x' ∉ free_evars p ->
  well_formed_closed_ex_aux p 1 ->
  (forall_quantify x' (evar_open x' 0 p))
  = (all , p)
.
Proof.
  intros H1 H2.
  unfold forall_quantify, patt_forall.
  by rewrite evar_quantify_evar_open.
Qed.

Lemma evar_fresh_nth_avoid {Σ : Signature} avoid m :
 evar_fresh_nth (avoid) m ∉ avoid
.
Proof.
  move: avoid.
  induction m; simpl; intros avoid.
  {
    apply set_evar_fresh_is_fresh'.
  }
  {
    specialize (IHm (avoid ∪ {[evar_fresh_s avoid]})).
    set_solver.
  }
Qed.

Lemma evar_fresh_nth_notin_free_evars_evar_open_fresh_iter_base
  {Σ : Signature} (avoid : EVarSet) (base : nat) (p : Pattern)
  :
  (forall m, (evar_fresh_nth avoid m) ∉ (free_evars p)) ->
  forall m, (evar_fresh_nth avoid m)
  ∉ free_evars (evar_open_fresh_iter_base avoid base m p)
.
Proof.
  intros H m.
  move: p base avoid H.
  induction m; simpl; intros p base avoid H.
  { exact (H 0). }
  {
    apply IHm.
    intros m0.
    apply evar_open_fresh_notin.
    3: {
      pose proof (H0 := evar_fresh_nth_avoid (avoid ∪ {[evar_fresh_s avoid]}) m0).
      clear -H0.
      set_solver.
    }
    1: {
      exact (H (S m0)).
    }
    {
      exact (H 0).
    }
  }
Qed.

Lemma wfce_eofib {Σ : Signature} avoid base m phi :
  well_formed_closed_ex_aux
    (evar_open_fresh_iter_base avoid base m phi) base
  = well_formed_closed_ex_aux phi (base+m)
.
Proof.
  move: avoid base phi.
  induction m; simpl; intros avoid base phi.
  {
    rewrite Nat.add_0_r. reflexivity.
  }
  {
    rewrite IHm.
    rewrite Nat.add_succ_r.
    remember (well_formed_closed_ex_aux phi^{evar:base + m↦evar_fresh_s avoid} (base + m))
      as b
    .
    destruct b.
    {
      symmetry in Heqb. symmetry.
      apply wfc_ex_aux_body_ex_imp2 in Heqb.
      exact Heqb.
    }
    {
      symmetry in Heqb.
      symmetry.
      rewrite -not_true_iff_false.
      rewrite -not_true_iff_false in Heqb.
      intros HContra. apply Heqb.
      apply wfc_ex_aux_body_ex_imp1.
      apply HContra.
    }
  }
Qed.

Lemma nested_const_fa' {Σ : Signature} Γ a l avoid (m : nat) (x : evar) :
  free_evars (a ---> (fold_right connect a l)) ⊆ avoid ->
  well_formed a = true ->
  well_formed_xy m 0 ((fold_right connect patt_bott l)) = true ->
  Γ ⊢i evar_open_fresh_iter avoid m (a ---> (fold_right connect a l))
  using AnyReasoning.
Proof.
  (*intros wfa wfl.*)
  move: m avoid a.
  induction l; simpl; intros m avoid a' Havoid wfa wfl.
  - unfold evar_open_fresh_iter.
    rewrite evar_open_fresh_iter_impl. useBasicReasoning. apply A_impl_A.
    assert (Hweak : well_formed_xy m 0 a' = true).
    { wf_auto2. eapply well_formed_closed_ex_aux_ind;[|apply H2]. lia. }
    clear wfa Havoid.
    move: a' Hweak wfl avoid.
    induction m; simpl; intros a Hweak wfl avoid.
    { wf_auto2. }
    { apply IHm.
      { wf_auto2. }
      { wf_auto2. }
    }
  - 
    simpl in *.
    unfold evar_open_fresh_iter.
    unfold evar_open_fresh_iter in IHl.
    destruct a as [p|].
    {
      simpl in Havoid.
      specialize (IHl m avoid a' ltac:(set_solver)).
      specialize (IHl ltac:(wf_auto2) ltac:(wf_auto2)).
      simpl in *.
      rewrite 2!evar_open_fresh_iter_impl.
      rewrite evar_open_fresh_iter_impl in IHl.

      assert (H2 : Γ ⊢i ((evar_open_fresh_iter avoid m (foldr connect a' l)) ---> ((evar_open_fresh_iter avoid m p) ---> (evar_open_fresh_iter avoid m (foldr connect a' l)))) using BasicReasoning).
      {
        simpl in wfl.
        apply P1.
        wf_auto2.
        apply well_formed_evar_open_fresh_iter.
        wf_auto2.
      }
      eapply syllogism_meta.
      5: useBasicReasoning; apply H2.
      4: apply IHl. all: wf_auto2.
    }
    {
      simpl.
      rewrite evar_open_fresh_iter_impl.
      simpl in wfl.
      simpl in Havoid.
      specialize (IHl (S m) avoid a' ltac:(set_solver) ltac:(wf_auto2)).
      specialize (IHl ltac:(wf_auto2)).
      rewrite evar_open_fresh_iter_impl in IHl.
      unfold evar_open_fresh_iter in *.
      rewrite evar_open_fresh_iter_base_forall.
      simpl in IHl.
      rewrite evar_open_foldr_connect in IHl.
      remember (avoid ∪ {[evar_fresh_s avoid]}) as avoid'.

      assert (Ha' : forall idx avoid'', a'^{evar:idx↦evar_fresh_s avoid''} = a').
      {
        intros idx avoid''.
        eapply evar_open_wfc_aux with (db1 := 0).
        { lia. }
        { wf_auto2. }
      }
      rewrite 2!Ha' in IHl.

      remember (evar_fresh_nth avoid m) as x'.
      replace
        (all , evar_open_fresh_iter_base avoid 1 m (foldr connect a' l))
      with
        (forall_quantify x' (evar_open x' 0 (evar_open_fresh_iter_base avoid 1 m (foldr connect a' l))))
      .
      2: {
        apply forall_quantify_evar_open.
        {
          subst x'.
          apply evar_fresh_nth_notin_free_evars_evar_open_fresh_iter_base.
          intros m0.
          pose proof (H0 := evar_fresh_nth_avoid avoid m0).
          clear -H0 Havoid.
          set_solver.
        }
        {
          Search (well_formed_closed_ex_aux (evar_open_fresh_iter_base _ _ _ _) _).
        }
      }
      apply forall_gen.
      rewrite evar_open_fresh_iter_impl.
      (* HERE *)
      

      apply IHl.
      
      
      rewrite evar_open_fresh_iter_impl in IHl.
      simpl in IHl.
      rewrite evar_open_fresh_iter_wfc_aux in IHl.
      { 
        
        wf_auto2.
      Search well_formed_closed_ex_aux bevar_subst.
      }
      fold bevar_subst in IHl.
    }
Defined.

Lemma MLGoal_exactn {Σ : Signature}
  (Γ : Theory)
  (l₁ l₂ : hypotheses)
  (name : string)
  (g : Pattern)
  (info : ProofInfo) :
  mkMLGoal Σ Γ (l₁ ++ (mkNH _ name g) :: l₂) g info.
Proof.
  mlExtractWF wfl₁gl₂ wfg.
  fromMLGoal.
  useBasicReasoning.
  unfold patterns_of in *.
  rewrite map_app.
  apply nested_const_middle.
  { exact wfg. }
  { abstract (
      pose proof (wfl₁ := wf_take (length (patterns_of l₁)) _ wfl₁gl₂);
      rewrite map_app in wfl₁;
      rewrite take_app in wfl₁;
      exact wfl₁
    ).
  }
  {
    abstract (
      pose proof (wfgl₂ := wf_drop (length (patterns_of l₁)) _ wfl₁gl₂);
      rewrite map_app in wfgl₂;
      rewrite drop_app in wfgl₂;
      unfold Pattern.wf in wfgl₂;
      simpl in wfgl₂;
      apply andb_prop in wfgl₂;
      destruct wfgl₂ as [_ wfl₂];
      exact wfl₂
    ).
  }
Defined.


Tactic Notation "mlExactn" constr(n) :=
  _mlReshapeHypsByIdx n;
  apply MLGoal_exactn.



Lemma MLGoal_exact {Σ : Signature} Γ l name g idx info:
  find_hyp name l = Some (idx, (mkNH _ name g)) ->
  mkMLGoal Σ Γ l g info.
Proof.
  intros Hfound.
  setoid_rewrite -> list.list_find_Some in Hfound.
  destruct Hfound as [Hfound1 [Hfound2 Hfound3] ].
  rewrite -[l](take_drop_middle l idx (mkNH _ name g)).
  { exact Hfound1. }
  apply MLGoal_exactn.
Defined.

Tactic Notation "mlExact" constr(name')
:= eapply MLGoal_exact with (name := name'); simpl; apply f_equal; reflexivity.

Local Example ex_mlExact {Σ : Signature} Γ a b c:
  well_formed a = true ->
  well_formed b = true ->
  well_formed c = true ->
  Γ ⊢i a ---> b ---> c ---> b using BasicReasoning.
Proof.
  intros wfa wfb wfc.
  toMLGoal.
  { wf_auto2. }
  mlIntro "H1". mlIntro "H2". mlIntro "H3". (* TODO: mlIntros "H1" "H2" "H3".*)
  mlExact "H2".
Defined.



Lemma MLGoal_weakenConclusion' {Σ : Signature} Γ l g g' (i : ProofInfo):
  Γ ⊢i g ---> g' using i ->
  mkMLGoal Σ Γ l g i ->
  mkMLGoal Σ Γ l g' i.
Proof.
  intros Hgg' Hlg.
  (*mlExtractWF wfl wfgp.*)
  unfold of_MLGoal in *. simpl in *.
  intros wfg' wfl.
  pose proof (wfimp := proved_impl_wf _ _ (proj1_sig Hgg')).
  apply well_formed_imp_proj1 in wfimp.
  eapply prf_weaken_conclusion_iter_meta_meta.
  5: apply Hlg.
  4: apply Hgg'.
  all: assumption.
Defined.

Lemma prf_contraction {Σ : Signature} Γ a b:
  well_formed a ->
  well_formed b ->
  Γ ⊢i ((a ---> a ---> b) ---> (a ---> b)) using BasicReasoning.
Proof.
  intros wfa wfb.
  assert (H1 : Γ ⊢i (a ---> ((a ---> b) ---> b)) using BasicReasoning).
  {
    apply modus_ponens; assumption.
  }
  assert (H2 : Γ ⊢i ((a ---> ((a ---> b) ---> b)) ---> ((a ---> (a ---> b)) ---> (a ---> b))) using BasicReasoning).
  {
    apply P2; wf_auto2.
  }
  eapply MP. 2: apply H2. apply H1.
Defined.

Lemma prf_weaken_conclusion_under_implication {Σ : Signature} Γ a b c:
  well_formed a ->
  well_formed b ->
  well_formed c ->
  Γ ⊢i ((a ---> b) ---> ((a ---> (b ---> c)) ---> (a ---> c))) using BasicReasoning.
Proof.
  intros wfa wfb wfc.
  assert (H1 : Γ ⊢i ((a ---> (b ---> c)) ---> (b ---> (a ---> c))) using BasicReasoning).
  {
    apply reorder; wf_auto2.
  }
  assert (H2 : Γ ⊢i (((b ---> (a ---> c)) ---> (a ---> c)) ---> ((a ---> (b ---> c)) ---> (a ---> c))) using BasicReasoning).
  {
    apply prf_strenghten_premise_meta;[wf_auto2|wf_auto2|wf_auto2|].
    apply H1.
  }
  eapply prf_weaken_conclusion_meta_meta.
  4: apply H2. 1-3: wf_auto2. clear H1 H2.

  assert (H3 : Γ ⊢i ((a ---> b) ---> ((b ---> (a ---> c)) ---> (a ---> (a ---> c)))) using BasicReasoning).
  {
    apply syllogism; wf_auto2.
  }
  assert (H4 : Γ ⊢i ((a ---> (a ---> c)) ---> (a ---> c)) using BasicReasoning).
  {
    apply prf_contraction; wf_auto2.
  }
  assert (Hiter: ((a ---> b) ---> (b ---> a ---> c) ---> a ---> c)
                 = foldr patt_imp (a ---> c) [(a ---> b); (b ---> a ---> c)]) by reflexivity.

  eapply (cast_proof' _ _ _ _ Hiter).

  eapply prf_weaken_conclusion_iter_meta_meta.
  5: apply H3. 4: apply H4. all: wf_auto2.
Defined.

Lemma prf_weaken_conclusion_under_implication_meta {Σ : Signature} Γ a b c (i : ProofInfo):
  well_formed a ->
  well_formed b ->
  well_formed c ->
  Γ ⊢i (a ---> b) using i ->
  Γ ⊢i ((a ---> (b ---> c)) ---> (a ---> c)) using i.
Proof.
  intros wfa wfb wfc H.
  eapply MP.
  2: { useBasicReasoning. apply prf_weaken_conclusion_under_implication; wf_auto2. }
  exact H.
Defined.

Lemma prf_weaken_conclusion_under_implication_meta_meta {Σ : Signature} Γ a b c i:
  well_formed a ->
  well_formed b ->
  well_formed c ->
  Γ ⊢i a ---> b using i ->
  Γ ⊢i a ---> b ---> c using i ->
  Γ ⊢i a ---> c using i.
Proof.
  intros wfa wfb wfc H1 H2.
  eapply MP.
  { apply H2. }
  { apply prf_weaken_conclusion_under_implication_meta.
    4: { apply H1. }
    all: wf_auto2.
  }
Defined.

Lemma prf_weaken_conclusion_iter_under_implication {Σ : Signature} Γ l g g':
  Pattern.wf l ->
  well_formed g ->
  well_formed g' ->
  Γ ⊢i (((g ---> g') ---> (foldr patt_imp g l)) ---> ((g ---> g') ---> (foldr patt_imp g' l)))
  using BasicReasoning.
Proof.
  intros wfl wfg wfg'.
  pose proof (H1 := prf_weaken_conclusion_iter Γ l g g' wfl wfg wfg').
  remember ((g ---> g')) as a.
  remember (foldr patt_imp g l) as b.
  remember (foldr patt_imp g' l) as c.
  assert (well_formed a) by (subst; wf_auto2).
  assert (well_formed b) by (subst; wf_auto2).
  assert (well_formed c) by (subst; wf_auto2).
  pose proof (H2' := prf_weaken_conclusion_under_implication Γ a b c ltac:(assumption) ltac:(assumption) ltac:(assumption)).
  apply reorder_meta in H2'. 2,3,4: subst;wf_auto2.
  eapply MP. 2: apply H2'. apply H1.
Defined.

Lemma prf_weaken_conclusion_iter_under_implication_meta {Σ : Signature} Γ l g g' (i : ProofInfo):
  Pattern.wf l ->
  well_formed g ->
  well_formed g' ->
  Γ ⊢i ((g ---> g') ---> (foldr patt_imp g l)) using i->
  Γ ⊢i ((g ---> g') ---> (foldr patt_imp g' l)) using i.
Proof.
  intros wfl wfg wfg' H.
  eapply MP.
  2: { useBasicReasoning. apply prf_weaken_conclusion_iter_under_implication; wf_auto2. }
  { exact H. }
Defined.

Lemma MLGoal_weakenConclusion_under_first_implication {Σ : Signature} Γ l name g g' i:
  mkMLGoal Σ Γ (mkNH _ name (g ---> g') :: l) g i ->
  mkMLGoal Σ Γ (mkNH _ name (g ---> g') :: l) g' i .
Proof.
  intros H. unfold of_MLGoal in *. simpl in *.
  intros wfg' wfgg'l.
  pose proof (Htmp := wfgg'l).
  unfold Pattern.wf in Htmp. simpl in Htmp. apply andb_prop in Htmp. destruct Htmp as [wfgg' wfl].
  apply well_formed_imp_proj1 in wfgg'. specialize (H wfgg' wfgg'l).
  apply prf_weaken_conclusion_iter_under_implication_meta; assumption.
Defined.

Lemma prf_weaken_conclusion_iter_under_implication_iter {Σ : Signature} Γ l₁ l₂ g g':
  Pattern.wf l₁ ->
  Pattern.wf l₂ ->
  well_formed g ->
  well_formed g' ->
  Γ ⊢i ((foldr patt_imp g (l₁ ++ (g ---> g') :: l₂)) --->
       (foldr patt_imp g' (l₁ ++ (g ---> g') :: l₂)))
  using BasicReasoning.
Proof.
  intros wfl₁ wfl₂ wfg wfg'.
  induction l₁; simpl.
  - apply prf_weaken_conclusion_iter_under_implication; auto.
  - pose proof (wfal₁ := wfl₁). unfold Pattern.wf in wfl₁. simpl in wfl₁. apply andb_prop in wfl₁.
    destruct wfl₁ as [wfa wfl₁]. specialize (IHl₁ wfl₁).
    eapply prf_weaken_conclusion_meta. 4: assumption. all: wf_auto2.
Defined.

Lemma prf_weaken_conclusion_iter_under_implication_iter_meta {Σ : Signature} Γ l₁ l₂ g g' i:
  Pattern.wf l₁ ->
  Pattern.wf l₂ ->
  well_formed g ->
  well_formed g' ->
  Γ ⊢i (foldr patt_imp g (l₁ ++ (g ---> g') :: l₂)) using i ->
  Γ ⊢i (foldr patt_imp g' (l₁ ++ (g ---> g') :: l₂)) using i.
Proof.
  intros wfl₁ wfl₂ wfg wfg' H.
  eapply MP.
  { apply H. }
  { useBasicReasoning. apply prf_weaken_conclusion_iter_under_implication_iter; wf_auto2. }
Defined.

Lemma MLGoal_weakenConclusion {Σ : Signature} Γ l₁ l₂ name g g' i:
  mkMLGoal Σ Γ (l₁ ++ (mkNH _ name (g ---> g')) :: l₂) g i ->
  mkMLGoal Σ Γ (l₁ ++ (mkNH _ name (g ---> g')) :: l₂) g' i.
Proof.
  unfold of_MLGoal in *. simpl in *.
  intros H wfg' wfl₁gg'l₂.

  unfold patterns_of in wfl₁gg'l₂.
  rewrite map_app in wfl₁gg'l₂.

  unfold patterns_of.
  rewrite map_app.

  apply prf_weaken_conclusion_iter_under_implication_iter_meta.
  { abstract (pose proof (wfl₁ := wf_take (length (patterns_of l₁)) _ wfl₁gg'l₂); simpl in wfl₁; rewrite take_app in wfl₁; exact wfl₁). }
  { abstract (
      pose proof (wfgg'l₂ := wf_drop (length (patterns_of l₁)) _ wfl₁gg'l₂);
      rewrite drop_app in wfgg'l₂;
      pose proof (Htmp := wfgg'l₂);
      unfold Pattern.wf in Htmp;
      simpl in Htmp;
      apply andb_prop in Htmp;
      destruct Htmp as [wfgg' wfl₂];
      exact wfl₂
    ).
  }
  {
    abstract(
      pose proof (wfgg'l₂ := wf_drop (length (patterns_of l₁)) _ wfl₁gg'l₂);
      rewrite drop_app in wfgg'l₂;
      pose proof (Htmp := wfgg'l₂);
      unfold Pattern.wf in Htmp;
      simpl in Htmp;
      apply andb_prop in Htmp;
      destruct Htmp as [wfgg' wfl₂];
      pose proof (wfg := well_formed_imp_proj1 _ _ wfgg');
      exact wfg
    ).
  }
  { exact wfg'. }

  unfold patterns_of in H.
  rewrite map_app in H.
  apply H.
  {
    abstract(
      pose proof (wfgg'l₂ := wf_drop (length (patterns_of l₁)) _ wfl₁gg'l₂);
      rewrite drop_app in wfgg'l₂;
      pose proof (Htmp := wfgg'l₂);
      unfold Pattern.wf in Htmp;
      simpl in Htmp;
      apply andb_prop in Htmp;
      destruct Htmp as [wfgg' wfl₂];
      pose proof (wfg := well_formed_imp_proj1 _ _ wfgg');
      exact wfg
    ).
  }
  exact wfl₁gg'l₂.
Defined.


Tactic Notation "mlApplyn" constr(n) :=
  _mlReshapeHypsByIdx n;
  apply MLGoal_weakenConclusion;
  _mlReshapeHypsBack.


Tactic Notation "mlApply" constr(name') :=
  _mlReshapeHypsByName name';
  apply MLGoal_weakenConclusion;
  _mlReshapeHypsBack.

Local Example ex_mlApplyn {Σ : Signature} Γ a b:
  well_formed a ->
  well_formed b ->
  Γ ⊢i a ---> (a ---> b) ---> b using BasicReasoning.
Proof.
  intros wfa wfb.
  toMLGoal.
  { wf_auto2. }
  mlIntro "H1".
  mlIntro "H2".
  mlApply "H2".
  fromMLGoal.
  apply P1; wf_auto2.
Defined.


Lemma Constructive_dilemma {Σ : Signature} Γ p q r s:
  well_formed p ->
  well_formed q ->
  well_formed r ->
  well_formed s ->
  Γ ⊢i ((p ---> q) ---> (r ---> s) ---> (p or r) ---> (q or s)) using BasicReasoning.
Proof.
  intros wfp wfq wfr wfs.
  unfold patt_or.

  toMLGoal.
  { wf_auto2. }

  mlIntro "H0". mlIntro "H1". mlIntro "H2". mlIntro "H3".
  mlApply "H1".
  mlApply "H2".
  mlIntro "H4".
  mlApply "H3".
  mlApply "H0".
  mlExact "H4".
Defined.

Lemma prf_impl_distr_meta {Σ : Signature} Γ a b c i:
  well_formed a ->
  well_formed b ->
  well_formed c ->
  Γ ⊢i (a ---> (b ---> c)) using i ->
  Γ ⊢i ((a ---> b) ---> (a ---> c)) using i.
Proof.
  intros wfa wfb wfc H.
  eapply MP.
  { apply H. }
  { useBasicReasoning. apply P2; wf_auto2. }
Defined.

Lemma prf_add_lemma_under_implication {Σ : Signature} Γ l g h:
  Pattern.wf l ->
  well_formed g ->
  well_formed h ->
  Γ ⊢i ((foldr patt_imp h l) --->
       ((foldr patt_imp g (l ++ [h])) --->
        (foldr patt_imp g l)))
  using BasicReasoning.
Proof.
  intros wfl wfg wfh.
  induction l; simpl.
  - apply modus_ponens; auto.
  - pose proof (wfal := wfl).
    unfold Pattern.wf in wfl. apply andb_prop in wfl. destruct wfl as [wfa wfl].
    specialize (IHl wfl).
    assert (H1: Γ ⊢i a --->
                    foldr patt_imp h l --->
                    foldr patt_imp g (l ++ [h]) --->
                    foldr patt_imp g l
            using BasicReasoning).
    { apply prf_add_assumption; try_wfauto2. assumption. }

    assert (H2 : Γ ⊢i (a ---> foldr patt_imp h l) --->
                     (a ---> foldr patt_imp g (l ++ [h]) --->
                     foldr patt_imp g l)
            using BasicReasoning).
    { apply prf_impl_distr_meta;[wf_auto2|wf_auto2|wf_auto2|]. apply H1. }

    assert (H3 : Γ ⊢i ((a ---> foldr patt_imp g (l ++ [h]) ---> foldr patt_imp g l)
                        ---> ((a ---> foldr patt_imp g (l ++ [h])) ---> (a ---> foldr patt_imp g l)))
            using BasicReasoning).
    { apply P2; wf_auto2. }

    eapply prf_weaken_conclusion_meta_meta.
    4: apply H3. 4: apply H2. all: wf_auto2.
Defined.

Lemma prf_add_lemma_under_implication_meta {Σ : Signature} Γ l g h i:
  Pattern.wf l ->
  well_formed g ->
  well_formed h ->
  Γ ⊢i (foldr patt_imp h l) using i ->
  Γ ⊢i ((foldr patt_imp g (l ++ [h])) ---> (foldr patt_imp g l)) using i.
Proof.
  intros WFl WFg WGh H.
  eapply MP.
  { apply H. }
  { useBasicReasoning. apply prf_add_lemma_under_implication. all: wf_auto2. }
Defined.

Lemma prf_add_lemma_under_implication_meta_meta {Σ : Signature} Γ l g h i:
  Pattern.wf l ->
  well_formed g ->
  well_formed h ->
  Γ ⊢i (foldr patt_imp h l) using i ->
  Γ ⊢i (foldr patt_imp g (l ++ [h])) using i ->
  Γ ⊢i (foldr patt_imp g l) using i.
Proof.
  intros WFl WFg WGh H H0.
  eapply MP.
  { apply H0. }
  { apply prf_add_lemma_under_implication_meta. 4: apply H. all: wf_auto2. }
Defined.

Lemma mlGoal_assert {Σ : Signature} Γ l name g h i:
  well_formed h ->
  mkMLGoal Σ Γ l h i ->
  mkMLGoal Σ Γ (l ++ [mkNH _ name h]) g i ->
  mkMLGoal Σ Γ l g i.
Proof.
  intros wfh H1 H2.
  unfold of_MLGoal in *. simpl in *.
  intros wfg wfl.
  eapply prf_add_lemma_under_implication_meta_meta.
  4: apply H1. 6: unfold patterns_of in H2; rewrite map_app in H2; apply H2. all: try assumption.
  { abstract (
      unfold Pattern.wf;
      rewrite map_app;
      rewrite foldr_app;
      simpl;
      rewrite wfh;
      simpl;
      exact wfl
    ).
  }
Defined.

Lemma prf_add_lemma_under_implication_generalized {Σ : Signature} Γ l1 l2 g h:
  Pattern.wf l1 ->
  Pattern.wf l2 ->
  well_formed g ->
  well_formed h ->
  Γ ⊢i ((foldr patt_imp h l1) ---> ((foldr patt_imp g (l1 ++ [h] ++ l2)) ---> (foldr patt_imp g (l1 ++ l2))))
  using BasicReasoning.
Proof.
  intros wfl1 wfl2 wfg wfh.
  induction l1; simpl.
  - apply modus_ponens; wf_auto2.
  - pose proof (wfal1 := wfl1).
    unfold Pattern.wf in wfl1. simpl in wfl1. apply andb_prop in wfl1. destruct wfl1 as [wfa wfl1].
    specialize (IHl1 wfl1).
    assert (H1: Γ ⊢i a ---> foldr patt_imp h l1 ---> foldr patt_imp g (l1 ++ [h] ++ l2) ---> foldr patt_imp g (l1 ++ l2) using BasicReasoning).
    { apply prf_add_assumption; try_wfauto2. assumption. }
    assert (H2 : Γ ⊢i (a ---> foldr patt_imp h l1) ---> (a ---> foldr patt_imp g (l1 ++ [h] ++ l2) ---> foldr patt_imp g (l1 ++ l2)) using BasicReasoning).
    { apply prf_impl_distr_meta;[wf_auto2|wf_auto2|wf_auto2|]. exact H1. }
    assert (H3 : Γ ⊢i ((a ---> foldr patt_imp g (l1 ++ [h] ++ l2) ---> foldr patt_imp g (l1 ++ l2))
                        ---> ((a ---> foldr patt_imp g (l1 ++ [h] ++ l2)) ---> (a ---> foldr patt_imp g (l1 ++ l2)))) using BasicReasoning).
    { apply P2; wf_auto2. }

    eapply prf_weaken_conclusion_meta_meta.
    4: apply H3. 4: assumption. all: wf_auto2.
Defined.

Lemma prf_add_lemma_under_implication_generalized_meta {Σ : Signature} Γ l1 l2 g h i:
  Pattern.wf l1 ->
  Pattern.wf l2 ->
  well_formed g ->
  well_formed h ->
  Γ ⊢i (foldr patt_imp h l1) using i ->
  Γ ⊢i ((foldr patt_imp g (l1 ++ [h] ++ l2)) ---> (foldr patt_imp g (l1 ++ l2))) using i.
Proof.
  intros WFl1 WFl2 WFg WGh H.
  eapply MP.
  { apply H. }
  { useBasicReasoning.
    apply prf_add_lemma_under_implication_generalized; wf_auto2.
  }
Defined.

Lemma prf_add_lemma_under_implication_generalized_meta_meta {Σ : Signature} Γ l1 l2 g h i:
  Pattern.wf l1 ->
  Pattern.wf l2 ->
  well_formed g ->
  well_formed h ->
  Γ ⊢i (foldr patt_imp h l1) using i ->
  Γ ⊢i (foldr patt_imp g (l1 ++ [h] ++ l2)) using i ->
  Γ ⊢i (foldr patt_imp g (l1 ++ l2)) using i.
Proof.
  intros WFl1 WFl2 WFg WGh H H0.
  eapply MP.
  { apply H0. }
  { apply prf_add_lemma_under_implication_generalized_meta.
    5: apply H. all: wf_auto2.
  }
Defined.

Lemma mlGoal_assert_generalized {Σ : Signature} Γ l1 l2 name g h i:
  well_formed h ->
  mkMLGoal Σ Γ l1 h i ->
  mkMLGoal Σ Γ (l1 ++ [mkNH _ name h] ++ l2) g i ->
  mkMLGoal Σ Γ (l1 ++ l2) g i.
Proof.
  intros wfh H1 H2.
  unfold of_MLGoal in *. simpl in *.
  intros wfg wfl1l2.
  unfold patterns_of.
  rewrite map_app.
  eapply prf_add_lemma_under_implication_generalized_meta_meta.
  5: apply H1. 7: unfold patterns_of in H2; rewrite map_app in H2; apply H2. all: try assumption.
  { abstract (
        apply (wf_take (length (patterns_of l1))) in wfl1l2;
        unfold patterns_of in wfl1l2;
        rewrite map_app in wfl1l2;
        rewrite take_app in wfl1l2;
        exact wfl1l2
    ).
  }
  { abstract (
        apply (wf_drop (length (patterns_of l1))) in wfl1l2;
        unfold patterns_of in wfl1l2;
        rewrite map_app in wfl1l2;
        rewrite drop_app in wfl1l2;
        exact wfl1l2
    ).
  }
  { abstract (
        apply (wf_take (length (patterns_of l1))) in wfl1l2;
        unfold patterns_of in wfl1l2;
        rewrite map_app in wfl1l2;
        rewrite take_app in wfl1l2;
        exact wfl1l2
    ).
  }
  {
    abstract(
      pose proof (wfl1 := wf_take (length (patterns_of l1)) _ wfl1l2);
      unfold patterns_of in wfl1;
      rewrite map_app in wfl1;
      rewrite take_app in wfl1;
      pose proof (wfl2 := wf_drop (length (patterns_of l1)) _ wfl1l2);
      unfold patterns_of in wfl2;
      rewrite map_app in wfl2;
      rewrite drop_app in wfl2;
      unfold Pattern.wf; rewrite map_app; rewrite foldr_app;
      simpl; rewrite wfh; unfold Pattern.wf in wfl2; rewrite wfl2;
      simpl; exact wfl1
    ).
  }
Defined.

Tactic Notation "_mlAssert_nocheck" "(" constr(name) ":" constr(t) ")" :=
  match goal with
  | |- @of_MLGoal ?Sgm (@mkMLGoal ?Sgm ?Ctx ?l ?g ?i) =>
    let Hwf := fresh "Hwf" in
    assert (Hwf : well_formed t);
    [idtac|
      let H := fresh "H" in
      assert (H : @mkMLGoal Sgm Ctx l t i);
      [ | (eapply (@mlGoal_assert Sgm Ctx l name g t i Hwf H); rewrite [_ ++ _]/=; clear H)]
    ]
  end.


(* TODO: make this bind tigther. *)
Tactic Notation "mlAssert" "(" constr(name) ":" constr(t) ")" :=
  _failIfUsed name;
  _mlAssert_nocheck (name : t)
.


Tactic Notation "mlAssert" "(" constr (t) ")" :=
  let hyps := _getHypNames in
  let name := eval lazy in (fresh hyps) in
  mlAssert (name : (t)).

Local Example ex_mlAssert {Σ : Signature} Γ a:
  well_formed a ->
  Γ ⊢i (a ---> a ---> a) using BasicReasoning.
Proof.
  intros wfa.
  toMLGoal.
  { wf_auto2. }
  mlIntro "H0". mlIntro "H1".
  mlAssert ("H2" : a).
  { wf_auto2. }
  { mlExact "H1". }
  mlAssert (a).
  { wf_auto2. }
  { mlExact "H1". }
  mlExact "H2".
Qed.

Ltac _getGoalProofInfo :=
  lazymatch goal with
  | |- @of_MLGoal ?Sgm (@mkMLGoal ?Sgm ?Ctx ?l ?g ?i)
    => i
  end.

Ltac _getGoalTheory :=
  lazymatch goal with
  | |- @of_MLGoal ?Sgm (@mkMLGoal ?Sgm ?Ctx ?l ?g ?i)
    => Ctx
  end.

Tactic Notation "mlAssert" "(" constr(name) ":" constr(t) ")" "using" "first" constr(n) :=
  _failIfUsed name;
  lazymatch goal with
  | |- @of_MLGoal ?Sgm (@mkMLGoal ?Sgm ?Ctx ?l ?g ?i) =>
    let l1 := fresh "l1" in
    let l2 := fresh "l2" in
    let Heql1 := fresh "Heql1" in
    let Heql2 := fresh "Heql2" in
    remember (take n l) as l1 eqn:Heql1 in |-;
    remember (drop n l) as l2 eqn:Heql2 in |-;
    simpl in Heql1; simpl in Heql2;
    eapply cast_proof_ml_hyps;
    [(
      rewrite -[l](take_drop n);
      reflexivity
    )|];
    let Hwf := fresh "Hwf" in
    assert (Hwf : well_formed t);
    [idtac|
      let H := fresh "H" in
      assert (H : @mkMLGoal Sgm Ctx l1 t i) ;
      [
        (eapply cast_proof_ml_hyps; [(rewrite Heql1; reflexivity)|]);  clear l1 l2 Heql1 Heql2
      | apply (cast_proof_ml_hyps _ _ _ (f_equal patterns_of Heql1)) in H;
        eapply (@mlGoal_assert_generalized Sgm Ctx (take n l) (drop n l) name g t i Hwf H);
        rewrite [_ ++ _]/=; clear l1 l2 Heql1 Heql2 H] 
    ]
  end.

Tactic Notation "mlAssert" "(" constr(t) ")" "using" "first" constr(n)  :=
  let hyps := _getHypNames in
  let name := eval cbv in (fresh hyps) in
  mlAssert (name : t) using first n.

Local Example ex_assert_using {Σ : Signature} Γ p q a b:
  well_formed a = true ->
  well_formed b = true ->
  well_formed p = true ->
  well_formed q = true ->
  Γ ⊢i a ---> p and q ---> b ---> ! ! q using BasicReasoning.
Proof.
  intros wfa wfb wfp wfq.
  toMLGoal.
  { wf_auto2. }
  mlIntro "H0".
  mlIntro "H1".
  mlIntro "H2".

  mlAssert ("H4" : p) using first 2.
  { wf_auto2. }
  { admit. }

  mlAssert (p) using first 2.
  { wf_auto2. }
  { admit. }
Abort.

Lemma P4i' {Σ : Signature} (Γ : Theory) (A : Pattern) :
  well_formed A →
  Γ ⊢i ((!A ---> A) ---> A) using BasicReasoning.
Proof.
  intros wfA.
  assert (H1: Γ ⊢i ((! A ---> ! ! A) ---> ! ! A) using BasicReasoning).
  { apply P4i. wf_auto2. }
  assert (H2: Γ ⊢i ((! A ---> A) ---> (! A ---> ! ! A)) using BasicReasoning).
  { eapply prf_weaken_conclusion_meta. 
    4: apply not_not_intro.
    all: wf_auto2.
  }

  eapply prf_strenghten_premise_meta_meta. 4: apply H2.
  4: eapply prf_weaken_conclusion_meta_meta. 7: apply not_not_elim.
  8: { apply H1. }
  all: wf_auto2.
Defined.

Lemma tofold {Σ : Signature} p:
  p = fold_right patt_imp p [].
Proof.
  reflexivity.
Defined.

Lemma consume {Σ : Signature} p q l:
  fold_right patt_imp (p ---> q) l = fold_right patt_imp q (l ++ [p]).
Proof.
  rewrite foldr_app. reflexivity.
Defined.

Lemma prf_disj_elim {Σ : Signature} Γ p q r:
  well_formed p ->
  well_formed q ->
  well_formed r ->
  Γ ⊢i ((p ---> r) ---> (q ---> r) ---> (p or q) ---> r)
  using BasicReasoning.
Proof.
  intros wfp wfq wfr.
  pose proof (H1 := Constructive_dilemma Γ p r q r wfp wfr wfq wfr).
  assert (Γ ⊢i ((r or r) ---> r) using BasicReasoning).
  { unfold patt_or. apply P4i'. wf_auto2. }
  eapply cast_proof' in H1.
  2: { rewrite -> tofold. do 3 rewrite -> consume. reflexivity. }
  eapply prf_weaken_conclusion_iter_meta_meta in H1. 5: apply H.
  { apply H1. }
  all: wf_auto2.
Defined.

Lemma prf_disj_elim_meta {Σ : Signature} Γ p q r i:
  well_formed p ->
  well_formed q ->
  well_formed r ->
  Γ ⊢i (p ---> r) using i ->
  Γ ⊢i ((q ---> r) ---> (p or q) ---> r) using i.
Proof.
  intros WFp WHq WFr H.
  eapply MP. apply H. useBasicReasoning. apply prf_disj_elim.
  all: wf_auto2.
Defined.

Lemma prf_disj_elim_meta_meta {Σ : Signature} Γ p q r i:
  well_formed p ->
  well_formed q ->
  well_formed r ->
  Γ ⊢i (p ---> r) using i ->
  Γ ⊢i (q ---> r) using i ->
  Γ ⊢i ((p or q) ---> r) using i.
Proof.
  intros WFp WHq WFr H H0.
  eapply MP. apply H0. apply prf_disj_elim_meta. 4: apply H.
  all: wf_auto2.
Defined.

Lemma prf_disj_elim_meta_meta_meta {Σ : Signature} Γ p q r i:
  well_formed p ->
  well_formed q ->
  well_formed r ->
  Γ ⊢i (p ---> r) using i ->
  Γ ⊢i (q ---> r) using i ->
  Γ ⊢i (p or q) using i ->
  Γ ⊢i r using i.
Proof.
  intros WFp WHq WFr H H0 H1.
  eapply MP. apply H1.
  apply prf_disj_elim_meta_meta.
  all: assumption.
Defined.

Lemma prf_add_proved_to_assumptions {Σ : Signature} Γ l a g i:
  Pattern.wf l ->
  well_formed a ->
  well_formed g ->
  Γ ⊢i a using i->
  Γ ⊢i ((foldr patt_imp g (a::l)) ---> (foldr patt_imp g l)) using i.
Proof.
  intros wfl wfa wfg Ha.
  induction l.
  - simpl.
    pose proof (modus_ponens Γ _ _ wfa wfg).
    eapply MP. apply Ha. useBasicReasoning. apply H.
  - pose proof (wfa0l := wfl).
    unfold Pattern.wf in wfl. simpl in wfl. apply andb_prop in wfl. destruct wfl as [wfa0 wfl].
    specialize (IHl wfl).
    simpl in IHl. simpl.
    (* < change a0 and a in the LHS > *)
    assert (H : Γ ⊢i (a ---> a0 ---> foldr patt_imp g l) ---> (a0 ---> a ---> foldr patt_imp g l) using BasicReasoning).
    { apply reorder; wf_auto2. }

    eapply cast_proof'.
    { rewrite -> tofold. rewrite -> consume. reflexivity. }
    pose proof (H0 := prf_strenghten_premise_iter_meta_meta Γ [] []).
    simpl in H0. simpl.
    specialize (H0 (a0 ---> a ---> foldr patt_imp g l) (a ---> a0 ---> foldr patt_imp g l)).
    specialize (H0 (a0 ---> foldr patt_imp g l)). simpl in H0. simpl.
    simpl. apply H0. all: try_wfauto2.
    { useBasicReasoning. apply H. }
    clear H0 H.
    (* </change a0 and a > *)
    assert (Γ ⊢i ((a ---> a0 ---> foldr patt_imp g l) ---> (a0 ---> foldr patt_imp g l)) using i).
    { eapply MP. 2: { useBasicReasoning. apply modus_ponens; wf_auto2. } apply Ha. }

    eapply prf_strenghten_premise_meta_meta. 5: apply H. all: try_wfauto2.
    useBasicReasoning.
    apply reorder; wf_auto2.
Defined.

Lemma prf_add_proved_to_assumptions_meta {Σ : Signature} Γ l a g i:
  Pattern.wf l ->
  well_formed a ->
  well_formed g ->
  Γ ⊢i a using i ->
  Γ ⊢i (foldr patt_imp g (a::l)) using i ->
  Γ ⊢i (foldr patt_imp g l) using i.
Proof.
  intros WFl WFa WFg H H0.
  eapply MP.
  apply H0.
  eapply prf_add_proved_to_assumptions.
  4: apply H.
  all: wf_auto2.
Defined.

Lemma MLGoal_add {Σ : Signature} Γ l name g h i:
  Γ ⊢i h using i ->
  mkMLGoal Σ Γ (mkNH _ name h::l) g i ->
  mkMLGoal Σ Γ l g i.
Proof.
  intros H H0.
  unfold of_MLGoal in *. simpl in *.
  intros wfg wfl.
  apply prf_add_proved_to_assumptions_meta with (a := h).
  5: apply H0.
  all: try assumption.
  { abstract (pose (tmp := proj1_sig H); apply proved_impl_wf in tmp; exact tmp). }
  { abstract (
        unfold Pattern.wf;
        simpl;
        pose (tmp := proj1_sig H);
        apply proved_impl_wf in tmp;
        rewrite tmp;
        simpl;
        exact wfl
    ).
  }
Defined.

Tactic Notation "mlAdd" constr(n) "as" constr(name') :=
  _failIfUsed name';
  match goal with
  | |- @of_MLGoal ?Sgm (@mkMLGoal ?Sgm ?Ctx ?l ?g ?i) =>
    apply (@MLGoal_add Sgm Ctx l name' g _ i n)
  end.

Tactic Notation "mlAdd" constr(n) :=
  let hyps := _getHypNames in
  let name := eval cbv in (fresh hyps) in
  mlAdd n as name.

Local Example ex_mlAdd {Σ : Signature} Γ l g h i:
  Pattern.wf l ->
  well_formed g ->
  well_formed h ->
  Γ ⊢i (h ---> g) using i ->
  Γ ⊢i h using i ->
  Γ ⊢i g using i.
Proof.
  intros WFl WFg WFh H H0. toMLGoal.
  { wf_auto2. }
  mlAdd H0 as "H0".
  mlAdd H.
  mlApply "0".
  mlExact "H0".
Defined.


Lemma prf_clear_hyp {Σ : Signature} Γ l1 l2 g h:
  Pattern.wf l1 ->
  Pattern.wf l2 ->
  well_formed g ->
  well_formed h ->
  Γ ⊢i (foldr patt_imp g (l1 ++ l2)) ---> (foldr patt_imp g (l1 ++ [h] ++ l2))
  using BasicReasoning.
Proof.
  intros wfl1 wfl2 wfg wfh.
  induction l1; simpl.
  - apply P1; wf_auto2.
  - unfold Pattern.wf in wfl1. simpl in wfl1. apply andb_prop in wfl1. destruct wfl1 as [wfa wfl1].
    specialize (IHl1 wfl1).

    assert (H1: Γ ⊢i a ---> foldr patt_imp g (l1 ++ l2) ---> foldr patt_imp g (l1 ++ [h] ++ l2) using BasicReasoning).
    {
      toMLGoal.
      { wf_auto2. }
      mlAdd IHl1 as "H0".
      mlIntro "H1". mlExact "H0".
    }
    apply prf_impl_distr_meta; try_wfauto2. apply H1.
Defined.

Lemma prf_clear_hyp_meta {Σ : Signature} Γ l1 l2 g h i:
  Pattern.wf l1 ->
  Pattern.wf l2 ->
  well_formed g ->
  well_formed h ->
  Γ ⊢i (foldr patt_imp g (l1 ++ l2)) using i ->
  Γ ⊢i (foldr patt_imp g (l1 ++ [h] ++ l2)) using i.
Proof.
  intros. eapply MP.
  apply H3.
  useBasicReasoning.
  apply prf_clear_hyp; wf_auto2.
Defined.  



Lemma mlGoal_clear_hyp {Σ : Signature} Γ l1 l2 g h i:
  mkMLGoal Σ Γ (l1 ++ l2) g i ->
  mkMLGoal Σ Γ (l1 ++ h::l2) g i.
Proof.
  intros H1.
  unfold of_MLGoal in *. simpl in *. intros wfg wfl1hl2.
  unfold patterns_of in *. rewrite map_app.
  rewrite map_app in wfl1hl2; simpl in wfl1hl2.
  apply prf_clear_hyp_meta.
  5: rewrite map_app in H1; apply H1. all: try assumption.
  { apply wfl₁hl₂_proj_l₁ in wfl1hl2. exact wfl1hl2. }
  { apply wfl₁hl₂_proj_l₂ in wfl1hl2. exact wfl1hl2. }
  { apply wfl₁hl₂_proj_h in wfl1hl2. exact wfl1hl2. }
  { apply wfl₁hl₂_proj_l₁l₂ in wfl1hl2. exact wfl1hl2. }
Defined.


Tactic Notation "mlClear" constr(name) := 
  _mlReshapeHypsByName name; apply mlGoal_clear_hyp; _mlReshapeHypsBack.

Local Example ex_mlClear {Σ : Signature} Γ a b c:
  well_formed a ->
  well_formed b ->
  well_formed c ->
  Γ ⊢i a ---> (b ---> (c ---> b)) using BasicReasoning.
Proof.
  intros wfa wfb wfc.
  toMLGoal.
  { wf_auto2. }
  mlIntro "H0". mlIntro "H1". mlIntro "H2".
  mlClear "H2".
  mlClear "H0".
  mlExact "H1".
Defined.


Lemma not_concl {Σ : Signature} Γ p q:
  well_formed p ->
  well_formed q ->
  Γ ⊢i (p ---> (q ---> ((p ---> ! q) ---> ⊥))) using BasicReasoning.
Proof.
  intros wfp wfq.
  eapply cast_proof'.
  {
    rewrite [(p ---> q ---> (p ---> ! q) ---> ⊥)]tofold.
    do 3 rewrite consume.
    rewrite [(((nil ++ [p]) ++ [q]) ++ [p ---> ! q])]/=.
    replace ([p; q; p--->!q]) with ([p] ++ [q; p ---> !q] ++ []) by reflexivity.
    reflexivity.
  }
  apply prf_reorder_iter_meta; try_wfauto2.
  simpl.
  fold (! q).
  apply modus_ponens; wf_auto2.
Defined.

(* TODO rename or remove *)
Lemma helper {Σ : Signature} Γ p q r:
  well_formed p ->
  well_formed q ->
  well_formed r ->
  Γ ⊢i (p ---> (q ---> ((p ---> (q ---> r)) ---> r))) using BasicReasoning.
Proof.
  intros wfp wfq wfr.
  eapply cast_proof'.
  {
    rewrite [(p ---> q ---> (p ---> q ---> r) ---> r)]tofold. repeat rewrite consume.
    replace ((([] ++ [p]) ++ [q]) ++ [p ---> (q ---> r)]) with ([p;q;p--->(q ---> r)]) by reflexivity.
    replace ([p;q;p--->(q ---> r)]) with ([p] ++ [q; p ---> (q ---> r)] ++ []) by reflexivity.
    reflexivity.
  }
  apply prf_reorder_iter_meta; try_wfauto2.
  simpl.
  apply modus_ponens; wf_auto2.
Defined.

Lemma reorder_last_to_head {Σ : Signature} Γ g x l:
  Pattern.wf l ->
  well_formed g ->
  well_formed x ->
  Γ ⊢i ((foldr patt_imp g (x::l)) ---> (foldr patt_imp g (l ++ [x]))) using BasicReasoning.
Proof.
  intros wfl wfg wfx.
  induction l.
  - simpl. apply A_impl_A. wf_auto2.
  - pose proof (wfal := wfl).
    unfold Pattern.wf in wfl. simpl in wfl. apply andb_prop in wfl. destruct wfl as [wfa wfl].
    specialize (IHl wfl).
    simpl. simpl in IHl.
    eapply cast_proof'.
    { rewrite -> tofold at 1. repeat rewrite -> consume. reflexivity. }
    eapply prf_weaken_conclusion_iter_meta_meta.
    4: { apply IHl. }
    all: try_wfauto2.
    eapply cast_proof'.
    {
      rewrite consume.
      replace ((([] ++ [x ---> a ---> foldr patt_imp g l]) ++ [a]) ++ [x])
        with ([x ---> a ---> foldr patt_imp g l] ++ [a;x] ++ []) by reflexivity.
      reflexivity.
    }
    apply prf_reorder_iter_meta; wf_auto2.
    simpl. apply A_impl_A. wf_auto2.
Defined.

Lemma reorder_last_to_head_meta {Σ : Signature} Γ g x l i:
  Pattern.wf l ->
  well_formed g ->
  well_formed x ->
  Γ ⊢i (foldr patt_imp g (x::l)) using i ->
  Γ ⊢i (foldr patt_imp g (l ++ [x])) using i.
Proof.
  intros WFl WFG WFx H.
  eapply MP.
  apply H.
  useBasicReasoning.
  apply reorder_last_to_head; wf_auto2.
Defined.

(* Iterated modus ponens.
 For l = [x₁, ..., xₙ], it says that
 Γ ⊢i ((x₁ -> ... -> xₙ -> (x₁ -> ... -> xₙ -> r)) -> r)
*)
Lemma modus_ponens_iter {Σ : Signature} Γ l r:
  Pattern.wf l ->
  well_formed r ->
  Γ ⊢i (foldr patt_imp r (l ++ [foldr patt_imp r l])) using BasicReasoning.
Proof.
  intros wfl wfr.
  induction l.
  - simpl. apply A_impl_A. exact wfr.
  - pose proof (wfal := wfl).
    unfold Pattern.wf in wfl. simpl in wfl. apply andb_prop in wfl. destruct wfl as [wfa wfl].
    specialize (IHl wfl).
    simpl.
    eapply cast_proof'.
    { rewrite foldr_app. simpl. rewrite consume. simpl. reflexivity. }
    eapply cast_proof' in IHl.
    2: { rewrite foldr_app. reflexivity. }
    simpl in IHl.
    eapply prf_weaken_conclusion_meta_meta.
    4: { apply reorder_last_to_head; wf_auto2. }
    all: try_wfauto2.
    simpl. apply modus_ponens; wf_auto2.
Defined.

Lemma and_impl {Σ : Signature} Γ p q r:
  well_formed p ->
  well_formed q ->
  well_formed r ->
  Γ ⊢i ((p and q ---> r) ---> (p ---> (q ---> r))) using BasicReasoning.
Proof.
  intros wfp wfq wfr.
  toMLGoal.
  { wf_auto2. }
  mlIntro "H0". mlIntro "H2". mlIntro "H3".
  unfold patt_and. mlApply "H0".
  mlIntro "H4". unfold patt_or at 2.
  mlAssert ("H5" : (! ! p)).
  { wf_auto2. }
  {
    mlAdd (not_not_intro Γ p wfp) as "H6".
    mlApply "H6".
    mlExact "H2".
  }
  mlAssert ("H6" : (! q)).
  { wf_auto2. }
  {
    mlApply "H4". mlExact "H5".
  }
  mlApply "H6". mlExact "H3".
Defined.

Lemma and_impl' {Σ : Signature} Γ p q r:
  well_formed p ->
  well_formed q ->
  well_formed r ->
  Γ ⊢i ((p ---> (q ---> r)) ---> ((p and q) ---> r)) using BasicReasoning.
Proof.
  intros wfp wfq wfr.
  toMLGoal.
  { wf_auto2. }
  mlIntro "H0". mlIntro "H1".
  mlAssert ("H2" : p).
  { wf_auto2. }
  {
    mlAdd (pf_conj_elim_l Γ p q wfp wfq) as "H2".
    mlApply "H2".
    mlExact "H1".
  }
  mlAssert ("H3" : q).
  { wf_auto2. }
  {
    mlAdd (pf_conj_elim_r Γ p q wfp wfq) as "H4".
    mlApply "H4".
    mlExact "H1".
  }
  (* This pattern is basically an "apply ... in" *)
  mlAssert ("H4" : (q ---> r)).
  { wf_auto2. }
  { mlApply "H0". mlExact "H2". }
  mlApply "H4". mlExact "H3".
Defined.

Lemma prf_disj_elim_iter {Σ : Signature} Γ l p q r:
  Pattern.wf l ->
  well_formed p ->
  well_formed q ->
  well_formed r ->
  Γ ⊢i ((fold_right patt_imp r (l ++ [p]))
         --->
         ((fold_right patt_imp r (l ++ [q]))
            --->
            (fold_right patt_imp r (l ++ [p or q]))))
  using BasicReasoning.
Proof.
  intros wfl wfp wfq wfr.
  induction l.
  - simpl. apply prf_disj_elim; wf_auto2.
  - pose proof (wfal := wfl).
    unfold Pattern.wf in wfl. simpl in wfl. apply andb_prop in wfl. destruct wfl as [wfa wfl].
    specialize (IHl wfl).
    simpl in *.
    toMLGoal.
    { wf_auto2. }
    mlIntro "H0". mlIntro "H1". mlIntro "H2". 
    mlAdd IHl as "H3".
    mlAssert ("H4" : (foldr patt_imp r (l ++ [p]))).
    { wf_auto2. }
    { mlApply "H0". mlExact "H2". }
    mlAssert ("H5" : (foldr patt_imp r (l ++ [q]))).
    { wf_auto2. }
    { mlApply "H1". mlExact "H2". }
    mlAssert ("H6" : (foldr patt_imp r (l ++ [q]) ---> foldr patt_imp r (l ++ [p or q]))).
    { wf_auto2. }
    { mlApply "H3". mlExact "H4". }
    mlApply "H6".
    mlExact "H5".
Defined.

Lemma prf_disj_elim_iter_2 {Σ : Signature} Γ l₁ l₂ p q r:
  Pattern.wf l₁ ->
  Pattern.wf l₂ ->
  well_formed p ->
  well_formed q ->
  well_formed r ->
  Γ ⊢i ((fold_right patt_imp r (l₁ ++ [p] ++ l₂))
         --->
         ((fold_right patt_imp r (l₁ ++ [q] ++ l₂))
            --->
            (fold_right patt_imp r (l₁ ++ [p or q] ++ l₂))))
  using BasicReasoning.
Proof.
  intros wfl₁ wfl₂ wfp wfq wfr.
  move: l₁ wfl₁.
  induction l₂; intros l₁ wfl₁.
  - simpl. apply prf_disj_elim_iter; wf_auto2.
  - pose proof (wfal₂ := wfl₂).
    unfold Pattern.wf in wfl₂. simpl in wfl₂. apply andb_prop in wfl₂. destruct wfl₂ as [wfa wfl₂].

    simpl. (* We need to move 'a' to the beginning of l₁; then we can apply IHl₂. *)
    (* Or we can swap p and a (move a to the end of l_1) *)
    remember (foldr patt_imp r (l₁ ++ p :: a :: l₂)) as A in |-.
    remember (foldr patt_imp r (l₁ ++ q :: a :: l₂)) as B in |-.
    remember (foldr patt_imp r (l₁ ++ (p or q) :: a :: l₂)) as C in |-.
    eapply cast_proof'.
    { rewrite -HeqA. rewrite -HeqB. rewrite -HeqC. reflexivity. }
    eapply cast_proof'.
    {
      rewrite -> tofold at 1. rewrite consume. rewrite consume. rewrite [_ ++ [B] ]/=.
      rewrite -> HeqA at 1. rewrite -> HeqB at 1. rewrite -> HeqC at 1.
      reflexivity.
    }
    eapply prf_weaken_conclusion_iter_meta_meta.
    4: {
      eapply cast_proof'.
      {
        replace (l₁ ++ (p or q) :: a :: l₂) with (l₁ ++ [p or q; a] ++ l₂) by reflexivity.
        reflexivity.
      }
      apply prf_reorder_iter; wf_auto2.
    }
    all: try_wfauto2.
    simpl.

    eapply cast_proof'.
    { 
      rewrite -> tofold at 1. repeat rewrite consume. rewrite [_ ++ [_] ]/=.

    replace
      ([foldr patt_imp r (l₁ ++ p :: a :: l₂); foldr patt_imp r (l₁ ++ q :: a :: l₂)])
      with
        ([foldr patt_imp r (l₁ ++ p :: a :: l₂)] ++ (foldr patt_imp r (l₁ ++ q :: a :: l₂))::[])
      by reflexivity.
      reflexivity.
    }

    eapply prf_strenghten_premise_iter_meta_meta with (h := foldr patt_imp r (l₁ ++ a :: q :: l₂)).
    6: { apply prf_reorder_iter; wf_auto2. }
    all: try_wfauto2.

    eapply cast_proof'.
    {
      replace
        ([foldr patt_imp r (l₁ ++ p :: a :: l₂)] ++ [foldr patt_imp r (l₁ ++ a :: q :: l₂)])
        with
        ([] ++ ((foldr patt_imp r (l₁ ++ p :: a :: l₂))::[foldr patt_imp r (l₁ ++ a :: q :: l₂)]))
        by reflexivity.
      reflexivity.
   }

    eapply prf_strenghten_premise_iter_meta_meta with (h := (foldr patt_imp r (l₁ ++ a :: p :: l₂))).
    6: {  apply prf_reorder_iter; wf_auto2. }
    all: try_wfauto2.

    simpl.
    eapply cast_proof'.
    {
      replace (l₁ ++ a :: p :: l₂) with ((l₁ ++ [a]) ++ [p] ++ l₂) by (rewrite <- app_assoc; reflexivity).
      replace (l₁ ++ a :: q :: l₂) with ((l₁ ++ [a]) ++ [q] ++ l₂) by (rewrite <- app_assoc; reflexivity).
      replace (l₁ ++ a :: (p or q) :: l₂) with ((l₁ ++ [a]) ++ [p or q] ++ l₂) by (rewrite <- app_assoc; reflexivity).
      reflexivity.
    }
    apply IHl₂; wf_auto2.
Defined.

Lemma prf_disj_elim_iter_2_meta {Σ : Signature} Γ l₁ l₂ p q r i:
  Pattern.wf l₁ ->
  Pattern.wf l₂ ->
  well_formed p ->
  well_formed q ->
  well_formed r ->
  Γ ⊢i (fold_right patt_imp r (l₁ ++ [p] ++ l₂)) using i ->
  Γ ⊢i ((fold_right patt_imp r (l₁ ++ [q] ++ l₂))
            --->
            (fold_right patt_imp r (l₁ ++ [p or q] ++ l₂))) using i.
Proof.
  intros WFl1 WFl2 WFp WFq WFr H.
  eapply MP.
  apply H.
  useBasicReasoning.
  apply prf_disj_elim_iter_2; wf_auto2.
Defined.

Lemma prf_disj_elim_iter_2_meta_meta {Σ : Signature} Γ l₁ l₂ p q r i:
  Pattern.wf l₁ ->
  Pattern.wf l₂ ->
  well_formed p ->
  well_formed q ->
  well_formed r ->
  Γ ⊢i (fold_right patt_imp r (l₁ ++ [p] ++ l₂)) using i ->
  Γ ⊢i (fold_right patt_imp r (l₁ ++ [q] ++ l₂)) using i ->
  Γ ⊢i (fold_right patt_imp r (l₁ ++ [p or q] ++ l₂)) using i.
Proof.
  intros WFl1 WFl2 WFp WFq WFr H H0.
  eapply MP.
  2: { apply prf_disj_elim_iter_2_meta; try_wfauto2. apply H. }
  apply H0.
Defined.

Lemma MLGoal_disj_elim {Σ : Signature} Γ l₁ l₂ pn p qn q pqn r i:
  mkMLGoal Σ Γ (l₁ ++ [mkNH _ pn p] ++ l₂) r i ->
  mkMLGoal Σ Γ (l₁ ++ [mkNH _ qn q] ++ l₂) r i ->
  mkMLGoal Σ Γ (l₁ ++ [mkNH _ pqn (p or q)] ++ l₂) r i.
Proof.
  intros H1 H2.
  unfold of_MLGoal in *. simpl in *.
  intros wfr Hwf.
  unfold patterns_of in *.
  rewrite map_app.
  rewrite map_app in H1.
  rewrite map_app in H2.
  apply prf_disj_elim_iter_2_meta_meta.
  7: apply H2.
  6: apply H1.
  all: try assumption; unfold patterns_of in *; rewrite map_app in Hwf.
  { abstract (apply wfl₁hl₂_proj_l₁ in Hwf; exact Hwf). }
  { abstract (apply wfl₁hl₂_proj_l₂ in Hwf; exact Hwf). }
  { abstract (apply wfl₁hl₂_proj_h in Hwf; wf_auto2). }
  { abstract (apply wfl₁hl₂_proj_h in Hwf; wf_auto2). }
  {
    pose proof (wfl₁hl₂_proj_l₁ _ _ _ Hwf).
    pose proof (wfl₁hl₂_proj_h _ _ _ Hwf).
    pose proof (wfl₁hl₂_proj_l₂ _ _ _ Hwf).
    apply wf_app; [assumption|].
    unfold patt_or,patt_not in *.
    simpl.
    wf_auto2.
  }
  {
    pose proof (wfl₁hl₂_proj_l₁ _ _ _ Hwf).
    pose proof (wfl₁hl₂_proj_h _ _ _ Hwf).
    pose proof (wfl₁hl₂_proj_l₂ _ _ _ Hwf).
    apply wf_app; [assumption|].
    unfold patt_or,patt_not in *.
    simpl.
    wf_auto2.
  }
Defined.

Tactic Notation "mlDestructOr" constr(name) "as" constr(name1) constr(name2) :=
  _failIfUsed name1; _failIfUsed name2;
  match goal with
  | |- @of_MLGoal ?Sgm (@mkMLGoal ?Sgm ?Ctx ?l ?g ?i) =>
    let Htd := fresh "Htd" in
    eapply cast_proof_ml_hyps;
    f_equal;
    _mlReshapeHypsByName name;
    apply MLGoal_disj_elim with (pqn := name) (pn := name1) (qn := name2);
    _mlReshapeHypsBack;
    simpl
  end.

Tactic Notation "mlDestructOr" constr(name) :=
  let hyps := _getHypNames in
  let name0 := eval cbv in (fresh hyps) in
  let name1 := eval cbv in (fresh (name0 :: hyps)) in
  mlDestructOr name as name0 name1.

Local Example exd {Σ : Signature} Γ a b p q c i:
  well_formed a ->
  well_formed b ->
  well_formed p ->
  well_formed q ->
  well_formed c ->
  Γ ⊢i (a ---> p ---> b ---> c) using i ->
  Γ ⊢i (a ---> q ---> b ---> c) using i->
  Γ ⊢i (a ---> (p or q) ---> b ---> c) using i.
Proof.
  intros WFa WFb WFp WFq WFc H H0.
  toMLGoal.
  { wf_auto2. } 
  mlIntro "H0".
  mlIntro "H1".
  mlIntro "H2".
  mlDestructOr "H1".
  - fromMLGoal. apply H.
  - fromMLGoal. apply H0.
Defined.

Lemma pf_iff_split {Σ : Signature} Γ A B i:
  well_formed A ->
  well_formed B ->
  Γ ⊢i A ---> B using i ->
  Γ ⊢i B ---> A using i ->
  Γ ⊢i A <---> B using i.
Proof.
  intros wfA wfB AimplB BimplA.
  unfold patt_iff.
  apply conj_intro_meta; try_wfauto2; assumption.
Defined.

Lemma pf_iff_proj1 {Σ : Signature} Γ A B i:
  well_formed A ->
  well_formed B ->
  Γ ⊢i A <---> B using i ->
  Γ ⊢i A ---> B using i.
Proof.
  intros WFA WFB H. unfold patt_iff in H.
  apply pf_conj_elim_l_meta in H; try_wfauto2; assumption.
Defined.

Lemma pf_iff_proj2 {Σ : Signature} Γ A B i:
  well_formed A ->
  well_formed B ->
  Γ ⊢i (A <---> B) using i ->
  Γ ⊢i (B ---> A) using i.
Proof.
  intros WFA WFB H. unfold patt_iff in H.
  apply pf_conj_elim_r_meta in H; try_wfauto2; assumption.
Defined.

Lemma pf_iff_iff {Σ : Signature} Γ A B i:
  well_formed A ->
  well_formed B ->
  prod ((Γ ⊢i (A <---> B) using i) -> (prod (Γ ⊢i (A ---> B) using i) (Γ ⊢i (B ---> A) using i)))
  ( (prod (Γ ⊢i (A ---> B) using i)  (Γ ⊢i (B ---> A) using i)) -> (Γ ⊢i (A <---> B) using i)).
Proof.
  intros WFA WFB.
  split; intros H.
  {
    pose proof (H1 := pf_iff_proj1 _ _ _ _ WFA WFB H).
    pose proof (H2 := pf_iff_proj2 _ _ _ _ WFA WFB H).
    split; assumption.
  }
  {
    destruct H as [H1 H2].
    apply pf_iff_split; assumption.
  }
Defined.

Lemma pf_iff_equiv_refl {Σ : Signature} Γ A :
  well_formed A ->
  Γ ⊢i (A <---> A) using BasicReasoning.
Proof.
  intros WFA.
  apply pf_iff_split; try_wfauto2; apply A_impl_A; assumption.
Defined.

Lemma pf_iff_equiv_sym {Σ : Signature} Γ A B i:
  well_formed A ->
  well_formed B ->
  Γ ⊢i (A <---> B) using i ->
  Γ ⊢i (B <---> A) using i.
Proof.
  intros wfA wfB H.
  pose proof (H2 := H).
  apply pf_iff_proj2 in H2; try_wfauto2.
  rename H into H1.
  apply pf_iff_proj1 in H1; try_wfauto2.
  apply pf_iff_split; try_wfauto2; assumption.
Defined.

Lemma pf_iff_equiv_trans {Σ : Signature} Γ A B C i:
  well_formed A ->
  well_formed B ->
  well_formed C ->
  Γ ⊢i (A <---> B) using i ->
  Γ ⊢i (B <---> C) using i ->
  Γ ⊢i (A <---> C) using i.
Proof.
  intros wfA wfB wfC AeqB BeqC.
  apply pf_iff_iff in AeqB; try_wfauto2. destruct AeqB as [AimpB BimpA].
  apply pf_iff_iff in BeqC; try_wfauto2. destruct BeqC as [BimpC CimpB].
  apply pf_iff_iff; try_wfauto2.
  split.
  {
    eapply syllogism_meta. 4,5: eassumption.
    1-3: wf_auto2.
  }
  {
    eapply syllogism_meta. 4,5: eassumption.
    1-3: wf_auto2.
  }
Defined.

Lemma prf_conclusion {Σ : Signature} Γ a b i:
  well_formed a ->
  well_formed b ->
  Γ ⊢i b using i ->
  Γ ⊢i (a ---> b) using i.
Proof.
  intros WFa WFb H. eapply MP.
  apply H.
  useBasicReasoning.
  apply P1; wf_auto2.
Defined.



Lemma and_of_negated_iff_not_impl {Σ : Signature} Γ p1 p2:
  well_formed p1 ->
  well_formed p2 ->
  Γ ⊢i (! (! p1 ---> p2) <---> ! p1 and ! p2)
  using BasicReasoning.
Proof.
  intros wfp1 wfp2.
  apply conj_intro_meta.
  { wf_auto2. }
  { wf_auto2. }
  - toMLGoal.
    { wf_auto2. }
    mlIntro "H0". mlIntro "H1".
    mlApply "H0".
    mlIntro "H2".
    unfold patt_or.
    mlAdd (not_not_elim Γ p2 ltac:(wf_auto2)) as "H3".
    mlApply "H3".
    mlApply "H1".
    mlAdd (not_not_intro Γ (! p1) ltac:(wf_auto2)) as "H4".
    mlApply "H4".
    mlExact "H2".
  - toMLGoal.
    { wf_auto2. }
    mlIntro "H0". mlIntro "H1".
    unfold patt_and.
    mlApply "H0".
    unfold patt_or.
    mlIntro "H2".
    mlAdd (@not_not_intro Σ Γ p2 ltac:(wf_auto2)) as "H3".
    mlApply "H3".
    mlApply "H1".
    mlAdd (@not_not_elim Σ Γ (! p1) ltac:(wf_auto2)) as "H4".
    mlApply "H4".
    mlExact "H2".
Defined.

Lemma and_impl_2 {Σ : Signature} Γ p1 p2:
  well_formed p1 ->
  well_formed p2 ->
  Γ ⊢i (! (p1 ---> p2) <---> p1 and ! p2)
  using BasicReasoning.
Proof.
  intros wfp1 wfp2.
  apply conj_intro_meta.
  { wf_auto2. }
  { wf_auto2. }
  - toMLGoal.
    { wf_auto2. }
    mlIntro "H0". mlIntro "H1".
    mlApply "H0".
    mlIntro "H2".
    unfold patt_or.
    mlAdd (not_not_elim Γ p2 ltac:(wf_auto2)) as "H3".
    mlApply "H3".
    mlApply "H1".
    mlAdd (not_not_intro Γ p1 ltac:(wf_auto2)) as "H4".
    mlApply "H4".
    mlExact "H2".
  - toMLGoal.
    { wf_auto2. }
    mlIntro "H0". mlIntro "H1".
    mlApply "H0".
    unfold patt_or.
    mlIntro "H2".
    mlAdd (not_not_intro Γ p2 ltac:(wf_auto2)) as "H3".
    mlApply "H3".
    mlApply "H1".
    mlAdd (not_not_elim Γ p1 ltac:(wf_auto2)) as "H4".
    mlApply "H4".
    mlExact "H2".
Defined.

Lemma conj_intro_meta_partial {Σ : Signature} (Γ : Theory) (A B : Pattern) (i : ProofInfo) :
  well_formed A → well_formed B →
  Γ ⊢i A using i →
  Γ ⊢i B ---> (A and B) using i.
Proof.
  intros WFA WFB H.
  eapply MP.
  - exact H.
  - useBasicReasoning. apply conj_intro.
    { wf_auto2. }
    { wf_auto2. }
Defined.

Lemma and_impl_patt {Σ : Signature} (A B C : Pattern) Γ (i : ProofInfo):
  well_formed A → well_formed B → well_formed C →
  Γ ⊢i A using i ->
  Γ ⊢i ((A and B) ---> C) using i ->
  Γ ⊢i (B ---> C) using i.
Proof.
  intros WFA WFB WFC H H0.
  eapply @syllogism_meta with (B := patt_and A B).
  { wf_auto2. }
  { wf_auto2. }
  { wf_auto2. }
  2: { exact H0. }
  apply conj_intro_meta_partial.
  { wf_auto2. }
  { wf_auto2. }
  exact H.
Defined.

Lemma conj_intro2 {Σ : Signature} (Γ : Theory) (A B : Pattern) :
  well_formed A -> well_formed B ->
  Γ ⊢i (A ---> (B ---> (B and A)))
  using BasicReasoning.
Proof.
  intros WFA WFB. eapply reorder_meta.
  { wf_auto2. }
  { wf_auto2. }
  { wf_auto2. }
  apply conj_intro.
  { wf_auto2. }
  { wf_auto2. }
Defined.

Lemma conj_intro_meta_partial2  {Σ : Signature} (Γ : Theory) (A B : Pattern) (i : ProofInfo):
  well_formed A → well_formed B →
  Γ ⊢i A using i →
  Γ ⊢i B ---> (B and A) using i.
Proof.
  intros WFA WFB H.
  eapply MP.
  - exact H.
  - useBasicReasoning. apply conj_intro2.
    { wf_auto2. }
    { wf_auto2. }
Defined.

Lemma and_impl_patt2 {Σ : Signature}  (A B C : Pattern) Γ (i : ProofInfo):
  well_formed A → well_formed B → well_formed C →
  Γ ⊢i A using i ->
  Γ ⊢i ((B and A) ---> C) using i ->
  Γ ⊢i (B ---> C) using i.
Proof.
  intros WFA WFB WFC H H0.
  eapply @syllogism_meta with (B := patt_and B A).
  { wf_auto2. }
  { wf_auto2. }
  { wf_auto2. }
  2: exact H0.
  apply conj_intro_meta_partial2.
  { wf_auto2. }
  { wf_auto2. }
  exact H.
Defined.


Lemma patt_and_comm_meta {Σ : Signature} (A B : Pattern) (Γ : Theory) (i : ProofInfo) :
  well_formed A → well_formed B
  ->
  Γ ⊢i A and B using i ->
  Γ ⊢i B and A using i.
Proof.
  intros WFA WFB H.
  apply pf_conj_elim_r_meta in H as P1.
  apply pf_conj_elim_l_meta in H as P2. all: try_wfauto2.
  apply conj_intro_meta; assumption.
Defined.

Lemma MLGoal_applyMeta {Σ : Signature} Γ r r' i:
  Γ ⊢i (r' ---> r) using i ->
  forall l,
  mkMLGoal Σ Γ l r' i ->
  mkMLGoal Σ Γ l r i.
Proof.
  intros Himp l H.
  unfold of_MLGoal in *. simpl in *.
  intros wfr wfl.
  eapply prf_weaken_conclusion_iter_meta_meta.
  4: apply Himp.
  4: apply H.
  all: try assumption.
  1,2: pose proof (wfrr' := proved_impl_wf _ _ (proj1_sig Himp)); wf_auto2.
Defined.


Ltac _mlApplyMetaRaw t :=
  eapply (@MLGoal_applyMeta _ _ _ _ _ t).

Tactic Notation "mlApplyMetaRaw" uconstr(t) :=
  _mlApplyMetaRaw t.

Ltac2 _mlApplyMetaRaw (t : constr) :=
  eapply (@MLGoal_applyMeta _ _ _ _ _ $t).

Lemma MLGoal_left {Σ : Signature} Γ l x y i:
  mkMLGoal Σ Γ l x i ->
  mkMLGoal Σ Γ l (patt_or x y) i.
Proof.
  intros H.
  unfold of_MLGoal in *. simpl in *.
  intros wfxy wfl.
  eapply prf_weaken_conclusion_iter_meta_meta.
  4: { useBasicReasoning. apply disj_left_intro. wf_auto2. wf_auto2. }
  { wf_auto2. }
  { wf_auto2. }
  { wf_auto2. }
  apply H.
  { wf_auto2. }
  { assumption. }
Defined.

Lemma MLGoal_right {Σ : Signature} Γ l x y i:
  mkMLGoal Σ Γ l y i ->
  mkMLGoal Σ Γ l (patt_or x y) i.
Proof.
  intros H.
  unfold of_MLGoal in *. simpl in *.
  intros wfxy wfl.
  eapply prf_weaken_conclusion_iter_meta_meta.
  4: { useBasicReasoning. apply disj_right_intro. wf_auto2. wf_auto2. }
  { wf_auto2. }
  { wf_auto2. }
  { wf_auto2. }
  apply H.
  { wf_auto2. }
  { assumption. }
Defined.

Ltac mlLeft := apply MLGoal_left.
Ltac mlRight := apply MLGoal_right.

Local Example ex_mlLeft {Σ : Signature} Γ a:
  well_formed a ->
  Γ ⊢i a ---> (a or a)
  using BasicReasoning.
Proof.
  intros wfa.
  toMLGoal.
  { wf_auto2. }
  mlIntro "H0".
  mlLeft.
  mlExact "H0".
Defined.

Lemma MLGoal_applyMetaIn {Σ : Signature} Γ n r n' r' i:
  Γ ⊢i (r ---> r') using i ->
  forall l₁ l₂ g,
    mkMLGoal Σ Γ (l₁ ++ (mkNH _ n' r')::l₂) g i ->
    mkMLGoal Σ Γ (l₁ ++ (mkNH _ n r)::l₂ ) g i.
Proof.
  intros Himp l₁ l₂ g H.
  unfold of_MLGoal in *. simpl in *.
  intros wfg Hwf.
  specialize (H wfg).
  unfold patterns_of in *.
  rewrite map_app in H.
  rewrite map_app.
  eapply prf_strenghten_premise_iter_meta_meta.
  6: apply Himp.
  6: apply H.
  all: rewrite map_app in Hwf.
  { abstract (apply wfapp_proj_1 in Hwf; exact Hwf). }
  { abstract (apply wfl₁hl₂_proj_l₂ in Hwf; exact Hwf). }
  { abstract (pose proof (Himp' := proj1_sig Himp); apply proved_impl_wf in Himp'; wf_auto2). }
  { abstract (apply wfl₁hl₂_proj_h in Hwf; exact Hwf). }
  { exact wfg. }
  { abstract(
      pose proof (wfapp_proj_1 _ _ Hwf);
      pose proof (wfl₁hl₂_proj_l₂ _ _ _ Hwf);
      pose proof (wfl₁hl₂_proj_h _ _ _ Hwf);
      unfold Pattern.wf;
      rewrite map_app;
      rewrite foldr_app;
      simpl;
      pose proof (Himp' := proj1_sig Himp);
      apply proved_impl_wf in Himp';
      apply well_formed_imp_proj2 in Himp';
      rewrite Himp';
      simpl;
      unfold Pattern.wf in H1;
      rewrite H1;
      exact H0
    ).
 }
Defined.

Ltac _mlApplyMetaRawIn t name :=
  eapply cast_proof_ml_hyps;
  f_equal;
  _mlReshapeHypsByName name;
  eapply (@MLGoal_applyMetaIn _ _ _ _ name _ _ t);
  _mlReshapeHypsBack.

Ltac2 _mlApplyMetaRawIn (t : constr) (name : constr) :=
  ltac1:(t' name' |- _mlApplyMetaRawIn t' name')
    (Ltac1.of_constr t)
    (Ltac1.of_constr name)
.

Tactic Notation "mlApplyMetaRaw" uconstr(t) "in" constr(name) :=
  _mlApplyMetaRawIn t name.


Local Example Private_ex_mlApplyMetaRawIn {Σ : Signature} Γ p q:
  well_formed p ->
  well_formed q ->
  Γ ⊢i p ---> (p or q)
  using BasicReasoning.
Proof.
  intros wfp wfq.
  toMLGoal.
  { wf_auto2. }
  mlIntro "H0".
  mlApplyMetaRaw (disj_left_intro Γ p q ltac:(wf_auto2) ltac:(wf_auto2)) in "H0".
  mlExact "H0".
Defined.

Ltac2 rec applyRec (f : constr) (xs : constr list) : constr option :=
  match xs with
  | [] => Some f
  | y::ys =>
    lazy_match! Constr.type f with
    | (forall _ : ?t, _) =>
      Control.plus (fun () => applyRec constr:($f $y) ys) (fun _ => None)
    | _ => None
    end
  end.

Ltac2 Eval (applyRec constr:(Nat.add) [constr:(1);constr:(2)]).

(*
  All thic complicated code is here only for one reason:
  I want to be able to first run the tactic with all the parameters
  inferred or question marked, which results in another goal.
  And then I want to handle the subgoals generated by the filling-in
  underscores / question marks.
  In particular, I want the proof mode goals to be generated first,
  and the other, uninteresting goals, next.
*)
Ltac2 rec fillWithUnderscoresAndCall
  (tac : constr -> unit) (t : constr) (args : constr list) :=
  (*
  Message.print (
    Message.concat
      (Message.of_string "fillWithUnderscoresAndCall: t = ")
      (Message.of_constr t)
  );
  Message.print (
    Message.concat
      (Message.of_string "fillWithUnderscoresAndCall: args = ")
      (List.fold_right (Message.concat) (Message.of_string "") (List.map Message.of_constr args))
  );
  *)
  let cont := (fun () =>
    lazy_match! Constr.type t with
    | (?t' -> ?t's) =>
      lazy_match! goal with
      | [|- ?g] =>
        let h := Fresh.in_goal ident:(h) in
        assert(h : $t' -> $g) > [(
          let pftprime := Fresh.in_goal ident:(pftprime) in
          intro $pftprime;
          let new_t := open_constr:($t ltac2:(Notations.exact0 false (fun () => Control.hyp (pftprime)))) in
          fillWithUnderscoresAndCall tac new_t args;
          Std.clear [pftprime]
        )|(apply &h)
        ]
      end
    | (forall _ : _, _) => fillWithUnderscoresAndCall tac open_constr:($t _) args
    | ?remainder => throw (Invalid_argument (Some (Message.concat (Message.concat (Message.of_string "Remainder type: ") (Message.of_constr remainder)) (Message.concat (Message.of_string ", of term") (Message.of_constr t)))))
    end
  ) in
  match (applyRec t args) with
  | None =>
    (* Cannot apply [t] to [args] => continue *)
    cont ()
  | Some result =>
    (* Can apply [to] to [args], *)
    lazy_match! Constr.type result with
    | (forall _ : _, _) =>
      (* but result would still accept an argument => continue *)
      cont ()
    | _ =>
      (* and nothing more can be applied to the result => we are done *)
      tac result
    end
  end
.

(*
  We have this double-primed version because we want to be able
  to feed it the proof before feeding it the ProofInfoLe.
*)
Lemma useGenericReasoning''  {Σ : Signature} (Γ : Theory) (ϕ : Pattern) i' i:
  Γ ⊢i ϕ using i' ->
  (ProofInfoLe i' i) ->
  Γ ⊢i ϕ using i.
Proof.
  intros H pile.
  eapply useGenericReasoning'.
  { apply pile. }
  apply H.
Defined.

Ltac2 _callCompletedAndCast (t : constr) (tac : constr -> unit) :=
  let tac' := (fun (t' : constr) =>
    let tcast := open_constr:(@useGenericReasoning'' _ _ _ _ _ $t') in
    fillWithUnderscoresAndCall tac tcast []
  ) in
  fillWithUnderscoresAndCall tac' t []
.

Ltac2 try_solve_pile_basic () :=
  Control.enter (fun () =>
    lazy_match! goal with
    | [ |- (@ProofInfoLe _ _ _)] =>
        try (solve
          [ apply pile_any
          | apply pile_refl
          | apply pile_basic_generic'
       ])
    | [|- _] => ()
    end
  )
.

Ltac2 try_wfa () :=
  Control.enter (fun () =>
    let wfa := (fun p =>
      if (Constr.has_evar p) then
        ()
      else
        ltac1:(try_wfauto2)
    ) in
    lazy_match! goal with
    | [|- well_formed ?p = true] => wfa p
    | [|- is_true (well_formed ?p) ] => wfa p
    | [|- Pattern.wf ?l = true] => wfa l
    | [|- is_true (Pattern.wf ?l) ] => wfa l
    | [|- _] => ()
    end
  )
.

Ltac2 mlApplyMeta (t : constr) :=
  _callCompletedAndCast t _mlApplyMetaRaw ;
  try_solve_pile_basic ();
  try_wfa ()
.

Ltac2 mlApplyMetaIn (t : constr) (name : constr) :=
  _callCompletedAndCast t (fun t =>
    _mlApplyMetaRawIn t name
  );
  try_solve_pile_basic ();
  try_wfa ()
.

Ltac _mlApplyMeta t :=
  let ff := ltac2:(t' |- mlApplyMeta (Option.get (Ltac1.to_constr(t')))) in
  ff t.

Ltac _mlApplyMetaIn t name :=
  let ff := ltac2:(t' name' |- mlApplyMetaIn (Option.get (Ltac1.to_constr(t'))) (Option.get (Ltac1.to_constr(name')))) in
  ff t name
.

Tactic Notation "mlApplyMeta" constr(t) :=
  _mlApplyMeta t.

Tactic Notation "mlApplyMeta" constr(t) "in" constr(name) :=
  _mlApplyMetaIn t name
.


Lemma MLGoal_destructAnd {Σ : Signature} Γ g l₁ l₂ nx x ny y nxy i:
    mkMLGoal Σ Γ (l₁ ++ (mkNH _ nx x)::(mkNH _ ny y)::l₂ ) g i ->
    mkMLGoal Σ Γ (l₁ ++ (mkNH _ nxy (x and y))::l₂) g i.
Proof.
  intros H.
  unfold of_MLGoal. intros wfg Hwf. pose proof (wfg' := wfg). pose proof (Hwf' := Hwf).
  revert wfg' Hwf'.
  cut (of_MLGoal (mkMLGoal Σ Γ (l₁ ++ (mkNH _ nxy (x and y))::l₂ ) g i)).
  { auto. }
  simpl in wfg, Hwf.

  mlAssert (ny : y) using first (length (l₁ ++ [mkNH _ nxy (x and y)])).

  all: unfold patterns_of in Hwf; rewrite map_app in Hwf.

  { abstract (
      apply wfapp_proj_2 in Hwf;
      unfold Pattern.wf in Hwf;
      simpl in Hwf;
      apply andb_prop in Hwf;
      destruct Hwf as [wfxy _];
      wf_auto2
    ).
  }
  {
    eapply cast_proof_ml_hyps.
    { replace (l₁ ++ (mkNH _ nxy (x and y)) :: l₂) with ((l₁ ++ [mkNH _ nxy (x and y)]) ++ l₂).
      2: { rewrite -app_assoc. reflexivity. }
      rewrite take_app.
      reflexivity.
    }
    assert (well_formed x).
    {
      abstract (
        apply wfapp_proj_2 in Hwf;
        unfold Pattern.wf in Hwf;
        simpl in Hwf;
        apply andb_prop in Hwf as [wfxy _];
        wf_auto2
      ).
    }

    mlApplyMeta pf_conj_elim_r.
    apply MLGoal_exactn.
    wf_auto2.
  }

  eapply cast_proof_ml_hyps.
  {
    replace (l₁ ++ (mkNH _ nxy (x and y)) :: l₂) with ((l₁ ++ [mkNH _ nxy (x and y)]) ++ l₂).
    2: { rewrite -app_assoc. reflexivity. }
    rewrite take_app. rewrite drop_app. reflexivity.
  }

  mlAssert (nx : x) using first (length (l₁ ++ [mkNH _ nxy (x and y)])).
  { abstract (
      apply wfapp_proj_2 in Hwf;
      unfold Pattern.wf in Hwf;
      simpl in Hwf;
      apply andb_prop in Hwf;
      destruct Hwf as [wfxy _];
      wf_auto2
    ).
  }
  {
    eapply cast_proof_ml_hyps.
    {
      replace (l₁ ++ (mkNH _ nxy (x and y)) :: l₂) with ((l₁++ [mkNH _ nxy (x and y)]) ++ l₂).
      2: { rewrite -app_assoc. reflexivity. }
      rewrite take_app.
      reflexivity.
    }
    assert (well_formed x).
    {
      abstract (
        apply wfapp_proj_2 in Hwf;
        unfold Pattern.wf in Hwf;
        simpl in Hwf;
        apply andb_prop in Hwf as [wfxy _];
        wf_auto2
      ).
    }
    mlApplyMeta pf_conj_elim_l.
    apply MLGoal_exactn.
    assumption.
  }

  eapply cast_proof_ml_hyps.
  {
    replace (l₁ ++ (mkNH _ nxy (x and y)) :: l₂) with ((l₁++ [mkNH _ nxy (x and y)]) ++ l₂).
    2: { rewrite -app_assoc. reflexivity. }
    rewrite take_app. rewrite drop_app. reflexivity.
  }

  eapply cast_proof_ml_hyps.
  {
    rewrite -app_assoc. reflexivity.
  }

 apply mlGoal_clear_hyp.
 exact H.
Defined.

Tactic Notation "mlDestructAnd" constr(name) "as" constr(name1) constr(name2) :=
  _failIfUsed name1; _failIfUsed name2;
  eapply cast_proof_ml_hyps;
  f_equal;
  _mlReshapeHypsByName name;
  apply MLGoal_destructAnd with (nxy := name) (nx := name1) (ny := name2);
  _mlReshapeHypsBack.

Tactic Notation "mlDestructAnd" constr(name) :=
  let hyps := _getHypNames in
  let name0 := eval cbv in (fresh hyps) in
  let name1 := eval cbv in (fresh (name0 :: hyps)) in
  mlDestructAnd name as name0 name1.

Local Example ex_mlDestructAnd {Σ : Signature} Γ a b p q:
  well_formed a ->
  well_formed b ->
  well_formed p ->
  well_formed q ->
  Γ ⊢i p and q ---> a and b ---> q ---> a
  using BasicReasoning.
Proof.
  intros. toMLGoal.
  { wf_auto2. }
  mlIntro "H0". mlIntro "H1". mlIntro "H2".
  mlDestructAnd "H1" as "H3" "H4".
  mlDestructAnd "H0".
  mlExact "H3".
Defined.

 
Lemma and_of_equiv_is_equiv {Σ : Signature} Γ p q p' q' i:
  well_formed p ->
  well_formed q ->
  well_formed p' ->
  well_formed q' ->
  Γ ⊢i (p <---> p') using i ->
  Γ ⊢i (q <---> q') using i ->
  Γ ⊢i ((p and q) <---> (p' and q')) using i.
Proof.
  intros wfp wfq wfp' wfq' pep' qeq'.
  pose proof (pip' := pep'). apply pf_conj_elim_l_meta in pip'; auto.
  pose proof (p'ip := pep'). apply pf_conj_elim_r_meta in p'ip; auto.
  pose proof (qiq' := qeq'). apply pf_conj_elim_l_meta in qiq'; auto.
  pose proof (q'iq := qeq'). apply pf_conj_elim_r_meta in q'iq; auto.

  apply conj_intro_meta; auto.
  - toMLGoal.
    { wf_auto2. }
    mlIntro "H0". unfold patt_and.
    mlIntro "H1". mlApply "H0".
    mlDestructOr "H1" as "H2" "H3".
    + apply modus_tollens in pip'; auto 10.
      mlAdd pip' as "H1".
      mlLeft.
      mlApply "H1".
      mlExact "H2".
    + apply modus_tollens in qiq'; auto 10.
      mlAdd qiq' as "H1".
      mlRight.
      mlApply "H1".
      mlExact "H3".
  - toMLGoal.
    { wf_auto2. }
    mlIntro "H0". unfold patt_and.
    mlIntro "H1". mlApply "H0".
    mlDestructOr "H1" as "H2" "H3".
    + mlLeft.
      apply modus_tollens in p'ip; auto.
      mlAdd p'ip as "H1".
      mlApply "H1".
      mlExact "H2".
    + mlRight.
      apply modus_tollens in q'iq; auto.
      mlAdd q'iq as "H1".
      mlApply "H1".
      mlExact "H3".
Defined. 

Lemma or_of_equiv_is_equiv {Σ : Signature} Γ p q p' q' i:
  well_formed p ->
  well_formed q ->
  well_formed p' ->
  well_formed q' ->
  Γ ⊢i (p <---> p') using i ->
  Γ ⊢i (q <---> q') using i ->
  Γ ⊢i ((p or q) <---> (p' or q')) using i.
Proof with try_wfauto2.
  intros wfp wfq wfp' wfq' pep' qeq'.
  pose proof (pip' := pep'). apply pf_conj_elim_l_meta in pip'...
  pose proof (p'ip := pep'). apply pf_conj_elim_r_meta in p'ip...
  pose proof (qiq' := qeq'). apply pf_conj_elim_l_meta in qiq'...
  pose proof (q'iq := qeq'). apply pf_conj_elim_r_meta in q'iq...

  apply conj_intro_meta; auto.
  - toMLGoal.
    { auto. }
    mlIntro "H0".
    mlDestructOr "H0" as "H1" "H2".
    + mlLeft. fromMLGoal. assumption.
    + mlRight. fromMLGoal. assumption.
  - toMLGoal.
    { auto. }
    mlIntro "H0".
    mlDestructOr "H0" as "H1" "H2".
    + mlLeft. fromMLGoal. assumption.
    + mlRight. fromMLGoal. assumption.
Defined.


Lemma impl_iff_notp_or_q {Σ : Signature} Γ p q:
  well_formed p ->
  well_formed q ->
  Γ ⊢i ((p ---> q) <---> (! p or q))
  using BasicReasoning.
Proof.
  intros wfp wfq.
  apply conj_intro_meta; auto.
  - toMLGoal.
    { wf_auto2. }
    mlIntro "H0".
    mlAdd (A_or_notA Γ p wfp) as "H1".
    mlDestructOr "H1" as "H2" "H3".
    + mlRight.
      mlApply "H0".
      mlExact "H2".
    + mlLeft.
      mlExact "H3".
  - toMLGoal.
    { wf_auto2. }
    mlIntro "H0". mlIntro "H2". unfold patt_or.
    mlApply "H0".
    mlApplyMeta not_not_intro.
    mlExact "H2".
Defined.

Lemma p_and_notp_is_bot {Σ : Signature} Γ p:
  well_formed p ->
  Γ ⊢i (⊥ <---> p and ! p)
  using BasicReasoning.
Proof.
  intros wfp.
  apply conj_intro_meta; auto.
  - apply bot_elim; auto.
  - unfold patt_and.
    toMLGoal.
    { wf_auto2. }
    mlIntro "H0".
    mlApply "H0".
    mlAdd (A_or_notA Γ (! p) ltac:(wf_auto2)) as "H1".
    mlExact "H1".
Defined.

Ltac mlExFalso :=
  mlApplyMeta bot_elim
.


Lemma weird_lemma  {Σ : Signature} Γ A B L R:
  well_formed A ->
  well_formed B ->
  well_formed L ->
  well_formed R ->
  Γ ⊢i (((L and A) ---> (B or R)) ---> (L ---> ((A ---> B) or R)))
  using BasicReasoning.
Proof.
  intros wfA wfB wfL wfR.
  toMLGoal.
  { wf_auto2. }
  mlIntro "H0". mlIntro "H1".
  mlAdd (A_or_notA Γ A wfA) as "H2".
  mlDestructOr "H2" as "H3" "H4".
  - mlAssert ("H2" : (B or R)).
    { wf_auto2. }
    { mlApply "H0".
      unfold patt_and at 2.
      mlIntro "H2".
      mlDestructOr "H2" as "H4" "H5".
      + mlApply "H4". mlExact "H1".
      + mlApply "H5". mlExact "H3".
    }
    mlDestructOr "H2" as "H4" "H5".
    + mlLeft. mlIntro "H2". mlExact "H4".
    + mlRight. mlExact "H5".
  - mlLeft.
    mlIntro "H2".
    mlExFalso.
    mlApply "H4". mlExact "H2".
Defined.

Lemma weird_lemma_meta {Σ : Signature} Γ A B L R i:
  well_formed A ->
  well_formed B ->
  well_formed L ->
  well_formed R ->
  Γ ⊢i ((L and A) ---> (B or R)) using i ->
  Γ ⊢i (L ---> ((A ---> B) or R)) using i.
Proof.
  intros WFA WFB WFL WFR H.
  eapply MP.
  2: { useBasicReasoning. apply weird_lemma; assumption. }
  exact H.
Defined.

Lemma imp_trans_mixed_meta {Σ : Signature} Γ A B C D i :
  well_formed A -> well_formed B -> well_formed C -> well_formed D ->
  Γ ⊢i (C ---> A) using i ->
  Γ ⊢i (B ---> D) using i ->
  Γ ⊢i ((A ---> B) ---> C ---> D) using i.
Proof.
  intros WFA WFB WFC WFD H H0.
  epose proof (H1 := prf_weaken_conclusion Γ A B D WFA WFB WFD).
  eapply useBasicReasoning in H1.
  eapply MP in H1.
  2: { exact H0. }
  epose proof (H2 := prf_strenghten_premise Γ A C D WFA WFC WFD).
  eapply useBasicReasoning in H2.
  eapply MP in H2.
  2: { exact H. }
  epose proof (H3 := syllogism_meta _ _ _ H1 H2).
  exact H3.
  Unshelve. all: wf_auto2.
Defined.

Lemma and_weaken {Σ : Signature} A B C Γ i:
  well_formed A -> well_formed B -> well_formed C ->
  Γ ⊢i (B ---> C) using i ->
  Γ ⊢i ((A and B) ---> (A and C)) using i.
Proof.
  intros WFA WFB WFC H.
  epose proof (H0 := and_impl' Γ A B (A and C) _ _ _).
  eapply MP. 2: { useBasicReasoning. exact H0. }
  apply reorder_meta.
  1-3: wf_auto2.
  epose proof (H1 := prf_strenghten_premise Γ C B (A ---> A and C) _ _ _).
  eapply MP.
  2: eapply MP.
  3: { useBasicReasoning. exact H1. }
  2: { exact H. }
  useBasicReasoning.
  apply conj_intro2; assumption.
  Unshelve.
  all: wf_auto2.
Defined.

Lemma impl_and {Σ : Signature} Γ A B C D i: 
  well_formed A -> well_formed B -> well_formed C -> well_formed D ->
  Γ ⊢i (A ---> B) using i ->
  Γ ⊢i (C ---> D) using i ->
  Γ ⊢i (A and C) ---> (B and D) using i.
Proof.
  intros WFA WFB WFC WFD H H0.
  toMLGoal.
  { wf_auto2. }
  {
    mlAdd H as "H0".
    mlAdd H0 as "H1".
    mlIntro "H2".
    mlDestructAnd "H2" as "H3" "H4".
    mlIntro "H5".
    mlDestructOr "H5" as "H6" "H7".
    {
      mlApply "H6".
      mlApply "H0".
      mlExact "H3".
    }
    {
      mlApply "H7".
      mlApply "H1".
      mlExact "H4".
    }
  }
Defined.

Lemma and_drop {Σ : Signature} A B C Γ i:
  well_formed A -> well_formed B -> well_formed C ->
  Γ ⊢i ((A and B) ---> C) using i ->
  Γ ⊢i ((A and B) ---> (A and C)) using i.
Proof.
  intros WFA WFB WFC H.
  toMLGoal.
  { wf_auto2. }
  mlAdd H as "H0".
  mlIntro "H1".
  mlIntro "H2".
  mlDestructOr "H2" as "H3" "H4".
  {
    mlDestructAnd "H1" as "H5" "H6".
    mlApply "H3".
    mlExact "H5".
  }
  {
    mlApply "H4".
    mlApply "H0".
    mlExact "H1".
  }
Defined.


Lemma prf_equiv_of_impl_of_equiv {Σ : Signature} Γ a b a' b' i:
  well_formed a = true ->
  well_formed b = true ->
  well_formed a' = true ->
  well_formed b' = true ->
  Γ ⊢i (a <---> a') using i ->
  Γ ⊢i (b <---> b') using i ->
  Γ ⊢i (a ---> b) <---> (a' ---> b') using i.
Proof.
  intros wfa wfb wfa' wfb' Haa' Hbb'.
  unshelve(epose proof (Haa'1 := pf_conj_elim_l_meta _ _ _ _ _ _ Haa')).
  { wf_auto2. }
  { wf_auto2. }
  unshelve(epose proof (Haa'2 := pf_conj_elim_r_meta _ _ _ _ _ _ Haa')).
  { wf_auto2. }
  { wf_auto2. }
  unshelve(epose proof (Hbb'1 := pf_conj_elim_l_meta _ _ _ _ _ _ Hbb')).
  { wf_auto2. }
  { wf_auto2. }
  unshelve(epose proof (Hbb'2 := pf_conj_elim_r_meta _ _ _ _ _ _ Hbb')).
  { wf_auto2. }
  { wf_auto2. }

  apply pf_iff_equiv_trans with (B := (a ---> b')).
  1-3: wf_auto2.
    + apply conj_intro_meta.
      1-2: wf_auto2.
      * toMLGoal.
        { wf_auto2. }
        mlIntro "H0". mlIntro "H1".
        mlAdd Hbb'1 as "H2".
        mlApply "H2".
        mlApply "H0".
        mlExact "H1".
      * toMLGoal.
        { wf_auto2. }
        mlIntro "H0". mlIntro "H1".
        mlAdd Hbb'2 as "H2".
        mlApply "H2".
        mlApply "H0".
        mlExact "H1".
    + apply conj_intro_meta.
      1-2: wf_auto2.
      * toMLGoal.
        { wf_auto2. }
        mlIntro "H0". mlIntro "H1".
        mlAdd Haa'2 as "H2".
        mlApply "H0".
        mlApply "H2".
        mlExact "H1".
      * toMLGoal.
        { wf_auto2. }
        mlIntro "H0". mlIntro "H1".
        mlAdd Haa'1 as "H2".
        mlApply "H0".
        mlApply "H2".
        mlExact "H1".
Defined.



Lemma lhs_to_and {Σ : Signature} Γ a b c i:
  well_formed a ->
  well_formed b ->
  well_formed c ->
  Γ ⊢i (a and b) ---> c using i ->
  Γ ⊢i a ---> b ---> c using i.
Proof.
  intros wfa wfb wfc H.
  toMLGoal.
  { wf_auto2. }
  mlIntro "H0". mlIntro "H1".
  mlApplyMeta H.
  fromMLGoal.
  useBasicReasoning.
  apply conj_intro.
  { wf_auto2. }
  { wf_auto2. }
Defined.

Lemma lhs_from_and {Σ : Signature} Γ a b c i:
  well_formed a ->
  well_formed b ->
  well_formed c ->
  Γ ⊢i a ---> b ---> c using i ->
  Γ ⊢i (a and b) ---> c using i.
Proof.
  intros wfa wfb wfc H.
  toMLGoal.
  { wf_auto2. }
  mlIntro "H0".
  mlAssert ("H1" : b).
  { wf_auto2. }
  { fromMLGoal. useBasicReasoning. apply pf_conj_elim_r.
    wf_auto2. wf_auto2.
  }
  mlAssert ("H2" : a) using first 1.
  { wf_auto2. }
  { fromMLGoal. useBasicReasoning. apply pf_conj_elim_l; wf_auto2. }
  mlAdd H as "H3".
  mlAssert ("H4" : (b ---> c)).
  { wf_auto2. }
  { mlApply "H3". mlExact "H2". }
  mlApply "H4".
  mlExact "H1".
Defined.

Lemma prf_conj_split {Σ : Signature} Γ a b l:
  well_formed a ->
  well_formed b ->
  Pattern.wf l ->
  Γ ⊢i (foldr patt_imp a l) ---> (foldr patt_imp b l) ---> (foldr patt_imp (a and b) l)
  using BasicReasoning.
Proof.
  intros wfa wfb wfl.
  induction l.
  - simpl. apply conj_intro; assumption.
  - simpl. pose proof (wfl' := wfl). unfold Pattern.wf in wfl'. simpl in wfl'. apply andb_prop in wfl' as [wfa0 wfl'].
    specialize (IHl wfl').
    toMLGoal.
    { wf_auto2. }
    mlIntro "H0". mlIntro "H1". mlIntro "H2".
    mlAssert ("H3" : (foldr patt_imp a l)).
    { wf_auto2. }
    { mlApply "H0". mlExact "H2". }
    mlAssert ("H4" : (foldr patt_imp b l)).
    { wf_auto2. }
    { mlApply "H1". mlExact "H2". }
    mlClear "H2". mlClear "H1". mlClear "H0".
    fromMLGoal. apply IHl.
Defined.

Lemma prf_conj_split_meta {Σ : Signature} Γ a b l (i : ProofInfo):
  well_formed a ->
  well_formed b ->
  Pattern.wf l ->
  Γ ⊢i (foldr patt_imp a l) using i -> 
  Γ ⊢i (foldr patt_imp b l) ---> (foldr patt_imp (a and b) l) using i.
Proof.
  intros. eapply MP. 2: { useBasicReasoning. apply prf_conj_split; assumption. }
  exact H2.
Defined.

Lemma prf_conj_split_meta_meta {Σ : Signature} Γ a b l (i : ProofInfo):
  well_formed a ->
  well_formed b ->
  Pattern.wf l ->
  Γ ⊢i (foldr patt_imp a l) using i -> 
  Γ ⊢i (foldr patt_imp b l) using i ->
  Γ ⊢i (foldr patt_imp (a and b) l) using i.
Proof.
  intros. eapply MP.
  2: {
    apply prf_conj_split_meta; assumption.
  }
  exact H3.
Defined.

Lemma MLGoal_splitAnd {Σ : Signature} Γ a b l i:
  mkMLGoal Σ Γ l a i ->
  mkMLGoal Σ Γ l b i ->
  mkMLGoal Σ Γ l (a and b) i.
Proof.
  intros Ha Hb.
  unfold of_MLGoal in *. simpl in *.
  intros wfab wfl.
  feed specialize Ha.
  { abstract(wf_auto2). }
  { exact wfl. }
  feed specialize Hb.
  { abstract(wf_auto2). }
  { exact wfl. }
  apply prf_conj_split_meta_meta; auto.
  { abstract (wf_auto2). }
  { abstract (wf_auto2). }
Defined.

Ltac mlSplitAnd := apply MLGoal_splitAnd.

Local Lemma ex_mlSplitAnd {Σ : Signature} Γ a b c:
  well_formed a ->
  well_formed b ->
  well_formed c ->
  Γ ⊢i a ---> b ---> c ---> (a and b)
  using BasicReasoning.
Proof.
  intros wfa wfb wfc.
  toMLGoal.
  { wf_auto2. }
  mlIntro "H0". mlIntro "H1". mlIntro "H2".
  mlSplitAnd.
  - mlExact "H0".
  - mlExact "H1".
Defined.

Lemma prf_local_goals_equiv_impl_full_equiv {Σ : Signature} Γ g₁ g₂ l:
  well_formed g₁ ->
  well_formed g₂ ->
  Pattern.wf l ->
  Γ ⊢i (foldr patt_imp (g₁ <---> g₂) l) --->
      ((foldr patt_imp g₁ l) <---> (foldr patt_imp g₂ l))
  using BasicReasoning.
Proof.
  intros wfg₁ wfg₂ wfl.
  induction l; simpl.
  - apply A_impl_A; wf_auto2.
  - pose proof (wfl' := wfl). unfold Pattern.wf in wfl'. simpl in wfl'. apply andb_prop in wfl' as [wfa wfl'].
    specialize (IHl wfl').
    toMLGoal.
    { wf_auto2. }
    mlIntro "H0". mlSplitAnd.
    + mlApplyMeta P2.
      mlRevertLast.
      mlApplyMeta P2.
      mlIntro "H0". mlClear "H0". mlIntro "H0".
      mlApplyMeta IHl in "H0".
      unfold patt_iff at 1. mlDestructAnd "H0" as "H1" "H2".
      mlExact "H1".
    + mlApplyMeta P2.
      mlRevertLast.
      mlApplyMeta P2.
      mlIntro "H0". mlClear "H0". mlIntro "H0".
      mlApplyMeta IHl in "H0".
      unfold patt_iff at 1. mlDestructAnd "H0" as "H1" "H2".
      mlExact "H2".
Defined.

Lemma prf_local_goals_equiv_impl_full_equiv_meta {Σ : Signature} Γ g₁ g₂ l i:
  well_formed g₁ ->
  well_formed g₂ ->
  Pattern.wf l ->
  Γ ⊢i (foldr patt_imp (g₁ <---> g₂) l) using i ->
  Γ ⊢i ((foldr patt_imp g₁ l) <---> (foldr patt_imp g₂ l)) using i.
Proof.
  intros wfg₁ wfg₂ wfl H.
  eapply MP.
  2: { useBasicReasoning. apply prf_local_goals_equiv_impl_full_equiv; assumption. }
  exact H.
Defined.

Lemma prf_local_goals_equiv_impl_full_equiv_meta_proj1 {Σ : Signature} Γ g₁ g₂ l i:
  well_formed g₁ ->
  well_formed g₂ ->
  Pattern.wf l ->
  Γ ⊢i (foldr patt_imp (g₁ <---> g₂) l) using i ->
  Γ ⊢i (foldr patt_imp g₁ l) using i ->
  Γ ⊢i (foldr patt_imp g₂ l) using i.
Proof.
  intros wfg₁ wfg₂ wfl H1 H2.
  eapply MP.
  2: eapply pf_iff_proj1.
  4: apply prf_local_goals_equiv_impl_full_equiv_meta.
  7: apply H1.
  1: exact H2.
  all: wf_auto2.
Defined.

Lemma prf_local_goals_equiv_impl_full_equiv_meta_proj2 {Σ : Signature} Γ g₁ g₂ l i:
  well_formed g₁ ->
  well_formed g₂ ->
  Pattern.wf l ->
  Γ ⊢i (foldr patt_imp (g₁ <---> g₂) l) using i ->
  Γ ⊢i (foldr patt_imp g₂ l) using i ->
  Γ ⊢i (foldr patt_imp g₁ l) using i.
Proof.
  intros wfg₁ wfg₂ wfl H1 H2.
  eapply MP.
  2: eapply pf_iff_proj2.
  4: apply prf_local_goals_equiv_impl_full_equiv_meta.
  7: apply H1.
  1: exact H2.
  all: wf_auto2.
Defined.



Lemma top_holds {Σ : Signature} Γ:
  Γ ⊢i Top using BasicReasoning.
Proof.
  apply bot_elim.
  { wf_auto2. }
Defined.

Lemma phi_iff_phi_top {Σ : Signature} Γ ϕ :
  well_formed ϕ ->
  Γ ⊢i ϕ <---> (ϕ <---> Top)
  using BasicReasoning.
Proof.
  intros wfϕ.
  toMLGoal.
  { wf_auto2. }
  mlSplitAnd; mlIntro "H0".
  - mlSplitAnd.
    + mlIntro "H1". mlClear "H1". mlClear "H0".
      fromMLGoal.
      apply top_holds. (* TODO: we need something like [mlExactMeta top_holds] *)
    + fromMLGoal.
      apply P1; wf_auto2.
  - mlDestructAnd "H0" as "H1" "H2".
    mlApply "H2".
    mlClear "H2".
    mlClear "H1".
    fromMLGoal.
    apply top_holds.
Defined.

Lemma not_phi_iff_phi_bott {Σ : Signature} Γ ϕ :
  well_formed ϕ ->
  Γ ⊢i (! ϕ ) <---> (ϕ <---> ⊥)
  using BasicReasoning.
Proof.
  intros wfϕ.
  toMLGoal.
  { wf_auto2. }
  mlSplitAnd; mlIntro "H0".
  - mlSplitAnd.
    + mlExact "H0".
    + mlClear "H0". fromMLGoal.
      apply bot_elim.
      { wf_auto2. }
  - mlDestructAnd "H0" as "H1" "H2".
    mlExact "H1".
Defined.

Lemma not_not_iff {Σ : Signature} (Γ : Theory) (A : Pattern) :
  well_formed A ->
  Γ ⊢i A <---> ! ! A
  using BasicReasoning.
Proof.
  intros wfA.
  apply pf_iff_split.
  { wf_auto2. }
  { wf_auto2. }
  - apply not_not_intro.
    { wf_auto2. }
  - apply not_not_elim.
    { wf_auto2. }
Defined.


Lemma patt_and_comm {Σ : Signature} Γ p q:
  well_formed p ->
  well_formed q ->
  Γ ⊢i (p and q) <---> (q and p)
  using BasicReasoning.
Proof.
  intros wfp wfq.
  toMLGoal.
  { wf_auto2. }
  mlSplitAnd; mlIntro "H0"; mlDestructAnd "H0" as "H1" "H2"; mlSplitAnd.
  - mlExact "H2".
  - mlExact "H1".
  - mlExact "H2".
  - mlExact "H1".
Defined.



(* We need to come up with tactics that make this easier. *)
Local Example ex_mt {Σ : Signature} Γ ϕ₁ ϕ₂:
  well_formed ϕ₁ ->
  well_formed ϕ₂ ->
  Γ ⊢i (! ϕ₁ ---> ! ϕ₂) ---> (ϕ₂ ---> ϕ₁)
  using BasicReasoning.
Proof.
  intros wfϕ₁ wfϕ₂.
  toMLGoal.
  { wf_auto2. }
  mlIntro "H0". mlIntro "H1".
  unfold patt_not.
  mlAssert ("H2" : ((ϕ₁ ---> ⊥) ---> ⊥)).
  { wf_auto2. }
  { mlIntro "H2".
    mlAssert ("H3" : (ϕ₂ ---> ⊥)).
    { wf_auto2. }
    { mlApply "H0". mlExact "H2". }
    mlApply "H3".
    mlExact "H1".
  }
  mlApplyMeta not_not_elim.
  mlExact "H2".
Defined.

Lemma lhs_and_to_imp {Σ : Signature} Γ (g x : Pattern) (xs : list Pattern):
  well_formed g ->
  well_formed x ->
  Pattern.wf xs ->
  Γ ⊢i (foldr patt_and x xs ---> g) ---> (foldr patt_imp g (x :: xs))
  using BasicReasoning.
Proof.
  intros wfg wfx wfxs.
  induction xs; simpl.
  - apply A_impl_A.
    { wf_auto2. }
  - pose proof (wfaxs := wfxs).
    unfold Pattern.wf in wfxs.
    simpl in wfxs.
    apply andb_prop in wfxs as [wfa wfxs].
    fold (Pattern.wf xs) in wfxs.
    specialize (IHxs wfxs).
    simpl in IHxs.
    assert (Hwffa: well_formed (foldr patt_and x xs)).
    { apply well_formed_foldr_and; assumption. }
    toMLGoal.
    { wf_auto2. }
    mlIntro "H0". mlIntro "H1". mlIntro "H2".
    mlAdd IHxs as "H3".
    mlAssert ("H4" : ((foldr patt_and x xs ---> g) ---> foldr patt_imp g xs)).
    { wf_auto2. }
    { mlIntro "H5".
      mlAssert ("H6" : (x ---> foldr patt_imp g xs)).
      { wf_auto2. }
      { mlApply "H3". mlExact "H5". }
      mlClear "H0".
      mlApply "H6".
      mlExact "H1".
    }
    mlClear "H3".
    mlApply "H4".
    mlClear "H4".
    mlIntro "H3".
    mlApply "H0".
    mlSplitAnd.
    + mlExact "H2".
    + mlExact "H3".
Defined.

Lemma lhs_and_to_imp_meta {Σ : Signature} Γ (g x : Pattern) (xs : list Pattern) i:
  well_formed g ->
  well_formed x ->
  Pattern.wf xs ->
  Γ ⊢i (foldr patt_and x xs ---> g) using i ->
  Γ ⊢i (foldr patt_imp g (x :: xs)) using i.
Proof.
  intros wfg wfx wfxs H.
  eapply MP.
  2: { useBasicReasoning. apply lhs_and_to_imp; assumption. }
  exact H.
Defined.

Lemma lhs_imp_to_and {Σ : Signature} Γ (g x : Pattern) (xs : list Pattern):
  well_formed g ->
  well_formed x ->
  Pattern.wf xs ->
  Γ ⊢i (foldr patt_imp g (x :: xs)) ---> (foldr patt_and x xs ---> g)
  using BasicReasoning.
Proof.
  intros wfg wfx wfxs.
  induction xs; simpl.
  {
    apply A_impl_A.
    wf_auto2.
  }
  {
    pose proof (wfaxs := wfxs).
    unfold Pattern.wf in wfxs.
    simpl in wfxs.
    apply andb_prop in wfxs as [wfa wfxs].
    fold (Pattern.wf xs) in wfxs.
    specialize (IHxs wfxs).
    simpl in IHxs.
    assert (Hwffa: well_formed (foldr patt_and x xs)).
    { apply well_formed_foldr_and; assumption. }
    toMLGoal.
    { wf_auto2. }
    mlAdd IHxs as "H".
    mlIntro "H1".
    mlIntro "H2".
    mlDestructAnd "H2" as "H3" "H4".
    mlApplyMeta reorder in "H1".
    mlAssert ("H5": (x ---> foldr patt_imp g xs)).
    { wf_auto2. }
    {
      mlApply "H1".
      mlExact "H3".  
    }
    mlAssert ("H6" : (foldr patt_and x xs ---> g)).
    { wf_auto2. }
    {
      mlApply "H".
      mlExact "H5".
    }
    mlApply "H6".
    mlExact "H4".
  }
Defined.


Lemma lhs_imp_to_and_meta {Σ : Signature} Γ (g x : Pattern) (xs : list Pattern) i:
  well_formed g ->
  well_formed x ->
  Pattern.wf xs ->
  Γ ⊢i (foldr patt_imp g (x :: xs)) using i ->
  Γ ⊢i (foldr patt_and x xs ---> g) using i.
Proof.
  intros wfg wfx wfxs H.
  eapply MP.
  2: { useBasicReasoning. apply lhs_imp_to_and; assumption. }
  exact H.
Defined.

Lemma foldr_and_impl_last {Σ : Signature} Γ (x : Pattern) (xs : list Pattern):
  well_formed x ->
  Pattern.wf xs ->
  Γ ⊢i (foldr patt_and x xs ---> x) using BasicReasoning.
Proof.
  intros wfx wfxs.
  induction xs; simpl.
  {
    apply A_impl_A.
    exact wfx.
  }
  {
    pose proof (wfaxs := wfxs).
    unfold Pattern.wf in wfxs.
    simpl in wfxs.
    apply andb_prop in wfxs as [wfa wfxs].
    fold (Pattern.wf xs) in wfxs.
    specialize (IHxs wfxs).
    assert (Hwf2: well_formed (foldr patt_and x xs)).
    { apply well_formed_foldr_and; assumption. }
    toMLGoal.
    { wf_auto2. }
    mlAdd IHxs as "IH".
    mlIntro "H".
    mlDestructAnd "H" as "Ha" "Hf".
    mlApply "IH".
    mlExact "Hf".
  }
Defined.

Lemma foldr_and_weaken_last {Σ : Signature} Γ (x y : Pattern) (xs : list Pattern):
  well_formed x ->
  well_formed y ->
  Pattern.wf xs ->
  Γ ⊢i (x ---> y) ---> (foldr patt_and x xs ---> foldr patt_and y xs) using BasicReasoning.
Proof.
  intros wfx wfy wfxs.
  induction xs; simpl.
  {
    apply A_impl_A.
    wf_auto2.
  }
  {
    pose proof (wfaxs := wfxs).
    unfold Pattern.wf in wfxs.
    simpl in wfxs.
    apply andb_prop in wfxs as [wfa wfxs].
    fold (Pattern.wf xs) in wfxs.
    assert (Hwf1: well_formed (foldr patt_and x xs)).
    { apply well_formed_foldr_and; assumption. }
    assert (Hwf2: well_formed (foldr patt_and y xs)).
    { apply well_formed_foldr_and; assumption. }
    specialize (IHxs wfxs).
    toMLGoal.
    {
      wf_auto2.
    }
    mlAdd IHxs as "IH".
    mlIntro "H1".
    mlIntro "H2".
    mlDestructAnd "H2" as "H3" "H4".
    mlSplitAnd;[mlExact "H3"|].
    mlAssert ("IH'": (foldr patt_and x xs ---> foldr patt_and y xs)).
    {
      wf_auto2.
    }
    {
      mlApply "IH".
      mlExact "H1".
    }
    mlApply "IH'".
    mlExact "H4".
  }
Defined.

Lemma foldr_and_weaken_last_meta {Σ : Signature} Γ (x y : Pattern) (xs : list Pattern) i:
  well_formed x ->
  well_formed y ->
  Pattern.wf xs ->
  Γ ⊢i (x ---> y) using i ->
  Γ ⊢i (foldr patt_and x xs ---> foldr patt_and y xs) using i.
Proof.
  intros wfx wfy wfxs H.
  eapply MP;[exact H|].
  useBasicReasoning.
  apply foldr_and_weaken_last; assumption.
Defined.

Lemma foldr_and_last_rotate {Σ : Signature} Γ (x1 x2 : Pattern) (xs : list Pattern):
  well_formed x1 ->
  well_formed x2 ->
  Pattern.wf xs ->
  Γ ⊢i ((foldr patt_and x2 (xs ++ [x1])) <---> (x2 and (foldr patt_and x1 xs))) using BasicReasoning.
Proof.
  intros wfx1 wfx2 wfxs.
  destruct xs; simpl.
  {
    apply patt_and_comm; assumption.
  }
  {
    pose proof (wfaxs := wfxs).
    unfold Pattern.wf in wfxs.
    simpl in wfxs.
    apply andb_prop in wfxs as [wfa wfxs].
    fold (Pattern.wf xs) in wfxs.

    assert (Hwf1: well_formed (foldr patt_and (x1 and x2) xs)).
    { apply well_formed_foldr_and;[wf_auto2|assumption]. }
    assert (Hwf2: well_formed (foldr patt_and x1 xs)).
    { apply well_formed_foldr_and; assumption. }
    assert (Hwf3: well_formed (foldr patt_and x2 xs)).
    { apply well_formed_foldr_and; assumption. }

    rewrite foldr_app. simpl. 
    toMLGoal.
    { wf_auto2. }
    mlSplitAnd; mlIntro "H".
    {
      mlDestructAnd "H" as "Ha" "Hf".
      repeat mlSplitAnd.
      { mlApplyMeta foldr_and_impl_last in "Hf".
        mlDestructAnd "Hf" as "Hx1" "Hx2".
        mlExact "Hx2".
      }
      { mlExact "Ha". }
      {
        mlApplyMeta foldr_and_weaken_last_meta in "Hf".
        2: { apply pf_conj_elim_l; wf_auto2. }
        2: wf_auto2.
        mlExact "Hf".
      }
    }
    {
      mlDestructAnd "H" as "H1" "H1'".
      mlDestructAnd "H1'" as "H2" "H3".
      mlSplitAnd;[mlExact "H2"|].
      mlAssert ("Hf": (x2 and foldr patt_and x1 xs)).
      { wf_auto2. }
      { mlSplitAnd;[mlExact "H1"|mlExact "H3"]. }
      mlAdd (foldr_and_weaken_last Γ x1 (x1 and x2) xs ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2))as "Hw".
      mlAssert ("Hw'" : (foldr patt_and x1 xs ---> foldr patt_and (x1 and x2) xs)).
      { wf_auto2. }
      {
        mlApply "Hw".
        mlIntro "Hx1".
        mlSplitAnd;[mlExact "Hx1"|mlExact "H1"].
      }
      mlApply "Hw'".
      mlExact "H3".
    }
  }
Defined.

Lemma foldr_and_last_rotate_1 {Σ : Signature} Γ (x1 x2 : Pattern) (xs : list Pattern):
  well_formed x1 ->
  well_formed x2 ->
  Pattern.wf xs ->
  Γ ⊢i ((foldr patt_and x2 (xs ++ [x1])) ---> (x2 and (foldr patt_and x1 xs))) using BasicReasoning.
Proof.
  intros.
  assert (well_formed (foldr patt_and (x1 and x2) xs)).
  { apply well_formed_foldr_and; wf_auto2. }
  assert (well_formed (foldr patt_and x1 xs)).
  { apply well_formed_foldr_and; wf_auto2. }
  eapply pf_iff_proj1.
  3: { apply foldr_and_last_rotate; assumption. }
  {
    rewrite foldr_app. simpl. wf_auto2.
  }
  apply well_formed_and; wf_auto2.
Defined.

Lemma foldr_and_last_rotate_2 {Σ : Signature} Γ (x1 x2 : Pattern) (xs : list Pattern):
  well_formed x1 ->
  well_formed x2 ->
  Pattern.wf xs ->
  Γ ⊢i ((x2 and (foldr patt_and x1 xs)) ---> ((foldr patt_and x2 (xs ++ [x1])))) using BasicReasoning.
Proof.
  intros.
  assert (well_formed (foldr patt_and (x1 and x2) xs)).
  { apply well_formed_foldr_and; wf_auto2. }
  assert (well_formed (foldr patt_and x1 xs)).
  { apply well_formed_foldr_and; wf_auto2. }
  eapply pf_iff_proj2.
  3: { apply foldr_and_last_rotate; assumption. }
  {
    rewrite foldr_app. simpl. wf_auto2.
  }
  apply well_formed_and; wf_auto2.
Defined.
Locate MP.
#[local]
Ltac tryExact l idx :=
  match l with
    | nil => idtac
    | (?a :: ?m) => try mlExactn idx; tryExact m (idx + 1)
  end.

#[global]
Ltac mlAssumption :=
  match goal with
    | [ |- @of_MLGoal ?Sgm (@mkMLGoal ?Sgm ?Ctx ?l ?g ?i) ] 
      =>
        tryExact l 0
  end.




Lemma impl_eq_or {Σ : Signature} Γ a b:
  well_formed a ->
  well_formed b ->
  Γ ⊢i ( (a ---> b) <---> ((! a) or b) )
  using BasicReasoning.
Proof.
  intros wfa wfb.
  toMLGoal.
  { wf_auto2. }
  mlIntro "H0".
  mlDestructOr "H0" as "H1" "H2".
  - mlApply "H1". mlIntro "H2". mlClear "H1". mlIntro "H1".
    mlApplyMeta not_not_elim in "H1".
    mlApply "H2". mlAssumption.
  - mlApply "H2". mlIntro "H0". mlClear "H2". mlIntro "H1".
    mlDestructOr "H0" as "H2" "H3".
    + mlExFalso.
      mlApply "H2". mlAssumption.
    + mlAssumption.
Defined.


Lemma nimpl_eq_and {Σ : Signature} Γ a b:
  well_formed a ->
  well_formed b ->
  Γ ⊢i ( ! (a ---> b) <---> (a and !b) )
  using BasicReasoning.
Proof.
  intros wfa wfb.
  toMLGoal.
  { wf_auto2. }
  mlIntro "H0".
  mlDestructOr "H0" as "H1" "H2".
  - mlApply "H1". mlIntro "H0".
    unfold patt_and. mlIntro "H2".
    mlApply "H0". mlIntro "H3".
    mlDestructOr "H2" as "H4" "H5".
    + mlExFalso.
      mlApply "H4". mlAssumption.
    + mlApplyMeta not_not_elim in "H5".
      mlAssumption.
  - mlApply "H2". mlIntro "H0". mlIntro "H1".
    mlDestructAnd "H0" as "H3" "H4". mlApply "H4". mlApply "H1".
    mlAssumption.
Defined.


Lemma deMorgan_nand {Σ : Signature} Γ a b:
    well_formed a ->
    well_formed b ->
    Γ ⊢i ( !(a and b) <---> (!a or !b) )
    using BasicReasoning.
  Proof.
    intros wfa wfb.
    toMLGoal.
    { wf_auto2. }
    mlIntro "H0".
    mlDestructOr "H0" as "H1" "H2".
    - mlRevertLast.
      mlApplyMeta not_not_intro. mlIntro "H0".
      mlApplyMeta not_not_elim in "H0".
      mlAssumption.
    - mlRevertLast.
      mlApplyMeta not_not_intro. mlIntro "H0".
      mlApplyMeta not_not_intro.
      mlAssumption.
Defined.

Lemma deMorgan_nor {Σ : Signature} Γ a b:
    well_formed a ->
    well_formed b ->
    Γ ⊢i ( !(a or b) <---> (!a and !b))
    using BasicReasoning.
  Proof.
    intros wfa wfb.
    toMLGoal.
    { wf_auto2. }
    mlIntro "H0".
    mlDestructOr "H0" as "H1" "H2".
    - mlRevertLast.
      mlApplyMeta not_not_intro.
      mlIntro "H0". mlIntro "H1".
      mlApply "H0".
      mlDestructOr "H1" as "H2" "H3".
      + mlApplyMeta not_not_elim in "H2".
        mlLeft. mlAssumption.
      + mlApplyMeta not_not_elim in "H3".
        mlRight. mlAssumption.
    - mlRevertLast.
      mlApplyMeta not_not_intro.
      mlIntro "H0". mlIntro "H1".
      mlDestructAnd "H0" as "H2" "H3".
      mlDestructOr "H1" as "H4" "H5".
      + mlApply "H2". mlAssumption.
      + mlApply "H3". mlAssumption.
  Defined.

Lemma not_not_eq {Σ : Signature} (Γ : Theory) (a : Pattern) :
  well_formed a ->
  Γ ⊢i (!(!a) <---> a)
  using BasicReasoning.
Proof.
  intros wfa.
  toMLGoal.
  { wf_auto2. }
  mlIntro "H0".
  mlDestructOr "H0" as "H1" "H2".
  - mlApply "H1". mlIntro "H0".
    mlApplyMeta not_not_elim in "H0".
    mlAssumption.
  - unfold patt_not. mlApply "H2". mlIntro "H0". mlIntro "H1".
    mlApply "H1". mlAssumption.
Defined.


Lemma and_singleton {Σ : Signature} : forall Γ p,
  well_formed p -> Γ ⊢i (p and p) <---> p using BasicReasoning.
Proof.
  intros Γ p WFp.
  toMLGoal. wf_auto2.
  mlSplitAnd; mlIntro "H".
  * mlDestructAnd "H". mlAssumption.
  * mlSplitAnd; mlAssumption.
Defined.

Lemma MLGoal_ExactMeta {Σ:Signature} : forall Γ l g i,
  Γ ⊢i g using i ->
  mkMLGoal Σ Γ l g i.
Proof.
  intros Γ l g i pf wfG wfl.
  unfold of_MLGoal. simpl in *.
  induction l; simpl; auto.
  simpl in wfl. apply wf_tail' in wfl as wfl'.
  cbn in wfl. apply andb_true_iff in wfl as [wfl _].
  apply prf_conclusion; try solve [wf_auto2].
  auto with nocore.
Defined.

Tactic Notation "mlExactMeta" uconstr(t) :=
  apply (@MLGoal_ExactMeta _ _ _ _ _ t).

Goal forall (Σ : Signature) Γ, Γ ⊢i Top using BasicReasoning.
Proof.
  intros. toMLGoal. wf_auto2.
  mlExactMeta (top_holds Γ).
Defined.

Local Example exfalso_test {Σ : Signature} p Γ i :
  well_formed p ->
  Γ ⊢i p and ! p ---> Top using i.
Proof.
  intro WF. toMLGoal.
  { wf_auto2. }
  mlIntro "H".
  mlDestructAnd "H" as "H0" "H1".
  mlExFalso.
  mlApply "H1".
  mlExact "H0".
Defined.

(**********************************************************************************)




(* This is an example and belongs to the end of this file.
   Its only purpose is only to show as many tactics as possible.\
 *)
 Example ex_and_of_equiv_is_equiv_2 {Σ : Signature} Γ p q p' q' i:
   well_formed p ->
   well_formed q ->
   well_formed p' ->
   well_formed q' ->
   Γ ⊢i (p <---> p') using i ->
   Γ ⊢i (q <---> q') using i ->
   Γ ⊢i ((p and q) <---> (p' and q')) using i.
Proof.
 intros wfp wfq wfp' wfq' pep' qeq'.
 pose proof (pip' := pep'). apply pf_conj_elim_l_meta in pip'; auto.
 pose proof (p'ip := pep'). apply pf_conj_elim_r_meta in p'ip; auto.
 pose proof (qiq' := qeq'). apply pf_conj_elim_l_meta in qiq'; auto.
 pose proof (q'iq := qeq'). apply pf_conj_elim_r_meta in q'iq; auto.

 toMLGoal.
 { wf_auto2. }
 unfold patt_iff.
 mlSplitAnd.
 - mlIntro "H0".
   mlDestructAnd "H0" as "H1" "H2".
   mlSplitAnd.
   + mlApplyMeta pip'.
     mlExactn 0.
   + mlApplyMeta qiq' in "H2".
     mlExact "H2".
 - mlIntro "H0".
   unfold patt_and at 2.
   unfold patt_not at 1.
   mlIntro "H1".
   mlDestructOr "H1" as "H2" "H3".
   + mlDestructAnd "H0" as "H3" "H4".
     unfold patt_not.
     mlApply "H2".
     mlClear "H2".
     mlClear "H4".
     fromMLGoal.
     exact p'ip.
   + mlAdd q'iq as "H1".
     mlDestructAnd "H0" as "H2" "H4".
     mlAssert ("Hq" : q).
     { wf_auto2. }
     { mlApply "H1". mlExact "H4". }
     unfold patt_not at 1.
     mlApply "H3".
     mlAssumption.
Defined.


#[local]
  Example ex_or_of_equiv_is_equiv_2 {Σ : Signature} Γ p q p' q' i:
    well_formed p ->
    well_formed q ->
    well_formed p' ->
    well_formed q' ->
    Γ ⊢i (p <---> p') using i ->
    Γ ⊢i (q <---> q') using i ->
    Γ ⊢i ((p or q) <---> (p' or q')) using i.
  Proof.
    intros wfp wfq wfp' wfq' pep' qeq'.

    pose proof (pip' := pep'). apply pf_conj_elim_l_meta in pip'; auto.
    pose proof (p'ip := pep'). apply pf_conj_elim_r_meta in p'ip; auto.
    pose proof (qiq' := qeq'). apply pf_conj_elim_l_meta in qiq'; auto.
    pose proof (q'iq := qeq'). apply pf_conj_elim_r_meta in q'iq; auto.

    toMLGoal.
    { wf_auto2. }
    unfold patt_iff.
    mlSplitAnd.
    - mlIntro "H0".
      mlDestructOr "H0" as "H1" "H2".
      mlLeft.
      + mlApplyMeta pip'.
        mlExact "H1".
      + mlRight.
        mlApplyMeta qiq'.
        mlExact "H2".
    - mlIntro "H0".
      mlDestructOr "H0" as "H1" "H2".
      mlLeft.
      + mlApplyMeta p'ip.
        mlExact "H1".
      + mlRight.
        mlApplyMeta q'iq.
        mlExact "H2". 
  Defined.

Close Scope string_scope.
Close Scope list_scope.
Close Scope ml_scope.
