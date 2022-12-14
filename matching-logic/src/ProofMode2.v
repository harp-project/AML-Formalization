From Coq Require Import ssreflect ssrfun ssrbool.

From Ltac2 Require Import Ltac2.

From Coq Require Import Ensembles Bool String Btauto.
From Coq.Logic Require Import FunctionalExtensionality Eqdep_dec.
From Equations Require Import Equations.

Require Import Coq.Program.Tactics.

From MatchingLogic Require Import Syntax DerivedOperators_Syntax ProofSystem IndexManipulation wftactics Logic ProofMode BasicProofSystemLemmas ProofInfo.

From stdpp Require Import list tactics fin_sets coGset gmap sets.

From MatchingLogic.Utils Require Import stdpp_ext.

Import extralibrary.

Import
  MatchingLogic.Logic.Notations
  MatchingLogic.DerivedOperators_Syntax.Notations
  MatchingLogic.ProofSystem.Notations
.

(* Exports *)
Export MatchingLogic.ProofSystem.

Set Default Proof Mode "Classic".

Open Scope string_scope.
Open Scope list_scope.
Open Scope ml_scope.


Inductive ProofModeEntry {Σ : Signature} :=
| pme_pattern (p : Pattern)
| pme_variable
.

Record named_hypothesis {Σ : Signature} := mkNH
  {
    nh_name : string;
    nh_pme : ProofModeEntry;
  }.

Notation "N ∶ P" :=
  (@mkNH _ N P)
  (at level 100, no associativity, format "N  '∶'  P", only printing).

Definition hypotheses {Σ : Signature} := list named_hypothesis.

Notation "" :=
  (@nil named_hypothesis)
  (at level 100, left associativity, only printing) : ml_scope.
(*TODO: Ensure that this does not add parentheses*)
Notation "x ," :=
  (@cons named_hypothesis x nil)
  (at level 100, left associativity, format "x ',' '//'", only printing) : ml_scope.
Notation "x , y , .. , z ," :=
  (@cons named_hypothesis x (cons y .. (cons z nil) ..))
  (at level 100, left associativity, format "x ',' '//' y ',' '//' .. ',' '//' z ',' '//'", only printing) : ml_scope.

Definition names_of {Σ : Signature} (h : hypotheses) : list string := map nh_name h.
Definition pmes_of {Σ : Signature} (h : hypotheses) : list ProofModeEntry := map nh_pme h.

Definition has_name {Σ : Signature} (n : string) (nh : named_hypothesis) : Prop
:= nh_name nh = n.

#[global]
Instance has_name_dec {Σ : Signature} n nh : Decision (has_name n nh).
Proof.
  unfold has_name.
  solve_decision.
Defined.

Definition find_hyp {Σ : Signature} (name : string) (hyps : hypotheses) : option (nat * named_hypothesis)%type
:= stdpp.list.list_find (has_name name) hyps.


Record MLGoal {Σ : Signature} : Type := mkMLGoal
  { mlTheory : Theory;
    mlHypotheses: hypotheses;
    mlConclusion : Pattern ;
    mlInfo : ProofSystem.ProofInfo ;
  }.

Definition MLGoal_from_goal
  {Σ : Signature} (Γ : Theory) (goal : Pattern) (pi : ProofInfo)
  :
  MLGoal
  := mkMLGoal Σ Γ nil goal pi.

Definition connect {Σ : Signature} (h : ProofModeEntry) (i : Pattern) :=
  (
    match h with
    | pme_pattern p => patt_imp p i
    | pme_variable => patt_forall i
    end
  ).

Definition MLGoal_to_pattern'
  {Σ : Signature} (concl: Pattern) (pmes : list ProofModeEntry)
  : Pattern
:= fold_right connect concl pmes.

Definition MLGoal_to_pattern {Σ : Signature} (MG : MLGoal) : Pattern
:= MLGoal_to_pattern' (mlConclusion MG) (pmes_of (mlHypotheses MG)).

Coercion of_MLGoal {Σ : Signature} (MG : MLGoal) : Type :=
  well_formed (MLGoal_to_pattern MG) ->
  (mlTheory MG) ⊢i (MLGoal_to_pattern MG)
  using (mlInfo MG).



  (* This is useful only for printing. 
     0x2c75 was used for the ⊢ to avoid collision *)
  Notation "G 'Ⱶ' g 'using' pi "
  := (mkMLGoal _ G [] g pi)
  (at level 95,
  no associativity,
  format "G  'Ⱶ' '//' g '//' 'using'  pi '//'",
  only printing).

  Notation "G 'Ⱶ' g"
  := (mkMLGoal _ G [] g AnyReasoning)
  (at level 95,
  no associativity,
  format "G  'Ⱶ' '//'  g '//'",
  only printing).

  Notation "G 'Ⱶ' l -------------------------------------- g 'using' pi "
  := (mkMLGoal _ G l g pi)
  (at level 95,
  no associativity,
  format "G  'Ⱶ' '//' l -------------------------------------- '//' g '//' 'using'  pi '//'",
  only printing).

  Notation "G 'Ⱶ' l -------------------------------------- g"
  := (mkMLGoal _ G l g AnyReasoning)
  (at level 95,
  no associativity,
  format "G  'Ⱶ' '//' l -------------------------------------- '//' g '//'",
  only printing).

Ltac toMLGoal :=
  unfold ProofSystem.derives;
  lazymatch goal with
  | [ |- ?G ⊢i ?phi using ?pi]
    => cut (of_MLGoal (MLGoal_from_goal G phi pi));
       unfold MLGoal_from_goal;
       [(unfold of_MLGoal; simpl; let H := fresh "H" in intros H; apply H; clear H; cbn)|]
  end.

Ltac fromMLGoal := unfold of_MLGoal; cbn; intros _.

Local Example ex_toMLGoal {Σ : Signature} Γ (p : Pattern) :
  well_formed p ->
  Γ ⊢i p ---> p using BasicReasoning.
Proof.
  intros wfp.
  toMLGoal.
  { wf_auto2. }
  match goal with
  | [ |- of_MLGoal (mkMLGoal Σ Γ [] (p ---> p) BasicReasoning) ] => idtac
  | _ => fail
  end.
  fromMLGoal.
Abort.


Lemma cast_proof_ml_hyps {Σ : Signature}
  Γ hyps hyps'
  (e : hyps = hyps') goal (i : ProofInfo)
  :
  mkMLGoal Σ Γ hyps goal i ->
  mkMLGoal Σ Γ hyps' goal i.
Proof.
  unfold of_MLGoal. simpl. intros H.
  intros wfall.
  feed specialize H.
  {
     rewrite e. exact wfall.
  }
  unshelve (eapply (@cast_proof' Σ Γ _ _ i _ H)).
  rewrite e.
  reflexivity.
Defined.

Lemma cast_proof_ml_goal {Σ : Signature}
  Γ hyps goal goal'
  (e : goal = goal') (i : ProofInfo):
  mkMLGoal Σ Γ hyps goal i ->
  mkMLGoal Σ Γ hyps goal' i .
Proof.
  unfold of_MLGoal. simpl. intros H.
  intros wfall.
  feed specialize H.
  { rewrite e. exact wfall. }
  unshelve (eapply (@cast_proof' Σ Γ _ _ i _ H)).
  rewrite e.
  reflexivity.
Defined.


(* Extracts well-formedness assumptions about (local) goal and (local) hypotheses. *)
Tactic Notation "mlExtractWF" ident(wfa) :=
match goal with
| [ |- ?g ] =>
  let wfa' := fresh "wfa'" in
  intros wfa';
  pose proof (wfa := wfa');
  revert wfa';
  fold g;
  cbn in wfa
end.

Local Example ex_extractWfAssumptions {Σ : Signature} Γ (p : Pattern) :
  well_formed p ->
  Γ ⊢i p ---> p using BasicReasoning.
Proof.
  intros wfp.
  toMLGoal.
  { wf_auto2. }
  mlExtractWF wfa.
  (* These two asserts by assumption only test presence of the two hypotheses *)
  assert (well_formed (p ---> p)) by assumption.
Abort.

Lemma MLGoal_introImpl {Σ : Signature} (Γ : Theory) (l : hypotheses) (name : string) (x g : Pattern)
  (i : ProofInfo) :
  mkMLGoal _ Γ (l ++ [mkNH _ name (pme_pattern x)]) g i ->
  mkMLGoal _ Γ l (x ---> g) i.
Proof.
  intros H.
  unfold of_MLGoal in H. simpl in H.
  unfold of_MLGoal.
  unfold MLGoal_to_pattern.
  unfold MLGoal_to_pattern'.
  unfold MLGoal_to_pattern in H.
  unfold MLGoal_to_pattern' in H.
  simpl. simpl in H. intros wfall.
  feed specialize H.
  {
    clear H.
    unfold pmes_of in *.
    rewrite map_app. simpl.
    rewrite foldr_app. simpl.
    exact wfall.
  }
  unfold pmes_of in H.
  rewrite map_app in H.
  simpl in H.
  rewrite foldr_app in H.
  simpl in H.
  exact H.
Defined.

Ltac simplLocalContext :=
  match goal with
    | [ |- @of_MLGoal ?Sgm (mkMLGoal ?Sgm ?Ctx ?l ?g ?i) ]
      => eapply cast_proof_ml_hyps;[(rewrite {1}[l]/app; reflexivity)|]
  end.

Ltac _getHypNames :=
  lazymatch goal with
  | [ |- of_MLGoal (mkMLGoal _ _ ?l _ _) ] => eval lazy in (names_of l)
  end.

Tactic Notation "_failIfUsed" constr(name) :=
  lazymatch goal with
  | [ |- of_MLGoal (mkMLGoal _ _ ?l _ _) ] =>
    lazymatch (eval cbv in (find_hyp name l)) with
    | Some _ => fail "The name" name "is already used"
    | _ => idtac
    end
  end.

Tactic Notation "mlIntro" constr(name') :=
_failIfUsed name'; apply MLGoal_introImpl with (name := name'); simplLocalContext.

Tactic Notation "mlIntro" :=
  let hyps := _getHypNames in
  let name' := eval cbv in (fresh hyps) in
  mlIntro name'.


Local Example ex_mlIntro {Σ : Signature} Γ a (i : ProofInfo) :
  well_formed a ->
  Γ ⊢i a ---> a ---> a ---> a ---> a using i.
Proof.
  intros wfa.
  toMLGoal.
  { wf_auto2. }

  mlIntro "h"%string.
  Fail mlIntro "h"%string.
  mlIntro "h'"%string.
  do 2 mlIntro.
Abort.

Lemma MLGoal_revertLast {Σ : Signature} (Γ : Theory) (l : hypotheses) (x g : Pattern) (n : string) i :
  mkMLGoal Σ Γ l (x ---> g) i ->
  mkMLGoal Σ Γ (l ++ [mkNH _ n (pme_pattern x)]) g i.
Proof.
  intros H.
  unfold of_MLGoal in H. simpl in H.
  unfold of_MLGoal. simpl. intros wfall.
  
  cbn in wfall. cbn in H.
  feed specialize H.
  {
    rewrite map_app in wfall. simpl in wfall.
    rewrite foldr_app in wfall. simpl in wfall.
    exact wfall.
  }
  cbn.
  rewrite map_app. simpl.
  rewrite foldr_app. simpl.
  exact H.
Defined.

#[global]
Ltac mlRevertLast :=
match goal with
| |- @of_MLGoal ?Sgm (mkMLGoal ?Sgm ?Ctx ?l ?g ?i)
=> eapply cast_proof_ml_hyps;
   [(rewrite -[l](take_drop (length l - 1)); rewrite [take _ _]/=; rewrite [drop _ _]/=; reflexivity)|];
   apply MLGoal_revertLast
end.

Lemma MLGoal_introForall {Σ : Signature} (Γ : Theory) (l : hypotheses) (name : string) (g : Pattern)
  (i : ProofInfo) :
  mkMLGoal _ Γ (l ++ [mkNH _ name (pme_variable)]) g i ->
  mkMLGoal _ Γ l (all, g) i.
Proof.
  intros H.
  unfold of_MLGoal in H. simpl in H.
  unfold of_MLGoal.
  unfold MLGoal_to_pattern.
  unfold MLGoal_to_pattern'.
  unfold MLGoal_to_pattern in H.
  unfold MLGoal_to_pattern' in H.
  simpl. simpl in H. intros wfall.
  feed specialize H.
  {
    clear H.
    unfold pmes_of in *.
    rewrite map_app. simpl.
    rewrite foldr_app. simpl.
    exact wfall.
  }
  unfold pmes_of in H.
  rewrite map_app in H.
  simpl in H.
  rewrite foldr_app in H.
  simpl in H.
  exact H.
Defined.


Tactic Notation "mlIntroForall" constr(name') :=
  _failIfUsed name';
  apply MLGoal_introForall with (name := name');
  simplLocalContext
.

Tactic Notation "mlIntroForall" :=
  let hyps := _getHypNames in
  let name' := eval cbv in (fresh hyps) in
  mlIntroForall name'
.

#[local]
Example ex_introForall
  {Σ : Signature} (Γ : Theory) (a b c : Pattern)
  :
  well_formed a ->
  well_formed b ->
  well_formed c ->
  Γ ⊢ all, (a ---> (all, (b ---> c)))
.
Proof.
  intros wfa wfb wfc.
  toMLGoal.
  { wf_auto2. }
  mlIntroForall "x"%string.
  mlIntro "H1"%string.
  mlIntroForall "y"%string.
  mlIntro "H2"%string.
Abort.


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

Fixpoint wfcex_pmes {Σ : Signature}
  (idx : nat) (pmes : list ProofModeEntry)
  : bool
  :=
  match pmes with
  | [] => true
  | (pme_pattern p)::pmes'
    => well_formed_closed_ex_aux p idx
       && wfcex_pmes idx pmes'
  | (pme_variable)::pmes'
    => wfcex_pmes (S idx) pmes'
  end.


Lemma wfc_ex_aux_foldr_connect' {Σ : Signature} g pmes k :
  well_formed_closed_ex_aux (foldr connect g pmes) k 
  = well_formed_closed_ex_aux g (k + (foralls_count pmes))
  && wfcex_pmes k pmes
.
Proof.
  move: k g.
  induction pmes; cbn; intros k g.
  {
    rewrite plus_0_r. rewrite andb_true_r. reflexivity.
  }
  {
    destruct a; unfold decide; simpl in *.
    {
      rewrite IHpmes.
      unfold foralls_count.
      remember (
        well_formed_closed_ex_aux p k) as A.
      remember (well_formed_closed_ex_aux g (k + length (filter is_variable pmes))) as B.
      remember (wfcex_pmes k pmes) as C.
      clear. btauto.
    }
    {
      rewrite IHpmes.
      rewrite -plus_Snm_nSm.
      unfold foralls_count.
      remember (well_formed_closed_ex_aux g (S k + length (filter is_variable pmes))) as A.
      btauto.
    }
  }
Qed.

Lemma lift_to_mixed_context' {Σ : Signature} (Γ : Theory)
  (concl₁ concl₂: Pattern) (pmes : list ProofModeEntry)
  (i : ProofInfo)
  (* TODO relax ExGen *)
  (pile : ProofInfoLe (ExGen := ⊤, SVSubst := ∅, KT := false) i)
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
  (pile : ProofInfoLe (ExGen := ⊤, SVSubst := ∅, KT := false) i)
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
  (pile : ProofInfoLe (ExGen := ⊤, SVSubst := ∅, KT := false) i)
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
  { wf_auto2. }
  { wf_auto2. }
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

Lemma evar_open_fresh_iter_top {Σ : Signature} avoid m  base :
  evar_open_fresh_iter_base avoid base m patt_top
  = patt_top
.
Proof.
  move: avoid.
  induction m; intros avoid; simpl.
  { reflexivity. }
  {
    rewrite IHm. reflexivity.
  }
Qed.

Lemma evar_open_fresh_iter_base_wfc_aux:
  ∀ {Σ : Signature} (db2 : nat) (phi : Pattern) avoid base,
	well_formed_closed_ex_aux phi 0 →
  evar_open_fresh_iter_base avoid base db2 phi = phi
.
Proof.
  intros.
  move: avoid base phi H.
  induction db2; intros avoid base phi Hwf.
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

Lemma evar_open_fresh_iter_wfc_aux:
  ∀ {Σ : Signature} (db2 : nat) (phi : Pattern) avoid,
	well_formed_closed_ex_aux phi 0 →
  evar_open_fresh_iter avoid db2 phi = phi
.
Proof.
  intros.
  apply evar_open_fresh_iter_base_wfc_aux.
  assumption.
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

Lemma wfcex_pmes_evar_open_pmes {Σ : Signature}
  m x l
  :
  wfcex_pmes m (evar_open_pmes m x l) = true ->
  wfcex_pmes (S m) l = true
.
Proof.
  move: x m.
  induction l; cbn; intros x m H.
  { reflexivity. }
  {
    destruct a as [p|].
    {
      simpl in *.
      destruct_and!.
      specialize (IHl x m).
      feed specialize IHl.
      { wf_auto2. }
      wf_auto2.
    }
    {
      simpl in *.
      specialize (IHl x (S m) H).
      exact IHl.
    }
  }
Qed.

Lemma wfc_ex_aux_body_iff' :
  forall {Σ : Signature} (phi : Pattern) (n : nat) (x : evar),
	well_formed_closed_ex_aux phi (S n) 
  = well_formed_closed_ex_aux phi^{evar:n↦x} n
.
Proof.
  intros.
  remember (well_formed_closed_ex_aux phi^{evar:n↦x} n) as b.
  symmetry in Heqb.
  destruct b.
  {
    apply wfc_ex_aux_body_iff in Heqb.
    exact Heqb.
  }
  {
    rewrite -not_true_iff_false.
    rewrite -not_true_iff_false in Heqb.
    intros HContra. apply Heqb.
    rewrite wfc_ex_aux_body_iff in HContra.
    exact HContra.
  }
Qed.

Lemma wfcex_pmes_evar_open_pmes_iff {Σ : Signature}
  m x l
  :
  wfcex_pmes m (evar_open_pmes m x l)
  = wfcex_pmes (S m) l
.
Proof.
  move: x m.
  induction l; cbn; intros x m.
  { reflexivity. }
  {
    destruct a as [p|]; simpl.
    {
      rewrite IHl.
      rewrite -wfc_ex_aux_body_iff'.
      reflexivity.
    }
    {
      rewrite IHl. reflexivity.
    }
  }
Qed.

Lemma evar_open_evar_open_fresh_iter_base
  {Σ : Signature} avoid m n phi :
  (evar_open_fresh_iter_base avoid (S n) m phi)^{evar:n↦(evar_fresh_nth avoid m)}
  = evar_open_fresh_iter_base avoid n (S m) phi
.
Proof.
  move: phi n avoid.
  induction m; simpl; intros phi n avoid.
  {
    rewrite Nat.add_0_r.
    reflexivity.
  }
  {
    rewrite IHm. clear IHm. simpl.
    rewrite Nat.add_succ_r.
    reflexivity.
  }
Qed.

Lemma nested_const_fa' {Σ : Signature} Γ a l avoid (m : nat) :
  free_evars (a ---> (fold_right connect a l)) ⊆ avoid ->
  well_formed a = true ->
  well_formed_xy m 0 ((fold_right connect patt_bott l)) = true ->
  Γ ⊢i evar_open_fresh_iter avoid m (a ---> (fold_right connect a l))
  using AnyReasoning.
Proof.
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
        apply ProofInfo.P1.
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
          wf_auto2_decompose_hyps_parts.
          (* This is a way how to give a name to a hypothesis that should exists somewhere *)
          assert (H'' : well_formed_closed_ex_aux
            (evar_open_fresh_iter_base avoid' 0 m
             (foldr connect a' (evar_open_pmes m (evar_fresh_s avoid) l))) 0 =
            true) by assumption
          .
          clear -H''.
          rewrite wfce_eofib.
          rewrite wfce_eofib in H''.
          simpl in H''.
          rewrite wfc_ex_aux_foldr_connect' in H''.
          rewrite wfc_ex_aux_foldr_connect'.
          simpl.
          rewrite foralls_count_evar_open_pmes in H''.
          destruct_and!.
          split_and.
          {
            wf_auto2.
          }
          {
            clear -H0.
            apply wfcex_pmes_evar_open_pmes in H0.
            exact H0.
          }
        }
      }
      apply forall_gen.
      {
        simpl.
        subst x'.
        unfold evar_is_fresh_in.
        apply evar_fresh_nth_notin_free_evars_evar_open_fresh_iter_base.
        intros m0.
        pose proof (H := evar_fresh_nth_avoid avoid m0).
        clear -H Havoid.
        set_solver.
      }
      { apply pile_any. }

      subst x'.
      rewrite evar_open_evar_open_fresh_iter_base.
      simpl.
      subst avoid'.

      rewrite [evar_open_fresh_iter_base avoid 0 m a']evar_open_fresh_iter_base_wfc_aux.
      { wf_auto2. }
      rewrite [evar_open_fresh_iter_base _ 0 m a']evar_open_fresh_iter_base_wfc_aux in IHl.
      { wf_auto2. }

      rewrite evar_open_foldr_connect. simpl.
      rewrite [evar_open _ _ a']evar_open_wfc.
      { wf_auto2. }
      apply IHl.
    }
Defined.

Lemma nested_const_fa {Σ : Signature} Γ a l :
  well_formed a = true ->
  well_formed ((fold_right connect patt_bott l)) = true ->
  Γ ⊢i (a ---> (fold_right connect a l))
  using AnyReasoning.
Proof.
  intros.
  apply (nested_const_fa' Γ a l (free_evars (a ---> foldr connect a l)) 0).
  { apply reflexivity. }
  { assumption. }
  { wf_auto2. }
Defined.


Fixpoint wfcmu_pmes {Σ : Signature}
  (idx : nat) (pmes : list ProofModeEntry)
  : bool
  :=
  match pmes with
  | [] => true
  | (pme_pattern p)::pmes'
    => well_formed_closed_mu_aux p idx
       && wfcmu_pmes idx pmes'
  | (pme_variable)::pmes'
    => wfcmu_pmes idx pmes'
  end.

Fixpoint wfp_pmes {Σ : Signature}
  (pmes : list ProofModeEntry)
  : bool
  :=
  match pmes with
  | [] => true
  | (pme_pattern p)::pmes'
    => well_formed_positive p
       && wfp_pmes pmes'
  | (pme_variable)::pmes'
    => wfp_pmes pmes'
  end
.


Lemma wfc_mu_aux_foldr_connect {Σ : Signature} g pmes k :
  well_formed_closed_mu_aux (foldr connect g pmes) k 
  = well_formed_closed_mu_aux g k
  && wfcmu_pmes k pmes
.
Proof.
  move: g k.
  induction pmes; cbn; intros g k.
  {
    rewrite andb_true_r. reflexivity.
  }
  {
    destruct a as [p|]; simpl.
    {
      rewrite IHpmes. clear IHpmes.
      remember (well_formed_closed_mu_aux g (k + length (filter is_variable pmes))) as B.
      btauto.
    }
    {
      rewrite IHpmes. clear IHpmes.
      btauto.
    }
  }
Qed.

Lemma wfp_foldr_connect {Σ : Signature} g pmes :
  well_formed_positive (foldr connect g pmes) 
  = well_formed_positive g
  && wfp_pmes pmes
.
Proof.
  move: g.
  induction pmes; cbn; intros g.
  {
    rewrite andb_true_r. reflexivity.
  }
  {
    destruct a as [p|]; simpl.
    {
      rewrite IHpmes. clear IHpmes.
      btauto.
    }
    {
      rewrite IHpmes. clear IHpmes.
      btauto.
    }
  }
Qed.

Lemma evar_open_pmes_app {Σ : Signature} idx x l₁ l₂:
  evar_open_pmes idx x (l₁ ++ l₂)
  = (evar_open_pmes idx x l₁)
  ++ (evar_open_pmes (idx + foralls_count l₁) x l₂)
.
Proof.
  move: idx l₂.
  induction l₁; cbn; intros idx l₂.
  {
    rewrite Nat.add_0_r. reflexivity.
  }
  {
    destruct a as [p|]; simpl.
    {
      rewrite IHl₁. clear IHl₁. unfold foralls_count.
      reflexivity.
    }
    {
      rewrite IHl₁. clear IHl₁. unfold foralls_count.
      rewrite Nat.add_succ_r. simpl.
      reflexivity.
    }
  }
Qed.

Lemma wfp_pmes_app {Σ : Signature} l1 l2:
  wfp_pmes (l1 ++ l2) = wfp_pmes l1 && wfp_pmes l2
.
Proof.
  induction l1; simpl.
  {
    reflexivity.
  }
  {
    destruct a as [p|].
    {
      rewrite IHl1. rewrite andb_assoc. reflexivity.
    }
    {
      exact IHl1.
    }
  }
Qed.

Lemma wfp_pmes_evar_open {Σ : Signature} l idx x:
  wfp_pmes (evar_open_pmes idx x l) = wfp_pmes l
.
Proof.
  move: idx x.
  induction l; simpl; intros idx x.
  { reflexivity. }
  {
    destruct a as [p|]; simpl.
    {
      rewrite IHl.
      f_equal.
      Search (well_formed_positive (evar_open _ _ _)).
      remember (well_formed_positive p) as b.
      symmetry in Heqb.
      destruct b.
      {
        apply wfp_evar_open. exact Heqb.
      }
      {
        rewrite -not_true_iff_false. rewrite -not_true_iff_false in Heqb.
        intros HContra. apply Heqb.
        apply evar_open_positive in HContra.
        exact HContra.
      }
    }
    {
      rewrite IHl. reflexivity.
    }
  }
Qed.

Lemma wfcmu_pmes_app {Σ : Signature} idx l1 l2:
  wfcmu_pmes idx (l1 ++ l2) = wfcmu_pmes idx l1 && wfcmu_pmes idx l2
.
Proof.
  induction l1; simpl.
  {
    reflexivity.
  }
  {
    destruct a as [p|].
    {
      rewrite IHl1. rewrite andb_assoc. reflexivity.
    }
    {
      exact IHl1.
    }
  }
Qed.


Lemma foralls_count_app {Σ : Signature} l1 l2:
  foralls_count (l1 ++ l2) = foralls_count l1 + foralls_count l2
.
Proof.
  unfold foralls_count.
  rewrite filter_app.
  rewrite app_length.
  reflexivity.
Qed.

Lemma foralls_count_cons_pattern {Σ : Signature} l p:
  foralls_count ((pme_pattern p)::l) = (foralls_count l)
.
Proof.
  cbn. unfold decide.
  reflexivity.
Qed.

Lemma foralls_count_cons_variable {Σ : Signature} l:
  foralls_count ((pme_variable)::l) = S (foralls_count l)
.
Proof.
  cbn. unfold decide.
  reflexivity.
Qed.

Lemma wfcex_pmes_app {Σ : Signature} k l1 l2:
  wfcex_pmes k (l1 ++ l2)
  = wfcex_pmes k l1 && wfcex_pmes (k + foralls_count l1) l2
.
Proof.
  move: k l2.
  induction l1; cbn; intros k l2.
  { rewrite Nat.add_0_r. reflexivity. }
  {
    destruct a as [p|];cbn; unfold decide.
    {
      rewrite IHl1. unfold foralls_count.
      rewrite !andb_assoc.
      reflexivity.
    }
    {
      rewrite IHl1. unfold foralls_count. simpl.
      rewrite Nat.add_succ_r.
      reflexivity.
    }
  }
Qed.

Lemma wfc_mu_aux_body_iff' {Σ : Signature}:
	 ∀ (phi : Pattern) (n : nat) (X : svar),
     well_formed_closed_mu_aux phi^{svar:n↦X} n      
     = well_formed_closed_mu_aux phi (S n)
.
Proof.
  intros.
  remember (well_formed_closed_mu_aux phi (S n)) as b.
  symmetry in Heqb.
  destruct b.
  {
    apply wfc_mu_aux_body_iff. exact Heqb.
  }
  {
    rewrite -not_true_iff_false.
    rewrite -not_true_iff_false in Heqb.
    intros HContra. apply Heqb. clear Heqb.
    rewrite -wfc_mu_aux_body_iff in HContra.
    exact HContra.
  }
Qed.
      
Lemma wfc_mu_aux_body_ex_iff' {Σ : Signature}:
	 ∀ (phi : Pattern) (n n' : nat) (x : evar),
     well_formed_closed_mu_aux phi^{evar:n'↦x} n      
     = well_formed_closed_mu_aux phi n
.
Proof.
  intros.
  remember (well_formed_closed_mu_aux phi n) as b.
  symmetry in Heqb.
  destruct b.
  {
    apply wfc_mu_aux_body_ex_imp1.
    exact Heqb.
  }
  {
    rewrite -not_true_iff_false.
    rewrite -not_true_iff_false in Heqb.
    intros HContra. apply Heqb. clear Heqb.
    apply wfc_mu_aux_body_ex_imp2 in HContra.
    exact HContra.
  }
Qed.

Lemma wfcmu_pmes_evar_open_pmes {Σ : Signature} m m' x l:
  wfcmu_pmes m (evar_open_pmes m' x l)
  = wfcmu_pmes m l
.
Proof.
  move: m m' x.
  induction l; cbn; intros m m' x.
  { reflexivity. }
  {
    destruct a as [p|]; simpl.
    {
      rewrite wfc_mu_aux_body_ex_iff'.
      rewrite IHl.
      reflexivity.
    }
    {
      rewrite IHl.
      reflexivity.
    }
  }
Qed.

Definition wf_simpl_rules := (
  @wfc_ex_aux_foldr_connect',
  @wfc_mu_aux_foldr_connect,
  @wfp_foldr_connect,
  @wfp_pmes_app,
  @wfp_pmes_evar_open,
  @wfcmu_pmes_app,
  @foralls_count_app,
  @foralls_count_evar_open_pmes,
  @foralls_count_cons_pattern,
  @foralls_count_cons_variable,
  @wfcex_pmes_app,
  @wfcex_pmes_evar_open_pmes_iff,
  @wfcmu_pmes_evar_open_pmes
).

Ltac wf_simpl_goal :=
  rewrite ?wf_simpl_rules
.

Ltac _wf_simpl_hyp H :=
  rewrite ?wf_simpl_rules in H
.

Tactic Notation "wf_simpl_hyp" ident(H) :=
  _wf_simpl_hyp H
.

Ltac2 Set simplify_wf_goal_hook as oldhook := fun () =>
  try ltac1:(wf_simpl_goal);
  oldhook ()
.

Ltac2 Set simplify_wf_hyp_part_hook as oldhook := fun (h : ident) =>
  ltac1:(h |- wf_simpl_hyp h) (Ltac1.of_ident h);
  oldhook h
.

Lemma top_holds_in_any_context {Σ : Signature} Γ l:
  well_formed (foldr connect patt_top l) ->
  Γ ⊢i foldr connect patt_top l using AnyReasoning
.
Proof.
  remember (S (length l)) as len.
  assert (Hlen : S (length l) <= len) by lia.
  clear Heqlen.
  move: l Hlen.
  induction len; intros l Hlen Hwf.
  {
    lia.
  }
  destruct l; cbn in *.
  { useBasicReasoning. apply A_impl_A. wf_auto2. }

  destruct p as [p|]; simpl.
  {
    eapply MP. 2: useBasicReasoning; apply ProofInfo.P1.
    {
      apply IHlen.
      { lia. }
      { wf_auto2. }
    }
    1,2: wf_auto2.
  }
  {
    remember (fresh_evar (foldr connect patt_top l)) as x.
    replace (foldr connect patt_top l)
      with (evar_quantify x 0 (evar_open x 0 (foldr connect patt_top l)))
    .
    2: {
      apply evar_quantify_evar_open.
      { subst x. apply set_evar_fresh_is_fresh. }
      wf_auto2.
    }
    apply universal_generalization.
    { apply pile_any. }
    { wf_auto2. }
    rewrite evar_open_foldr_connect. simpl. mlSimpl.
    apply IHlen.
    {
      rewrite length_evar_open_pmes. lia.
    }
    {
      wf_auto2.
    }
  }
Qed.

(*
Check evar_open_pmes.
Lemma evar_open_fresh_iter_base_foldr_connect
  {Σ : Signature} (base idx : nat) (a : Pattern) l:
  evar_open_fresh_iter_base evs base idx (foldr connect a l)
  = foldr
      connect
      (evar_open_fresh_iter_base evs base idx a)
      (evar_open_pmes ).
*)
Lemma nested_const_middle_fa {Σ : Signature} Γ a l₁ l₂ :
  well_formed_closed_ex_aux a (foralls_count l₁) = true ->
  well_formed ((fold_right connect a (l₁ ++ (pme_pattern a) :: l₂))) = true ->
  Γ ⊢i (fold_right connect (a) (l₁ ++ (pme_pattern a) :: l₂))
  using AnyReasoning.
Proof.


  remember (S (length l₁)) as len.
  assert (Hlen : S (length l₁) <= len) by lia.
  clear Heqlen.
  move: a l₁ l₂ Hlen.
  induction len; intros a l₁ l₂ Hlen Ha H.
  {
    lia.
  }
  destruct l₁; cbn in *.
  {
    apply nested_const_fa.
    { wf_auto2. }
    { wf_auto2. }
  }
  {
    destruct p as [p|]; simpl.
    {
      eapply MP. 2: useBasicReasoning; apply ProofInfo.P1.
      2,3: wf_auto2.
      apply IHlen.
      { lia. }
      { wf_auto2. }
      { wf_auto2. }
    }
    {
      unfold decide in Ha. simpl in Ha.
      remember (fresh_evar (foldr connect a (l₁ ++ pme_pattern a :: l₂))) as x.
      replace (foldr connect a (l₁ ++ pme_pattern a :: l₂))
        with (evar_quantify x 0 (evar_open x 0 (foldr connect a (l₁ ++ pme_pattern a :: l₂))))
      .
      2: {
        apply evar_quantify_evar_open.
        { subst x. apply set_evar_fresh_is_fresh. }
        wf_auto2.
      }
      apply universal_generalization.
      { apply pile_any. }
      { wf_auto2. }
      
      rewrite evar_open_foldr_connect.
      simpl.
      rewrite evar_open_pmes_app. simpl.
      simpl in H.
      unfold foralls_count. rewrite filter_app. rewrite app_length.
      cbn. unfold decide.
      remember (a^{evar:length (filter is_variable l₁) + length (filter is_variable l₂)↦x}) as a''.
      remember (a^{evar:length (filter is_variable l₁)↦x}) as a'.

      unfold decide in Ha. cbn in Ha.

      specialize (IHlen a' (evar_open_pmes 0 x l₁)).
      specialize (IHlen (evar_open_pmes (length (filter is_variable l₁)) x l₂)).
      feed specialize IHlen.
      { rewrite length_evar_open_pmes. lia. }
      { rewrite foralls_count_evar_open_pmes. wf_auto2. }
      { subst a' a''.
        
        clear -H.
        fold (foralls_count l₁).

        wf_auto2.
        {
          apply wfc_ex_aux_bsvar_subst_le;[lia|idtac|].
          wf_auto2.
          wf_auto2.
        }
      }
      

      remember (length (filter is_variable l₂)) as len2.
      destruct len2.
      {
        rewrite Nat.add_0_r in Heqa''.
        subst a'' a'.
        apply IHlen.
      }
      assert (a'' = a').
      {
        destruct len2.
        admit. admit.
      }

      (* apply IHlen. *)
      admit.
    }
  }
Abort.

Close Scope ml_scope.
