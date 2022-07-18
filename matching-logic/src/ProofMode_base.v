From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Ltac2 Require Import Ltac2.

From Coq Require Import Ensembles Bool String.
From Coq.Logic Require Import FunctionalExtensionality Eqdep_dec.
From Equations Require Import Equations.

Require Import Coq.Program.Tactics.

From MatchingLogic Require Import Syntax DerivedOperators_Syntax ProofSystem IndexManipulation wftactics.

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

Record named_hypothesis {Σ : Signature} := mkNH
  {
    nh_name : string;
    nh_patt : Pattern;
  }.

Notation "N :- P" :=
  (@mkNH _ N P)
  (at level 100, no associativity, format "N ':-'  P", only printing).

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
Definition patterns_of {Σ : Signature} (h : hypotheses) : list Pattern := map nh_patt h.

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
  := @mkMLGoal Σ Γ nil goal pi.

Coercion of_MLGoal {Σ : Signature} (MG : MLGoal) : Type :=
  well_formed (mlConclusion MG) ->
  Pattern.wf (patterns_of (mlHypotheses MG)) ->
  (mlTheory MG) ⊢i (fold_right patt_imp (mlConclusion MG) (patterns_of (mlHypotheses MG)))
  using (mlInfo MG).



  (* This is useful only for printing. *)
  Notation "G ⊢ l -------------------------------------- g 'using' pi "
  := (@mkMLGoal _ G l g pi)
  (at level 95,
  no associativity,
  format "G  ⊢ '//' l -------------------------------------- '//' g '//' 'using'  pi '//'",
  only printing).

  Notation "G ⊢ l -------------------------------------- g"
  := (@mkMLGoal _ G l g AnyReasoning)
  (at level 95,
  no associativity,
  format "G  ⊢ '//' l -------------------------------------- '//' g '//'",
  only printing).

Ltac toMLGoal :=
  unfold ProofSystem.derives;
  lazymatch goal with
  | [ |- ?G ⊢i ?phi using ?pi]
    => cut (of_MLGoal (MLGoal_from_goal G phi pi));
       unfold MLGoal_from_goal;
       [(unfold of_MLGoal; simpl; let H := fresh "H" in intros H; apply H; clear H; [|reflexivity])|]
  end.

Ltac fromMLGoal := unfold of_MLGoal; simpl; intros _ _.

Ltac solve_pim_simple := constructor; simpl;[(set_solver)|(set_solver)|(reflexivity)|(apply reflexivity)].


Lemma useBasicReasoning {Σ : Signature} (Γ : Theory) (ϕ : Pattern) (i : ProofInfo) :
Γ ⊢i ϕ using BasicReasoning ->
Γ ⊢i ϕ using i.
Proof.
intros H.
pose proof (Hpf := proj2_sig H).
remember (proj1_sig H) as _H.
exists (_H).
clear Heq_H.
abstract (
  destruct Hpf as [Hpf1 Hpf2 Hpf3 Hpf4];
destruct i; constructor; simpl in *;
[set_solver|set_solver|idtac|set_solver];
(destruct (uses_kt _H); simpl in *; try congruence)).
Defined.


Lemma mlUseBasicReasoning
  {Σ : Signature} (Γ : Theory) (l : hypotheses) (g : Pattern) (i : ProofInfo) :
  @mkMLGoal Σ Γ l g BasicReasoning ->
  @mkMLGoal Σ Γ l g i.
Proof.
  intros H wf1 wf2.
  specialize (H wf1 wf2).
  apply useBasicReasoning.
  exact H.
Defined.


Ltac useBasicReasoning :=
  unfold ProofSystem.derives;
  lazymatch goal with
  | [ |- of_MLGoal (@mkMLGoal _ _ _ _ _) ] => apply mlUseBasicReasoning
  | [ |- _ ⊢i _ using _ ] => apply useBasicReasoning
  end.

  

(* Extracts well-formedness assumptions about (local) goal and (local) hypotheses. *)
Tactic Notation "mlExtractWF" ident(wfl) ident(wfg) :=
match goal with
| [ |- ?g ] =>
  let wfl' := fresh "wfl'" in
  let wfg' := fresh "wfg'" in
  intros wfg' wfl';
  pose proof (wfl := wfl');
  pose proof (wfg := wfg');
  revert wfg' wfl';
  fold g;
  rewrite /mlConclusion in wfg;
  rewrite /mlHypotheses in wfl
end.

Local Example ex_extractWfAssumptions {Σ : Signature} Γ (p : Pattern) :
  well_formed p ->
  Γ ⊢i p ---> p using BasicReasoning.
Proof.
  intros wfp.
  toMLGoal.
  { auto. }
  mlExtractWF wfl wfg.
  (* These two asserts by assumption only test presence of the two hypotheses *)
  assert (Pattern.wf []) by assumption.
  assert (well_formed (p ---> p)) by assumption.
Abort.

Lemma cast_proof' {Σ : Signature} (Γ : Theory) (ϕ ψ : Pattern) (i : ProofInfo) (e : ψ = ϕ) :
  Γ ⊢i ϕ using i ->
  Γ ⊢i ψ using i.
Proof.
  intros [pf Hpf].
  unshelve (eexists).
  {
    apply (cast_proof e).
    exact pf.
  }
  { abstract(
    destruct Hpf as [Hpf2 Hpf3 Hpf4];
    constructor; [
    (
      rewrite elem_of_subseteq in Hpf2;
      rewrite elem_of_subseteq;
      intros x Hx;
      specialize (Hpf2 x);
      apply Hpf2; clear Hpf2;
      rewrite elem_of_gset_to_coGset in Hx;
      rewrite uses_of_ex_gen_correct in Hx;
      rewrite elem_of_gset_to_coGset;
      rewrite uses_of_ex_gen_correct;
      rewrite indifferent_to_cast_uses_ex_gen in Hx;
      exact Hx
    )|
    (
      rewrite elem_of_subseteq in Hpf3;
      rewrite elem_of_subseteq;
      intros x Hx;
      specialize (Hpf3 x);
      apply Hpf3; clear Hpf3;
      rewrite elem_of_gset_to_coGset in Hx;
      rewrite uses_of_svar_subst_correct in Hx;
      rewrite elem_of_gset_to_coGset;
      rewrite uses_of_svar_subst_correct;
      rewrite indifferent_to_cast_uses_svar_subst in Hx;
      exact Hx
    )|
    (
      rewrite indifferent_to_cast_uses_kt;
      apply Hpf4
    )|
    (
      rewrite framing_patterns_cast_proof;
      destruct i; assumption
    )
    ]).
  }
Defined.

Lemma cast_proof_ml_hyps {Σ : Signature} Γ hyps hyps' (e : patterns_of hyps = patterns_of hyps') goal (i : ProofInfo) :
  @mkMLGoal Σ Γ hyps goal i ->
  @mkMLGoal Σ Γ hyps' goal i.
Proof.
  unfold of_MLGoal. simpl. intros H.
  intros wfg wfhyps'.
  feed specialize H.
  { exact wfg. }
  { rewrite e. exact wfhyps'. }
  unshelve (eapply (@cast_proof' Σ Γ _ _ i _ H)).
  rewrite e.
  reflexivity.
Defined.

Lemma cast_proof_ml_goal {Σ : Signature} Γ hyps goal goal' (e : goal = goal') (i : ProofInfo):
  @mkMLGoal Σ Γ hyps goal i ->
  @mkMLGoal Σ Γ hyps goal' i .
Proof.
  unfold of_MLGoal. simpl. intros H.
  intros wfgoal' wfhyps.
  feed specialize H.
  { rewrite e. exact wfgoal'. }
  { exact wfhyps. }
  unshelve (eapply (@cast_proof' Σ Γ _ _ i _ H)).
  rewrite e.
  reflexivity.
Defined.


Lemma MLGoal_intro {Σ : Signature} (Γ : Theory) (l : hypotheses) (name : string) (x g : Pattern)
  (i : ProofInfo) :
  @mkMLGoal Σ Γ (l ++ [mkNH name x]) g i ->
  @mkMLGoal Σ Γ l (x ---> g) i.
Proof.
  intros H.
  unfold of_MLGoal in H. simpl in H.
  unfold of_MLGoal. simpl. intros wfxig wfl.

  feed specialize H.
  { abstract (apply well_formed_imp_proj2 in wfxig; exact wfxig). }
  { abstract (unfold Pattern.wf in *; unfold patterns_of;
    rewrite map_app map_app foldr_app; simpl;
    apply well_formed_imp_proj1 in wfxig; rewrite wfxig; simpl; exact wfl).
  }
  unshelve (eapply (cast_proof' _ H)).
  { unfold patterns_of. rewrite map_app foldr_app. simpl. reflexivity. }
Defined.

Ltac simplLocalContext :=
  match goal with
    | [ |- @of_MLGoal ?Sgm (@mkMLGoal ?Sgm ?Ctx ?l ?g ?i) ]
      => eapply cast_proof_ml_hyps;[(rewrite {1}[l]/app; reflexivity)|]
  end.

Ltac _getHypNames :=
  lazymatch goal with
  | [ |- of_MLGoal (@mkMLGoal _ _ ?l _ _) ] => eval lazy in (names_of l)
  end.

Tactic Notation "_failIfUsed" constr(name) :=
  lazymatch goal with
  | [ |- of_MLGoal (@mkMLGoal _ _ ?l _ _) ] =>
    lazymatch (eval cbv in (find_hyp name l)) with
    | Some _ => fail "The name" name "is already used"
    | _ => idtac
    end
  end.

Tactic Notation "mlIntro" constr(name') :=
_failIfUsed name'; apply MLGoal_intro with (name := name'); simplLocalContext.

Tactic Notation "mlIntro" :=
  let hyps := _getHypNames in
  let name' := eval cbv in (fresh hyps) in
  mlIntro name'.

Local Example ex_toMLGoal {Σ : Signature} Γ (p : Pattern) :
well_formed p ->
Γ ⊢i p ---> p using BasicReasoning.
Proof.
intros wfp.
toMLGoal.
{ wf_auto2. }
match goal with
| [ |- of_MLGoal (@mkMLGoal Σ Γ [] (p ---> p) BasicReasoning) ] => idtac
| _ => fail
end.
fromMLGoal.
Abort.

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
@mkMLGoal Σ Γ l (x ---> g) i ->
@mkMLGoal Σ Γ (l ++ [mkNH n x]) g i.
Proof.
intros H.
unfold of_MLGoal in H. simpl in H.
unfold of_MLGoal. simpl. intros wfxig wfl.

unfold patterns_of in wfl.
rewrite map_app in wfl.
feed specialize H.
{
  abstract (
      apply wfapp_proj_2 in wfl;
      unfold Pattern.wf in wfl;
      simpl in wfl;
      rewrite andbT in wfl;
      wf_auto2
    ).
}
{
  abstract (apply wfapp_proj_1 in wfl; exact wfl).
}

eapply cast_proof'.
{ unfold patterns_of. rewrite map_app.  rewrite foldr_app. simpl. reflexivity. }
exact H.
Defined.

#[global]
Ltac mlRevertLast :=
match goal with
| |- @of_MLGoal ?Sgm (@mkMLGoal ?Sgm ?Ctx ?l ?g ?i)
=> eapply cast_proof_ml_hyps;
   [(rewrite -[l](take_drop (length l - 1)); rewrite [take _ _]/=; rewrite [drop _ _]/=; reflexivity)|];
   apply MLGoal_revertLast
end.

Lemma pile_evs_subseteq {Σ : Signature} evs1 evs2 svs kt fp:
  evs1 ⊆ evs2 ->
  ProofInfoLe
    ((ExGen := evs1, SVSubst := svs, KT := kt, FP := fp))
    ((ExGen := evs2, SVSubst := svs, KT := kt, FP := fp)).
Proof.
  intros Hsub.
  constructor.
  intros Γ ϕ pf Hpf.
  destruct Hpf as [Hpf2 Hpf3 Hpf4 Hpf5].
  constructor; simpl in *.
  { clear -Hsub Hpf2. set_solver. }
  { exact Hpf3. }
  { exact Hpf4. }
  { apply Hpf5. }
Qed.

Lemma pile_svs_subseteq {Σ : Signature} evs svs1 svs2 kt fp:
  svs1 ⊆ svs2 ->
  ProofInfoLe
    ( (ExGen := evs, SVSubst := svs1, KT := kt, FP := fp))
    ( (ExGen := evs, SVSubst := svs2, KT := kt, FP := fp)).
Proof.
  intros Hsub.
  constructor.
  intros Γ ϕ pf Hpf.
  destruct Hpf as [Hpf2 Hpf3 Hpf4 Hpf5].
  constructor; simpl in *.
  { exact Hpf2. }
  { clear -Hsub Hpf3. set_solver. }
  { exact Hpf4. }
  { exact Hpf5. }
Qed.

Lemma pile_kt_impl {Σ : Signature} evs svs kt1 kt2 fp:
  kt1 ==> kt2 ->
  ProofInfoLe
    ((ExGen := evs, SVSubst := svs, KT := kt1, FP := fp))
    ((ExGen := evs, SVSubst := svs, KT := kt2, FP := fp)).
Proof.
  intros Hsub.
  constructor.
  intros Γ ϕ pf Hpf.
  destruct Hpf as [Hpf2 Hpf3 Hpf4 Hpf5].
  constructor; simpl in *.
  { exact Hpf2. }
  { exact Hpf3. }
  { unfold implb in *.  destruct (uses_kt pf),kt1; simpl in *; try reflexivity.
    { exact Hsub. }
    { inversion Hpf4. }
  }
  { apply Hpf5. }
Qed.

Lemma pile_fp_subseteq  {Σ : Signature} evs svs kt fp1 fp2:
  fp1 ⊆ fp2 ->
  ProofInfoLe
    ((ExGen := evs, SVSubst := svs, KT := kt, FP := fp1))
    ((ExGen := evs, SVSubst := svs, KT := kt, FP := fp2)).
Proof.
  intros Hsub.
  constructor.
  intros Γ ϕ pf Hpf.
  destruct Hpf as [Hpf2 Hpf3 Hpf4 Hfp5].
  constructor; simpl in *.
  { exact Hpf2. }
  { exact Hpf3. }
  { exact Hpf4. }
  { set_solver. }
Qed.


Lemma pile_evs_svs_kt {Σ : Signature} evs1 evs2 svs1 svs2 kt1 kt2 fp1 fp2:
evs1 ⊆ evs2 ->
svs1 ⊆ svs2 ->
kt1 ==> kt2 ->
fp1 ⊆ fp2 ->
ProofInfoLe
  ((ExGen := evs1, SVSubst := svs1, KT := kt1, FP := fp1))
  ((ExGen := evs2, SVSubst := svs2, KT := kt2, FP := fp2)).
Proof.
intros Hevs Hsvs Hkt Hfp.
eapply pile_trans.
{
  apply pile_evs_subseteq. apply Hevs.
}
eapply pile_trans.
{
  apply pile_svs_subseteq. apply Hsvs.
}
eapply pile_trans.
{
  apply pile_kt_impl.
  apply Hkt.
}
apply pile_fp_subseteq. apply Hfp.
Qed.




Lemma pile_any {Σ : Signature} i:
  ProofInfoLe i AnyReasoning.
Proof.
  unfold AnyReasoning.
  destruct i.
  apply pile_evs_svs_kt.
  { clear. set_solver. }
  { clear. set_solver. }
  { unfold implb. destruct pi_uses_kt; reflexivity. }
  { clear. set_solver. }
Qed.



Lemma pile_basic_generic {Σ : Signature} eg svs kt fp:
ProofInfoLe BasicReasoning ( (ExGen := eg, SVSubst := svs, KT := kt, FP := fp)).
Proof.
constructor.
intros Γ ϕ pf Hpf.
destruct Hpf as [Hpf2 Hpf3 Hpf4]. simpl in *.
constructor; simpl.
{ set_solver. }
{ set_solver. }
{ unfold implb in Hpf4. case_match.
  { inversion Hpf4. }
  simpl. reflexivity.
}
{ set_solver. }
Qed.

Lemma pile_basic_generic' {Σ : Signature} i:
ProofInfoLe BasicReasoning i.
Proof.
  destruct i.
  apply pile_basic_generic.
Qed.


Tactic Notation "_mlReshapeHypsByIdx" constr(n) :=
  unshelve (eapply (@cast_proof_ml_hyps _ _ _ _ _ _ _));
  [shelve|(apply f_equal; rewrite <- (firstn_skipn n); rewrite /firstn; rewrite /skipn; reflexivity)|idtac]
.

Tactic Notation "_mlReshapeHypsByName" constr(n) :=
  unshelve (eapply (@cast_proof_ml_hyps _ _ _ _ _ _ _));
  [shelve|(
    apply f_equal;
    lazymatch goal with
    | [|- _ = ?l] =>
      lazymatch (eval cbv in (find_hyp n l)) with
      | Some (?n, _) =>
        rewrite <- (firstn_skipn n);
        rewrite /firstn;
        rewrite /skipn;
        reflexivity
      end
    end
    )
  |idtac]
.

Ltac2 _mlReshapeHypsByName (name' : constr) :=
  ltac1:(name'' |- _mlReshapeHypsByName name'') (Ltac1.of_constr name')
.

Tactic Notation "_mlReshapeHypsBack" :=
  let hyps := fresh "hyps" in rewrite [hyps in @mkMLGoal _ _ hyps _]/app
.

Ltac2 _mlReshapeHypsBack () :=
  ltac1:(_mlReshapeHypsBack)
.