From Coq Require Import ssreflect ssrfun ssrbool.

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

(* Exports *)
Export MatchingLogic.ProofSystem.

Set Default Proof Mode "Classic".

Open Scope ml_scope.

Record named_hypothesis {Σ : Signature} := mkNH
  {
    nh_name : string;
    nh_patt : Pattern;
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
  := mkMLGoal Σ Γ nil goal pi.

Coercion of_MLGoal {Σ : Signature} (MG : MLGoal) : Type :=
  well_formed (mlConclusion MG) ->
  Pattern.wf (patterns_of (mlHypotheses MG)) ->
  (mlTheory MG) ⊢i (fold_right patt_imp (mlConclusion MG) (patterns_of (mlHypotheses MG)))
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
       [(unfold of_MLGoal; simpl; let H := fresh "H" in intros H; apply H; clear H; [|reflexivity])|]
  end.

Ltac fromMLGoal := unfold of_MLGoal; simpl; intros _ _.

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
  mkMLGoal Σ Γ hyps goal i ->
  mkMLGoal Σ Γ hyps' goal i.
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
  mkMLGoal Σ Γ hyps goal i ->
  mkMLGoal Σ Γ hyps goal' i .
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
  mkMLGoal _ Γ (l ++ [mkNH _ name x]) g i ->
  mkMLGoal _ Γ l (x ---> g) i.
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
  unshelve (eapply (cast_proof' _ _ _ _ _ H)).
  { unfold patterns_of. rewrite map_app foldr_app. simpl. reflexivity. }
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

Ltac _enterProofMode :=
  toMLGoal;[wf_auto2|]
.

Ltac _ensureProofMode :=
  lazymatch goal with
  | [ |- of_MLGoal (mkMLGoal _ _ _ _ _)] => idtac
  | _ => _enterProofMode
  end
.

Tactic Notation "mlIntro" constr(name') :=
  _ensureProofMode;
  _failIfUsed name';
  apply MLGoal_intro with (name := name');
  simplLocalContext
.

Tactic Notation "mlIntro" :=
  _ensureProofMode;
  let hyps := _getHypNames in
  let name' := eval cbv in (fresh hyps) in
  mlIntro name'
.

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

Local Example ex_mlIntro {Σ : Signature} Γ a (i : ProofInfo) :
  well_formed a ->
  Γ ⊢i a ---> a ---> a ---> a ---> a using i.
Proof.
  intros wfa.
  (* This happens automatically *)
  (*
  toMLGoal.
  { wf_auto2. }
  *)
  
  mlIntro "h"%string.
  Fail mlIntro "h"%string.
  mlIntro "h'"%string.
  do 2 mlIntro.
Abort.

Lemma MLGoal_revertLast {Σ : Signature} (Γ : Theory) (l : hypotheses) (x g : Pattern) (n : string) i :
  mkMLGoal Σ Γ l (x ---> g) i ->
  mkMLGoal Σ Γ (l ++ [mkNH _ n x]) g i.
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
| |- @of_MLGoal ?Sgm (mkMLGoal ?Sgm ?Ctx ?l ?g ?i)
=> eapply cast_proof_ml_hyps;
   [(rewrite -[l](take_drop (length l - 1)); rewrite [take _ _]/=; rewrite [drop _ _]/=; reflexivity)|];
   apply MLGoal_revertLast
end.

Close Scope ml_scope.