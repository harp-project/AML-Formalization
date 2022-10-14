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

Definition connect {Σ : Signature} := (fun h => fun i =>
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

Close Scope ml_scope.