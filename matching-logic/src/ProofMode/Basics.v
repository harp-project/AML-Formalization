From Coq Require Import ssreflect ssrfun ssrbool.

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
  ProofInfo
  wftactics
  Experimental.ProofModePattern
.

From stdpp Require Import list tactics fin_sets coGset gmap sets.

Import
  MatchingLogic.Utils.stdpp_ext
  MatchingLogic.Utils.extralibrary
  MatchingLogic.Syntax.Notations
  MatchingLogic.DerivedOperators_Syntax.Notations
  MatchingLogic.ProofSystem.Notations_private
  MatchingLogic.ProofInfo.Notations
.

Set Default Proof Mode "Classic".

Open Scope ml_scope.

Record named_hypothesis {Σ : Signature} := mkNH
  {
    nh_name : string;
    nh_patt : Pattern; (* PMPattern *)
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
Definition patterns_of {Σ : Signature} (h : hypotheses) : list Pattern (*PMPattern*) := map nh_patt h.

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
    mlInfo : ProofInfo ;
  }.

Definition MLGoal_from_goal
  {Σ : Signature} (Γ : Theory) (goal : Pattern) (pi : ProofInfo)
  :
  MLGoal
  := mkMLGoal Σ Γ nil goal pi.

(*
Lemma wf_pmp_to_ln
  {Σ : Signature}
  (ϕ : PMPattern)
  :
  Pattern.well_formed (PMPattern_to_ln ϕ)
.
*)


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

Ltac2 _toMLGoal () :=
  unfold derives;
  lazy_match! goal with
  | [ |- ?g ⊢i ?phi using ?pi]
    => (Std.cut constr:(of_MLGoal (MLGoal_from_goal $g $phi $pi));cbn)>
       [
       (unfold MLGoal_from_goal;
        unfold of_MLGoal;
         simpl;
         let h := Fresh.in_goal ident:(Halmost) in
         intros $h;
         let h_hyp := Control.hyp h in
         apply $h_hyp >
         [()|reflexivity]
       )
       |unfold MLGoal_from_goal]

  end.

Ltac2 Notation "toMLGoal" :=
  _toMLGoal ()
.

Tactic Notation "toMLGoal" :=
  ltac2:(_toMLGoal ())
.

Ltac2 _fromMLGoal () :=
  unfold of_MLGoal;
  simpl;
  intros _ _
.

Ltac2 Notation "fromMLGoal" :=
  _fromMLGoal ()
.

Tactic Notation "fromMLGoal" :=
  ltac2:(_fromMLGoal ())
.

Lemma mlUseBasicReasoning
  {Σ : Signature} (Γ : Theory) (l : hypotheses) (g : Pattern) (i : ProofInfo) :
  mkMLGoal Σ Γ l g BasicReasoning ->
  mkMLGoal Σ Γ l g i.
Proof.
  intros H wf1 wf2.
  specialize (H wf1 wf2).
  apply useBasicReasoning.
  exact H.
Defined.


Ltac2 _useBasicReasoning () :=
  Control.enter ( fun () =>
    unfold derives;
    lazy_match! goal with
    | [ |- of_MLGoal (mkMLGoal _ _ _ _ _) ] => apply mlUseBasicReasoning
    | [ |- _ ⊢i _ using _ ] => apply useBasicReasoning
    end
  )
.

Ltac2 Notation "useBasicReasoning" :=
  _useBasicReasoning ()
.

Tactic Notation "useBasicReasoning" :=
  ltac2:(_useBasicReasoning ())
.

Lemma mlUseGenericReasoning
  {Σ : Signature} (Γ : Theory) (l : hypotheses) (g : Pattern) (i i' : ProofInfo) :
  ProofInfoLe i i' ->
  mkMLGoal Σ Γ l g i ->
  mkMLGoal Σ Γ l g i'.
Proof.
  intros pile H wf1 wf2.
  specialize (H wf1 wf2).
  simpl in *.
  destruct i.
  eapply useGenericReasoning.
  { apply pile. }
  exact H.
Defined.

(* Extracts well-formedness assumptions about (local) goal and (local) hypotheses. *)
Ltac2 _mlExtractWF (wfl : ident) (wfg : ident) :=
  Control.enter(fun () =>
    lazy_match! goal with
    | [ |- ?g ] =>
      let wfl' := Fresh.in_goal ident:(wfl') in
      let wfg' := Fresh.in_goal ident:(wfg') in
      intros $wfg' $wfl';
      assert ($wfl := &wfl');
      assert ($wfg := &wfg');
      revert $wfg' $wfl';
      fold $g;
      unfold mlConclusion in $wfg;
      unfold mlHypotheses in $wfl
    end
).

Ltac2 Notation "mlExtractWF" wfl(ident) wfg(ident) :=
  _mlExtractWF wfl wfg
.

Tactic Notation "mlExtractWF" ident(wfl) ident(wfg) :=
  let f := ltac2:(wfl wfg |- _mlExtractWF (Option.get (Ltac1.to_ident wfl)) (Option.get (Ltac1.to_ident wfg))) in
  f wfl wfg
.

Local Example ex_extractWfAssumptions {Σ : Signature} Γ (p : Pattern) :
  well_formed p ->
  Γ ⊢i p ---> p using BasicReasoning.
Proof.
  intros wfp.
  toMLGoal.
  {
    wf_auto2.
  }
  (*{ wf_auto2. }*)
  mlExtractWF wfl wfg.
  (* These two asserts by assumption only test presence of the two hypotheses *)
  assert (Pattern.wf []) by assumption.
  assert (well_formed (p ---> p)) by assumption.
Abort.

(* We no longer have the original `cast_proof` thing;
   however, something we may want to rewrite only in the local hypotheses
   part of a goal, for which a lemma like this is useful.
*)
Lemma cast_proof_ml_hyps {Σ : Signature} Γ hyps hyps' (e : patterns_of hyps = patterns_of hyps') goal (i : ProofInfo) :
  mkMLGoal Σ Γ hyps goal i ->
  mkMLGoal Σ Γ hyps' goal i.
Proof.
  unfold of_MLGoal. simpl. intros H.
  intros wfg wfhyps'.
  feed specialize H.
  { exact wfg. }
  { rewrite e. exact wfhyps'. }
  rewrite -e.
  exact H.
Defined.

Ltac2 do_mlReshapeHypsByIdx (n:constr) :=
  ltac1:(unshelve ltac2:(eapply (@cast_proof_ml_hyps _ _ _ _ _ _ _)))>
  [ltac1:(shelve)|(apply f_equal; rewrite <- (firstn_skipn $n); ltac1:(rewrite /firstn); ltac1:(rewrite /skipn); reflexivity)|()]
.

Ltac2 Notation "mlReshapeHypsByIdx" n(constr) :=
  do_mlReshapeHypsByIdx n
.

Tactic Notation "_mlReshapeHypsByIdx" constr(n) :=
  let f := ltac2:(n |- (do_mlReshapeHypsByIdx (Option.get (Ltac1.to_constr n)))) in
  f n
.
(* Tactic Notation "_mlReshapeHypsByName" constr(n) :=
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
. *)

Ltac2 do_mlReshapeHypsByName (name : constr) :=
  match! goal with
  | [ |- @of_MLGoal _ (@mkMLGoal _ _ ?l _ _) ] =>
    match! (eval cbv in (index_of $name (names_of $l))) with
    | (Some ?i) => do_mlReshapeHypsByIdx i
    | None => Message.print (Message.concat (Message.of_string "No such name: ") (Message.of_constr name))
    end
  end
.

Ltac2 _mlReshapeHypsByName (name' : constr) :=
  do_mlReshapeHypsByName name'
.

Tactic Notation "_mlReshapeHypsByName" constr(name) :=
  let f := ltac2:(name |- do_mlReshapeHypsByName (Option.get (Ltac1.to_constr name))) in
  f name
.

Ltac2 do_mlReshapeHypsBack () :=
  Control.enter (fun () =>
    let hyps := Fresh.in_goal ident:(hyps) in
    ltac1:(hyps |- rewrite [hyps in mkMLGoal _ _ hyps _]/app) (Ltac1.of_ident hyps)
  )
.

Ltac2 Notation "_mlReshapeHypsBack" :=
  do_mlReshapeHypsBack ()
.

Tactic Notation "_mlReshapeHypsBack" :=
  ltac2:(do_mlReshapeHypsBack ())
.

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
  unfold patterns_of in H. rewrite map_app foldr_app in H. simpl in H.
  exact H.
Defined.

Ltac2 _simplLocalContext () :=
  lazy_match! goal with
    | [ |- @of_MLGoal ?sgm (mkMLGoal ?sgm ?ctx ?l ?g ?i) ]
      => let f := ltac1:(l |- rewrite {1}[l]/app) in
         (f (Ltac1.of_constr l))
  end.

Ltac2 Notation "simplLocalContext" :=
  _simplLocalContext ()
.

Tactic Notation "simplLocalContext" :=
  ltac2:(_simplLocalContext ())
.


Ltac2 do_getHypNames () : constr :=
  lazy_match! goal with
  | [ |- of_MLGoal (mkMLGoal _ _ ?l _ _) ]
    => eval lazy in (names_of $l)
  end.

Ltac2 Notation "getHypNames" :=
  do_getHypNames ()
.

(* [do_getHypNames ()] returns a value, which is imho not doable with ltac1 notations *)
(* Tactic Notation "getHypNames" := ???. *)

(* Tactic Notation "_failIfUsed" constr(name) :=
  lazymatch goal with
  | [ |- of_MLGoal (mkMLGoal _ _ ?l _ _) ] =>
    lazymatch (eval cbv in (find_hyp name l)) with
    | Some _ => fail "The name" name "is already used"
    | _ => idtac
    end
  end. *)

Ltac2 do_failIfUsed (name : constr) :=
lazy_match! goal with
| [ |- of_MLGoal (mkMLGoal _ _ ?l _ _) ] =>
  lazy_match! (eval cbv in (find (fun x => String.eqb x $name) (names_of $l))) with
  | Some _ => Message.print (
    Message.concat
      (Message.of_string "The name ")
      (Message.concat (Message.of_constr name) (Message.of_string " is already used")));
      fail
  | _ => () (* should not fail on other values*)
  end
end.

Ltac2 Notation "_failIfUsed" name(constr) :=
  do_failIfUsed name
.

Tactic Notation "_failIfUsed" constr(name) :=
  ltac2:(name |- do_failIfUsed (Option.get (Ltac1.to_constr name)))
.

Ltac2 do_introAllWf () :=
  unfold is_true;
  repeat (
    lazy_match! goal with
    | [ |- well_formed _ = true -> _ ] =>
      let h := Fresh.in_goal ident:(Hwf) in
      intros $h
    | [ |- Pattern.wf _ = true -> _ ] =>
      let h := Fresh.in_goal ident:(Hwfl) in
      intros $h
    end
  )
.

Ltac2 Notation "_introAllWf" :=
  do_introAllWf ()
.

Tactic Notation "_introAllWf" :=
  ltac2:(do_introAllWf ())
.

Ltac2 wf_auto2 () :=
  ltac1:(wf_auto2)
.

Ltac2 do_enterProofMode () :=
  _introAllWf;toMLGoal>[wf_auto2 ()|]
.

Ltac2 Notation "_enterProofMode" :=
  do_enterProofMode ()
.

Tactic Notation "_enterProofMode" :=
  ltac2:(do_enterProofMode ())
.

Ltac2 do_ensureProofMode () :=
  lazy_match! goal with
  | [ |- of_MLGoal (mkMLGoal _ _ _ _ _)] => ()
  | [ |- _] => do_enterProofMode ()
  end
.

Ltac2 Notation "_ensureProofMode" :=
  do_ensureProofMode ()
.

Tactic Notation "_ensureProofMode" :=
  ltac2:(do_ensureProofMode ())
.

Ltac2 do_mlIntro (name' : constr) :=
  Control.enter(fun () => 
    do_ensureProofMode ();
    do_failIfUsed name';
    apply MLGoal_intro with (name := $name');
    simplLocalContext
  )
.

Ltac2 Notation "mlIntro" name(constr) :=
  do_mlIntro name
.

Tactic Notation "mlIntro" constr(name') :=
  let f := ltac2:(name' |- do_mlIntro (Option.get (Ltac1.to_constr name'))) in
  f name'
.

Ltac2 do_mlIntro_anon () :=
  Control.enter(fun () => 
    do_ensureProofMode ();
    let hyps := do_getHypNames () in
    let name' := eval cbv in (fresh $hyps) in
    mlIntro $name'
  )
.

Ltac2 Notation "mlIntro" :=
  do_mlIntro_anon ()
.

Tactic Notation "mlIntro" :=
  ltac2:(do_mlIntro_anon ())
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

  unfold patterns_of. rewrite map_app.  rewrite foldr_app. simpl.
  exact H.
Defined.

(* Just a conveniece *)
Lemma cast_proof' {Σ : Signature} (Γ : Theory) (ϕ ψ : Pattern) (i : ProofInfo) (e : ψ = ϕ) :
  Γ ⊢i ϕ using i ->
  Γ ⊢i ψ using i.
Proof.
  intros H. rewrite e. exact H.
Defined.

#[global]
Ltac2 do_mlRevertLast () :=
  Control.enter(fun () =>
    lazy_match! goal with
    | [|- @of_MLGoal ?sgm (mkMLGoal ?sgm ?ctx ?l ?g ?i)]
    => eapply cast_proof_ml_hyps>
      [(ltac1:(l |- rewrite -[l](take_drop (length l - 1)); rewrite [take _ _]/=; rewrite [drop _ _]/=) (Ltac1.of_constr l); reflexivity)|()];
      apply MLGoal_revertLast
    end
  )
.

Ltac2 Notation "mlRevertLast" :=
  do_mlRevertLast ()
.

Ltac mlRevertLast :=
  ltac2:(do_mlRevertLast ())
.

Close Scope ml_scope.