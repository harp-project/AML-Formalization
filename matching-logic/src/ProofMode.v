From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Ltac2 Require Import Ltac2.

From Coq Require Import Ensembles Bool.
From Coq.Logic Require Import FunctionalExtensionality Eqdep_dec.
Require Import Unicoq.Unicoq.
From Equations Require Import Equations.

Require Import Coq.Program.Tactics.

From MatchingLogic Require Import Syntax Semantics DerivedOperators ProofSystem.

From stdpp Require Import list tactics fin_sets.

From MatchingLogic.Utils Require Import stdpp_ext.

Import extralibrary.

Import
  MatchingLogic.Syntax.Notations
  MatchingLogic.DerivedOperators.Notations
  MatchingLogic.ProofSystem.Notations
.

Set Default Proof Mode "Classic".

Open Scope ml_scope.


(* TODO: move wf and related lemmas to Syntax.v *)

  Definition wf {Σ : Signature} (l : list Pattern) := fold_right andb true (map well_formed l).

  (* TODO: maybe generalize to any connective? *)
  Lemma well_formed_foldr {Σ : Signature} g xs :
    well_formed g = true ->
    wf xs = true ->
    well_formed (foldr patt_imp g xs) = true.
  Proof.
    intros wfg wfxs.
    induction xs.
    - simpl. exact wfg.
    - simpl. unfold wf in wfxs. simpl in wfxs.
      apply andb_prop in wfxs. destruct wfxs. auto.
  Qed.

  #[local] Hint Resolve well_formed_foldr : core.
  
  Lemma wf_take {Σ : Signature} n xs :
    wf xs = true ->
    wf (take n xs) = true.
  Proof.
    unfold wf. intros H.
    rewrite map_take.
    rewrite foldr_andb_true_take; auto.
  Qed.

  #[local] Hint Resolve wf_take : core.

  Lemma wf_drop {Σ : Signature} n xs:
    wf xs = true ->
    wf (drop n xs) = true.
  Proof.
    unfold wf. intros H.
    rewrite map_drop.
    rewrite foldr_andb_true_drop; auto.
  Qed.

  #[local] Hint Resolve wf_drop : core.

  Lemma wf_insert {Σ : Signature} n p xs:
    wf xs = true ->
    well_formed p = true ->
    wf (<[n := p]> xs) = true.
  Proof.
    intros wfxs wfp.
    move: xs wfxs.
    induction n; intros xs wfxs; destruct xs; simpl; auto.
    - unfold wf in wfxs. simpl in wfxs. apply andb_prop in wfxs.
      destruct wfxs as [wfp0 wfxs].
      unfold wf. simpl. rewrite wfp. rewrite wfxs.
      reflexivity.
    - unfold wf in wfxs. simpl in wfxs. apply andb_prop in wfxs.
      destruct wfxs as [wfp0 wfxs].
      unfold wf. simpl.
      unfold wf in IHn.
      rewrite wfp0.
      rewrite IHn; auto.
  Qed.

  #[local] Hint Resolve wf_insert : core.

  Lemma wf_tail' {Σ : Signature} p xs:
    wf (p :: xs) = true ->
    wf xs = true.
  Proof.
    unfold wf. intros H. simpl in H. apply andb_prop in H. rewrite (proj2 H). reflexivity.
  Qed.

  #[local] Hint Resolve wf_tail' : core.

  Lemma wf_cons {Σ : Signature} x xs:
    well_formed x = true ->
    wf xs = true ->
    wf (x :: xs) = true.
  Proof.
    intros wfx wfxs.
    unfold wf. simpl. rewrite wfx.
    unfold wf in wfxs. rewrite wfxs.
    reflexivity.
  Qed.

  #[local] Hint Resolve wf_cons : core.
  
  Lemma wf_app {Σ : Signature} xs ys:
    wf xs = true ->
    wf ys = true ->
    wf (xs ++ ys) = true.
  Proof.
    intros wfxs wfys.
    unfold wf in *.
    rewrite map_app.
    rewrite foldr_app.
    rewrite wfys.
    rewrite wfxs.
    reflexivity.
  Qed.

  #[local] Hint Resolve wf_app : core.


Record MyGoal {Σ : Signature} : Type := mkMyGoal { mgTheory : Theory; mgHypotheses: list Pattern; mgConclusion : Pattern }.

Definition MyGoal_from_goal {Σ : Signature} (Γ : Theory) (goal : Pattern) : MyGoal := @mkMyGoal Σ Γ nil goal.

Notation "[ S , G ⊢ l ==> g ]" := (@mkMyGoal S G l g).


Coercion of_MyGoal {Σ : Signature} (MG : MyGoal) : Type :=
  well_formed (mgConclusion MG) ->
  wf (mgHypotheses MG) ->
  (mgTheory MG) ⊢ (fold_right patt_imp (mgConclusion MG) (mgHypotheses MG)).

Ltac toMyGoal :=
  lazymatch goal with
  | [ |- ?G ⊢ ?phi ]
    => cut (of_MyGoal (MyGoal_from_goal G phi));
       unfold MyGoal_from_goal;
       [(unfold of_MyGoal; simpl; let H := fresh "H" in intros H; apply H; clear H; [|reflexivity])|]
  end.

Ltac fromMyGoal := unfold of_MyGoal; simpl.


(*
Structure myNWFProofProperty
          {Σ : Signature} (P : proofbpred) (Γ : Theory) (l : list Pattern) (g : Pattern)
  := MyNWFProofProperty
       { mnpp_proof : of_MyGoal (mkMyGoal Γ l g) ;
         mnpp_proof_property :
         forall wfg wfl,
           P Γ (foldr patt_imp g l)
             (mnpp_proof wfg wfl) = false ;
       }.
*)

Class IndifCast {Σ : Signature} (P : proofbpred)
  := mkIndifCast { cast_indif : indifferent_to_cast P }.

Class IndifProp {Σ : Signature} (P : proofbpred)
  := mkIndifProp { prop_indif : indifferent_to_prop P }.

#[export]
 Instance uses_svar_subst_IndifCast {Σ : Signature} (SvS : SVarSet) : IndifCast (@uses_svar_subst Σ SvS)
  := mkIndifCast (indifferent_to_cast_uses_svar_subst SvS).

#[export]
 Instance uses_svar_subst_IndifProp {Σ : Signature} (SvS : SVarSet) : IndifProp (@uses_svar_subst Σ SvS)
  := mkIndifProp (indifferent_to_prop_uses_svar_subst SvS).

#[export]
 Instance uses_ex_gen_IndifCast {Σ : Signature} (EvS : EVarSet) : IndifCast (@uses_ex_gen Σ EvS)
  := mkIndifCast (indifferent_to_cast_uses_ex_gen EvS).

#[export]
 Instance uses_ex_gen_IndifProp {Σ : Signature} (EvS : EVarSet) : IndifProp (@uses_ex_gen Σ EvS)
  := mkIndifProp (indifferent_to_prop_uses_ex_gen EvS).

#[export]
 Instance uses_kt_IndifCast {Σ : Signature} : IndifCast (@uses_kt Σ)
  := mkIndifCast (indifferent_to_cast_uses_kt).

#[export]
 Instance uses_kt_IndifProp {Σ : Signature} : IndifProp (@uses_kt Σ)
  := mkIndifProp (indifferent_to_prop_uses_kt).


Structure proofProperty0 {Σ : Signature} (P : proofbpred) (Γ : Theory) (ϕ : Pattern)
  := ProofProperty0 { pp0_proof : Γ ⊢ ϕ; pp0_proof_property : P Γ ϕ pp0_proof = false  }.

Arguments ProofProperty0 [Σ] P [Γ ϕ] pp0_proof _.

Structure proofProperty1 {Σ : Signature} (P : proofbpred) (Γ : Theory) (ϕ ψ₁ : Pattern)
  := ProofProperty1 {
      pp1_proof : Γ ⊢ ψ₁ -> Γ ⊢ ϕ;
      pp1_proof_property :
      forall (pf₁ : Γ ⊢ ψ₁),
        P Γ ψ₁ pf₁ = false ->
        P Γ ϕ (pp1_proof pf₁) = false;
    }.

Arguments ProofProperty1 [Σ] P [Γ ϕ ψ₁] pp1_proof%function_scope _%function_scope.

Structure proofProperty2 {Σ : Signature} (P : proofbpred) (Γ : Theory) (ϕ ψ₁ ψ₂ : Pattern)
  := ProofProperty2 {
      pp2_proof : Γ ⊢ ψ₁ -> Γ ⊢ ψ₂ -> Γ ⊢ ϕ;
      pp2_proof_property :
      forall (pf₁ : Γ ⊢ ψ₁) (pf₂ : Γ ⊢ ψ₂),
        P Γ ψ₁ pf₁ = false ->
        P Γ ψ₂ pf₂ = false ->
        P Γ ϕ (pp2_proof pf₁ pf₂) = false;
    }.

Arguments ProofProperty2 [Σ] P [Γ ϕ ψ₁ ψ₂] pp2_proof%function_scope _%function_scope.

Ltac2 mutable solve_indif () := ltac1:(repeat (
                        eapply pp0_proof_property
                        || eapply pp1_proof_property
                        || eapply pp2_proof_property)).

Ltac solve_indif := ltac2:(solve_indif ()).


Program Canonical Structure P1_pp0 {Σ : Signature} (P : proofbpred) {Pip : IndifProp P}
          (Γ : Theory) (ϕ₁ ϕ₂ : Pattern) (wfϕ₁ : well_formed ϕ₁) (wfϕ₂ : well_formed ϕ₂)
:= ProofProperty0 P (@P1 Σ Γ ϕ₁ ϕ₂ wfϕ₁ wfϕ₂) _.
Next Obligation.
  intros Σ P [[Hp1 [Hp2 [Hp3 Hmp]]]] ?????.
  apply Hp1.
Qed.

Program Canonical Structure P2_pp0 {Σ : Signature} (P : proofbpred) {Pip : IndifProp P}
          (Γ : Theory) (ϕ₁ ϕ₂ ϕ₃ : Pattern)
          (wfϕ₁ : well_formed ϕ₁) (wfϕ₂ : well_formed ϕ₂) (wfϕ₃ : well_formed ϕ₃)
:= ProofProperty0 P (@P2 Σ Γ ϕ₁ ϕ₂ ϕ₃ wfϕ₁ wfϕ₂ wfϕ₃) _.
Next Obligation.
  intros Σ P [[Hp1 [Hp2 [Hp3 Hmp]]]] ???????.
  apply Hp2.
Qed.

Program Canonical Structure P3_pp0 {Σ : Signature} (P : proofbpred) {Pip : IndifProp P}
          (Γ : Theory) (ϕ₁ : Pattern) (wfϕ₁ : well_formed ϕ₁)
:= ProofProperty0 P (@P3 Σ Γ ϕ₁ wfϕ₁) _.
Next Obligation.
  intros Σ P [[Hp1 [Hp2 [Hp3 Hmp]]]] ???.
  apply Hp3.
Qed.

Program Canonical Structure MP_pp2 {Σ : Signature} (P : proofbpred) {Pip : IndifProp P}
          (Γ : Theory) (ϕ₁ ϕ₂ : Pattern) (wfϕ₁ : well_formed ϕ₁) (wfϕ₁₂ : well_formed (ϕ₁ ---> ϕ₂))
:= ProofProperty2 P (fun pf1 pf2 => @Modus_ponens Σ Γ ϕ₁ ϕ₂ wfϕ₁ wfϕ₁₂ pf1 pf2) _.
Next Obligation.
  intros Σ P [[Hp1 [Hp2 [Hp3 Hmp]]]] ??????? H1 H2.
  rewrite Hmp. apply orb_false_intro. exact H1. exact H2.
Qed.

Program Canonical Structure cast_proof_indifferent_S
        {Σ : Signature} (P : proofbpred) {Pic : IndifCast P} (Γ : Theory)
        (ϕ ψ : Pattern) (e : ψ = ϕ)
  := ProofProperty1 P (@cast_proof Σ Γ ϕ ψ e) _.
Next Obligation. intros. destruct Pic as [hic]. rewrite hic. exact H. Qed.


Section FOL_helpers.

  Context {Σ : Signature}.


  Lemma A_impl_A (Γ : Theory) (A : Pattern)  :
    (well_formed A) -> Γ ⊢ (A ---> A).
  Proof. 
    intros WFA.
    epose proof (_1 := P2 Γ A (A ---> A) A _ _ _).
    epose proof (_2 := P1 Γ A (A ---> A) _ _).

    epose proof (_3 := Modus_ponens _ _ _ _ _ _2 _1). (*M_p th phi1 phi2 wf_phi1 wf_phi2 phi1_proved phi1->phi2_proved*)
    
    epose proof (_4 := P1 Γ A A _ _).
    
    epose proof (_5 := Modus_ponens Γ _ _ _ _ _4 _3).
    exact _5.
    Unshelve.

    all: auto 10.
  Defined.

  #[local] Hint Resolve A_impl_A : core.
  
  Lemma A_impl_A_indifferent
        P {HP : IndifProp P} Γ A (wfA : well_formed A):
    P _ _ (@A_impl_A Γ A wfA) = false.
  Proof.
    unfold A_impl_A.
    solve_indif.
  Qed.

  Canonical Structure A_impl_A_indifferent_S P {HP : IndifProp P} Γ A (wfA : well_formed A)
    := ProofProperty0 P _ (A_impl_A_indifferent Γ wfA).

  Lemma P4m (Γ : Theory) (A B : Pattern) :
    (well_formed A) -> (well_formed B) -> Γ ⊢ ((A ---> B) ---> ((A ---> !B) ---> !A)).
  Proof.
    intros WFA WFB. eapply (Modus_ponens Γ _ _ _ _).
    - eapply(P1 _ (A ---> B) (A ---> B ---> Bot) _ _).
    - eapply (Modus_ponens _ _ _ _ _).
      + eapply (Modus_ponens _ _ _ _ _).
        * eapply (Modus_ponens _ _ _ _ _).
          -- eapply(P2 _ A B Bot _ _ _).
          -- eapply(P2 _ (A ---> B ---> Bot) (A ---> B) (A ---> Bot) _ _ _).
        * eapply (P1 _ (((A ---> B ---> Bot) ---> A ---> B) ---> (A ---> B ---> Bot) ---> A ---> Bot)
                     (A ---> B) _ _).
      + eapply (P2 _ (A ---> B)
                   ((A ---> B ---> Bot) ---> A ---> B)
                   ((A ---> B ---> Bot) ---> A ---> Bot) _ _ _).
        Unshelve.
        all: auto 10.
  Defined.

  Program Canonical Structure P4m_indifferent_S P {HP : IndifProp P}
            Γ A B (wfA : well_formed A) (wfB: well_formed B)
    := ProofProperty0 P (P4m Γ wfA wfB) _.
  Next Obligation.
    intros. unfold P4m. solve_indif.
  Qed.


  Lemma P4i (Γ : Theory) (A : Pattern) :
    well_formed A -> Γ ⊢ ((A ---> !A) ---> !A).
  Proof.
    intros WFA. eapply (Modus_ponens _ _ _ _ _).
    - eapply (@A_impl_A _ A _). (*In the outdated: A_impl_A = P1*)
    - eapply (@P4m _ A A _ _).
      Unshelve.
      all: auto 10.
  Defined.

  Program Canonical Structure P4i_indifferent_S P {HP : IndifProp P}
            Γ A (wfA : well_formed A)
    := ProofProperty0 P (P4i Γ wfA) _.
  Next Obligation.
    intros. unfold P4m. solve_indif.
  Qed.


  Lemma reorder (Γ : Theory) (A B C : Pattern) :
    well_formed A -> well_formed B -> well_formed C -> Γ ⊢ ((A ---> B ---> C) ---> ( B ---> A ---> C)).
  Proof.
    intros WFA WFB WFC.
    epose proof (t1 := (Modus_ponens Γ _ _ _ _
                                     (P1 Γ ((A ---> B) ---> A ---> C) B _ _)
                                     (P1 Γ (((A ---> B) ---> A ---> C) ---> B ---> (A ---> B) ---> A ---> C) (A ---> B ---> C) _ _))).
    
    pose(ABC := (A ---> B ---> C)).
    
    eapply (Modus_ponens _ _ _ _ _).
    - eapply (Modus_ponens _ _ _ _ _).
      + eapply(P1 _ B A _ _).
      + eapply(P1 _ (B ---> A ---> B) (A ---> B ---> C) _ _).
    - eapply (Modus_ponens _ _ _ _ _).
      + eapply (Modus_ponens _ _ _ _ _).
        * eapply (Modus_ponens _ _ _ _ _).
          -- eapply (Modus_ponens _ _ _ _ _).
             ++ eapply (@A_impl_A _ ABC _).
             ++ eapply (Modus_ponens _ _ _ _ _).
                ** eapply (Modus_ponens _ _ _ _ _).
                   --- eapply(P2 _ A B C _ _ _).
                   --- eapply(P1 _ _ (A ---> B ---> C) _ _).
                ** eapply(P2 _ ABC ABC ((A ---> B) ---> (A ---> C)) _ _ _).
          -- eapply (Modus_ponens _ _ _ _ _).
             ++ eapply t1.
             ++ eapply(P2 _ ABC ((A ---> B) ---> (A ---> C)) (B ---> (A ---> B) ---> (A ---> C)) _ _ _).
        * eapply (Modus_ponens _ _ _ _ _).
          -- eapply (Modus_ponens _ _ _ _ _).
             ++ eapply(P2 _ B (A ---> B) (A ---> C) _ _ _).
             ++ eapply(P1 _ _ ABC _ _).
          -- eapply(P2 _ ABC (B ---> (A ---> B) ---> A ---> C) ((B ---> A ---> B) ---> B ---> A ---> C) _ _ _).
      + eapply(P2 _ ABC (B ---> A ---> B) (B ---> A ---> C) _ _ _).
        Unshelve.
        all: try unfold ABC; auto 10.
  Defined.

  Lemma reorder_indifferent
        P {HP : IndifProp P} Γ A B C
        (wfA : well_formed A)
        (wfB : well_formed B)
        (wfC : well_formed C):
    P _ _ (@reorder Γ A B C wfA wfB wfC) = false.
  Proof.
    unfold reorder. solve_indif.
  Qed.

  Canonical Structure reorder_indifferent_S P {HP : IndifProp P} Γ A B C
            (wfA : well_formed A) (wfB : well_formed B) (wfC : well_formed C)
    := ProofProperty0 P _ (reorder_indifferent Γ wfA wfB wfC).

  Lemma reorder_meta (Γ : Theory) {A B C : Pattern} :
    well_formed A -> well_formed B -> well_formed C ->  
    Γ ⊢ (A ---> B ---> C) -> Γ ⊢ (B ---> A ---> C).
  Proof.
    intros H H0 H1 H2.
    eapply (Modus_ponens _ _ _ _ _).
    - exact (P1 _ B A H0 H).
    - eapply (Modus_ponens _ _ _ _ _).
      + eapply (Modus_ponens _ _ _ _ _).
        * eapply (Modus_ponens _ _ _ _ _).
          -- exact H2.
          -- eapply(P2 _ A B C _ _ _).
        * assert (well_formed ((A ---> B) ---> A ---> C)).
          -- shelve. 
          -- exact (P1 _ ((A ---> B) ---> A ---> C) B H3 H0).
      + assert(well_formed (A ---> B)).
        * shelve.
        * assert(well_formed (A ---> C)).
          -- shelve.
          -- exact (P2 _ B (A ---> B) (A ---> C) H0 H3 H4).
             Unshelve.
             all:auto 10.
  Defined.

  Lemma reorder_meta_indifferent
        P {HP : IndifProp P} Γ A B C
        (wfA : well_formed A)
        (wfB : well_formed B)
        (wfC : well_formed C)
        (AimpBimpC : Γ ⊢ A ---> B ---> C):
    P _ _ AimpBimpC = false ->
    P _ _ (@reorder_meta Γ A B C wfA wfB wfC AimpBimpC) = false.
  Proof.
    intros H. solve_indif. assumption.
  Qed.

  Program Canonical Structure reorder_meta_indifferent_S
          (P : proofbpred) {Pip : IndifProp P}
          (Γ : Theory) (A B C : Pattern)
          (wfA : well_formed A) (wfB : well_formed B) (wfC : well_formed C)
    := ProofProperty1 P (fun pf1 => @reorder_meta Γ A B C wfA wfB wfC pf1) _.
  Next Obligation.
    intros. apply reorder_meta_indifferent; assumption.
  Qed.

  Lemma syllogism (Γ : Theory) (A B C : Pattern) :
    well_formed A -> well_formed B -> well_formed C -> Γ ⊢ ((A ---> B) ---> (B ---> C) ---> (A ---> C)).
  Proof.
    intros WFA WFB WFC.
    eapply (reorder_meta _ _ _).
    eapply (Modus_ponens _ _ _ _ _).
    - eapply(P1 _ (B ---> C) A _ _).
    - eapply (Modus_ponens _ _ _ _ _).
      + eapply (Modus_ponens _ _ _ _ _).
        * eapply (P2 _ A B C _ _ _).
        * eapply (P1 _ ((A ---> B ---> C) ---> (A ---> B) ---> A ---> C) (B ---> C) _ _).
      + eapply (P2 _ (B ---> C) (A ---> B ---> C) ((A ---> B) ---> A ---> C) _ _ _).
        Unshelve.
        all: auto 10.
  Defined.

  #[local] Hint Resolve syllogism : core.

  Lemma syllogism_indifferent
        P {Pip : IndifProp P} Γ A B C
        (wfA : well_formed A)
        (wfB : well_formed B)
        (wfC : well_formed C):
    P _ _ (@syllogism Γ A B C wfA wfB wfC) = false.
  Proof.
    unfold syllogism. solve_indif.
  Qed.

  Canonical Structure syllogism_indifferent_S P {HP : IndifProp P} Γ A B C
            (wfA : well_formed A) (wfB : well_formed B) (wfC : well_formed C)
    := ProofProperty0 P _ (syllogism_indifferent Γ wfA wfB wfC).

  
  Lemma syllogism_intro (Γ : Theory) (A B C : Pattern) :
    well_formed A -> well_formed B -> well_formed C -> Γ ⊢ (A ---> B) -> Γ ⊢ (B ---> C) -> Γ ⊢ (A ---> C).
  Proof.
    intros H H0 H1 H2 H3.
    eapply (Modus_ponens _ _ _ _ _).
    - exact H2.
    - eapply (Modus_ponens _ _ _ _ _).
      + exact H3.
      + eapply (reorder_meta _ _ _). exact (@syllogism _ A B C H H0 H1).
        Unshelve.
        all: auto.
  Defined.

  (* TODO: remove these hints *)
  #[local] Hint Resolve syllogism_intro : core.

  Lemma syllogism_intro_indifferent
        P {Pip : IndifProp P} Γ A B C
        (wfA : well_formed A)
        (wfB : well_formed B)
        (wfC : well_formed C)
        (AimpB : Γ ⊢ A ---> B)
        (BimpC : Γ ⊢ B ---> C):
    P _ _ AimpB = false ->
    P _ _ BimpC = false ->
    P _ _ (@syllogism_intro Γ A B C wfA wfB wfC AimpB BimpC) = false.
  Proof.
    intros H1 H2. unfold syllogism_intro. solve_indif; assumption.
  Qed.

  Program Canonical Structure syllogism_intro_indifferent_S (P : proofbpred) {Pip : IndifProp P}
          (Γ : Theory) (A B C : Pattern)
          (wfA : well_formed A)
          (wfB : well_formed B)
          (wfC : well_formed C)
    := ProofProperty2 P (fun pf1 pf2 => @syllogism_intro Γ A B C wfA wfB wfC pf1 pf2) _.
  Next Obligation.
    intros. apply syllogism_intro_indifferent; assumption.
  Qed.
  
  Lemma modus_ponens (Γ : Theory) ( A B : Pattern) :
    well_formed A -> well_formed B -> Γ ⊢ (A ---> (A ---> B) ---> B).
  Proof.
    intros WFA WFB.
    eapply (Modus_ponens _ _ _ _ _).
    - eapply (P1 _ A (A ---> B) _ _).
    - eapply (Modus_ponens _ _ _ _ _).
      + eapply (Modus_ponens _ _ _ _ _).
        * eapply (@A_impl_A _ (A ---> B) _).
        * eapply (P2 _ (A ---> B) A B _ _ _).
      + eapply (reorder_meta _ _ _).
        * eapply (@syllogism _ A ((A ---> B) ---> A) ((A ---> B) ---> B) _ _ _).
          Unshelve.
          all: auto 10.
  Defined.

  (* TODO: remove this hint *)
  #[local] Hint Resolve modus_ponens : core.
  
  Lemma modus_ponens_indifferent
        P {Pip : IndifProp P} Γ A B
        (wfA : well_formed A)
        (wfB : well_formed B):
    P _ _ (@modus_ponens Γ A B wfA wfB) = false.
  Proof.
    unfold modus_ponens. solve_indif.
  Qed.

  Lemma not_not_intro (Γ : Theory) (A : Pattern) :
    well_formed A -> Γ ⊢ (A ---> !(!A)).
  Proof.
    intros WFA.
    assert(@well_formed Σ Bot).
    shelve.
    exact (@modus_ponens _ A Bot WFA H).
    Unshelve.
    all: auto.
  Defined.

  #[local] Hint Resolve not_not_intro : core.

  (* FIXME this has a very wrong name. Do we need it at all? *)
  Lemma deduction (Γ : Theory) (A B : Pattern) :
    well_formed A -> well_formed B -> Γ ⊢ A -> Γ ⊢ B -> Γ ⊢ (A ---> B).
  Proof.
    intros WFA WFB H H0.
    eapply (Modus_ponens _ _ _ _ _).
    - exact H0.
    - eapply (P1 _ B A _ _).
      Unshelve.
      all: auto.
  Defined.

  Lemma P4_intro (Γ : Theory) (A B : Pattern)  :
    well_formed A -> well_formed B -> 
    Γ ⊢ ((! B) ---> (! A)) -> Γ ⊢ (A ---> B).
  Proof.
    intros H H0 H1.
    epose (@Modus_ponens _ Γ _ _ _ _ H1 (@P4m Γ (! B) (! A) _ _)).
    epose (P1 Γ (! !A) (! B) _ _).
    epose (@syllogism_intro Γ (! (! A)) (! B ---> ! (! A)) (! (! B)) _ _ _ m0 m).
    epose (@not_not_intro Γ A _).
    epose (@not_not_intro Γ B _).
    epose (@syllogism_intro Γ A (! (! A)) (! (! B)) _ _ _ m2 m1).
    unfold patt_not in m4.
    epose (P3 Γ B _).
    epose (@syllogism_intro Γ A ((B ---> Bot) ---> Bot) B _ _ _ m4 m5).
    exact m6.

    Unshelve.
    all: auto.
    auto 10.
  Defined.


  Lemma P4 (Γ : Theory) (A B : Pattern)  :
    well_formed A -> well_formed B -> 
    Γ ⊢ (((! A) ---> (! B)) ---> (B ---> A)).
  Proof.
    intros WFA WFB.
    epose (P3 Γ A _).
    epose (P1 Γ (((A ---> Bot) ---> Bot) ---> A) B _ _).
    epose (P2 Γ (B) ((A ---> Bot) ---> Bot) (A) _ _ _).
    epose (Modus_ponens Γ _ _ _ _ m m0).
    epose (Modus_ponens Γ _ _ _ _ m2 m1).
    epose (P1 Γ ((B ---> (A ---> Bot) ---> Bot) ---> B ---> A) ((A ---> Bot) ---> (B ---> Bot)) _ _ ).
    epose (Modus_ponens Γ _ _ _ _ m3 m4).
    epose (P2 Γ ((A ---> Bot) ---> (B ---> Bot)) (B ---> (A ---> Bot) ---> Bot) (B ---> A) _ _ _).
    epose (Modus_ponens Γ _ _ _ _ m5 m6).
    epose (@reorder Γ (A ---> Bot) (B) (Bot) _ _ _).
    eapply (Modus_ponens Γ _ _ _ _ m8 m7).
    Unshelve.
    all: auto 10.
  Defined.

  Lemma P4_indifferent
        P {Pip : IndifProp P} Γ a b
        (wfa : well_formed a = true)
        (wfb : well_formed b = true):
    P _ _ (@P4 Γ a b wfa wfb) = false.
  Proof.
    solve_indif.
  Qed.

  Program Canonical Structure P4_indifferent_S
          (P : proofbpred) {Pip : IndifProp P}
          (Γ : Theory) (A B : Pattern)
          (wfA : well_formed A) (wfB : well_formed B)
    := ProofProperty0 P (@P4 Γ A B wfA wfB) _.
  Next Obligation. intros. apply P4_indifferent; assumption. Qed.


  Lemma conj_intro (Γ : Theory) (A B : Pattern) :
    well_formed A -> well_formed B -> Γ ⊢ (A ---> B ---> (A and B)).
  Proof.
    intros WFA WFB.
    epose(tB := (@A_impl_A Γ B _)).
    epose(t1 := Modus_ponens Γ _ _ _ _ (P2 _ (!(!A) ---> !B) A Bot _ _ _)
                             (P1 _ _ B _ _)).
    epose(t2 := Modus_ponens Γ _ _ _ _  (reorder_meta _ _ _ (@P4 _ (!A) B _ _))
                             (P1 _ _ B _ _)).
    epose(t3'' := Modus_ponens Γ _ _ _ _ (P1 _ A (!(!A) ---> !B) _ _)
                               (P1 _ _ B _ _)).
    epose(t4 := Modus_ponens Γ _ _ _ _ tB
                             (Modus_ponens Γ _ _ _ _ t2
                                           (P2 _ B B _ _ _ _))).
    epose(t5'' := 
            Modus_ponens Γ _ _ _ _ t4
                         (Modus_ponens Γ _ _ _ _ t1
                                       (P2 _ B ((!(!A) ---> !B) ---> !A)
                                           (((!(!A) ---> !B) ---> A) ---> !(!(!A) ---> !B)) _ _ _))).
    
    epose(tA := (P1 Γ A B) _ _).
    epose(tB' := Modus_ponens Γ _ _ _ _ tB
                              (P1 _ (B ---> B) A _ _)).
    epose(t3' := Modus_ponens Γ _ _ _ _ t3''
                              (P2 _ B A ((!(!A) ---> !B) ---> A) _ _ _)).
    epose(t3 := Modus_ponens Γ _ _ _ _ t3'
                             (P1 _ ((B ---> A) ---> B ---> (! (! A) ---> ! B) ---> A) A _ _)).
    epose(t5' := Modus_ponens Γ _ _ _ _ t5''
                              (P2 _ B ((!(!A) ---> !B) ---> A) (!(!(!A) ---> !B)) _ _ _)).
    epose(t5 := Modus_ponens Γ _ _ _ _ t5' 
                             (P1 _ ((B ---> (! (! A) ---> ! B) ---> A) ---> B ---> ! (! (! A) ---> ! B))
                                 A _ _)).
    epose(t6 := Modus_ponens Γ _ _ _ _ tA
                             (Modus_ponens Γ _ _ _ _ t3
                                           (P2 _ A (B ---> A) (B ---> (!(!A) ---> !B) ---> A) _ _ _))).
    epose(t7 := Modus_ponens Γ _ _ _ _ t6 
                             (Modus_ponens Γ _ _ _ _ t5 
                                           (P2 _ A (B ---> (!(!A) ---> !B) ---> A) (B ---> !(!(!A) ---> !B)) _ _ _))).
    unfold patt_and.  unfold patt_or.
    exact t7.
    Unshelve.
    all: auto 10.
  Defined.

  Program Canonical Structure conj_intro_indifferent_S
          (P : proofbpred) {Pip : IndifProp P}
          (Γ : Theory) (A B : Pattern)
          (wfA : well_formed A) (wfB : well_formed B)
    := ProofProperty0 P (@conj_intro Γ A B wfA wfB) _.
  Next Obligation. intros. solve_indif. Qed.


  Lemma conj_intro_meta (Γ : Theory) (A B : Pattern) :
    well_formed A -> well_formed B -> Γ ⊢ A -> Γ ⊢ B -> Γ ⊢ (A and B).
  Proof.
    intros WFA WFB H H0.
    eapply (Modus_ponens _ _ _ _ _).
    - exact H0.
    - eapply (Modus_ponens _ _ _ _ _).
      + exact H.
      + exact (@conj_intro _ A B WFA WFB).
        Unshelve.
        all: auto.
  Defined.
  
  Lemma conj_intro_meta_indifferent
        P {Pip : IndifProp P} Γ A B
        (wfA : well_formed A)
        (wfB : well_formed B)
        (HA : Γ ⊢ A)
        (HB : Γ ⊢ B):
    P _ _ HA = false ->
    P _ _ HB = false ->
    P _ _ (@conj_intro_meta Γ A B wfA wfB HA HB) = false.
  Proof. intros H1 H2. solve_indif; assumption. Qed.

  Canonical Structure conj_intro_meta_indifferent_S
            (P : proofbpred) {Pip : IndifProp P}
          (Γ : Theory) (A B : Pattern)
          (wfA : well_formed A) (wfB : well_formed B)
    := ProofProperty2 P _ (@conj_intro_meta_indifferent P _ Γ _ _ wfA wfB).

  
  (* Lemma conj_intro_meta_e (Γ : Theory) (A B : Pattern) : *) 
  Definition conj_intro_meta_e := conj_intro_meta.    (*The same as conj_intro_meta*)

  Lemma disj (Γ : Theory) (A B : Pattern) :
    well_formed A -> well_formed B -> Γ ⊢ (A ---> B ---> (A or B)).
  Proof.
    intros WFA WFV. unfold patt_or.
    
    epose proof (t1 := (P1 Γ B (!A) _ _)).
    
    epose proof (t2 := (P1 Γ (B ---> (!A ---> B)) A _ _)).
    
    epose proof (t3 := Modus_ponens Γ _ _ _ _ t1 t2).
    
    exact t3.
    Unshelve.
    all: auto 10.
  Defined.

  Lemma disj_intro (Γ : Theory) (A B : Pattern) :
    well_formed A -> well_formed B -> Γ ⊢ A -> Γ ⊢ B -> Γ ⊢ (A or B).
  Proof.
    intros WFA WFB H H0.
    eapply (Modus_ponens _ _ _ _ _).
    - exact H0.
    - eapply (Modus_ponens _ _ _ _ _).
      + exact H.
      + exact (@disj _ A B WFA WFB).
        Unshelve.
        all: auto.
  Defined.

  Lemma syllogism_4_meta (Γ : Theory) (A B C D : Pattern) :
    well_formed A -> well_formed B -> well_formed C -> well_formed D ->
    Γ ⊢ (A ---> B ---> C) -> Γ ⊢ (C ---> D) -> Γ ⊢ (A ---> B ---> D).
  Proof.
    intros WFA WFB WFC WFD H H0.
    eapply (Modus_ponens _ _ _ _ _).
    - exact H.
    - eapply (Modus_ponens _ _ _ _ _).
      + eapply (Modus_ponens _ _ _ _ _).
        * eapply (Modus_ponens _ _ _ _ _).
          -- eapply (Modus_ponens _ _ _ _ _).
             ++ exact H0.
             ++ eapply (P1 _ (C ---> D) B _ _).
          -- eapply (P2 _ B C D _ _ _).
        * eapply (P1 _ ((B ---> C) ---> B ---> D) A _ _).
      + eapply (P2 _ A (B ---> C) (B ---> D) _ _ _).
        Unshelve.
        all: auto 10.
  Defined.

  Lemma syllogism_4_meta_indifferent
        P {Pip : IndifProp P} Γ a b c d
        (wfa : well_formed a = true)
        (wfb : well_formed b = true)
        (wfc : well_formed c = true)
        (wfd : well_formed d = true)
        (pf1 : Γ ⊢ a ---> b ---> c)
        (pf2 : Γ ⊢ c ---> d):
    P _ _ pf1 = false ->
    P _ _ pf2 = false ->
    P _ _ (@syllogism_4_meta Γ a b c d wfa wfb wfc wfd pf1 pf2) = false.
  Proof. intros. solve_indif; assumption. Qed.

  Canonical Structure syllogism_4_meta_indifferent_S
        P {Pip : IndifProp P} Γ a b c d
        (wfa : well_formed a = true)
        (wfb : well_formed b = true)
        (wfc : well_formed c = true)
        (wfd : well_formed d = true)
    := ProofProperty2 P _ (@syllogism_4_meta_indifferent P _ Γ _ _ _ _ wfa wfb wfc wfd).


  Lemma bot_elim (Γ : Theory) (A : Pattern) :
    well_formed A -> Γ ⊢ (Bot ---> A).
  Proof.
    intros WFA.
    eapply (Modus_ponens _ _ _ _ _).
    - eapply (Modus_ponens _ _ _ _ _).
      + eapply (Modus_ponens _ _ _ _ _).
        * eapply (Modus_ponens _ _ _ _ _).
          -- eapply (P1 _ Bot Bot _ _).
          -- eapply (P2 _ Bot Bot Bot _ _ _).
        * eapply (@P4 _ Bot Bot _ _).
      + eapply (P1 _ (Bot ---> Bot) (A ---> Bot) _ _).
    - eapply (@P4 _ A Bot _ _).
      Unshelve.
      all: auto.
  Defined.

  Lemma bot_elim_indifferent
        P {Pip : IndifProp P} Γ a (wfa : well_formed a = true):
    P _ _ (@bot_elim Γ a wfa) = false.
  Proof. solve_indif. Qed.

  Canonical Structure bot_elim_indifferent_S
        P {Pip : IndifProp P} Γ a
        (wfa : well_formed a = true)
    := ProofProperty0 P _ (@bot_elim_indifferent P _ Γ _ wfa).

  Lemma modus_ponens' (Γ : Theory) (A B : Pattern) :
    well_formed A -> well_formed B -> Γ ⊢ (A ---> (!B ---> !A) ---> B).
  Proof.
    intros WFA WFB.
    assert(well_formed (! B ---> ! A)).
    shelve.
    exact (@reorder_meta Γ _ _ _ H WFA WFB (@P4 _ B A WFB WFA)).
    Unshelve.
    all: auto.
  Defined.

  Program Canonical Structure modus_ponens'_indifferent_S
            P {Pip : IndifProp P} Γ A B (wfA : well_formed A) (wfB : well_formed B)
    := ProofProperty0 P (@modus_ponens' Γ A B wfA wfB) _.
  Next Obligation. intros. solve_indif. Qed.

  Lemma disj_right_intro (Γ : Theory) (A B : Pattern) :
    well_formed A -> well_formed B -> Γ ⊢ (B ---> (A or B)).
  Proof.
    intros WFA WFB.
    assert(well_formed (!A)).
    shelve.
    exact (P1 _ B (!A) WFB H).
    Unshelve.
    all: auto.
  Defined.

  #[local] Hint Resolve disj_right_intro : core.

  Lemma disj_right_intro_indifferent
        P {Pip : IndifProp P} Γ a b
        (wfa : well_formed a = true)
        (wfb : well_formed b = true) :
    P _ _ (@disj_right_intro Γ a b wfa wfb) = false.
  Proof. solve_indif. Qed.

  Canonical Structure disj_right_intro_indifferent_S
        P {Pip : IndifProp P} Γ a b
        (wfa : well_formed a = true)
        (wfb : well_formed b = true)
    := ProofProperty0 P _ (@disj_right_intro_indifferent P _ Γ a b wfa wfb).

  
  Lemma disj_left_intro (Γ : Theory) (A B : Pattern) :
    well_formed A -> well_formed B -> Γ ⊢ (A ---> (A or B)).
  Proof.
    intros WFA WFB.
    eapply (@syllogism_4_meta _ _ _ _ _ _ _ _ _ (@modus_ponens _ A Bot _ _) (@bot_elim _ B _)).
    Unshelve.
    all: auto.
  Defined.

  #[local] Hint Resolve disj_left_intro : core.

  Lemma disj_left_intro_indifferent
        P {Pip : IndifProp P} Γ a b
        (wfa : well_formed a = true)
        (wfb : well_formed b = true) :
    P _ _ (@disj_left_intro Γ a b wfa wfb) = false.
  Proof. solve_indif. Qed.

  Canonical Structure disj_left_intro_indifferent_S
        P {Pip : IndifProp P} Γ a b
        (wfa : well_formed a = true)
        (wfb : well_formed b = true)
    := ProofProperty0 P _ (@disj_left_intro_indifferent P _ Γ a b wfa wfb).

  Lemma disj_right_intro_meta (Γ : Theory) (A B : Pattern) :
    well_formed A ->
    well_formed B ->
    Γ ⊢ B ->
    Γ ⊢ (A or B).
  Proof.
    intros HwfA HwfB HB.
    eapply (Modus_ponens _ _ _ _ _).
    { exact HB. }
    eapply disj_right_intro; assumption.
    Unshelve.
    all: auto.
  Defined.

  Program Canonical Structure disj_right_intro_meta_indifferent_S
        P {Pip : IndifProp P} Γ a b
        (wfa : well_formed a = true)
        (wfb : well_formed b = true)
    := ProofProperty1 P (@disj_right_intro_meta Γ a b wfa wfb) _.
  Next Obligation. intros. solve_indif; assumption. Qed.

  Lemma disj_left_intro_meta (Γ : Theory) (A B : Pattern) :
    well_formed A ->
    well_formed B ->
    Γ ⊢ A ->
    Γ ⊢ (A or B).
  Proof.
    intros HwfA HwfB HA.
    eapply (Modus_ponens _ _ _ _ _).
    { exact HA. }
    eapply disj_left_intro; assumption.
    Unshelve.
    all: auto.
  Defined.

  Program Canonical Structure disj_left_intro_meta_indifferent_S
        P {Pip : IndifProp P} Γ a b
        (wfa : well_formed a = true)
        (wfb : well_formed b = true)
    := ProofProperty1 P (@disj_left_intro_meta Γ a b wfa wfb) _.
  Next Obligation. intros. solve_indif; assumption. Qed.

  Lemma not_not_elim (Γ : Theory) (A : Pattern) :
    well_formed A -> Γ ⊢ (!(!A) ---> A).
  Proof.
    intros WFA.
    unfold patt_not.
    exact (P3 Γ A WFA).
  Defined.

  #[local] Hint Resolve not_not_elim : core.

  Lemma not_not_elim_indifferent
        P {Pip : IndifProp P} Γ a (wfa : well_formed a = true):
    P _ _ (@not_not_elim Γ a wfa) = false.
  Proof. solve_indif. Qed.

  Canonical Structure not_not_elim_indifferent_S
        P {Pip : IndifProp P} Γ a (wfa : well_formed a = true)
    := ProofProperty0 P _ (@not_not_elim_indifferent P _ Γ _ wfa).

  Lemma not_not_elim_meta Γ A :
    well_formed A ->
    Γ ⊢ (! ! A) ->
    Γ ⊢ A.
  Proof.
    intros wfA nnA.
    pose proof (H := @not_not_elim Γ A wfA).
    eapply Modus_ponens. 4: apply H.
    all: auto.
  Defined.

  #[local] Hint Resolve not_not_elim_meta : core.

  Program Canonical Structure not_not_elim_meta_indifferent_S
        P {Pip : IndifProp P} Γ a (wfa : well_formed a = true)
    := ProofProperty1 P (@not_not_elim_meta Γ a wfa) _.
  Next Obligation. intros. solve_indif; assumption. Qed.

  Lemma double_neg_elim (Γ : Theory) (A B : Pattern) :
    well_formed A -> well_formed B -> Γ ⊢ (((!(!A)) ---> (!(!B))) ---> (A ---> B)).
  Proof.
    intros WFA WFB.
    eapply (@syllogism_intro _ _ _ _ _ _ _).
    - eapply (@P4 _ (!A) (!B) _ _).
    - eapply (@P4 _ B A _ _).
      Unshelve.
      all: auto.
  Defined.

  Program Canonical Structure double_neg_elim_indifferent_S
        P {Pip : IndifProp P} Γ a b (wfa : well_formed a = true) (wfb : well_formed b = true)
    := ProofProperty0 P (@double_neg_elim Γ a b wfa wfb) _.
  Next Obligation. intros. solve_indif; assumption. Qed.

  Lemma double_neg_elim_meta (Γ : Theory) (A B : Pattern) :
    well_formed A -> well_formed B -> 
    Γ ⊢ ((!(!A)) ---> (!(!B))) -> Γ ⊢ (A ---> B).
  Proof.
    intros WFA WFB H.
    eapply (Modus_ponens _ _ _ _ _).
    - exact H.
    - exact (@double_neg_elim _ A B WFA WFB).
      Unshelve.
      all: auto 10.
  Defined.

  Program Canonical Structure double_neg_elim_meta_indifferent_S
        P {Pip : IndifProp P} Γ a b (wfa : well_formed a = true) (wfb : well_formed b = true)
    := ProofProperty1 P (@double_neg_elim_meta Γ a b wfa wfb) _.
  Next Obligation. intros. solve_indif; assumption. Qed.


  Lemma P4_rev_meta (Γ : Theory) (A B : Pattern) :
    well_formed A -> well_formed B -> Γ ⊢ (A ---> B) -> Γ ⊢ ((A ---> B) ---> (!B ---> !A)).
  Proof.
    intros WFA WFB H.
    eapply (@deduction _ _ _ _ _).
    - exact H.
    - eapply (Modus_ponens _ _ _ _ _).
      + eapply (@syllogism_intro _ _ _ _ _ _ _).
        * eapply (@syllogism_intro _ _ _ _ _ _ _).
          -- eapply (@not_not_elim _ A _).
          -- exact H.
        * eapply (@not_not_intro _ B _).
      + eapply (@P4 _ (!A) (!B) _ _).
        Unshelve.
        all: auto 10.
  Defined.

  Program Canonical Structure P4_rev_meta_indifferent_S
        P {Pip : IndifProp P} Γ a b (wfa : well_formed a = true) (wfb : well_formed b = true)
    := ProofProperty1 P (@P4_rev_meta Γ a b wfa wfb) _.
  Next Obligation. intros. solve_indif; assumption. Qed.

  Lemma P4_rev_meta' (Γ : Theory) (A B : Pattern) :
    well_formed A ->
    well_formed B ->
    Γ ⊢ (A ---> B) ->
    Γ ⊢ (!B ---> !A).
  Proof.
    intros wfA wfB AimpB.
    pose proof (H := @P4_rev_meta Γ A B wfA wfB AimpB).
    eapply Modus_ponens.
    4: apply H.
    all: auto.
  Defined.

  #[local] Hint Resolve P4_rev_meta' : core.
  
  Program Canonical Structure P4_rev_meta'_indifferent_S
        P {Pip : IndifProp P} Γ a b (wfa : well_formed a = true) (wfb : well_formed b = true)
    := ProofProperty1 P (@P4_rev_meta' Γ a b wfa wfb) _.
  Next Obligation. intros. solve_indif; assumption. Qed.


  Lemma P4m_neg (Γ : Theory) (A B : Pattern) :
    well_formed A -> well_formed B -> Γ ⊢ ((!B ---> !A) ---> (A ---> !B) --->  !A).
  Proof.
    intros WFA WFB.
    epose proof (PT := (@P4 Γ B A _ _)).
    eapply (@syllogism_intro _ _ _ _ _ _ _).
    - exact PT.
    - eapply (@P4m _ _ _ _ _).
      Unshelve.
      all: auto.
  Defined.

  Program Canonical Structure P4m_neg_indifferent_S
        P {Pip : IndifProp P} Γ a b (wfa : well_formed a = true) (wfb : well_formed b = true)
    := ProofProperty0 P (@P4m_neg Γ a b wfa wfb) _.
  Next Obligation. intros. solve_indif; assumption. Qed.

  Lemma not_not_impl_intro_meta (Γ : Theory) (A B : Pattern) :
    well_formed A -> well_formed B -> Γ ⊢ (A ---> B) -> Γ ⊢ ((! ! A) ---> (! ! B)).
  Proof.
    intros WFA WFB H.
    epose proof (NN1 := @not_not_elim Γ A _).
    epose proof (NN2 := @not_not_intro Γ B _).
    
    epose proof (S1 := @syllogism_intro _ _ _ _ _ _ _ H NN2).
    
    epose proof (S2 := @syllogism_intro _ _ _ _ _ _ _ NN1 S1).
    exact S2.
    Unshelve.
    all: auto.
  Defined.

  Program Canonical Structure not_not_impl_intro_meta_indifferent_S
        P {Pip : IndifProp P} Γ a b (wfa : well_formed a = true) (wfb : well_formed b = true)
    := ProofProperty1 P (@not_not_impl_intro_meta Γ a b wfa wfb) _.
  Next Obligation. intros. solve_indif; assumption. Qed.

  Lemma not_not_impl_intro (Γ : Theory) (A B : Pattern) :
    well_formed A -> well_formed B -> Γ ⊢ ((A ---> B) ---> ((! ! A) ---> (! ! B))).
  Proof.
    intros WFA WFB.
    
    epose (S1 := @syllogism Γ (! ! A) A B _ _ _).
    
    epose (MP1 := Modus_ponens _ (! (! A) ---> A) ((A ---> B) ---> ! (! A) ---> B) _ _ (@not_not_elim _ A _) S1).
    
    epose(NNB := @not_not_intro Γ B _).

    epose(P1 := (P1 Γ (B ---> ! (! B)) (! ! A) _ _)).
    
    epose(MP2 := Modus_ponens _ _ _ _ _ NNB P1).
    
    epose(P2 := (P2 Γ (! ! A) B (! !B) _ _ _)).
    
    epose(MP3 := Modus_ponens _ _ _ _ _ MP2 P2).
    
    eapply @syllogism_intro with (B := (! (! A) ---> B)).
    - shelve.
    - shelve.
    - shelve.
    - assumption.
    - assumption.
      Unshelve.
      all: auto 10.
  Defined.

  Program Canonical Structure not_not_impl_intro_indifferent_S
        P {Pip : IndifProp P} Γ a b (wfa : well_formed a = true) (wfb : well_formed b = true)
    := ProofProperty0 P (@not_not_impl_intro Γ a b wfa wfb) _.
  Next Obligation. intros. solve_indif; assumption. Qed.

  Lemma contraposition (Γ : Theory) (A B : Pattern) : 
    well_formed A -> well_formed B -> 
    Γ ⊢ ((A ---> B) ---> ((! B) ---> (! A))).
  Proof.
    intros WFA WFB.
    epose proof (@P4 Γ (! A) (! B) _ _) as m.
    apply syllogism_intro with (B := (! (! A) ---> ! (! B))).
    - shelve.
    - shelve.
    - shelve.
    - eapply (@not_not_impl_intro _ _ _ _ _).
    - exact m. (* apply (P4 _ _ _). shelve. shelve. *)
      Unshelve.
      all: auto.
  Defined.

  Program Canonical Structure contraposition_indifferent_S
        P {Pip : IndifProp P} Γ a b (wfa : well_formed a = true) (wfb : well_formed b = true)
    := ProofProperty0 P (@contraposition Γ a b wfa wfb) _.
  Next Obligation. intros. solve_indif; assumption. Qed.

  Lemma or_comm_meta (Γ : Theory) (A B : Pattern) :
    well_formed A -> well_formed B ->
    Γ ⊢ (A or B) -> Γ ⊢ (B or A).
  Proof.
    intros WFA WFB H. unfold patt_or in *.
    
    epose proof (P4 := (@P4 Γ A (!B) _ _)).
    
    epose proof (NNI := @not_not_intro Γ B _).
    
    epose proof (SI := @syllogism_intro Γ _ _ _ _ _ _ H NNI).
    
    eapply (Modus_ponens _ _ _ _ _).
    - exact SI.
    - exact P4.
      Unshelve.
      all: auto 10.
  Defined.

  Program Canonical Structure or_comm_meta_indifferent_S
        P {Pip : IndifProp P} Γ a b (wfa : well_formed a = true) (wfb : well_formed b = true)
    := ProofProperty1 P (@or_comm_meta Γ a b wfa wfb) _.
  Next Obligation. intros. solve_indif; assumption. Qed.


  Lemma A_implies_not_not_A_alt (Γ : Theory) (A : Pattern) :
    well_formed A -> Γ ⊢ A -> Γ ⊢ (!( !A )).
  Proof.
    intros WFA H. unfold patt_not.
    epose proof (NN := @not_not_intro Γ A _).
    
    epose proof (MP := Modus_ponens _ _ _ _ _ H NN).
    assumption.
    Unshelve.
    all: auto.
  Defined.

  Program Canonical Structure A_implies_not_not_A_alt_indifferent_S
        P {Pip : IndifProp P} Γ a (wfa : well_formed a = true)
    := ProofProperty1 P (@A_implies_not_not_A_alt Γ a wfa) _.
  Next Obligation. intros. solve_indif; assumption. Qed.

  Lemma P5i (Γ : Theory) (A B : Pattern) :
    well_formed A -> well_formed B -> Γ ⊢ (! A ---> (A ---> B)).
  Proof.
    intros WFA WFB.
    
    epose proof (Ax1 := (P1 Γ (!A) (!B) _ _)).
    
    epose proof (Ax2 := (@P4 Γ B A _ _)).
    
    epose proof (TRANS := @syllogism_intro _ _ _ _ _ _ _ Ax1 Ax2).
    assumption.
    Unshelve.
    all: auto.
  Defined.

  Program Canonical Structure P5i_indifferent_S
        P {Pip : IndifProp P} Γ a b (wfa : well_formed a = true) (wfb : well_formed b = true)
    := ProofProperty0 P (@P5i Γ a b wfa wfb) _.
  Next Obligation. intros. solve_indif; assumption. Qed.

  Lemma false_implies_everything (Γ : Theory) (phi : Pattern) :
    well_formed phi -> Γ ⊢ (Bot ---> phi).
  Proof.
    intros WFA.
    
    epose proof (B_B := (@A_impl_A Γ Bot _)).
    epose proof (P4 := @P5i Γ Bot phi _ _).
    
    eapply (Modus_ponens _ _ _ _ _) in P4.
    - assumption.
    - assumption.
      Unshelve.
      all: auto.
  Defined.

  Program Canonical Structure false_implies_everthing_indifferent_S
        P {Pip : IndifProp P} Γ a (wfa : well_formed a = true)
    := ProofProperty0 P (@false_implies_everything Γ a wfa) _.
  Next Obligation. intros. solve_indif; assumption. Qed.


  (* Goal  forall (A B : Pattern) (Γ : Theory) , well_formed A -> well_formed B ->
  Γ ⊢ ((A $ Bot) $ B ---> Bot).
Proof.
  intros.
  epose (Prop_bott_right Γ A H).
  epose (Framing_left Γ (A $ Bot) (Bot) B (m)).
  epose (Prop_bott_left Γ B H0).
  epose (syllogism_intro Γ _ _ _ _ _ _ (m0) (m1)).
  exact m2.
  Unshelve.
  all: auto.
Defined. *)

  (*Was an axiom in AML_definition.v*)
  Lemma Prop_bot (Γ : Theory) (C : Application_context) :
    Γ ⊢ ((subst_ctx C patt_bott) ---> patt_bott).
  Proof.
    induction C.
    - simpl. eapply false_implies_everything. shelve.
    - simpl. epose proof (m0 := Framing_left Γ (subst_ctx C Bot) (Bot) p Prf IHC).
      epose proof (m1 := @syllogism_intro Γ _ _ _ _ _ _ (m0) (Prop_bott_left Γ p Prf)). exact m1.
    - simpl. epose proof (m2 := Framing_right Γ (subst_ctx C Bot) (Bot) p Prf IHC).

      epose proof (m3 := @syllogism_intro Γ _ _ _ _ _ _ (m2) (Prop_bott_right Γ p Prf)). exact m3.
      
      Unshelve.
      all: auto 10.
  Defined.

  (*Was an axiom in AML_definition.v*)
  Lemma Framing (Γ : Theory) (C : Application_context) (A B : Pattern):
    well_formed A -> well_formed B -> Γ ⊢ (A ---> B) -> Γ ⊢ ((subst_ctx C A) ---> (subst_ctx C B)).
  Proof.
    induction C; intros WFA WFB H.
    - simpl. exact H.
    - simpl. epose (Framing_left Γ (subst_ctx C A) (subst_ctx C B) p Prf (IHC _ _ H)). exact m.
    - simpl. epose (Framing_right Γ (subst_ctx C A) (subst_ctx C B) p Prf (IHC _ _ H)). exact m.
      Unshelve.
      all: auto.
  Defined.

  Lemma A_implies_not_not_A_ctx (Γ : Theory) (A : Pattern) (C : Application_context) :
    well_formed A -> Γ ⊢ A -> Γ ⊢ (! (subst_ctx C ( !A ))).
  Proof.
    intros WFA H.
    epose proof (ANNA := @A_implies_not_not_A_alt Γ _ _ H).
    replace (! (! A)) with ((! A) ---> Bot) in ANNA. 2: auto.
    epose proof (EF := @Framing _ C (! A) Bot _ _ ANNA).
    epose proof (PB := Prop_bot Γ C).
    
    epose (TRANS := @syllogism_intro _ _ _ _ _ _ _ EF PB).
    
    unfold patt_not.
    assumption.
    Unshelve.
    2,4:assert (@well_formed Σ (! A)).
    6,7:assert (@well_formed Σ (Bot)).
    all: auto.
  Defined.


  Lemma A_implies_not_not_A_alt_Γ (G : Theory) (A : Pattern) :
    well_formed A -> G ⊢ A -> G ⊢ (!( !A )).
  Proof.
    intros WFA H. unfold patt_not.
    epose proof (NN := @not_not_intro G A _).
    
    epose proof (MP := Modus_ponens G _ _ _ _ H NN).
    
    assumption.
    Unshelve.
    all: auto.
  Defined.


  Program Canonical Structure A_implies_not_not_A_alt_Γ_indifferent_S
        P {Pip : IndifProp P} Γ a (wfa : well_formed a = true)
    := ProofProperty1 P (@A_implies_not_not_A_alt_Γ Γ a wfa) _.
  Next Obligation. intros. solve_indif; assumption. Qed.

  (* Lemma equiv_implies_eq (Γ : Theory) (A B : Pattern) :
  well_formed A -> well_formed B -> Γ ⊢ (A <---> B) -> Γ ⊢ ()
   *) (*Need equal*)
  
  (* Lemma equiv_implies_eq_Γ *)

  (*...Missing some lemmas because of the lack of defidness definition...*)

  Lemma ctx_bot_prop (Γ : Theory) (C : Application_context) (A : Pattern) :
    well_formed A -> Γ ⊢ (A ---> Bot) -> Γ ⊢ (subst_ctx C A ---> Bot).
  Proof.
    intros WFA H.
    epose proof (FR := @Framing Γ C A Bot _ _ H).
    epose proof (BPR := @Prop_bot Γ C).
    
    epose proof (TRANS := @syllogism_intro _ _ _ _ _ _ _ FR BPR).
    
    assumption.
    Unshelve.
    4: assert (@well_formed Σ (Bot)).
    all: auto.
  Defined.

  Lemma not_not_A_ctx_implies_A (Γ : Theory) (C : Application_context) (A : Pattern):
    well_formed A -> Γ ⊢ (! (subst_ctx C ( !A ))) -> Γ ⊢ A.
  Proof.
    intros WFA H.
    unfold patt_not in H at 1.
    
    epose (BIE := @false_implies_everything Γ (subst_ctx C Bot) _).
    
    epose (TRANS := @syllogism_intro _ _ _ _ _ _ _ H BIE).
    
    induction C.
    - simpl in TRANS.
      epose (NN := @not_not_elim Γ A _).
      epose (MP := Modus_ponens _ _ _ _ _ TRANS NN). assumption.
    - eapply IHC.
      Unshelve.
      all: auto.
  Abort.

  (* TODO remove *)
  Definition empty_Γ := Empty_set (@Pattern Σ).

  Lemma exclusion (G : Theory) (A : Pattern) :
    well_formed A -> G ⊢ A -> G ⊢ (A ---> Bot) -> G ⊢ Bot.
  Proof.
    intros WFA H H0.
    epose(Modus_ponens G A Bot _ _ H H0).
    assumption.
    Unshelve.
    all: auto.
  Defined.

  Program Canonical Structure exclusion_indifferent_S
        P {Pip : IndifProp P} Γ a (wfa : well_formed a = true)
    := ProofProperty2 P (@exclusion Γ a wfa) _.
  Next Obligation. intros. solve_indif; assumption. Qed.

  Lemma modus_tollens Γ A B :
    well_formed A ->
    well_formed B ->
    Γ ⊢ (A ---> B) ->
    Γ ⊢ (!B ---> !A).
  Proof.
    intros WFA WFB H.
    eapply Modus_ponens.
    4: apply contraposition.
    all: auto.
  Defined.

  Program Canonical Structure modus_tollens_indifferent_S
        P {Pip : IndifProp P} Γ a b (wfa : well_formed a = true) (wfb : well_formed b = true)
    := ProofProperty1 P (@modus_tollens Γ a b wfa wfb) _.
  Next Obligation. intros. solve_indif; assumption. Qed.
  
  Lemma A_impl_not_not_B Γ A B :
    well_formed A ->
    well_formed B ->
    Γ ⊢ ((A ---> ! !B) ---> (A ---> B)).
  Proof.
    intros WFA WFB.
    assert (Γ ⊢ (! !B ---> B)) by auto.
    assert (Γ ⊢ ((A ---> ! !B) ---> (! !B ---> B) ---> (A ---> B))) by auto.
    apply reorder_meta in H0; auto.
    eapply Modus_ponens. 4: apply H0. all: auto 10.
  Defined.

  (* TODO remove this hint *)
  #[local] Hint Resolve A_impl_not_not_B : core.

  Program Canonical Structure A_impl_not_not_B_indifferent_S
        P {Pip : IndifProp P} Γ a b (wfa : well_formed a = true) (wfb : well_formed b = true)
    := ProofProperty0 P (@A_impl_not_not_B Γ a b wfa wfb) _.
  Next Obligation. intros. solve_indif; assumption. Qed.

  Lemma prf_weaken_conclusion Γ A B B' :
    well_formed A ->
    well_formed B ->
    well_formed B' ->
    Γ ⊢ ((B ---> B') ---> ((A ---> B) ---> (A ---> B'))).
  Proof.
    intros wfA wfB wfB'.
    apply reorder_meta; auto.
  Defined.

  Program Canonical Structure prf_weaken_conclusion_indifferent_S
        P {Pip : IndifProp P} Γ a b c
        (wfa : well_formed a = true) (wfb : well_formed b = true) (wfc : well_formed c = true)
    := ProofProperty0 P (@prf_weaken_conclusion Γ a b c wfa wfb wfc) _.
  Next Obligation. intros. solve_indif; assumption. Qed.
  
  Lemma prf_weaken_conclusion_meta Γ A B B' :
    well_formed A ->
    well_formed B ->
    well_formed B' ->
    Γ ⊢ (B ---> B') ->
    Γ ⊢ ((A ---> B) ---> (A ---> B')).
  Proof.
    intros wfA wfB wfB' BimpB'.
    assert (H1: Γ ⊢ ((A ---> B) ---> (B ---> B') ---> (A ---> B'))) by auto.
    apply reorder_meta in H1; auto.
    eapply Modus_ponens. 4: apply H1. all: auto 10.
  Defined.

  Program Canonical Structure prf_weaken_conclusion_meta_indifferent_S
        P {Pip : IndifProp P} Γ a b c
        (wfa : well_formed a = true) (wfb : well_formed b = true) (wfc : well_formed c = true)
    := ProofProperty1 P (@prf_weaken_conclusion_meta Γ a b c wfa wfb wfc) _.
  Next Obligation. intros. solve_indif; assumption. Qed.

  Lemma prf_weaken_conclusion_iter Γ l g g'
          (wfl : wf l) (wfg : well_formed g) (wfg' : well_formed g') :
    Γ ⊢ ((g ---> g') ---> (fold_right patt_imp g l ---> fold_right patt_imp g' l)).
  Proof.
    induction l.
    - apply A_impl_A; auto.
    - pose proof (wfl' := wfl).
      apply andb_prop in wfl. destruct wfl as [wfa wfl].
      specialize (IHl wfl).
      eapply syllogism_intro.
      5: eapply prf_weaken_conclusion.
      4: apply IHl.
      all: auto.
      apply well_formed_imp.
      all: apply well_formed_foldr; auto.
  Defined.

  Program Canonical Structure prf_weaken_conclusion_iter_indifferent_S
        P {Pip : IndifProp P} Γ l a b (wfl : wf l = true) (wfa : well_formed a = true) (wfb : well_formed b = true)
    := ProofProperty0 P (@prf_weaken_conclusion_iter Γ l a b wfl wfa wfb) _.
  Next Obligation.
    intros. induction l.
    - simpl. solve_indif.
    - simpl.
      case_match.
      solve_indif. apply IHl.
  Qed.

  Lemma prf_weaken_conclusion_iter_meta Γ l g g':
    wf l ->
    well_formed g ->
    well_formed g' ->
    Γ ⊢ (g ---> g') ->
    Γ ⊢ ((fold_right patt_imp g l) ---> (fold_right patt_imp g' l)).
  Proof.
    intros wfl wfg wfg' gimpg'.
    eapply Modus_ponens.
    4: apply prf_weaken_conclusion_iter.
    all: auto.
  Defined.

  Program Canonical Structure prf_weaken_conclusion_iter_meta_indifferent_S
        P {Pip : IndifProp P} Γ l a b (wfl : wf l = true) (wfa : well_formed a = true) (wfb : well_formed b = true)
    := ProofProperty1 P (@prf_weaken_conclusion_iter_meta Γ l a b wfl wfa wfb) _.
  Next Obligation. intros. solve_indif; assumption. Qed.

  Lemma prf_weaken_conclusion_iter_meta_meta Γ l g g':
    wf l ->
    well_formed g ->
    well_formed g' ->
    Γ ⊢ (g ---> g') ->
    Γ ⊢ (fold_right patt_imp g l) ->
    Γ ⊢ (fold_right patt_imp g' l).
  Proof.
    intros wfl wfg wfg' gimpg' H.
    eapply Modus_ponens. 4: apply prf_weaken_conclusion_iter_meta. 3: apply H.
    all: auto.
  Defined.

  Program Canonical Structure prf_weaken_conclusion_iter_meta_meta_indifferent_S
        P {Pip : IndifProp P} Γ l a b (wfl : wf l = true) (wfa : well_formed a = true) (wfb : well_formed b = true)
    := ProofProperty2 P (@prf_weaken_conclusion_iter_meta_meta Γ l a b wfl wfa wfb) _.
  Next Obligation. intros. solve_indif; assumption. Qed.
    
  Lemma prf_weaken_conclusion_meta_meta Γ A B B' :
    well_formed A ->
    well_formed B ->
    well_formed B' ->
    Γ ⊢ (B ---> B') ->
    Γ ⊢ (A ---> B) ->
    Γ ⊢ (A ---> B').
  Proof.
    intros WFA WFB WFB' H H0.
    eapply Modus_ponens. 4: apply prf_weaken_conclusion_meta. 3: apply H0. all: auto.
  Defined.

  Program Canonical Structure prf_weaken_conclusion_meta_meta_indifferent_S
        P {Pip : IndifProp P} Γ a b c
        (wfa : well_formed a = true) (wfb : well_formed b = true) (wfc : well_formed c = true)
    := ProofProperty2 P (@prf_weaken_conclusion_meta_meta Γ a b c wfa wfb wfc) _.
  Next Obligation. intros. solve_indif; assumption. Qed.

  Lemma prf_strenghten_premise Γ A A' B :
    well_formed A ->
    well_formed A' ->
    well_formed B ->
    Γ ⊢ ((A' ---> A) ---> ((A ---> B) ---> (A' ---> B))).
  Proof.
    intros wfA wfA' wfB. auto. (* TODO be more explicit here *)
  Defined.

  Program Canonical Structure prf_strenghten_premise_indifferent_S
        P {Pip : IndifProp P} Γ a b c
        (wfa : well_formed a = true) (wfb : well_formed b = true) (wfc : well_formed c = true)
    := ProofProperty0 P (@prf_strenghten_premise Γ a b c wfa wfb wfc) _.
  Next Obligation. intros. solve_indif; assumption. Qed.

  Lemma prf_strenghten_premise_iter Γ l₁ l₂ h h' g :
    wf l₁ -> wf l₂ ->
    well_formed h ->
    well_formed h' ->
    well_formed g ->
    Γ ⊢ (h' ---> h) --->
        foldr patt_imp g (l₁ ++ h::l₂) --->
        foldr patt_imp g (l₁ ++ h'::l₂).
  Proof.
    intros wfl₁ wfl₂ wfh wfh' wfg.
    induction l₁.
    - simpl. apply prf_strenghten_premise. all: auto.
    - pose proof (wfal₁ := wfl₁).
      remember (foldr patt_imp g (h::l₂)) as g1.
      remember (foldr patt_imp g (h'::l₂)) as g2.
      unfold wf in wfl₁. simpl in wfl₁. apply andb_prop in wfl₁.
      destruct wfl₁ as [wfa wfl₁].
      specialize (IHl₁ wfl₁).
      remember (foldr patt_imp g (l₁ ++ h::l₂)) as b.
      remember (foldr patt_imp g (l₁ ++ h'::l₂)) as b'.

      assert (prf: Γ ⊢ ((b ---> b') ---> ((a ---> b) ---> (a ---> b')))).
      { apply prf_weaken_conclusion; subst; auto. }

      eapply syllogism_intro. 5: subst; apply prf. all: subst; auto 10.
  Defined.

  Program Canonical Structure prf_strenghten_premise_iter_indifferent_S
        P {Pip : IndifProp P} Γ l₁ l₂ a b c
        (wfl₁ : wf l₁) (wfl₂ : wf l₂)
        (wfa : well_formed a = true) (wfb : well_formed b = true) (wfc : well_formed c = true)
    := ProofProperty0 P (@prf_strenghten_premise_iter Γ l₁ l₂ a b c wfl₁ wfl₂ wfa wfb wfc) _.
  Next Obligation.
    intros.
    induction l₁.
    - solve_indif.
    - simpl.
      case_match. simpl.
      unfold eq_rec_r. unfold eq_rec. unfold eq_rect. unfold eq_sym.
      solve_indif. apply IHl₁.
  Qed.

  Lemma prf_strenghten_premise_meta Γ A A' B :
    well_formed A ->
    well_formed A' ->
    well_formed B ->
    Γ ⊢ (A' ---> A) ->
    Γ ⊢ ((A ---> B) ---> (A' ---> B)).
  Proof.
    intros wfA wfA' wfB A'impA.
    assert (H1: Γ ⊢ ((A' ---> A) ---> (A ---> B) ---> (A' ---> B))) by auto.
    eapply Modus_ponens. 4: apply H1. all: auto 10.
  Defined.

  Program Canonical Structure prf_strenghten_premise_meta_indifferent_S
        P {Pip : IndifProp P} Γ a b c
        (wfa : well_formed a = true) (wfb : well_formed b = true) (wfc : well_formed c = true)
    := ProofProperty1 P (@prf_strenghten_premise_meta Γ a b c wfa wfb wfc) _.
  Next Obligation. intros. solve_indif; assumption. Qed.

  Lemma prf_strenghten_premise_meta_meta Γ A A' B :
    well_formed A ->
    well_formed A' ->
    well_formed B ->
    Γ ⊢ (A' ---> A) ->
    Γ ⊢ (A ---> B) ->
    Γ ⊢ (A' ---> B).
  Proof.
    intros wfA wfA' wfB A'impA AimpB.
    eapply Modus_ponens. 4: apply prf_strenghten_premise_meta. 3: apply AimpB. all: auto.
  Defined.

  Program Canonical Structure prf_strenghten_premise_meta_meta_indifferent_S
        P {Pip : IndifProp P} Γ a b c
        (wfa : well_formed a = true) (wfb : well_formed b = true) (wfc : well_formed c = true)
    := ProofProperty2 P (@prf_strenghten_premise_meta_meta Γ a b c wfa wfb wfc) _.
  Next Obligation. intros. solve_indif; assumption. Qed.

  Lemma prf_strenghten_premise_iter_meta Γ l₁ l₂ h h' g :
    wf l₁ -> wf l₂ ->
    well_formed h ->
    well_formed h' ->
    well_formed g ->
    Γ ⊢ (h' ---> h) ->
    Γ ⊢ foldr patt_imp g (l₁ ++ h::l₂) --->
         foldr patt_imp g (l₁ ++ h'::l₂).  
  Proof.
    intros WFl₁ WFl₂ WFh WFh' WFg H.
    eapply Modus_ponens.
    4: apply prf_strenghten_premise_iter.
    all: auto 10.
  Defined.

  Program Canonical Structure prf_strenghten_premise_iter_meta_indifferent_S
        P {Pip : IndifProp P} Γ l₁ l₂ a b c
        (wfl₁ : wf l₁) (wfl₂ : wf l₂)
        (wfa : well_formed a = true) (wfb : well_formed b = true) (wfc : well_formed c = true)
    := ProofProperty1 P (@prf_strenghten_premise_iter_meta Γ l₁ l₂ a b c wfl₁ wfl₂ wfa wfb wfc) _.
  Next Obligation. intros. solve_indif; assumption. Qed.

  Lemma prf_strenghten_premise_iter_meta_meta Γ l₁ l₂ h h' g :
    wf l₁ -> wf l₂ ->
    well_formed h ->
    well_formed h' ->
    well_formed g ->
    Γ ⊢ (h' ---> h) ->
    Γ ⊢ foldr patt_imp g (l₁ ++ h::l₂) ->
    Γ ⊢ foldr patt_imp g (l₁ ++ h'::l₂).  
  Proof.
    intros WFl₁ WFl₂ WFh WFh' WFg H H0.
    eapply Modus_ponens.
    4: eapply prf_strenghten_premise_iter_meta.
    9: eassumption. all: auto 10.
  Defined.

  Program Canonical Structure prf_strenghten_premise_iter_meta_meta_indifferent_S
        P {Pip : IndifProp P} Γ l₁ l₂ a b c
        (wfl₁ : wf l₁) (wfl₂ : wf l₂)
        (wfa : well_formed a = true) (wfb : well_formed b = true) (wfc : well_formed c = true)
    := ProofProperty2 P (@prf_strenghten_premise_iter_meta_meta Γ l₁ l₂ a b c wfl₁ wfl₂ wfa wfb wfc) _.
  Next Obligation. intros. solve_indif; assumption. Qed.

  (* TODO rename *)
  Lemma rewrite_under_implication Γ g g':
    well_formed g ->
    well_formed g' ->
    Γ ⊢ ((g ---> g') ---> g) ->
    Γ ⊢ ((g ---> g') ---> g').
  Proof.
    intros wfg wfg' H.
    assert (H1 : Γ ⊢ ((g ---> g') ---> (g ---> g'))) by auto.
    assert (H2 : Γ ⊢ (((g ---> g') ---> (g ---> g'))
                        --->
                        (((g ---> g') ---> g) ---> ((g ---> g') ---> g')))) by auto using P2.
    assert (H3 : Γ ⊢ (((g ---> g') ---> g) ---> ((g ---> g') ---> g'))).
    { eapply Modus_ponens. 4: apply H2. all: auto 10. }
    eapply Modus_ponens. 4: apply H3. all: auto.
  Defined.

  Program Canonical Structure prf_rewrite_under_implication_indifferent_S
        P {Pip : IndifProp P} Γ a b
        (wfa : well_formed a = true) (wfb : well_formed b = true)
    := ProofProperty1 P (@rewrite_under_implication Γ a b wfa wfb) _.
  Next Obligation. intros. solve_indif; assumption. Qed.


  Local Example example_nested_const Γ a b c:
    well_formed a ->
    well_formed b ->
    well_formed c ->
    (* like P2 but nested a bit *)
    Γ ⊢ (a ---> (b ---> (c ---> a))).
  Proof.
    intros wfa wfb wfc.
    assert (H1: Γ ⊢ ((c ---> a) ---> (b ---> (c ---> a)))) by auto using P1.
    assert (H2: Γ ⊢ (a ---> (c ---> a))) by auto using P1.
    eapply (@syllogism_intro _ _ _ _ _ _ _ H2 H1).
    Unshelve. all: auto.
  Defined.

  (* This will form a base for the tactic 'exact 0' *)
  Lemma nested_const Γ a l:
    well_formed a ->
    wf l ->
    Γ ⊢ (a ---> (fold_right patt_imp a l)).
  Proof.
    intros wfa wfl.
    induction l; simpl.
    - auto.
    - pose proof (wfa0l := wfl).
      unfold wf in wfl. simpl in wfl. apply andb_prop in wfl. destruct wfl as [wfa0 wfl].
      specialize (IHl wfl).
      assert (H1 : Γ ⊢ ((foldr patt_imp a l) ---> (a0 ---> (foldr patt_imp a l)))) by auto using P1.
      eapply syllogism_intro.
      5: apply H1. all: auto.
  Defined.

  Program Canonical Structure nested_const_indifferent_S
        P {Pip : IndifProp P} Γ l a
        (wfl : wf l)
        (wfa : well_formed a = true)
    := ProofProperty0 P (@nested_const Γ a l wfa wfl) _.
  Next Obligation.
    intros. induction l; simpl.
    - solve_indif.
    - case_match. solve_indif; apply IHl.
  Qed.

  Lemma nested_const_middle Γ a l₁ l₂:
    well_formed a ->
    wf l₁ ->
    wf l₂ ->
    Γ ⊢ (fold_right patt_imp a (l₁ ++ a :: l₂)).
  Proof.
    intros wfa wfl₁ wfl₂.
    induction l₁; simpl.
    - apply nested_const; auto.
    - pose proof (wfa0l₁ := wfl₁).
      unfold wf in wfl₁. simpl in wfl₁. apply andb_prop in wfl₁. destruct wfl₁ as [wfa0 wfl₁].
      specialize (IHl₁ wfl₁). simpl in IHl₁.

      eapply Modus_ponens. 4: apply P1. all: auto 10.
  Defined.

  Program Canonical Structure nested_const_middle_indifferent_S
        P {Pip : IndifProp P} Γ l₁ l₂ a
        (wfl₁ : wf l₁) (wfl₂ : wf l₂)
        (wfa : well_formed a = true)
    := ProofProperty0 P (@nested_const_middle Γ a l₁ l₂ wfa wfl₁ wfl₂) _.
  Next Obligation.
    intros. induction l₁; simpl.
    - solve_indif.
    - case_match. solve_indif; apply IHl₁.
  Qed.

  Lemma prf_reorder_iter Γ a b g l₁ l₂:
    well_formed a ->
    well_formed b ->
    well_formed g ->
    wf l₁ ->
    wf l₂ ->
    Γ ⊢ ((fold_right patt_imp g (l₁ ++ [a;b] ++ l₂)) ---> (fold_right patt_imp g (l₁ ++ [b;a] ++ l₂))).
  Proof.
    intros wfa wfb wfg wfl₁ wfl₂.
    induction l₁; simpl in *.
    - apply reorder; auto.
    - pose proof (wfa0l₁ := wfl₁).
      unfold wf in wfl₁. apply andb_prop in wfl₁. destruct wfl₁ as [wfa0 wfl₁].
      specialize (IHl₁ wfl₁).
      eapply prf_weaken_conclusion_meta; auto 10.
  Defined.

  Program Canonical Structure prf_reorder_iter_indifferent_S
        P {Pip : IndifProp P} Γ l₁ l₂ a b c
        (wfl₁ : wf l₁) (wfl₂ : wf l₂)
        (wfa : well_formed a = true) (wfb : well_formed b = true) (wfc : well_formed c = true)
    := ProofProperty0 P (@prf_reorder_iter Γ a b c l₁ l₂ wfa wfb wfc wfl₁ wfl₂) _.
  Next Obligation.
    intros. induction l₁; simpl.
    - solve_indif.
    - case_match. solve_indif; apply IHl₁.
  Qed.

  Lemma prf_reorder_iter_meta Γ a b g l₁ l₂:
    well_formed a ->
    well_formed b ->
    well_formed g ->
    wf l₁ ->
    wf l₂ ->
    Γ ⊢ (fold_right patt_imp g (l₁ ++ [a;b] ++ l₂)) ->
    Γ ⊢ (fold_right patt_imp g (l₁ ++ [b;a] ++ l₂)).
  Proof.
    (* TODO we should have a function/lemma for creating these "meta" variants. *)
    intros WFa WFb WFg Wfl1 Wfl2 H.
    eapply Modus_ponens.
    4: { apply prf_reorder_iter; auto. }
    all: auto 10.
  Defined.

  Program Canonical Structure prf_reorder_iter_meta_indifferent_S
        P {Pip : IndifProp P} Γ l₁ l₂ a b c
        (wfl₁ : wf l₁) (wfl₂ : wf l₂)
        (wfa : well_formed a = true) (wfb : well_formed b = true) (wfc : well_formed c = true)
    := ProofProperty1 P (@prf_reorder_iter_meta Γ a b c l₁ l₂ wfa wfb wfc wfl₁ wfl₂) _.
  Next Obligation. intros. solve_indif; assumption. Qed.
  
  
  (*
  Lemma prf_reorder_move_to_top Γ a g l₁ l₂:
    well_formed a ->
    well_formed g ->
    wf l₁ ->
    wf l₂ ->
    Γ ⊢ ((a --> (fold_right patt_imp g (l₁ ++ [a;b] ++ l₂))) ---> (fold_right patt_imp g (l₁ ++ [b;a] ++ l₂))).
    *)
  
  Lemma A_impl_not_not_B_meta Γ A B :
    well_formed A ->
    well_formed B ->
    Γ ⊢ A ---> ! !B ->
    Γ ⊢ A ---> B.
  Proof.
    intros WFA WFB H.
    eapply Modus_ponens.
    4: { apply A_impl_not_not_B; auto. }
    all: auto 10.
  Defined.

  Program Canonical Structure A_impl_not_not_B_meta_indifferent_S
        P {Pip : IndifProp P} Γ a b
        (wfa : well_formed a = true) (wfb : well_formed b = true)
    := ProofProperty1 P (@A_impl_not_not_B_meta Γ a b wfa wfb) _.
  Next Obligation. intros. solve_indif; assumption. Qed.

  Lemma pf_conj_elim_l Γ A B :
    well_formed A ->
    well_formed B ->
    Γ ⊢ A and B ---> A.
  Proof.
    intros WFA WFB. unfold patt_and. unfold patt_not at 1.

    assert (Γ ⊢ (! A ---> (! A or ! B))) by auto.
    assert (Γ ⊢ ((! A or ! B) ---> (! A or ! B ---> ⊥) ---> ⊥)) by auto.
    assert (Γ ⊢ (! A ---> ((! A or ! B ---> ⊥) ---> ⊥))).
    { eapply syllogism_intro. 5: apply H0. 4: apply H. all: auto 10. }
    epose proof (reorder_meta _ _ _ H1).
    apply A_impl_not_not_B_meta; auto.
    Unshelve.
    all: auto.
  Defined.

  Program Canonical Structure pf_conj_elim_l_indifferent_S
        P {Pip : IndifProp P} Γ a b
        (wfa : well_formed a = true) (wfb : well_formed b = true)
    := ProofProperty0 P (@pf_conj_elim_l Γ a b wfa wfb) _.
  Next Obligation. intros. solve_indif; assumption. Qed.

  Lemma pf_conj_elim_r Γ A B :
    well_formed A ->
    well_formed B ->
    Γ ⊢ A and B ---> B.
  Proof.
    intros WFA WFB. unfold patt_and. unfold patt_not at 1.

    assert (Γ ⊢ (! B ---> (! A or ! B))) by auto.
    assert (Γ ⊢ ((! A or ! B) ---> (! A or ! B ---> ⊥) ---> ⊥)) by auto.
    assert (Γ ⊢ (! B ---> ((! A or ! B ---> ⊥) ---> ⊥))).
    { eapply syllogism_intro. 5: apply H0. 4: apply H. all: auto 10. }
    epose proof (reorder_meta  _ _ _ H1).
    apply A_impl_not_not_B_meta; auto.
    Unshelve.
    all: auto.
  Defined.

  Program Canonical Structure pf_conj_elim_r_indifferent_S
        P {Pip : IndifProp P} Γ a b
        (wfa : well_formed a = true) (wfb : well_formed b = true)
    := ProofProperty0 P (@pf_conj_elim_r Γ a b wfa wfb) _.
  Next Obligation. intros. solve_indif; assumption. Qed.

  Lemma pf_conj_elim_l_meta Γ A B :
    well_formed A ->
    well_formed B ->
    Γ ⊢ A and B ->
    Γ ⊢ A.
  Proof.
    intros WFA WFB H.
    eapply Modus_ponens.
    4: apply pf_conj_elim_l.
    3: apply H.
    all: auto.
  Defined.

  Program Canonical Structure pf_conj_elim_l_meta_indifferent_S
        P {Pip : IndifProp P} Γ a b
        (wfa : well_formed a = true) (wfb : well_formed b = true)
    := ProofProperty1 P (@pf_conj_elim_l_meta Γ a b wfa wfb) _.
  Next Obligation. intros. solve_indif; assumption. Qed.
  
  Lemma pf_conj_elim_r_meta Γ A B :
    well_formed A ->
    well_formed B ->
    Γ ⊢ A and B ->
    Γ ⊢ B.
  Proof.
    intros WFA WFB H.
    eapply Modus_ponens.
    4: apply pf_conj_elim_r.
    3: apply H.
    all: auto.
  Defined.

  Program Canonical Structure pf_conj_elim_r_meta_indifferent_S
        P {Pip : IndifProp P} Γ a b
        (wfa : well_formed a = true) (wfb : well_formed b = true)
    := ProofProperty1 P (@pf_conj_elim_r_meta Γ a b wfa wfb) _.
  Next Obligation. intros. solve_indif; assumption. Qed.

  Lemma A_or_notA Γ A :
    well_formed A ->
    Γ ⊢ A or ! A.
  Proof.
    intros wfA.
    unfold patt_or.
    auto. (* TODO be more explicit here *)
  Defined.

  Program Canonical Structure A_or_notA_indifferent_S
        P {Pip : IndifProp P} Γ a
        (wfa : well_formed a = true)
    := ProofProperty0 P (@A_or_notA Γ a wfa) _.
  Next Obligation. intros. solve_indif; assumption. Qed.

  Lemma P4m_meta (Γ : Theory) (A B : Pattern) :
    well_formed A ->
    well_formed B ->
    Γ ⊢ A ---> B ->
    Γ ⊢ A ---> !B ->
    Γ ⊢ !A.
  Proof.
    intros wfA wfB AimpB AimpnB.
    pose proof (H1 := @P4m Γ A B wfA wfB).
    assert (H2 : Γ ⊢ (A ---> ! B) ---> ! A).
    { eapply Modus_ponens. 4: apply H1. all: auto 10. }
    eapply Modus_ponens. 4: apply H2. all: auto.
  Defined.

  Program Canonical Structure P4m_meta_indifferent_S
        P {Pip : IndifProp P} Γ a b
        (wfa : well_formed a = true) (wfb : well_formed b = true)
    := ProofProperty2 P (@P4m_meta Γ a b wfa wfb) _.
  Next Obligation. intros. solve_indif; assumption. Qed.


End FOL_helpers.

(* TODO remove these hints *)
#[export] Hint Resolve A_impl_A : core.
#[export] Hint Resolve syllogism : core.
#[export] Hint Resolve syllogism_intro : core.
#[export] Hint Resolve modus_ponens : core.
#[export] Hint Resolve not_not_intro : core.
#[export] Hint Resolve disj_right_intro : core.
#[export] Hint Resolve disj_left_intro : core.
#[export] Hint Resolve not_not_elim : core.
#[export] Hint Resolve not_not_elim_meta : core.
#[export] Hint Resolve P4_rev_meta' : core.
#[export] Hint Resolve A_impl_not_not_B : core.
#[export] Hint Resolve well_formed_foldr : core.
#[export] Hint Resolve wf_take : core.
#[export] Hint Resolve wf_drop : core.
#[export] Hint Resolve wf_insert : core.
#[export] Hint Resolve wf_tail' : core.
#[export] Hint Resolve wf_cons : core.
#[export] Hint Resolve wf_app : core.



Structure TaggedPattern {Σ : Signature} := TagPattern { untagPattern :> Pattern; }.

Definition reshape_nil {Σ : Signature} p := TagPattern p.
Canonical Structure reshape_cons {Σ : Signature} p := reshape_nil p.

Structure ImpReshapeS {Σ : Signature} (g : Pattern) (l : list Pattern) :=
ImpReshape
  { irs_flattened :> TaggedPattern ;
    irs_pf : (untagPattern irs_flattened) = foldr patt_imp g l ;
  }.

Lemma ImpReshape_nil_pf0:
  ∀ (Σ : Signature) (g : Pattern),
    g = foldr patt_imp g [].
Proof. intros. reflexivity. Qed.

Canonical Structure ImpReshape_nil {Σ : Signature} (g : Pattern) : ImpReshapeS g [] :=
  @ImpReshape Σ g [] (reshape_nil g) (ImpReshape_nil_pf0 g).


Program Canonical Structure ImpReshape_cons
        {Σ : Signature} (g x : Pattern) (xs : list Pattern) (r : ImpReshapeS g xs)
: ImpReshapeS g (x::xs) :=
  @ImpReshape Σ g (x::xs) (reshape_cons (x ---> untagPattern (reshape_cons r))) _.
Next Obligation.
  intros Σ g x xs r. simpl.
  rewrite irs_pf.
  reflexivity.
Qed.


Lemma reshape {Σ : Signature} (Γ : Theory) (g : Pattern) (xs: list Pattern) :
  forall (r : ImpReshapeS g (xs)),
     Γ ⊢ foldr (patt_imp) g (xs) ->
     Γ ⊢ (untagPattern (irs_flattened r)).
Proof.
  intros r H.
  eapply cast_proof.
  { rewrite irs_pf; reflexivity. }
  exact H.
Defined.


Local Example ex_reshape {Σ : Signature} Γ a b c d:
  well_formed a ->
  well_formed b ->
  well_formed c ->
  well_formed d ->
  Γ ⊢ a ---> (b ---> (c ---> d)).
Proof.
  intros wfa wfb wfc wfd.
  apply reshape.
  (* Now the goal has the right shape *)
Abort.

Local Example ex_toMyGoal {Σ : Signature} Γ (p : Pattern) :
  well_formed p ->
  Γ ⊢ p ---> p.
Proof.
  intros wfp.
  toMyGoal.
  { auto. }
  fromMyGoal. intros _ _. apply A_impl_A. exact wfp.
Qed.

Tactic Notation "mgExtractWF" ident(wfl) ident(wfg) :=
match goal with
| [ |- ?g ] =>
  let wfl' := fresh "wfl'" in
  let wfg' := fresh "wfg'" in
  intros wfg' wfl';
  pose proof (wfl := wfl');
  pose proof (wfg := wfg');
  revert wfg' wfl';
  fold g;
  rewrite /mgConclusion in wfg;
  rewrite /mgHypotheses in wfl
end.

Local Example ex_extractWfAssumptions {Σ : Signature} Γ (p : Pattern) :
  well_formed p ->
  Γ ⊢ p ---> p.
Proof.
  intros wfp.
  toMyGoal.
  { auto. }
  mgExtractWF wfl wfg.
  assert (wf []) by assumption.
  assert (well_formed (p ---> p)) by assumption.
Abort.
  

Lemma cast_proof_mg_hyps {Σ : Signature} Γ hyps hyps' (e : hyps = hyps') goal:
  @mkMyGoal Σ Γ hyps goal ->
  @mkMyGoal Σ Γ hyps' goal.
Proof.
  unfold of_MyGoal. simpl. intros H.
  intros wfg wfhyps'.
  feed specialize H.
  { exact wfg. }
  { rewrite e. exact wfhyps'. }
  unshelve (eapply (@cast_proof Σ Γ _ _ _ H)).
  rewrite e.
  reflexivity.
Defined.

Lemma cast_proof_mg_goal {Σ : Signature} Γ hyps goal goal' (e : goal = goal'):
  @mkMyGoal Σ Γ hyps goal ->
  @mkMyGoal Σ Γ hyps goal'.
Proof.
  unfold of_MyGoal. simpl. intros H.
  intros wfgoal' wfhyps.
  feed specialize H.
  { rewrite e. exact wfgoal'. }
  { exact wfhyps. }
  unshelve (eapply (@cast_proof Σ Γ _ _ _ H)).
  rewrite e.
  reflexivity.
Defined.

Lemma cast_proof_mg_hyps_indifferent
      Σ P Γ hyps hyps' (e : hyps = hyps') goal (pf : @mkMyGoal Σ Γ hyps goal) wf1 wf2 wf3 wf4:
  indifferent_to_cast P ->
  P _ _ (@cast_proof_mg_hyps Σ Γ hyps hyps' e goal pf wf1 wf2) = P _ _ (pf wf3 wf4).
Proof.
  intros Hp. simpl. unfold cast_proof_mg_hyps.
  rewrite Hp.
  apply f_equal. f_equal.
  { apply UIP_dec; apply bool_eqdec. }
  { apply UIP_dec. apply bool_eqdec. }
Qed.

Lemma cast_proof_mg_goal_indifferent
      Σ P Γ hyps goal goal' (e : goal = goal') (pf : @mkMyGoal Σ Γ hyps goal) wf1 wf2 wf3 wf4:
  indifferent_to_cast P ->
  P _ _ (@cast_proof_mg_goal Σ Γ hyps goal goal' e pf wf1 wf2) = P _ _ (pf wf3 wf4).
Proof.
  intros Hp. simpl. unfold cast_proof_mg_goal.
  rewrite Hp.
  apply f_equal. f_equal.
  { apply UIP_dec; apply bool_eqdec. }
  { apply UIP_dec. apply bool_eqdec. }
Qed.



Definition liftP {Σ : Signature} (P : proofbpred) (Γ : Theory) (l : list Pattern) (g : Pattern)
           (pf : Γ ⊢ (foldr patt_imp g l)) := P _ _ pf.

Arguments liftP {Σ} _ Γ l%list_scope g _.

Lemma liftP_impl_P {Σ : Signature} (P : proofbpred) (Γ : Theory) (p : Pattern)
      (pf : Γ ⊢ p) :
  @liftP Σ P Γ [] p pf = false -> P Γ p pf = false.
Proof.
  intros H. apply H.
Qed.

Structure tacticProperty0 {Σ : Signature} (P : proofbpred) (Γ : Theory)
          (l₁ : list Pattern) (g₁ : Pattern)
  := TacticProperty0 {
      tp0_tactic : @mkMyGoal Σ Γ l₁ g₁;
      tp0_tactic_property :
        (forall wf1 wf2, liftP P _ _ _ (tp0_tactic  wf1 wf2) = false)
    }.

Arguments TacticProperty0 [Σ] P [Γ] [l₁]%list_scope [g₁] tp0_tactic _%function_scope.

Structure tacticProperty1 {Σ : Signature} (P : proofbpred) (Γ : Theory)
          (l₁ l₂ : list Pattern) (g₁ g₂ : Pattern)
  := TacticProperty1 {
      tp1_tactic : @mkMyGoal Σ Γ l₁ g₁ -> @mkMyGoal Σ Γ l₂ g₂ ;
      tp1_tactic_property :
      forall (pf : @mkMyGoal Σ Γ l₁ g₁),
        (forall wf3 wf4, liftP P _ _ _ (pf wf3 wf4) = false) ->
        (forall wf1 wf2, liftP P _ _ _ ((tp1_tactic pf) wf1 wf2) = false)
    }.

Arguments TacticProperty1 [Σ] P [Γ] [l₁ l₂]%list_scope [g₁ g₂] tp1_tactic%function_scope _%function_scope.

Structure tacticProperty2 {Σ : Signature} (P : proofbpred) (Γ : Theory)
          (l₁ l₂ l₃ : list Pattern) (g₁ g₂ g₃ : Pattern)
  := TacticProperty2 {
      tp2_tactic : @mkMyGoal Σ Γ l₁ g₁ -> @mkMyGoal Σ Γ l₂ g₂ -> @mkMyGoal Σ Γ l₃ g₃ ;
      tp2_tactic_property :
      forall (pf₁ : @mkMyGoal Σ Γ l₁ g₁) (pf₂ : @mkMyGoal Σ Γ l₂ g₂),
        (forall wf3 wf4, liftP P _ _ _ (pf₁ wf3 wf4) = false) ->
        (forall wf5 wf6, liftP P _ _ _ (pf₂ wf5 wf6) = false) ->
        (forall wf1 wf2, liftP P _ _ _ ((tp2_tactic pf₁ pf₂) wf1 wf2) = false)
    }.

Arguments TacticProperty2 [Σ] P [Γ] [l₁ l₂ l₃]%list_scope [g₁ g₂ g₃] tp2_tactic%function_scope _%function_scope.


Ltac2 Set solve_indif :=
  (fun () =>
     ltac1:(
              repeat (
                  intros;
                  (
                    lazymatch goal with
                    | [ |- liftP _ _ _ _ _ = _ ] =>
                        (
                          eapply tp0_tactic_property
                          || eapply tp1_tactic_property
                          || eapply tp2_tactic_property
                        )
                                                    
                    | _ => (
                            eapply pp0_proof_property
                            || eapply pp1_proof_property
                            || eapply pp2_proof_property
                          )
                    end
                  )
                )
            )
  ).


Lemma MyGoal_intro {Σ : Signature} (Γ : Theory) (l : list Pattern) (x g : Pattern):
  @mkMyGoal Σ Γ (l ++ [x]) g ->
  @mkMyGoal Σ Γ l (x ---> g).
Proof.
  intros H.
  unfold of_MyGoal in H. simpl in H.
  unfold of_MyGoal. simpl. intros wfxig wfl.

  feed specialize H.
  { abstract (apply well_formed_imp_proj2 in wfxig; exact wfxig). }
  { abstract (unfold wf; unfold wf in wfl; rewrite map_app foldr_app; simpl;
              apply well_formed_imp_proj1 in wfxig; rewrite wfxig; simpl; exact wfl).
  }
  unshelve (eapply (cast_proof _ H)).
  { rewrite foldr_app. reflexivity. }
Defined.

Lemma MyGoal_intro_indifferent {Σ : Signature} (P : proofbpred) {Hcast : IndifCast P} Γ l x g pf:
  (forall wf3 wf4, P _ _ (pf wf3 wf4) = false) ->
  (forall wf1 wf2, P _ _ (@MyGoal_intro Σ Γ l x g pf wf1 wf2) = false).
Proof.
  intros H wf1 wf2.
  unfold MyGoal_intro. simpl.
  destruct Hcast as [Hcast].
  rewrite Hcast. simpl in H. apply H.
Qed.

Program Canonical Structure MyGoal_intro_indifferent_S 
          {Σ : Signature} (P : proofbpred) {Pic : IndifCast P}
          Γ l x g
  := TacticProperty1 P (fun pf => @MyGoal_intro Σ Γ l x g pf) _.
Next Obligation. intros. simpl. apply MyGoal_intro_indifferent. exact Pic. exact H. Qed.

Program Canonical Structure cast_proof_mg_hyps_indifferent_S
        {Σ : Signature} (P : proofbpred) {Pic : IndifCast P} (Γ : Theory)
        (l₁ l₂ : list Pattern) (g : Pattern) (e : l₁ = l₂)
  := TacticProperty1 P (@cast_proof_mg_hyps Σ Γ l₁ l₂ e g) _.
Next Obligation.
  intros. unfold liftP. simpl. unfold cast_proof_mg_hyps.
  pose proof (Pic' := Pic). destruct Pic' as [cast_indif0].
  rewrite cast_indif0. simpl in *. unfold liftP in H. apply H.
Qed.

Program Canonical Structure cast_proof_mg_goal_indifferent_S
        {Σ : Signature} (P : proofbpred) {Pic : IndifCast P} (Γ : Theory)
        (l : list Pattern) (g₁ g₂ : Pattern) (e : g₁ = g₂)
  := TacticProperty1 P (@cast_proof_mg_goal Σ Γ l g₁ g₂ e) _.
Next Obligation.
  intros. unfold liftP. simpl. unfold cast_proof_mg_goal.
  pose proof (Pic' := Pic). destruct Pic' as [cast_indif0].
  rewrite cast_indif0. simpl in *. unfold liftP in H. apply H.
Qed.

Ltac simplLocalContext :=
  match goal with
    | [ |- @of_MyGoal ?Sgm (@mkMyGoal ?Sgm ?Ctx ?l ?g) ] => rewrite {1}[l]/app
  end.

#[global]
 Ltac mgIntro := apply MyGoal_intro; simplLocalContext.

Local Example ex_mgIntro {Σ : Signature} Γ a:
  well_formed a ->
  Γ ⊢ a ---> a.
Proof.
  intros wfa.
  toMyGoal.
  { auto. }
  mgIntro. fromMyGoal. intros _ _. apply A_impl_A; assumption.
Defined.

Lemma MyGoal_exactn {Σ : Signature} (Γ : Theory) (l₁ l₂ : list Pattern) (g : Pattern):
  @mkMyGoal Σ Γ (l₁ ++ g :: l₂) g.
Proof.
  fromMyGoal. intros wfg wfl₁gl₂.
  apply nested_const_middle.
  { exact wfg. }
  { abstract (
      pose proof (wfl₁ := wf_take (length l₁) wfl₁gl₂);
      rewrite take_app in wfl₁;
      exact wfl₁
    ).
  }
  {
    abstract (
      pose proof (wfgl₂ := wf_drop (length l₁) wfl₁gl₂);
      rewrite drop_app in wfgl₂;
      unfold wf in wfgl₂;
      simpl in wfgl₂;
      apply andb_prop in wfgl₂;
      destruct wfgl₂ as [_ wfl₂];
      exact wfl₂
    ).
  }
Defined.

Lemma MyGoal_exactn_indifferent {Σ : Signature} (P : proofbpred) {Pip : IndifProp P} Γ l₁ l₂ g:
  (forall wf1 wf2, P _ _ (@MyGoal_exactn Σ Γ l₁ l₂ g wf1 wf2) = false).
Proof.
  intros wf1 wf2.
  unfold MyGoal_exactn.
  solve_indif.
Qed.

Program Canonical Structure MyGoal_exactn_indifferent_S {Σ : Signature} (P : proofbpred) {Pip : IndifProp P}
          Γ l₁ l₂ g
  := TacticProperty0 P (@MyGoal_exactn Σ Γ l₁ l₂ g) _.
Next Obligation. intros. simpl. apply MyGoal_exactn_indifferent. exact Pip. Qed.

Tactic Notation "mgExactn" constr(n) :=
  unshelve (eapply (@cast_proof_mg_hyps _ _ _ _ _ _ _));
  [shelve|(rewrite <- (firstn_skipn n); rewrite /firstn; rewrite /skipn; reflexivity)|idtac];
  apply MyGoal_exactn.

Local Example ex_mgExactn {Σ : Signature} Γ a b c:
  well_formed a = true ->
  well_formed b = true ->
  well_formed c = true ->
  Γ ⊢ a ---> b ---> c ---> b.
Proof.
  intros wfa wfb wfc.
  toMyGoal.
  { auto. }
  mgIntro. mgIntro. mgIntro.
  mgExactn 1.
Defined.

Local Example ex_mgExactn_indif_S {Σ : Signature} P {Pip : IndifProp P} {Pic : IndifCast P} Γ a b c
  (wfa : well_formed a = true)
  (wfb : well_formed b = true)
  (wfc : well_formed c = true):
  P _ _ (@ex_mgExactn Σ Γ a b c wfa wfb wfc) = false.
Proof.
  Print tacticProperty0.
  unfold ex_mgExactn. Set Printing Implicit.
  apply liftP_impl_P.
  solve_indif.
Qed.



Section FOL_helpers.

  Context {Σ : Signature}.

  Lemma MyGoal_weakenConclusion' Γ l g g':
    Γ ⊢ g ---> g' ->
    @mkMyGoal Σ Γ l g ->
    @mkMyGoal Σ Γ l g'.
  Proof.
    intros H.
    unfold of_MyGoal in *. simpl in *.
    intros Hg wfg' wfl.
    pose proof (wfimp := proved_impl_wf _ _ H).
    apply well_formed_imp_proj1 in wfimp.
    eapply prf_weaken_conclusion_iter_meta_meta.
    5: apply Hg.
    all: assumption.
  Defined.

(*
  Program Canonical Structure MyGoal_weakenConclusion'_indifferent_S
          (P : proofbpred) {Pip : IndifProp P} (Γ : Theory)
          (l : list Pattern) (g₁ g₂ : Pattern)
    := TacticProperty1 P (@MyGoal_weakenConclusion Γ l g₁ g₂) _.
  Next Obligation.
*)
  
  Lemma prf_contraction Γ a b:
    well_formed a ->
    well_formed b ->
    Γ ⊢ ((a ---> a ---> b) ---> (a ---> b)).
  Proof.
    intros wfa wfb.
    assert (H1 : Γ ⊢ (a ---> ((a ---> b) ---> b))) by auto.
    assert (H2 : Γ ⊢ ((a ---> ((a ---> b) ---> b)) ---> ((a ---> (a ---> b)) ---> (a ---> b)))) by auto using P2.
    eapply Modus_ponens. 4: apply H2. all: auto 10.
  Defined.

  #[local] Hint Resolve prf_contraction : core.

  Program Canonical Structure prf_contraction_indifferent_S
            (P : proofbpred) {Pip : IndifProp P} (Γ : Theory)
            (ϕ₁ ϕ₂ : Pattern) (wfϕ₁ : well_formed ϕ₁) (wfϕ₂ : well_formed ϕ₂)
    := ProofProperty0 P (@prf_contraction Γ ϕ₁ ϕ₂ wfϕ₁ wfϕ₂) _.
  Next Obligation. solve_indif. Qed.

  Lemma prf_weaken_conclusion_under_implication Γ a b c:
    well_formed a ->
    well_formed b ->
    well_formed c ->
    Γ ⊢ ((a ---> b) ---> ((a ---> (b ---> c)) ---> (a ---> c))).
  Proof.
    intros wfa wfb wfc.
    assert (H1 : Γ ⊢ ((a ---> (b ---> c)) ---> (b ---> (a ---> c)))) by auto using reorder.
    assert (H2 : Γ ⊢ (((b ---> (a ---> c)) ---> (a ---> c)) ---> ((a ---> (b ---> c)) ---> (a ---> c)))).
    { apply prf_strenghten_premise_meta; auto. }
    eapply prf_weaken_conclusion_meta_meta.
    4: apply H2. all: auto. clear H1 H2.
    assert (H3 : Γ ⊢ ((a ---> b) ---> ((b ---> (a ---> c)) ---> (a ---> (a ---> c))))) by auto.
    assert (H4 : Γ ⊢ ((a ---> (a ---> c)) ---> (a ---> c))) by auto.
    assert (Hiter: ((a ---> b) ---> (b ---> a ---> c) ---> a ---> c)
                   = foldr patt_imp (a ---> c) [(a ---> b); (b ---> a ---> c)]) by reflexivity.
    rewrite Hiter. 
    eapply prf_weaken_conclusion_iter_meta_meta.
    4: apply H4. all: auto 10.
  Defined.

  Program Canonical Structure prf_weaken_conclusion_under_implication_indifferent_S
            (P : proofbpred) {Pip : IndifProp P} (Γ : Theory)
            (ϕ₁ ϕ₂ ϕ₃ : Pattern)
            (wfϕ₁ : well_formed ϕ₁) (wfϕ₂ : well_formed ϕ₂) (wfϕ₃ : well_formed ϕ₃)
    := ProofProperty0 P (@prf_weaken_conclusion_under_implication Γ ϕ₁ ϕ₂ ϕ₃ wfϕ₁ wfϕ₂ wfϕ₃) _.
  Next Obligation. solve_indif. Qed.

  Lemma prf_weaken_conclusion_under_implication_meta Γ a b c:
    well_formed a ->
    well_formed b ->
    well_formed c ->
    Γ ⊢ (a ---> b) ->
    Γ ⊢ ((a ---> (b ---> c)) ---> (a ---> c)).
  Proof.
    intros wfa wfb wfc H.
    eapply Modus_ponens.
    4: apply prf_weaken_conclusion_under_implication.
    all: auto 10.
  Defined.

  Program Canonical Structure prf_weaken_conclusion_under_implication_meta_indifferent_S
            (P : proofbpred) {Pip : IndifProp P} (Γ : Theory)
            (ϕ₁ ϕ₂ ϕ₃ : Pattern)
            (wfϕ₁ : well_formed ϕ₁) (wfϕ₂ : well_formed ϕ₂) (wfϕ₃ : well_formed ϕ₃)
    := ProofProperty1 P (@prf_weaken_conclusion_under_implication_meta Γ ϕ₁ ϕ₂ ϕ₃ wfϕ₁ wfϕ₂ wfϕ₃) _.
  Next Obligation. solve_indif; assumption. Qed.


  Lemma prf_weaken_conclusion_under_implication_meta_meta Γ a b c:
    well_formed a ->
    well_formed b ->
    well_formed c ->
    Γ ⊢ a ---> b ->
    Γ ⊢ a ---> b ---> c ->
    Γ ⊢ a ---> c.
  Proof.
    intros wfa wfb wfc H1 H2.
    eapply Modus_ponens.
    4: apply prf_weaken_conclusion_under_implication_meta. 3: apply H2.
    all: auto.
  Defined.

  Program Canonical Structure prf_weaken_conclusion_under_implication_meta_meta_indifferent_S
            (P : proofbpred) {Pip : IndifProp P} (Γ : Theory)
            (ϕ₁ ϕ₂ ϕ₃ : Pattern)
            (wfϕ₁ : well_formed ϕ₁) (wfϕ₂ : well_formed ϕ₂) (wfϕ₃ : well_formed ϕ₃)
    := ProofProperty2 P (@prf_weaken_conclusion_under_implication_meta_meta Γ ϕ₁ ϕ₂ ϕ₃ wfϕ₁ wfϕ₂ wfϕ₃) _.
  Next Obligation. solve_indif; assumption. Qed.

  Lemma prf_weaken_conclusion_iter_under_implication Γ l g g':
    wf l ->
    well_formed g ->
    well_formed g' ->
    Γ ⊢ (((g ---> g') ---> (foldr patt_imp g l)) ---> ((g ---> g') ---> (foldr patt_imp g' l))).
  Proof.
    intros wfl wfg wfg'.
    pose proof (H1 := @prf_weaken_conclusion_iter Σ Γ l g g' wfl wfg wfg').
    remember ((g ---> g')) as a.
    remember (foldr patt_imp g l) as b.
    remember (foldr patt_imp g' l) as c.
    pose proof (H2 := @prf_weaken_conclusion_under_implication Γ a b c ltac:(subst;auto) ltac:(subst;auto) ltac:(subst; auto)).
    apply reorder_meta in H2. 2,3,4: subst;auto.
    eapply Modus_ponens. 4: apply H2. all: subst;auto 10.
  Defined.

  Program Canonical Structure prf_weaken_conclusion_iter_under_implication_indifferent_S
            (P : proofbpred) {Pip : IndifProp P} (Γ : Theory)
            (l : list Pattern) (ϕ₁ ϕ₂ : Pattern)
            (wfl : wf l) (wfϕ₁ : well_formed ϕ₁) (wfϕ₂ : well_formed ϕ₂)
    := ProofProperty0 P (@prf_weaken_conclusion_iter_under_implication Γ l ϕ₁ ϕ₂ wfl wfϕ₁ wfϕ₂) _.
  Next Obligation. intros. solve_indif. Defined.

  Lemma prf_weaken_conclusion_iter_under_implication_meta Γ l g g':
    wf l ->
    well_formed g ->
    well_formed g' ->
    Γ ⊢ ((g ---> g') ---> (foldr patt_imp g l)) ->
    Γ ⊢ ((g ---> g') ---> (foldr patt_imp g' l)).
  Proof.
    intros wfl wfg wfg' H.
    eapply Modus_ponens. 4: apply prf_weaken_conclusion_iter_under_implication.
    all: auto.
  Defined.

  Program Canonical Structure prf_weaken_conclusion_iter_under_implication_meta_indifferent_S
            (P : proofbpred) {Pip : IndifProp P} (Γ : Theory)
            (l : list Pattern) (ϕ₁ ϕ₂ : Pattern)
            (wfl : wf l) (wfϕ₁ : well_formed ϕ₁) (wfϕ₂ : well_formed ϕ₂)
    := ProofProperty1 P (@prf_weaken_conclusion_iter_under_implication_meta Γ l ϕ₁ ϕ₂ wfl wfϕ₁ wfϕ₂) _.
  Next Obligation. intros. solve_indif; assumption. Defined.
  
  Lemma MyGoal_weakenConclusion_under_first_implication Γ l g g':
    @mkMyGoal Σ Γ ((g ---> g') :: l) g ->
    @mkMyGoal Σ Γ ((g ---> g') :: l) g'.
  Proof.
    intros H. unfold of_MyGoal in *. simpl in *.
    intros wfg' wfgg'l.
    pose proof (Htmp := wfgg'l).
    unfold wf in Htmp. simpl in Htmp. apply andb_prop in Htmp. destruct Htmp as [wfgg' wfl].
    apply well_formed_imp_proj1 in wfgg'. specialize (H wfgg' wfgg'l).
    apply prf_weaken_conclusion_iter_under_implication_meta; assumption.
  Defined.

  Program Canonical Structure MyGoal_weakenConclusion_under_first_implication_indifferent_S
            (P : proofbpred) {Pip : IndifProp P} {Pic : IndifCast P} (Γ : Theory)
            (l : list Pattern) (ϕ₁ ϕ₂ : Pattern)
            (wfl : wf l) (wfϕ₁ : well_formed ϕ₁) (wfϕ₂ : well_formed ϕ₂)
    := TacticProperty1 P (@MyGoal_weakenConclusion_under_first_implication Γ l ϕ₁ ϕ₂) _.
  Next Obligation.
    intros. simpl. 
    unfold MyGoal_weakenConclusion_under_first_implication.
    case_match. unfold liftP. solve_indif. apply H.
  Qed.

  Lemma prf_weaken_conclusion_iter_under_implication_iter Γ l₁ l₂ g g':
    wf l₁ ->
    wf l₂ ->
    well_formed g ->
    well_formed g' ->
    Γ ⊢ ((foldr patt_imp g (l₁ ++ (g ---> g') :: l₂)) ---> (foldr patt_imp g' (l₁ ++ (g ---> g') :: l₂))).
  Proof.
    intros wfl₁ wfl₂ wfg wfg'.
    induction l₁; simpl.
    - apply prf_weaken_conclusion_iter_under_implication; auto.
    - pose proof (wfal₁ := wfl₁). unfold wf in wfl₁. simpl in wfl₁. apply andb_prop in wfl₁.
      destruct wfl₁ as [wfa wfl₁]. specialize (IHl₁ wfl₁).
      eapply prf_weaken_conclusion_meta. all: auto 10.
  Defined.

  Program Canonical Structure prf_weaken_conclusion_iter_under_implication_iter_indifferent_S
            (P : proofbpred) {Pip : IndifProp P} {Pic : IndifCast P} (Γ : Theory)
            (l₁ l₂ : list Pattern) (ϕ₁ ϕ₂ : Pattern)
            (wfl₁ : wf l₁) (wfl₂ : wf l₂) (wfϕ₁ : well_formed ϕ₁) (wfϕ₂ : well_formed ϕ₂)
    := ProofProperty0 P (@prf_weaken_conclusion_iter_under_implication_iter Γ l₁ l₂ ϕ₁ ϕ₂ wfl₁ wfl₂ wfϕ₁ wfϕ₂) _.
  Next Obligation.
    intros.
    induction l₁.
    - solve_indif.
    - simpl. case_match. solve_indif. apply IHl₁.
  Qed.

  Lemma prf_weaken_conclusion_iter_under_implication_iter_meta Γ l₁ l₂ g g':
    wf l₁ ->
    wf l₂ ->
    well_formed g ->
    well_formed g' ->
    Γ ⊢ (foldr patt_imp g (l₁ ++ (g ---> g') :: l₂)) ->
    Γ ⊢ (foldr patt_imp g' (l₁ ++ (g ---> g') :: l₂)).
  Proof.
    intros wfl₁ wfl₂ wfg wfg' H.
    eapply Modus_ponens.
    4: apply prf_weaken_conclusion_iter_under_implication_iter.
    all: auto 10.
  Defined.

  Program Canonical Structure prf_weaken_conclusion_iter_under_implication_iter_meta_indifferent_S
            (P : proofbpred) {Pip : IndifProp P} {Pic : IndifCast P} (Γ : Theory)
            (l₁ l₂ : list Pattern) (ϕ₁ ϕ₂ : Pattern)
            (wfl₁ : wf l₁) (wfl₂ : wf l₂) (wfϕ₁ : well_formed ϕ₁) (wfϕ₂ : well_formed ϕ₂)
    := ProofProperty1 P (@prf_weaken_conclusion_iter_under_implication_iter_meta Γ l₁ l₂ ϕ₁ ϕ₂ wfl₁ wfl₂ wfϕ₁ wfϕ₂) _.
  Next Obligation. solve_indif; assumption. Qed.

  Lemma MyGoal_weakenConclusion Γ l₁ l₂ g g':
    @mkMyGoal Σ Γ (l₁ ++ (g ---> g') :: l₂) g ->
    @mkMyGoal Σ Γ (l₁ ++ (g ---> g') :: l₂) g'.
  Proof.
    unfold of_MyGoal in *. simpl in *.
    intros H wfg' wfl₁gg'l₂.
    
    apply prf_weaken_conclusion_iter_under_implication_iter_meta.
    { abstract (pose proof (wfl₁ := wf_take (length l₁) wfl₁gg'l₂); rewrite take_app in wfl₁; exact wfl₁). }
    { abstract (
        pose proof (wfgg'l₂ := wf_drop (length l₁) wfl₁gg'l₂);
        rewrite drop_app in wfgg'l₂;
        pose proof (Htmp := wfgg'l₂);
        unfold wf in Htmp;
        simpl in Htmp;
        apply andb_prop in Htmp;
        destruct Htmp as [wfgg' wfl₂];
        exact wfl₂
      ).
    }
    {
      abstract(
        pose proof (wfgg'l₂ := wf_drop (length l₁) wfl₁gg'l₂);
        rewrite drop_app in wfgg'l₂;
        pose proof (Htmp := wfgg'l₂);
        unfold wf in Htmp;
        simpl in Htmp;
        apply andb_prop in Htmp;
        destruct Htmp as [wfgg' wfl₂];
        pose proof (wfg := well_formed_imp_proj1 wfgg');
        exact wfg
      ).
    }
    { exact wfg'. }
    apply H.
    {
      abstract(
        pose proof (wfgg'l₂ := wf_drop (length l₁) wfl₁gg'l₂);
        rewrite drop_app in wfgg'l₂;
        pose proof (Htmp := wfgg'l₂);
        unfold wf in Htmp;
        simpl in Htmp;
        apply andb_prop in Htmp;
        destruct Htmp as [wfgg' wfl₂];
        pose proof (wfg := well_formed_imp_proj1 wfgg');
        exact wfg
      ).
    }
    exact wfl₁gg'l₂.
  Defined.

  Program Canonical Structure MyGoal_weakenConclusion_indifferent_S
            (P : proofbpred) {Pip : IndifProp P} {Pic : IndifCast P} (Γ : Theory)
            (l₁ l₂ : list Pattern) (ϕ₁ ϕ₂ : Pattern)
    := TacticProperty1 P (@MyGoal_weakenConclusion Γ l₁ l₂ ϕ₁ ϕ₂) _.
  Next Obligation. intros. unfold MyGoal_weakenConclusion. unfold liftP. solve_indif. apply H. Qed.

End FOL_helpers.

Tactic Notation "mgApply" constr(n) :=
  unshelve (eapply (@cast_proof_mg_hyps _ _ _ _ _ _ _));
  [shelve|(rewrite <- (firstn_skipn n); rewrite /firstn; rewrite /skipn; reflexivity)|idtac];
  apply MyGoal_weakenConclusion;
  let hyps := fresh "hyps" in rewrite [hyps in @mkMyGoal _ _ hyps _]/app.

Local Example ex_mgApply {Σ : Signature} Γ a b:
  well_formed a ->
  well_formed b ->
  Γ ⊢ a ---> (a ---> b) ---> b.
Proof.
  intros wfa wfb.
  toMyGoal.
  { auto. }
  mgIntro. mgIntro.
  mgApply 1.
  fromMyGoal. intros _ _. apply P1; auto.
Defined.

Section FOL_helpers.

  Context {Σ : Signature}.
  
  Lemma Constructive_dilemma Γ p q r s:
    well_formed p ->
    well_formed q ->
    well_formed r ->
    well_formed s ->
    Γ ⊢ ((p ---> q) ---> (r ---> s) ---> (p or r) ---> (q or s)).
  Proof.
    intros wfp wfq wfr wfs.
    unfold patt_or.

    toMyGoal.
    { auto 10. }

    mgIntro. mgIntro. mgIntro. mgIntro.
    mgApply 1.
    mgApply 2.
    mgIntro.
    mgApply 3.
    mgApply 0.
    mgExactn 4.
  Defined.

  Program Canonical Structure Constructive_dilemma_indifferent_S
            (P : proofbpred) {Pip : IndifProp P} {Pic : IndifCast P} (Γ : Theory)
            (p q r s : Pattern)
            (wfp : well_formed p)
            (wfq : well_formed q)
            (wfr : well_formed r)
            (wfs : well_formed s)
    := ProofProperty0 P (@Constructive_dilemma Γ p q r s wfp wfq wfr wfs) _.
  Next Obligation. intros. apply liftP_impl_P. solve_indif. Qed.

  Lemma prf_add_assumption Γ a b :
    well_formed a ->
    well_formed b ->
    Γ ⊢ b ->
    Γ ⊢ (a ---> b).
  Proof.
    intros wfa wfb H.
    eapply Modus_ponens.
    4: apply P1. all: auto.
  Defined.

  Program Canonical Structure prf_add_assumption_indifferent_S
            (P : proofbpred) {Pip : IndifProp P} (Γ : Theory)
            (p q : Pattern)
            (wfp : well_formed p)
            (wfq : well_formed q)
    := ProofProperty1 P (@prf_add_assumption Γ p q wfp wfq) _.
  Next Obligation. solve_indif; assumption. Qed.

  Lemma prf_impl_distr_meta Γ a b c:
    well_formed a ->
    well_formed b ->
    well_formed c ->
    Γ ⊢ (a ---> (b ---> c)) ->
    Γ ⊢ ((a ---> b) ---> (a ---> c)).
  Proof.
    intros wfa wfb wfc H.
    eapply Modus_ponens. 4: apply P2. all: auto.
  Defined.

  Program Canonical Structure prf_impl_distr_meta_indifferent_S
            (P : proofbpred) {Pip : IndifProp P} (Γ : Theory)
            (p q r : Pattern)
            (wfp : well_formed p)
            (wfq : well_formed q)
            (wfr : well_formed r)
    := ProofProperty1 P (@prf_impl_distr_meta Γ p q r wfp wfq wfr) _.
  Next Obligation. solve_indif; assumption. Qed.

  Lemma prf_add_lemma_under_implication Γ l g h:
    wf l ->
    well_formed g ->
    well_formed h ->
    Γ ⊢ ((foldr patt_imp h l) ---> ((foldr patt_imp g (l ++ [h])) ---> (foldr patt_imp g l))).
  Proof.
    intros wfl wfg wfh.
    induction l; simpl.
    - apply modus_ponens; auto.
    - pose proof (wfal := wfl).
      unfold wf in wfl. apply andb_prop in wfl. destruct wfl as [wfa wfl].
      specialize (IHl wfl).
      assert (H1: Γ ⊢ a ---> foldr patt_imp h l ---> foldr patt_imp g (l ++ [h]) ---> foldr patt_imp g l).
      { apply prf_add_assumption; auto 10. }
      assert (H2 : Γ ⊢ (a ---> foldr patt_imp h l) ---> (a ---> foldr patt_imp g (l ++ [h]) ---> foldr patt_imp g l)).
      { apply prf_impl_distr_meta; auto 10. }
      assert (H3 : Γ ⊢ ((a ---> foldr patt_imp g (l ++ [h]) ---> foldr patt_imp g l)
                          ---> ((a ---> foldr patt_imp g (l ++ [h])) ---> (a ---> foldr patt_imp g l)))).
      { auto 10 using P2. }

      eapply prf_weaken_conclusion_meta_meta.
      4: apply H3. all: auto 10.
  Defined.

  Program Canonical Structure prf_add_lemma_under_implication_indifferent_S
            (P : proofbpred) {Pip : IndifProp P} (Γ : Theory)
            (l : list Pattern)
            (p q : Pattern)
            (wfl : wf l)
            (wfp : well_formed p)
            (wfq : well_formed q)
    := ProofProperty0 P (@prf_add_lemma_under_implication Γ l p q wfl wfp wfq) _.
  Next Obligation.
    intros.
    induction l.
    - solve_indif.
    - simpl. case_match. solve_indif. apply IHl.
  Qed.

  Lemma prf_add_lemma_under_implication_meta Γ l g h:
    wf l ->
    well_formed g ->
    well_formed h ->
    Γ ⊢ (foldr patt_imp h l) ->
    Γ ⊢ ((foldr patt_imp g (l ++ [h])) ---> (foldr patt_imp g l)).
  Proof.
    intros WFl WFg WGh H. eapply Modus_ponens. 4: apply prf_add_lemma_under_implication. all: auto 7.
  Defined.

  Program Canonical Structure prf_add_lemma_under_implication_meta_indifferent_S
            (P : proofbpred) {Pip : IndifProp P} (Γ : Theory)
            (l : list Pattern)
            (p q : Pattern)
            (wfl : wf l)
            (wfp : well_formed p)
            (wfq : well_formed q)
    := ProofProperty1 P (@prf_add_lemma_under_implication_meta Γ l p q wfl wfp wfq) _.
  Next Obligation. solve_indif; assumption. Qed.

  Lemma prf_add_lemma_under_implication_meta_meta Γ l g h:
    wf l ->
    well_formed g ->
    well_formed h ->
    Γ ⊢ (foldr patt_imp h l) ->
    Γ ⊢ (foldr patt_imp g (l ++ [h])) ->
    Γ ⊢ (foldr patt_imp g l).
  Proof.
    intros WFl WFg WGh H H0. eapply Modus_ponens. 4: apply prf_add_lemma_under_implication_meta.
    3: apply H0. all: auto 7.
  Defined.

  Program Canonical Structure prf_add_lemma_under_implication_meta_meta_indifferent_S
            (P : proofbpred) {Pip : IndifProp P} (Γ : Theory)
            (l : list Pattern)
            (p q : Pattern)
            (wfl : wf l)
            (wfp : well_formed p)
            (wfq : well_formed q)
    := ProofProperty2 P (@prf_add_lemma_under_implication_meta_meta Γ l p q wfl wfp wfq) _.
  Next Obligation. solve_indif; assumption. Qed.

  Lemma myGoal_assert Γ l g h:
    well_formed h ->
    @mkMyGoal Σ Γ l h ->
    @mkMyGoal Σ Γ (l ++ [h]) g ->
    @mkMyGoal Σ Γ l g.
  Proof.
    intros wfh H1 H2.
    unfold of_MyGoal in *. simpl in *.
    intros wfg wfl.
    eapply prf_add_lemma_under_implication_meta_meta.
    4: apply H1. 6: apply H2. all: try assumption.
    { abstract (
        unfold wf;
        rewrite map_app;
        rewrite foldr_app;
        simpl;
        rewrite wfh;
        simpl;
        exact wfl
      ).
    }
  Defined.

  Program Canonical Structure myGoal_assert_indifferent_S
            (P : proofbpred) {Pip : IndifProp P} (Γ : Theory)
            (l : list Pattern)
            (p q : Pattern)
            (wfq : well_formed q)
    := TacticProperty2 P (@myGoal_assert Γ l p q wfq) _.
  Next Obligation.
    intros. unfold myGoal_assert. unfold liftP.
    solve_indif.
    - apply H.
    - apply H0.
  Qed.

  Lemma prf_add_lemma_under_implication_generalized Γ l1 l2 g h:
    wf l1 ->
    wf l2 ->
    well_formed g ->
    well_formed h ->
    Γ ⊢ ((foldr patt_imp h l1) ---> ((foldr patt_imp g (l1 ++ [h] ++ l2)) ---> (foldr patt_imp g (l1 ++ l2)))).
  Proof.
    intros wfl1 wfl2 wfg wfh.
    induction l1; simpl.
    - apply modus_ponens; auto.
    - pose proof (wfal1 := wfl1).
      unfold wf in wfl1. simpl in wfl1. apply andb_prop in wfl1. destruct wfl1 as [wfa wfl1].
      specialize (IHl1 wfl1).
      assert (H1: Γ ⊢ a ---> foldr patt_imp h l1 ---> foldr patt_imp g (l1 ++ [h] ++ l2) ---> foldr patt_imp g (l1 ++ l2)).
      { apply prf_add_assumption; auto 10. }
      assert (H2 : Γ ⊢ (a ---> foldr patt_imp h l1) ---> (a ---> foldr patt_imp g (l1 ++ [h] ++ l2) ---> foldr patt_imp g (l1 ++ l2))).
      { apply prf_impl_distr_meta; auto 10. }
      assert (H3 : Γ ⊢ ((a ---> foldr patt_imp g (l1 ++ [h] ++ l2) ---> foldr patt_imp g (l1 ++ l2))
                          ---> ((a ---> foldr patt_imp g (l1 ++ [h] ++ l2)) ---> (a ---> foldr patt_imp g (l1 ++ l2))))).
      { auto 10 using P2. }

      eapply prf_weaken_conclusion_meta_meta.
      4: apply H3. all: auto 10.
  Defined.
  
  Program Canonical Structure prf_add_lemma_under_implication_generalized_indifferent_S
            (P : proofbpred) {Pip : IndifProp P} (Γ : Theory)
            (l₁ l₂ : list Pattern)
            (p q : Pattern)
            (wfl₁ : wf l₁)
            (wfl₂ : wf l₂)
            (wfp : well_formed p)
            (wfq : well_formed q)
    := ProofProperty0 P (@prf_add_lemma_under_implication_generalized Γ l₁ l₂ p q wfl₁ wfl₂ wfp wfq) _.
  Next Obligation.
    intros.
    induction l₁.
    - solve_indif.
    - simpl. case_match. solve_indif. apply IHl₁.
  Qed.

  Lemma prf_add_lemma_under_implication_generalized_meta Γ l1 l2 g h:
    wf l1 ->
    wf l2 ->
    well_formed g ->
    well_formed h ->
    Γ ⊢ (foldr patt_imp h l1) ->
    Γ ⊢ ((foldr patt_imp g (l1 ++ [h] ++ l2)) ---> (foldr patt_imp g (l1 ++ l2))).
  Proof.
    intros WFl1 WFl2 WFg WGh H. eapply Modus_ponens. 4: apply prf_add_lemma_under_implication_generalized. all: auto 10.
  Defined.

  Program Canonical Structure prf_add_lemma_under_implication_generalized_meta_indifferent_S
            (P : proofbpred) {Pip : IndifProp P} (Γ : Theory)
            (l₁ l₂ : list Pattern)
            (p q : Pattern)
            (wfl₁ : wf l₁)
            (wfl₂ : wf l₂)
            (wfp : well_formed p)
            (wfq : well_formed q)
    := ProofProperty1 P (@prf_add_lemma_under_implication_generalized_meta Γ l₁ l₂ p q wfl₁ wfl₂ wfp wfq) _.
  Next Obligation. solve_indif; assumption. Qed.
  
  Lemma prf_add_lemma_under_implication_generalized_meta_meta Γ l1 l2 g h:
    wf l1 ->
    wf l2 ->
    well_formed g ->
    well_formed h ->
    Γ ⊢ (foldr patt_imp h l1) ->
    Γ ⊢ (foldr patt_imp g (l1 ++ [h] ++ l2)) ->
    Γ ⊢ (foldr patt_imp g (l1 ++ l2)).
  Proof.
    intros WFl1 WFl2 WFg WGh H H0. eapply Modus_ponens. 4: apply prf_add_lemma_under_implication_generalized_meta.
    3: apply H0. all: auto 7.
  Defined.

  Program Canonical Structure prf_add_lemma_under_implication_generalized_meta_meta_indifferent_S
            (P : proofbpred) {Pip : IndifProp P} (Γ : Theory)
            (l₁ l₂ : list Pattern)
            (p q : Pattern)
            (wfl₁ : wf l₁)
            (wfl₂ : wf l₂)
            (wfp : well_formed p)
            (wfq : well_formed q)
    := ProofProperty2 P (@prf_add_lemma_under_implication_generalized_meta_meta Γ l₁ l₂ p q wfl₁ wfl₂ wfp wfq) _.
  Next Obligation. solve_indif; assumption. Qed.

  Lemma myGoal_assert_generalized Γ l1 l2 g h:
    well_formed h ->
    @mkMyGoal Σ Γ l1 h ->
    @mkMyGoal Σ Γ (l1 ++ [h] ++ l2) g ->
    @mkMyGoal Σ Γ (l1 ++ l2) g.
  Proof.
    intros wfh H1 H2.
    unfold of_MyGoal in *. simpl in *.
    intros wfg wfl1l2.
    eapply prf_add_lemma_under_implication_generalized_meta_meta.
    5: apply H1. 7: apply H2. all: try assumption.
    { abstract (
          apply (wf_take (length l1)) in wfl1l2;
          rewrite take_app in wfl1l2;
          exact wfl1l2
      ).
    }
    { abstract (
          apply (wf_drop (length l1)) in wfl1l2;
          rewrite drop_app in wfl1l2;
          exact wfl1l2
      ).
    }
    { abstract (
          apply (wf_take (length l1)) in wfl1l2;
          rewrite take_app in wfl1l2;
          exact wfl1l2
      ).
    }
    {
      abstract(
        pose proof (wfl1 := wf_take (length l1) wfl1l2);
        rewrite take_app in wfl1;
        pose proof (wfl2 := wf_drop (length l1) wfl1l2);
        rewrite drop_app in wfl2;
        unfold wf; rewrite map_app; rewrite foldr_app;
        simpl; rewrite wfh; unfold wf in wfl2; rewrite wfl2;
        simpl; exact wfl1
      ).
    }
  Defined.

  Program Canonical Structure myGoal_assert_generalized_indifferent_S
            (P : proofbpred) {Pip : IndifProp P} (Γ : Theory)
            (l₁ l₂ : list Pattern)
            (p q : Pattern)
            (wfq : well_formed q)
    := TacticProperty2 P (@myGoal_assert_generalized Γ l₁ l₂ p q wfq) _.
  Next Obligation. intros. unfold liftP. solve_indif. apply H. apply H0. Qed.
  
End FOL_helpers.

Tactic Notation "mgAssert" "(" constr(t) ")" :=
  match goal with
  | |- @of_MyGoal ?Sgm (@mkMyGoal ?Sgm ?Ctx ?l ?g) =>
    let Hwf := fresh "Hwf" in
    assert (Hwf : well_formed t);
    [idtac|
      let H := fresh "H" in
      assert (H : @mkMyGoal Sgm Ctx l t);
      [ | (eapply (@myGoal_assert Sgm Ctx l g t Hwf H); rewrite [_ ++ _]/=; clear H)]
    ]
  end.

Local Example ex_mgAssert {Σ : Signature} Γ a:
  well_formed a ->
  Γ ⊢ (a ---> a ---> a).
Proof.
  intros wfa.
  toMyGoal.
  { auto. }
  mgIntro. mgIntro.
  mgAssert (a).
  { auto. }
  { mgExactn 1. }
  { mgExactn 2. }
Qed.

Tactic Notation "mgAssert" "(" constr(t) ")" "using" "first" constr(n) :=
  lazymatch goal with
  | |- @of_MyGoal ?Sgm (@mkMyGoal ?Sgm ?Ctx ?l ?g) =>
    let l1 := fresh "l1" in
    let l2 := fresh "l2" in
    let Heql1 := fresh "Heql1" in
    let Heql2 := fresh "Heql2" in
    remember (take n l) as l1 eqn:Heql1 in |-;
    remember (drop n l) as l2 eqn:Heql2 in |-;
    simpl in Heql1; simpl in Heql2;
    eapply cast_proof_mg_hyps;
    [(
      rewrite -[l](take_drop n);
      reflexivity
     )|];
    let Hwf := fresh "Hwf" in
    assert (Hwf : well_formed t);
    [idtac|
      let H := fresh "H" in
      assert (H : @mkMyGoal Sgm Ctx l1 t) ;
      [
        (eapply cast_proof_mg_hyps; [(rewrite Heql1; reflexivity)|]);  clear l1 l2 Heql1 Heql2
      | apply (cast_proof_mg_hyps Heql1) in H;
        eapply (@myGoal_assert_generalized Sgm Ctx (take n l) (drop n l) g t Hwf H);
        rewrite [_ ++ _]/=; clear l1 l2 Heql1 Heql2 H] 
    ]
  end.

Local Example ex_assert_using {Σ : Signature} Γ p q a b:
  well_formed a = true ->
  well_formed b = true ->
  well_formed p = true ->
  well_formed q = true ->
  Γ ⊢ a ---> p and q ---> b ---> ! ! q.
Proof.
  intros wfa wfb wfp wfq.
  toMyGoal.
  { auto 10. }
  do 3 mgIntro.
  mgAssert (p) using first 2.
  { auto. }
  { admit. }
  { admit. }
Abort.


Section FOL_helpers.

  Context {Σ : Signature}.
  
  Lemma P4i' (Γ : Theory) (A : Pattern) :
    well_formed A →
    Γ ⊢ ((!A ---> A) ---> A).
  Proof.
    intros wfA.
    assert (H1: Γ ⊢ ((! A ---> ! ! A) ---> ! ! A)).
    { apply P4i. auto. }
    assert (H2: Γ ⊢ ((! A ---> A) ---> (! A ---> ! ! A))).
    { eapply prf_weaken_conclusion_meta; auto. }
    
    eapply prf_strenghten_premise_meta_meta. 4: apply H2. all: auto.
    eapply prf_weaken_conclusion_meta_meta. 4: apply not_not_elim. all: auto.
  Defined.

  #[local] Hint Resolve P4i' : core.

  Program Canonical Structure P4i'_indifferent_S
            (P : proofbpred) {Pip : IndifProp P} (Γ : Theory)
            (q : Pattern)
            (wfq : well_formed q)
    := ProofProperty0 P (@P4i' Γ q wfq) _.
  Next Obligation. solve_indif. Qed.

  Lemma tofold p:
    p = fold_right patt_imp p [].
  Proof.
    reflexivity.
  Defined.

  Lemma consume p q l:
    fold_right patt_imp (p ---> q) l = fold_right patt_imp q (l ++ [p]).
  Proof.
    rewrite foldr_app. reflexivity.
  Defined.
  
  
  Lemma prf_disj_elim Γ p q r:
    well_formed p ->
    well_formed q ->
    well_formed r ->
    Γ ⊢ ((p ---> r) ---> (q ---> r) ---> (p or q) ---> r).
  Proof.
    intros wfp wfq wfr.
    pose proof (H1 := @Constructive_dilemma Σ Γ p r q r wfp wfr wfq wfr).
    assert (Γ ⊢ ((r or r) ---> r)).
    { unfold patt_or. apply P4i'; auto. }
    eapply cast_proof in H1.
    2: { rewrite -> tofold. do 3 rewrite -> consume. reflexivity. }
    eapply prf_weaken_conclusion_iter_meta_meta in H1. 5: apply H. all: auto 10.
  Defined.

  Program Canonical Structure prf_disj_elim_indifferent_S
            (P : proofbpred) {Pip : IndifProp P} {Pic : IndifCast P} (Γ : Theory)
            (p q r : Pattern)
            (wfp : well_formed p)
            (wfq : well_formed q)
            (wfr : well_formed r)
    := ProofProperty0 P (@prf_disj_elim Γ p q r wfp wfq wfr) _.
  Next Obligation. solve_indif. Qed.

  Lemma prf_disj_elim_meta Γ p q r:
    well_formed p ->
    well_formed q ->
    well_formed r ->
    Γ ⊢ (p ---> r) ->
    Γ ⊢ ((q ---> r) ---> (p or q) ---> r).
  Proof.
    intros WFp WHq WFr H. eapply Modus_ponens. 4: apply prf_disj_elim.
    all: auto 10.
  Defined.
  

  Program Canonical Structure prf_disj_elim_meta_indifferent_S
            (P : proofbpred) {Pip : IndifProp P} {Pic : IndifCast P} (Γ : Theory)
            (p q r : Pattern)
            (wfp : well_formed p)
            (wfq : well_formed q)
            (wfr : well_formed r)
    := ProofProperty1 P (@prf_disj_elim_meta Γ p q r wfp wfq wfr) _.
  Next Obligation. solve_indif; assumption. Qed.
  
  Lemma prf_disj_elim_meta_meta Γ p q r:
    well_formed p ->
    well_formed q ->
    well_formed r ->
    Γ ⊢ (p ---> r) ->
    Γ ⊢ (q ---> r) ->
    Γ ⊢ ((p or q) ---> r).
  Proof.
    intros WFp WHq WFr H H0. eapply Modus_ponens. 4: apply prf_disj_elim_meta.
    all: auto.
  Defined.

  Program Canonical Structure prf_disj_elim_meta_meta_indifferent_S
            (P : proofbpred) {Pip : IndifProp P} {Pic : IndifCast P} (Γ : Theory)
            (p q r : Pattern)
            (wfp : well_formed p)
            (wfq : well_formed q)
            (wfr : well_formed r)
    := ProofProperty2 P (@prf_disj_elim_meta_meta Γ p q r wfp wfq wfr) _.
  Next Obligation. solve_indif; assumption. Qed.

  (* TODO: add an indifference canonical structure for this (ProofProperty3) *)
  Lemma prf_disj_elim_meta_meta_meta Γ p q r:
    well_formed p ->
    well_formed q ->
    well_formed r ->
    Γ ⊢ (p ---> r) ->
    Γ ⊢ (q ---> r) ->
    Γ ⊢ (p or q) ->
    Γ ⊢ r.
  Proof.
    intros WFp WHq WFr H H0 H1. eapply Modus_ponens. 4: apply prf_disj_elim_meta_meta. 3: apply H1.
    all: auto.
  Defined.
  

  Lemma prf_add_proved_to_assumptions Γ l a g:
    wf l ->
    well_formed a ->
    well_formed g ->
    Γ ⊢ a ->
    Γ ⊢ ((foldr patt_imp g (a::l)) ---> (foldr patt_imp g l)).
  Proof.
    intros wfl wfa wfg Ha.
    induction l.
    - simpl.
      pose proof (@modus_ponens Σ Γ _ _ wfa wfg).
      eapply Modus_ponens. 4: apply H. all: auto.
    - pose proof (wfa0l := wfl).
      unfold wf in wfl. simpl in wfl. apply andb_prop in wfl. destruct wfl as [wfa0 wfl].
      specialize (IHl wfl).
      simpl in IHl. simpl.
      (* < change a0 and a in the LHS > *)
      assert (H : Γ ⊢ (a ---> a0 ---> foldr patt_imp g l) ---> (a0 ---> a ---> foldr patt_imp g l)).
      { apply reorder; auto. }

      rewrite -> tofold. rewrite consume.
      pose proof (H0 := @prf_strenghten_premise_iter_meta_meta Σ Γ [] []).
      simpl in H0. simpl.
      specialize (H0 (a0 ---> a ---> foldr patt_imp g l) (a ---> a0 ---> foldr patt_imp g l)).
      specialize (H0 (a0 ---> foldr patt_imp g l)). simpl in H0. simpl.
      simpl. apply H0. all: auto. clear H0 H.
      (* </change a0 and a > *)
      assert (Γ ⊢ ((a ---> a0 ---> foldr patt_imp g l) ---> (a0 ---> foldr patt_imp g l))).
      { eapply Modus_ponens. 4: apply modus_ponens. all: auto 10. }
      
      eapply prf_strenghten_premise_meta_meta. 5: apply H. all: auto.
      apply reorder; auto.
  Defined.

  Lemma prf_add_proved_to_assumptions_indifferent
    P {Pip : IndifProp P} Γ l h g
    (wfl : wf l)
    (wfg : well_formed g)
    (wfh : well_formed h)
    (pfh : Γ ⊢ h):
    P _ _ pfh = false ->
    P _ _ (@prf_add_proved_to_assumptions Γ l h g wfl wfh wfg pfh) = false.
  Proof.
    intros H. pose proof (Hp' := Pip). destruct Hp' as [[Hp1 [Hp2 [Hp3 Hmp]]]].
    induction l.
    - solve_indif; assumption.
    - simpl.
      case_match.
      unfold eq_rec_r. unfold eq_rec. unfold eq_rect. unfold eq_sym. unfold tofold. unfold consume.
      unfold eq_ind_r. unfold eq_ind. unfold eq_sym.
      remember (foldr_app Pattern Pattern patt_imp []
              [h ---> a ---> foldr patt_imp g l] (a ---> foldr patt_imp g l)) as fa.
      simpl in fa.
      clear Heqfa.
      replace fa with (@erefl Pattern (((h ---> a ---> foldr patt_imp g l) ---> a ---> foldr patt_imp g l))).
      2: { apply UIP_dec. intros x y. apply Pattern_eqdec. }
      simpl.
      solve_indif.

      epose proof (Htmp :=
                     pp2_proof_property (
                         @prf_strenghten_premise_iter_meta_meta_indifferent_S
                           Σ P Pip Γ [] [] (a ---> h ---> foldr patt_imp g l) (h ---> a ---> foldr patt_imp g l)
                       _ _ _ _ _ _)
                  ).
      apply Htmp; clear Htmp.
      solve_indif. solve_indif. assumption.
  Qed.

  Program Canonical Structure prf_add_proved_to_assumptions_indifferent_S
            (P : proofbpred) {Pip : IndifProp P} (Γ : Theory)
            (l : list Pattern)
            (p q : Pattern)
            (wfl : wf l)
            (wfp : well_formed p)
            (wfq : well_formed q)
    := ProofProperty1 P (@prf_add_proved_to_assumptions Γ l p q wfl wfp wfq) _.
  Next Obligation.
    intros. apply prf_add_proved_to_assumptions_indifferent; assumption. Qed.

  Lemma prf_add_proved_to_assumptions_meta Γ l a g:
    wf l ->
    well_formed a ->
    well_formed g ->
    Γ ⊢ a ->
    Γ ⊢ (foldr patt_imp g (a::l)) ->
    Γ ⊢ (foldr patt_imp g l).
  Proof.
    intros WFl WFa WFg H H0.
    eapply Modus_ponens.
    4: eapply prf_add_proved_to_assumptions.
    3: apply H0.
    all: auto.
  Defined.

  Program Canonical Structure prf_add_proved_to_assumptions_meta_indifferent_S
            (P : proofbpred) {Pip : IndifProp P} (Γ : Theory)
            (l : list Pattern)
            (p q : Pattern)
            (wfl : wf l)
            (wfp : well_formed p)
            (wfq : well_formed q)
    := ProofProperty2 P (@prf_add_proved_to_assumptions_meta Γ l p q wfl wfp wfq) _.
  Next Obligation. solve_indif; assumption. Qed.
  
  Lemma MyGoal_add Γ l g h:
    Γ ⊢ h ->
    @mkMyGoal Σ Γ (h::l) g ->
    @mkMyGoal Σ Γ l g.
  Proof.
    intros H H0.
    unfold of_MyGoal in *. simpl in *.
    intros wfg wfl.
    apply prf_add_proved_to_assumptions_meta with (a := h).
    5: apply H0.
    all: try assumption.
    { abstract (apply proved_impl_wf in H; exact H). }
    { abstract (
          unfold wf;
          simpl;
          apply proved_impl_wf in H;
          rewrite H;
          simpl;
          exact wfl
      ).
    }
  Defined.

  Lemma MyGoal_add_indifferent
    P Γ l g h pfh pf:
    indifferent_to_prop P ->
    P _ _ pfh = false ->
    (forall wf3 wf4, P _ _ (pf wf3 wf4) = false) ->
    (forall wf1 wf2, P _ _ (@MyGoal_add Γ l g h pfh pf wf1 wf2) = false).
  Proof.
    intros Hp H1 H2. pose proof (Hp' := Hp). destruct Hp' as [Hp1 [Hp2 [Hp3 Hmp]]].
    simpl in *. unfold MyGoal_add. unfold prf_add_proved_to_assumptions_meta.
    intros wf1 wf2.
    rewrite Hmp. simpl.
    rewrite H2. simpl.
    rewrite prf_add_proved_to_assumptions_indifferent; auto.
  Qed.


End FOL_helpers.

(*
Lemma cast_proof_collapse {Σ : Signature} Γ ϕ₁ ϕ₂ ϕ₃ (pf : Γ ⊢ ϕ₁) (e₂₁ : ϕ₂ = ϕ₁) (e₃₂ : ϕ₃ = ϕ₂):
  @cast_proof Σ Γ ϕ₂ ϕ₃ e₃₂ (@cast_proof Σ Γ ϕ₁ ϕ₂ e₂₁ pf ) = (@cast_proof Σ Γ ϕ₁ ϕ₃ (eq_trans e₃₂ e₂₁) pf ).
Proof.
  unfold cast_proof,eq_rec_r,eq_rec,eq_rect.
  repeat case_match.
  replace (eq_sym (eq_trans e₃₂ e₂₁)) with (@eq_refl _ ϕ₁) by (apply UIP_dec; intros x' y'; apply Pattern_eqdec).
  reflexivity.
Qed.

Lemma MyGoal_add_indifferent_extended {Σ : Signature}
      P Γ l g h pfh pf:
  indifferent_to_cast P ->
  indifferent_to_prop P ->
  P _ _ pfh = false ->
  (forall wf3 wf4, P _ _ (pf wf3 wf4) = false) ->
  (forall wf1 wf2 ϕ₂ (e: ϕ₂ = (foldr patt_imp g l)),
      P _ ϕ₂ (@cast_proof Σ Γ (foldr patt_imp g l) ϕ₂ e (@MyGoal_add Σ Γ l g h pfh pf wf1 wf2)) = false).
Proof.
  intros Hc Hp H1 H2. pose proof (Hp' := Hp). destruct Hp' as [Hp1 [Hp2 [Hp3 Hmp]]].
  simpl in *. unfold MyGoal_add. unfold prf_add_proved_to_assumptions_meta.
  intros wf1 wf2 ϕ₂ e.
  unfold indifferent_to_cast in Hc. rewrite Hc.
  rewrite Hmp. simpl.
  rewrite H2. simpl.
  rewrite prf_add_proved_to_assumptions_indifferent; auto.
Qed.


Definition relax_P {Σ : Signature} (P: proofbpred) (Γ : Theory) (ϕ₁ : Pattern) (pf : Γ ⊢ ϕ₁) (ϕ₂ : Pattern)
: bool
:=
if (decide (ϕ₁ = ϕ₂)) is left _ then P Γ ϕ₁ pf else negb (P Γ ϕ₁ pf).

Check @cast_proof.
Lemma relax {Σ : Signature} (P: proofbpred) (Γ : Theory) (ϕ₁ : Pattern) (pf : Γ ⊢ ϕ₁)
      (ϕ₂ : Pattern) (e : ϕ₁ = ϕ₂):
  @relax_P Σ P Γ ϕ₁ (@cast_proof Σ Γ _ _ e pf) ϕ₂ ->
  P Γ ϕ₂ pf.


Lemma MyGoal_add_indifferent_relaxed {Σ : Signature}
      P Γ l g h pfh pf ϕ₂:
  ϕ₂ = foldr patt_imp g l ->
  indifferent_to_prop P ->
  P _ _ pfh = false ->
  (forall wf3 wf4, P _ _ (pf wf3 wf4) = false) ->
  (forall wf1 wf2, @relax_P Σ P Γ (foldr patt_imp g l) (@MyGoal_add Σ Γ l g h pfh pf wf1 wf2) ϕ₂ = false).
Proof.
  intros Hϕ₂.
  intros. unfold relax_P.
  case_match.
  + apply MyGoal_add_indifferent; assumption.
  + symmetry in Hϕ₂. contradiction.
Qed.
*)

Definition Pattern_of {Σ : Signature} {Γ : Theory} {ϕ : Pattern} (pf : Γ ⊢ ϕ) : Pattern := ϕ.

Structure equals_pf {Σ : Signature} (Γ : Theory) (ϕ : Pattern) (pf : Γ ⊢ ϕ) := Pack_pf { unpack_pf : Γ ⊢ ϕ }.
Canonical Structure equate_pf {Σ : Signature} (Γ : Theory) (ϕ : Pattern) (pf : Γ ⊢ ϕ) := Pack_pf pf pf.

Structure equals_pat {Σ : Signature} (ϕ : Pattern) := Pack_pat { unpack_pat : Pattern }.
Canonical Structure equate_pat {Σ : Signature} (ϕ : Pattern) := Pack_pat ϕ ϕ.

Print ImpReshapeS.

(*
Structure helper {Σ : Signature} (P : proofbpred) (Γ : Theory) (ϕ : Pattern)
 := Helper
      { helper_packed_ϕ : equals_pat ϕ;
        helper_P : (fun (pf : Γ ⊢ (unpack_pat helper_packed_ϕ) ) => P Γ (unpack_pat helper_packed_ϕ) pf);
      }.
*)

(*
Lemma my_mnpp_proof_property {Σ : Signature} (P : proofbpred) (Γ : Theory) (l : list Pattern) (g : Pattern)
          (r : ImpReshapeS g l) (mnpp : @myNWFProofProperty Σ P Γ l g):
         forall wfg wfl pf,
           pf = (mnpp_proof mnpp wfg wfl) ->
           P Γ (untagPattern (irs_flattened r)) pf = false.
*)

(*
Canonical Structure myProofProperty_from_myNWFProofProperty
          {Σ : Signature} (P : proofbpred) (Γ : Theory)
          (l : list Pattern) (g : Pattern)
          (wfl : wf l) (wfg : well_formed g)
          (*r : ImpReshapeS g l*)
          (MNPP : myNWFProofProperty P Γ l g)
  : myProofProperty P Γ (*untagPattern (irs_flattened r)*) (foldr patt_imp g l)
  := @MyProofProperty Σ P Γ (*untagPattern (irs_flattened r)*) (foldr patt_imp g l)
                      (mnpp_proof MNPP wfg wfl)
                      (mnpp_proof_property MNPP wfg wfl).
*)
Print Canonical Projections.
(*Print myProofProperty_from_myNWFProofProperty.*)
(*
Program Canonical Structure myNWFProofProperty_from_myProofProperty
          {Σ : Signature} (P : proofbpred) (Γ : Theory)
          (l : list Pattern) (g : Pattern)
          (r : ImpReshapeS g l)
          (MPP : myProofProperty P Γ (untagPattern (irs_flattened r)))
  : myNWFProofProperty P Γ l g
  := @MyNWFProofProperty Σ P Γ l g (fun _ _ => mpp_proof MPP) (fun _ _ => mpp_proof_property MPP).
Next Obligation.
  intros Σ P Γ l g r Hmpp wfl wfg.
  apply irs_pf.
Defined.
Next Obligation.
  intros Σ P Γ l g r MPP wfl wfg.
  simpl.
  unfold eq_rect. unfold myNWFProofProperty_from_myProofProperty_obligation_1.
  destruct r. simpl in *. case_match. reflexivity.
Qed.
*)

Program Canonical Structure MyGoal_add_indifferent_S
          {Σ : Signature} (P : proofbpred) {Pip : IndifProp P} (Γ : Theory) (*ϕ : Pattern*)
          (l: list Pattern)
          (g h : Pattern)
          (P_pfh : myProofProperty P Γ h)
          (P_pf : myNWFProofProperty P Γ (h::l) g)
  := @MyNWFProofProperty Σ P Γ l g
                         (fun wfl wfg =>
                            (@MyGoal_add Σ Γ l g h (mpp_proof P_pfh) (mnpp_proof P_pf) wfl wfg)
                         )
                         _
.
Next Obligation.
  intros Σ P Γ Pip l g h P_pfh P_pf wfg wfl.
  apply MyGoal_add_indifferent.
  { apply prop_indif. }
  { apply mpp_proof_property. }
  { apply mnpp_proof_property. }
Qed.

Print MyGoal_add_indifferent_S.


Tactic Notation "mgAdd" constr(n) :=
  match goal with
  | |- @of_MyGoal ?Sgm (@mkMyGoal ?Sgm ?Ctx ?l ?g) =>
    apply (@MyGoal_add Sgm Ctx l g _ n)
  end.

Section FOL_helpers.
  
  Context {Σ : Signature}.
  
  Local Example ex_mgAdd Γ l g h:
    wf l ->
    well_formed g ->
    well_formed h ->
    Γ ⊢ (h ---> g) ->
    Γ ⊢ h ->
    Γ ⊢ g.
  Proof.
    intros WFl WFg WFh H H0. toMyGoal.
    { auto. }
    mgAdd H0.
    mgAdd H.
    mgApply 0. mgExactn 1.
  Defined.


  Lemma prf_clear_hyp Γ l1 l2 g h:
    wf l1 ->
    wf l2 ->
    well_formed g ->
    well_formed h ->
    Γ ⊢ (foldr patt_imp g (l1 ++ l2)) ---> (foldr patt_imp g (l1 ++ [h] ++ l2)).
  Proof.
    intros wfl1 wfl2 wfg wfh.
    induction l1; simpl.
    - apply P1; auto.
    - unfold wf in wfl1. simpl in wfl1. apply andb_prop in wfl1. destruct wfl1 as [wfa wfl1].
      specialize (IHl1 wfl1).

      assert (H1: Γ ⊢ a ---> foldr patt_imp g (l1 ++ l2) ---> foldr patt_imp g (l1 ++ [h] ++ l2)).
      {
        toMyGoal.
        { auto 10. }
        mgAdd IHl1.
        mgIntro. mgExactn 0.
      }
      apply prf_impl_distr_meta; auto.
  Defined.

(*
  Lemma helper (P : proofbpred) Γ ϕ₁ ϕ₂ (pf1: Γ ⊢ ϕ₁) (pf2 : Γ ⊢ ϕ₂) (e : pf1 = pf2):
    pf1 -> pf2.*)


  (*
  About MyGoal_add_indifferent.
  Arguments MyGoal_add_indifferent _ _ _ & _ _ _ _ _ _ _ _ _ _.
  *)
  Lemma prf_clear_hyp_indifferent
    P Γ l₁ l₂ g h
    (wfl₁ : wf l₁)
    (wfl₂ : wf l₂)
    (wfg : well_formed g)
    (wfh : well_formed h):
    indifferent_to_prop P ->
    P _ _ (@prf_clear_hyp Γ l₁ l₂ g h wfl₁ wfl₂ wfg wfh) = false.
  Proof.
    intros HP.
    destruct HP as [HP1 [HP2 [HP3 HMP]]].
    induction l₁; simpl.
    - apply HP1.
    - case_match.
      unfold prf_impl_distr_meta.
      rewrite HMP.
      + apply orb_false_intro.
        * Set Printing Implicit.
          Check MyGoal_add_indifferent.
          (*Fail apply (@MyGoal_add_indifferent Σ P Γ).*)
          (*apply (@MyGoal_add_indifferent Σ P Γ []).*)
          
(*
          pose proof (Htmp := @MyGoal_add_indifferent Σ P Γ).
          simpl in Htmp.
          Fail rewrite Htmp.
          About MyGoal_add_indifferent.
*)
          Set Unicoq Debug. Check mnpp_proof_property.
          simpl.
          (*apply: overloaded_lemma.*)

(*          apply: (@mnpp_proof_property Σ P Γ).*)
          apply: (@mnpp_proof_property Σ P Γ []).
(*          apply: (@mpp_proof_property Σ P Γ).*)
(*          apply mnpp_proof_property with (l := []).*)
(*
          rapply (@MyGoal_add_indifferent_r Σ P Γ _).
          rapply MyGoal_add_indifferent_r.
*)
          (*Set Debug "tactic-unification".*)
(*
          apply: MyGoal_add_indifferent_r.
          apply (@MyGoal_add_indifferent Σ P Γ []).
          specialize (Htmp [])
          rewrite Htmp.
      simpl.
  Qed.
*)
Abort.

  Lemma prf_clear_hyp_meta Γ l1 l2 g h:
    wf l1 ->
    wf l2 ->
    well_formed g ->
    well_formed h ->
    Γ ⊢ (foldr patt_imp g (l1 ++ l2)) ->
    Γ ⊢ (foldr patt_imp g (l1 ++ [h] ++ l2)).
  Proof.
    intros. eapply Modus_ponens.
    4: { apply prf_clear_hyp; auto. }
    all: auto 10.
  Defined.  

  Lemma wfapp_proj_1 l₁ l₂:
    wf (l₁ ++ l₂) = true ->
    wf l₁ = true.
  Proof.
    intros H.
    apply (wf_take (length l₁)) in H.
    rewrite take_app in H.
    exact H.
  Qed.

  Lemma wfapp_proj_2 l₁ l₂:
    wf (l₁ ++ l₂) = true ->
    wf l₂ = true.
  Proof.
    intros H.
    apply (wf_drop (length l₁)) in H.
    rewrite drop_app in H.
    exact H.
  Qed.

  Lemma wfl₁hl₂_proj_l₁ l₁ h l₂:
    wf (l₁ ++ h :: l₂) ->
    wf l₁.
  Proof.
    apply wfapp_proj_1.
  Qed.

  Lemma wfl₁hl₂_proj_h l₁ h l₂:
    wf (l₁ ++ h :: l₂) ->
    well_formed h.
  Proof.
    intros H. apply wfapp_proj_2 in H. unfold wf in H.
    simpl in H. apply andb_prop in H as [H1 H2].
    exact H1.
  Qed.

  Lemma wfl₁hl₂_proj_l₂ l₁ h l₂:
    wf (l₁ ++ h :: l₂) ->
    wf l₂.
  Proof.
    intros H. apply wfapp_proj_2 in H. unfold wf in H.
    simpl in H. apply andb_prop in H as [H1 H2].
    exact H2.
  Qed.

  Lemma wfl₁hl₂_proj_l₁l₂ l₁ h l₂:
    wf (l₁ ++ h :: l₂) ->
    wf (l₁ ++ l₂).
  Proof.
    intros H.
    pose proof (wfl₁hl₂_proj_l₁ H).
    pose proof (wfl₁hl₂_proj_l₂ H).
    apply wf_app; assumption.
  Qed.

  Lemma myGoal_clear_hyp Γ l1 l2 g h:
    @mkMyGoal Σ Γ (l1 ++ l2) g ->
    @mkMyGoal Σ Γ (l1 ++ h::l2) g.
  Proof.
    intros H1.
    unfold of_MyGoal in *. simpl in *. intros wfg wfl1hl2.
    apply prf_clear_hyp_meta.
    5: apply H1. all: try assumption.
    { apply wfl₁hl₂_proj_l₁ in wfl1hl2. exact wfl1hl2. }
    { apply wfl₁hl₂_proj_l₂ in wfl1hl2. exact wfl1hl2. }
    { apply wfl₁hl₂_proj_h in wfl1hl2. exact wfl1hl2. }
    { apply wfl₁hl₂_proj_l₁l₂ in wfl1hl2. exact wfl1hl2. }
  Defined.

  
End FOL_helpers.


Tactic Notation "mgClear" constr(n) :=
  match goal with
  | |- @of_MyGoal ?Sgm (@mkMyGoal ?Sgm ?Ctx ?l ?g) =>
    let l1 := fresh "l1" in
    let l2 := fresh "l2" in
    let Heql1 := fresh "Heql1" in
    let Heql2 := fresh "Heql2" in
    eapply cast_proof_mg_hyps;
    [(
      rewrite -[l](take_drop n); reflexivity)|];
    remember (take n l) as l1 eqn:Heql1;
    remember (drop n l) as l2 eqn:Heql2;
    simpl in Heql1; simpl in Heql2;
    let a := fresh "a" in
    destruct l2 as [|a l2];[congruence|];
    inversion Heql2; subst l1 a l2; clear Heql2;
    apply myGoal_clear_hyp;rewrite {1}[_ ++ _]/=
  end.

Local Example ex_mgClear {Σ : Signature} Γ a b c:
  well_formed a ->
  well_formed b ->
  well_formed c ->
  Γ ⊢ a ---> (b ---> (c ---> b)).
Proof.
  intros wfa wfb wfc.
  toMyGoal.
  { auto. }
  repeat mgIntro.
  mgClear 2.
  mgClear 0.
  mgExactn 0.
Qed.

Section FOL_helpers.
  
  Context {Σ : Signature}.
  
  Lemma not_concl Γ p q:
    well_formed p ->
    well_formed q ->
    Γ ⊢ (p ---> (q ---> ((p ---> ! q) ---> ⊥))).
  Proof.
    intros wfp wfq.
    rewrite -> tofold. repeat rewrite consume.
    replace ((([] ++ [p]) ++ [q]) ++ [p ---> ! q]) with ([p;q;p--->!q]) by reflexivity.
    replace ([p;q;p--->!q]) with ([p] ++ [q; p ---> !q] ++ []) by reflexivity.
    apply prf_reorder_iter_meta; auto.
    simpl.
    fold (! q).
    apply modus_ponens; auto.
  Defined.

  Lemma helper Γ p q r:
    well_formed p ->
    well_formed q ->
    well_formed r ->
    Γ ⊢ (p ---> (q ---> ((p ---> (q ---> r)) ---> r))).
  Proof.
    intros wfp wfq wfr.
    rewrite -> tofold. repeat rewrite consume.
    replace ((([] ++ [p]) ++ [q]) ++ [p ---> (q ---> r)]) with ([p;q;p--->(q ---> r)]) by reflexivity.
    replace ([p;q;p--->(q ---> r)]) with ([p] ++ [q; p ---> (q ---> r)] ++ []) by reflexivity.
    apply prf_reorder_iter_meta; auto.
    simpl.
    apply modus_ponens; auto.
  Defined.

  Lemma reorder_last_to_head Γ g x l:
    wf l ->
    well_formed g ->
    well_formed x ->
    Γ ⊢ ((foldr patt_imp g (x::l)) ---> (foldr patt_imp g (l ++ [x]))).
  Proof.
    intros wfl wfg wfx.
    induction l.
    - simpl. auto.
    - pose proof (wfal := wfl).
      unfold wf in wfl. simpl in wfl. apply andb_prop in wfl. destruct wfl as [wfa wfl].
      specialize (IHl wfl).
      simpl. simpl in IHl.
      rewrite -> tofold. rewrite !consume.
      eapply prf_weaken_conclusion_iter_meta_meta.
      4: { apply IHl. }
      all: auto 10.
      rewrite consume.
      replace ((([] ++ [x ---> a ---> foldr patt_imp g l]) ++ [a]) ++ [x])
        with ([x ---> a ---> foldr patt_imp g l] ++ [a;x] ++ []) by reflexivity.
      apply prf_reorder_iter_meta; auto 10.
      simpl. auto 10.
  Defined.

  Lemma reorder_last_to_head_meta Γ g x l:
    wf l ->
    well_formed g ->
    well_formed x ->
    Γ ⊢ (foldr patt_imp g (x::l)) ->
    Γ ⊢ (foldr patt_imp g (l ++ [x])).
  Proof.
    intros WFl WFG WFx H.
    eapply Modus_ponens.
    4: apply reorder_last_to_head.
    all: auto 10.
  Defined.
  
  (* Iterated modus ponens.
     For l = [x₁, ..., xₙ], it says that
     Γ ⊢ ((x₁ -> ... -> xₙ -> (x₁ -> ... -> xₙ -> r)) -> r)
  *)
  Lemma modus_ponens_iter Γ l r:
    wf l ->
    well_formed r ->
    Γ ⊢ (foldr patt_imp r (l ++ [foldr patt_imp r l])).
  Proof.
    intros wfl wfr.
    induction l.
    - simpl. auto.
    - pose proof (wfal := wfl).
      unfold wf in wfl. simpl in wfl. apply andb_prop in wfl. destruct wfl as [wfa wfl].
      specialize (IHl wfl).
      simpl. rewrite foldr_app. simpl. rewrite consume. simpl.
      rewrite foldr_app in IHl. simpl in IHl.
      eapply prf_weaken_conclusion_meta_meta.
      4: { apply reorder_last_to_head; auto. }
      all: auto 10.
      simpl. apply modus_ponens; auto.
  Defined.
  

  
  Lemma and_impl Γ p q r:
    well_formed p ->
    well_formed q ->
    well_formed r ->
    Γ ⊢ ((p and q ---> r) ---> (p ---> (q ---> r))).
  Proof.
    intros wfp wfq wfr.
    toMyGoal.
    { auto 10. }
    repeat mgIntro.
    unfold patt_and. mgApply 0.
    mgIntro. unfold patt_or at 2.
    mgAssert ((! ! p)).
    { auto. }
    {
      mgAdd (@not_not_intro Σ Γ p wfp).
      mgApply 0.
      mgExactn 2.
    }
    mgAssert ((! q)).
    { auto. }
    {
      mgApply 3. mgExactn 4.
    }
    mgApply 5. mgExactn 2.
  Defined.

  
  Lemma and_impl' Γ p q r:
    well_formed p ->
    well_formed q ->
    well_formed r ->
    Γ ⊢ ((p ---> (q ---> r)) ---> ((p and q) ---> r)).
  Proof.
    intros wfp wfq wfr.
    toMyGoal.
    { auto 10. }
    repeat mgIntro.
    mgAssert (p).
    { auto. }
    {
      mgAdd (@pf_conj_elim_l Σ Γ p q wfp wfq).
      mgApply 0.
      mgExactn 2.
    }
    mgAssert (q).
    { auto. }
    {
      mgAdd (@pf_conj_elim_r Σ Γ p q wfp wfq).
      mgApply 0.
      mgExactn 2.
    }
    (* This pattern is basically an "apply ... in" *)
    mgAssert ((q ---> r)).
    { auto. }
    { mgApply 0. mgExactn 2. }
    mgApply 4. mgExactn 3.
  Defined.
  

  Lemma prf_disj_elim_iter Γ l p q r:
    wf l ->
    well_formed p ->
    well_formed q ->
    well_formed r ->
    Γ ⊢ ((fold_right patt_imp r (l ++ [p]))
           --->
           ((fold_right patt_imp r (l ++ [q]))
              --->                                                                
              (fold_right patt_imp r (l ++ [p or q])))).
            
  Proof.
    intros wfl wfp wfq wfr.
    induction l.
    - simpl. apply prf_disj_elim; auto.
    - pose proof (wfal := wfl).
      unfold wf in wfl. simpl in wfl. apply andb_prop in wfl. destruct wfl as [wfa wfl].
      specialize (IHl wfl).
      simpl in *.
      toMyGoal.
      { auto 10. }
      repeat mgIntro.
      mgAdd IHl.
      mgAssert ((foldr patt_imp r (l ++ [p]))).
      { auto 10. }
      { mgApply 1. mgExactn 3. }
      mgAssert ((foldr patt_imp r (l ++ [q]))).
      { auto. }
      { mgApply 2. mgExactn 3. }
      mgAssert ((foldr patt_imp r (l ++ [q]) ---> foldr patt_imp r (l ++ [p or q]))).
      { auto 10. }
      { mgApply 0. mgExactn 4. }
      mgApply 6.
      mgExactn 5.
  Defined.

  
  Lemma prf_disj_elim_iter_2 Γ l₁ l₂ p q r:
    wf l₁ ->
    wf l₂ ->
    well_formed p ->
    well_formed q ->
    well_formed r ->
    Γ ⊢ ((fold_right patt_imp r (l₁ ++ [p] ++ l₂))
           --->
           ((fold_right patt_imp r (l₁ ++ [q] ++ l₂))
              --->                                                                
              (fold_right patt_imp r (l₁ ++ [p or q] ++ l₂)))).
            
  Proof.
    intros wfl₁ wfl₂ wfp wfq wfr.
    move: l₁ wfl₁.
    induction l₂; intros l₁ wfl₁.
    - simpl. apply prf_disj_elim_iter; auto.
    - pose proof (wfal₂ := wfl₂).
      unfold wf in wfl₂. simpl in wfl₂. apply andb_prop in wfl₂. destruct wfl₂ as [wfa wfl₂].

      simpl. (* We need to move 'a' to the beginning of l₁; then we can apply IHl₂. *)
      (* Or we can swap p and a (move a to the end of l_1) *)
      remember (foldr patt_imp r (l₁ ++ p :: a :: l₂)) as A.
      remember (foldr patt_imp r (l₁ ++ q :: a :: l₂)) as B.
      remember (foldr patt_imp r (l₁ ++ (p or q) :: a :: l₂)) as C.
      rewrite -> tofold. rewrite consume. rewrite consume. rewrite [_ ++ [B]]/=.
      subst.
      eapply prf_weaken_conclusion_iter_meta_meta.
      4: {
        replace (l₁ ++ (p or q) :: a :: l₂) with (l₁ ++ [p or q; a] ++ l₂) by reflexivity.
        apply prf_reorder_iter; auto.
      }
      all: auto 10.
      simpl.
      rewrite -> tofold. repeat rewrite consume. rewrite [_ ++ [_]]/=.
      


      replace
        ([foldr patt_imp r (l₁ ++ p :: a :: l₂); foldr patt_imp r (l₁ ++ q :: a :: l₂)])
        with
          ([foldr patt_imp r (l₁ ++ p :: a :: l₂)] ++ (foldr patt_imp r (l₁ ++ q :: a :: l₂))::[])
        by reflexivity.

      eapply prf_strenghten_premise_iter_meta_meta with (h := foldr patt_imp r (l₁ ++ a :: q :: l₂)).
      6: { apply prf_reorder_iter; auto. }
      all: auto 10.

      replace
        ([foldr patt_imp r (l₁ ++ p :: a :: l₂)] ++ [foldr patt_imp r (l₁ ++ a :: q :: l₂)])
        with
          ([] ++ ((foldr patt_imp r (l₁ ++ p :: a :: l₂))::[foldr patt_imp r (l₁ ++ a :: q :: l₂)]))
        by reflexivity.

      eapply prf_strenghten_premise_iter_meta_meta with (h := (foldr patt_imp r (l₁ ++ a :: p :: l₂))).
      6: {  apply prf_reorder_iter; auto. }
      all: auto 10.

      simpl.
      replace (l₁ ++ a :: p :: l₂) with ((l₁ ++ [a]) ++ [p] ++ l₂) by (rewrite <- app_assoc; reflexivity).
      replace (l₁ ++ a :: q :: l₂) with ((l₁ ++ [a]) ++ [q] ++ l₂) by (rewrite <- app_assoc; reflexivity).
      replace (l₁ ++ a :: (p or q) :: l₂) with ((l₁ ++ [a]) ++ [p or q] ++ l₂) by (rewrite <- app_assoc; reflexivity).
      apply IHl₂; auto.
Defined.

  Lemma prf_disj_elim_iter_2_meta Γ l₁ l₂ p q r:
    wf l₁ ->
    wf l₂ ->
    well_formed p ->
    well_formed q ->
    well_formed r ->
    Γ ⊢ (fold_right patt_imp r (l₁ ++ [p] ++ l₂)) ->
    Γ ⊢ ((fold_right patt_imp r (l₁ ++ [q] ++ l₂))
              --->                                                                
              (fold_right patt_imp r (l₁ ++ [p or q] ++ l₂))).
            
  Proof.
    intros WFl1 WFl2 WFp WFq WFr H.
    eapply Modus_ponens.
    4: { apply prf_disj_elim_iter_2; auto. }
    all: auto 10.
  Defined.
  
  Lemma prf_disj_elim_iter_2_meta_meta Γ l₁ l₂ p q r:
    wf l₁ ->
    wf l₂ ->
    well_formed p ->
    well_formed q ->
    well_formed r ->
    Γ ⊢ (fold_right patt_imp r (l₁ ++ [p] ++ l₂)) ->
    Γ ⊢ (fold_right patt_imp r (l₁ ++ [q] ++ l₂)) ->
    Γ ⊢ (fold_right patt_imp r (l₁ ++ [p or q] ++ l₂)).
  Proof.
    intros WFl1 WFl2 WFp WFq WFr H H0.
    eapply Modus_ponens.
    4: { apply prf_disj_elim_iter_2_meta; auto. }
    all: auto 10.
  Defined.

  Lemma MyGoal_disj_elim Γ l₁ l₂ p q r:
    @mkMyGoal Σ Γ (l₁ ++ [p] ++ l₂) r ->
    @mkMyGoal Σ Γ (l₁ ++ [q] ++ l₂) r ->
    @mkMyGoal Σ Γ (l₁ ++ [p or q] ++ l₂) r.
  Proof.
    intros H1 H2.
    unfold of_MyGoal in *. simpl in *.
    intros wfr Hwf.
    apply prf_disj_elim_iter_2_meta_meta.
    7: apply H2.
    6: apply H1.
    all: try assumption.
    { abstract (apply wfl₁hl₂_proj_l₁ in Hwf; exact Hwf). }
    { abstract (apply wfl₁hl₂_proj_l₂ in Hwf; exact Hwf). }
    { abstract (apply wfl₁hl₂_proj_h in Hwf; wf_auto2). }
    { abstract (apply wfl₁hl₂_proj_h in Hwf; wf_auto2). }
    { abstract (
        pose proof (wfl₁hl₂_proj_l₁ Hwf);
        pose proof (wfl₁hl₂_proj_h Hwf);
        pose proof (wfl₁hl₂_proj_l₂ Hwf);
        apply wf_app; [assumption|];
        unfold patt_or,patt_not in *;
        wf_auto2
      ).
    }
    { abstract (
        pose proof (wfl₁hl₂_proj_l₁ Hwf);
        pose proof (wfl₁hl₂_proj_h Hwf);
        pose proof (wfl₁hl₂_proj_l₂ Hwf);
        apply wf_app; [assumption|];
        unfold patt_or,patt_not in *;
        wf_auto2
      ).
    }
  Defined.

End FOL_helpers.

Check @MyGoal_disj_elim.

Lemma MyGoal_disj_elim_indifferent {Σ : Signature}
      P Γ l₁ l₂ p q r pf₁ pf₂:
  indifferent_to_prop P ->
  (forall wf3 wf4, P _ _ (pf₁ wf3 wf4) = false) ->
  (forall wf3 wf4, P _ _ (pf₂ wf3 wf4) = false) ->
  (forall wf1 wf2, P _ _ (@MyGoal_disj_elim Σ Γ l₁ l₂ p q r pf₁ pf₂ wf1 wf2) = false).
Proof.
  intros H
Qed.


Tactic Notation "mgDestructOr" constr(n) :=
  match goal with
  | |- @of_MyGoal ?Sgm (@mkMyGoal ?Sgm ?Ctx ?l ?g) =>
    let Htd := fresh "Htd" in
    eapply cast_proof_mg_hyps;
    [(
      epose proof (Htd :=take_drop);
      specialize (Htd n l);
      rewrite [take _ _]/= in Htd;
      rewrite [drop _ _]/= in Htd;
      rewrite -Htd; clear Htd;
      epose proof (Htd :=take_drop);
      specialize (Htd 1 (drop n l));
      rewrite [take _ _]/= in Htd;
      rewrite ![drop _ _]/= in Htd;
      rewrite -Htd; clear Htd; reflexivity
      )|];
    apply MyGoal_disj_elim; simpl
  end.

Section FOL_helpers.

  Context {Σ : Signature}.
  
  Local Example exd Γ a b p q c:
    well_formed a ->
    well_formed b ->
    well_formed p ->
    well_formed q ->
    well_formed c ->
    Γ ⊢ (a ---> p ---> b ---> c) ->
    Γ ⊢ (a ---> q ---> b ---> c) ->
    Γ ⊢ (a ---> (p or q) ---> b ---> c).
  Proof.
    intros WFa WFb WFp WFq WFc H H0.
    toMyGoal.
    { wf_auto2. } 
    repeat mgIntro.
    mgDestructOr 1.
  Abort.
  
  
  Lemma conclusion_anyway_meta Γ A B:
    well_formed A ->
    well_formed B ->
    Γ ⊢ (A ---> B) ->
    Γ ⊢ (! A ---> B) ->
    Γ ⊢ B.
  Proof.
    intros wfA wfB AimpB nAimpB.
    assert (H1: Γ ⊢ (B ---> ! ! B)) by auto.
    assert (H2: Γ ⊢ (! A ---> ! ! B)).
    { eapply syllogism_intro. 5: apply H1. all: auto. }
    clear H1.
    assert (H3: Γ ⊢ (! B ---> ! A)) by auto.
    epose proof (H4 := @P4m_neg Σ Γ (!B) A _ _).
    assert (H5: Γ ⊢ ((! B ---> ! A) ---> ! ! B)).
    { eapply Modus_ponens. 4: apply H4. all: auto 10. }
    assert (H6: Γ ⊢ (! ! B)).
    { eapply Modus_ponens. 4: apply H5. all: auto. }
    auto.
    Unshelve. all: auto.
  Defined.
    
  Lemma pf_or_elim Γ A B C :
    well_formed A ->
    well_formed B ->
    well_formed C ->
    Γ ⊢ A ---> C ->
    Γ ⊢ B ---> C ->
    Γ ⊢ A or B ->
    Γ ⊢ C.
  Proof.
    intros wfA wfB wfC AimpC BimpC AorB.
    unfold patt_or.
    assert (H1: Γ ⊢ ((! A ---> B) ---> (B ---> C) ---> (! A ---> C))).
    { eapply syllogism; auto. }
    apply reorder_meta in H1; auto.
    assert (H2: Γ ⊢ ((! A ---> B) ---> (! A ---> C))).
    { eapply Modus_ponens. 4: apply H1. all: auto 10. }
    unfold patt_or in AorB.
    assert (H3: Γ ⊢ (! A ---> C)).
    { eapply Modus_ponens. 4: apply H2. all: auto. }
    eapply conclusion_anyway_meta. 4: apply H3. all: auto.
  Defined.
  
  Lemma pf_iff_split Γ A B:
    well_formed A ->
    well_formed B ->
    Γ ⊢ A ---> B ->
    Γ ⊢ B ---> A ->
    Γ ⊢ A <---> B.
  Proof.
    intros wfA wfB AimplB BimplA.
    unfold patt_iff.
    apply conj_intro_meta; auto.
  Defined.

  Lemma pf_iff_split_indifferent
        P Γ A B
        (wfA : well_formed A)
        (wfB : well_formed B)
        (AimpB : Γ ⊢ A ---> B)
        (BimpA : Γ ⊢ B ---> A):
    indifferent_to_prop P ->
    P _ _ AimpB = false ->
    P _ _ BimpA = false ->
    P _ _ (@pf_iff_split Γ A B wfA wfB AimpB BimpA) = false.
  Proof.
    intros [Hp1 [Hp2 [Hp3 Hp4]]] H1 H2.
    unfold pf_iff_split. unfold conj_intro_meta. rewrite Hp4. rewrite H2. simpl.
    rewrite Hp4. rewrite H1. simpl.
    unfold conj_intro.
    rewrite !(Hp1,Hp2,Hp3,Hp4).
    reflexivity.
  Qed.

  
  Lemma pf_iff_proj1 Γ A B:
    well_formed A ->
    well_formed B ->
    Γ ⊢ A <---> B ->
    Γ ⊢ A ---> B.
  Proof.
    intros WFA WFB H. unfold patt_iff in H.
    apply pf_conj_elim_l_meta in H; auto.
  Defined.

  (* TODO: use indifference proofs for subproofs *)
  Lemma pf_iff_proj1_indifferent
        P Γ A B
        (wfA : well_formed A)
        (wfB : well_formed B)
        (AiffB : Γ ⊢ A <---> B):
    indifferent_to_prop P ->
    P _ _ AiffB = false ->
    P _ _ (@pf_iff_proj1 Γ A B wfA wfB AiffB) = false.
  Proof.
    intros [Hp1 [Hp2 [Hp3 Hmp]]] H.
    unfold pf_iff_proj1. unfold pf_conj_elim_l_meta.
    rewrite Hmp. rewrite H. simpl.
    unfold pf_conj_elim_l.
    rewrite !(Hp1,Hp2,Hp3,Hmp).
    reflexivity.
  Qed.

  Lemma pf_iff_proj2 Γ A B:
    well_formed A ->
    well_formed B ->
    Γ ⊢ (A <---> B) ->
    Γ ⊢ (B ---> A).
  Proof.
    intros WFA WFB H. unfold patt_iff in H.
    apply pf_conj_elim_r_meta in H; auto.
  Defined.

  (* TODO: use indifference proofs for subproofs *)
  Lemma pf_iff_proj2_indifferent
        P Γ A B
        (wfA : well_formed A)
        (wfB : well_formed B)
        (AiffB : Γ ⊢ A <---> B):
    indifferent_to_prop P ->
    P _ _ AiffB = false ->
    P _ _ (@pf_iff_proj2 Γ A B wfA wfB AiffB) = false.
  Proof.
    intros [Hp1 [Hp2 [Hp3 Hmp]]] H.
    unfold pf_iff_proj2. unfold pf_conj_elim_r_meta.
    rewrite Hmp. rewrite H. simpl.
    unfold pf_conj_elim_r.
    rewrite !(Hp1,Hp2,Hp3,Hmp).
    reflexivity.
  Qed.


  Lemma pf_iff_iff Γ A B:
    well_formed A ->
    well_formed B ->
    prod ((Γ ⊢ (A <---> B)) -> (prod (Γ ⊢ (A ---> B)) (Γ ⊢ (B ---> A))))
    ( (prod (Γ ⊢ (A ---> B))  (Γ ⊢ (B ---> A))) -> (Γ ⊢ (A <---> B))).
  Proof.
    intros WFA WFB. firstorder using pf_iff_proj1,pf_iff_proj2,pf_iff_split.
  Defined.

  Lemma pf_iff_equiv_refl Γ A :
    well_formed A ->
    Γ ⊢ (A <---> A).
  Proof.
    intros WFA.
    apply pf_iff_split; auto.
  Defined.

  Lemma pf_iff_equiv_sym Γ A B :
    well_formed A ->
    well_formed B ->
    Γ ⊢ (A <---> B) ->
    Γ ⊢ (B <---> A).
  Proof.
    intros wfA wfB H.
    pose proof (H2 := H).
    apply pf_iff_proj2 in H2; auto.
    rename H into H1.
    apply pf_iff_proj1 in H1; auto.
    apply pf_iff_split; auto.
  Defined.

  Lemma pf_iff_equiv_trans Γ A B C :
    well_formed A ->
    well_formed B ->
    well_formed C ->
    Γ ⊢ (A <---> B) ->
    Γ ⊢ (B <---> C) ->
    Γ ⊢ (A <---> C).
  Proof.
    intros wfA wfB wfC AeqB BeqC.
    apply pf_iff_iff in AeqB; auto. destruct AeqB as [AimpB BimpA].
    apply pf_iff_iff in BeqC; auto. destruct BeqC as [BimpC CimpB].
    apply pf_iff_iff; auto.
    split; eauto.
  Defined.

  Lemma pf_iff_equiv_trans_indifferent
        P Γ A B C
        (wfA : well_formed A)
        (wfB : well_formed B)
        (wfC : well_formed C)
        (AiffB : Γ ⊢ A <---> B)
        (BiffC : Γ ⊢ B <---> C):
    indifferent_to_prop P ->
    P _ _ AiffB = false ->
    P _ _ BiffC = false ->
    P _ _ (@pf_iff_equiv_trans Γ A B C wfA wfB wfC AiffB BiffC) = false.
  Proof.
    intros Hp H1 H2. unfold pf_iff_equiv_trans. simpl.
    pose proof (Hp' := Hp). unfold indifferent_to_prop in Hp'.
    destruct Hp' as [Hp1 [Hp2 [Hp3 Hp4]]].
    rewrite pf_iff_split_indifferent; auto;
      rewrite syllogism_intro_indifferent; auto; try apply A_impl_A_indifferent; auto;
      rewrite syllogism_intro_indifferent; auto.
    + apply pf_iff_proj1_indifferent; auto.
    + apply pf_iff_proj1_indifferent; auto.
    + apply pf_iff_proj2_indifferent; auto.
    + apply pf_iff_proj2_indifferent; auto.
  Qed.


  Lemma prf_conclusion Γ a b:
    well_formed a ->
    well_formed b ->
    Γ ⊢ b ->
    Γ ⊢ (a ---> b).
  Proof.
    intros WFa WFb H. eapply Modus_ponens. 4: apply P1. all: auto.
  Defined.
    
  Lemma prf_prop_bott_iff Γ AC:
    Γ ⊢ ((subst_ctx AC patt_bott) <---> patt_bott).
  Proof.
    induction AC; simpl.
    - apply pf_iff_equiv_refl; auto.
    - apply pf_iff_iff in IHAC; auto.
      destruct IHAC as [IH1 IH2].
      apply pf_iff_split; auto.
      + pose proof (H := IH1).
        eapply Framing_left in H.
        eassert (Γ ⊢ (⊥ $ ?[psi] ---> ⊥)).
        { apply Prop_bott_left. shelve. }
        eapply syllogism_intro. 5: apply H0. 4: apply H. 1,2,3,4: auto.
      + apply bot_elim; auto.
    - apply pf_iff_iff in IHAC; auto.
      destruct IHAC as [IH1 IH2].
      apply pf_iff_split; auto.
      + pose proof (H := IH1).
        eapply Framing_right in H.
        eassert (Γ ⊢ ( ?[psi] $ ⊥ ---> ⊥)).
        { apply Prop_bott_right. shelve. }
        eapply syllogism_intro. 5: apply H0. 4: apply H. 1,2,3,4: auto.
      + apply bot_elim; auto.
        Unshelve. all: auto.
  Defined.
  
  Lemma prf_prop_or_iff Γ AC p q:
    well_formed p ->
    well_formed q ->
    Γ ⊢ ((subst_ctx AC (p or q)) <---> ((subst_ctx AC p) or (subst_ctx AC q))).
  Proof.
    intros wfp wfq.
    induction AC; simpl.
    - apply pf_iff_equiv_refl; auto.
    - apply pf_iff_iff in IHAC; auto.
      destruct IHAC as [IH1 IH2].
      apply pf_iff_split; auto.
      + pose proof (H := IH1).
        eapply Framing_left in H.
        eapply syllogism_intro. 4: apply H.
        all:auto.
        remember (subst_ctx AC p) as p'.
        remember (subst_ctx AC q) as q'.
        apply Prop_disj_left. all: subst; auto.
      + eapply prf_disj_elim_meta_meta; auto.
        * apply Framing_left; auto.
          eapply prf_weaken_conclusion_meta_meta. 4: apply IH2. all: auto.
        * apply Framing_left; auto.
          eapply prf_weaken_conclusion_meta_meta. 4: apply IH2. all: auto.
    - apply pf_iff_iff in IHAC; auto.
      destruct IHAC as [IH1 IH2].
      apply pf_iff_split; auto.
      + pose proof (H := IH1).
        eapply Framing_right in H.
        eapply syllogism_intro. 4: apply H.
        all:auto.
        remember (subst_ctx AC p) as p'.
        remember (subst_ctx AC q) as q'.
        apply Prop_disj_right. all: subst; auto.
      + eapply prf_disj_elim_meta_meta; auto.
        * apply Framing_right; auto.
          eapply prf_weaken_conclusion_meta_meta. 4: apply IH2. all: auto.
        * apply Framing_right; auto.
          eapply prf_weaken_conclusion_meta_meta. 4: apply IH2. all: auto.
  Defined.

  Lemma prf_prop_ex_iff Γ AC p x:
    evar_is_fresh_in x (subst_ctx AC p) ->
    well_formed (patt_exists p) = true ->
    Γ ⊢ ((subst_ctx AC (patt_exists p)) <---> (exists_quantify x (subst_ctx AC (evar_open 0 x p)))).
  Proof.
    intros Hx Hwf.

    induction AC; simpl.
    - simpl in Hx.
      unfold exists_quantify.
      erewrite evar_quantify_evar_open by assumption.
      apply pf_iff_equiv_refl; auto.
    -
      assert (Hwfex: well_formed (ex , subst_ctx AC p)).
      { unfold well_formed. simpl.
        pose proof (Hwf' := Hwf).
        unfold well_formed in Hwf. simpl in Hwf.
        apply andb_prop in Hwf. destruct Hwf as [Hwfp Hwfc].
        apply (@wp_sctx _ AC p) in Hwfp. rewrite Hwfp. simpl. clear Hwfp.
        unfold well_formed_closed. unfold well_formed_closed in Hwfc. simpl in Hwfc. simpl.
        split_and!.
        + apply wcmu_sctx. destruct_and!. assumption.
        + apply wcex_sctx. destruct_and!. assumption.
      }

      assert(Hxfr1: evar_is_fresh_in x (subst_ctx AC p)).
      { simpl in Hx.
        eapply evar_is_fresh_in_richer.
        2: { apply Hx. }
        solve_free_evars_inclusion 5.
      }

      simpl in Hx.
      pose proof (Hxfr1' := Hxfr1).
      rewrite -> evar_is_fresh_in_subst_ctx in Hxfr1'.
      destruct Hxfr1' as [Hxfrp HxAC].
      
      assert(Hwf': well_formed (exists_quantify x (subst_ctx AC (evar_open 0 x p)))).
      {
        unfold exists_quantify.
        clear -HxAC Hwf.
        apply wf_ex_eq_sctx_eo.
        apply Hwf.
      }

      (* TODO automate this *)
      assert (Hwfeo: well_formed (evar_open 0 x p)).
      {
        unfold well_formed.
        unfold well_formed,well_formed_closed in Hwf. apply andb_prop in Hwf. simpl in Hwf.
        rewrite wfp_evar_open.
        { apply Hwf. }
        unfold well_formed_closed.
        destruct_and!.
        split_and!; auto.
      }
      
      
      (* TODO automate this. The problem is that [well_formed_app] and others do not have [= true];
         that is why [auto] does not work. But [auto] is not suitable for this anyway.
         A better way would be to create some `simpl_well_formed` tuple, that might use the type class
         mechanism for extension...
       *)
      assert(Hwf'p0: well_formed (exists_quantify x (subst_ctx AC (evar_open 0 x p) $ p0))).
      {
        unfold exists_quantify.
        apply wf_ex_evar_quantify.
        apply well_formed_app.
        2: { apply Prf. }
        auto.
      }
      
      apply pf_iff_iff in IHAC; auto.
           
      destruct IHAC as [IH1 IH2].
      apply pf_iff_split; auto.
      + pose proof (H := IH1).
        eapply Framing_left in IH1.
        eapply syllogism_intro. 4: apply IH1.
        all:auto.
        remember (subst_ctx AC (evar_open 0 x p)) as p'.
        unfold exists_quantify.
        simpl. rewrite [evar_quantify x 0 p0]evar_quantify_fresh.
        { eapply evar_is_fresh_in_app_r. apply Hx. }
        apply Prop_ex_left. all: subst; auto.
      + clear IH1.

        eapply Framing_left in IH2.
        eapply syllogism_intro. 5: eapply IH2. all: auto.

        apply Ex_gen; auto.
        2: {
          unfold exists_quantify.
          simpl.
          rewrite free_evars_evar_quantify.
          unfold evar_is_fresh_in in Hx. simpl in Hx. clear -Hx.
          set_solver.
        }
        
        apply Framing_left; auto.
        unfold evar_open.
        rewrite subst_ctx_bevar_subst.
        unfold exists_quantify. simpl.
        fold (evar_open 0 x (subst_ctx AC p)).
        rewrite -> evar_quantify_evar_open by assumption.
        apply Ex_quan; auto.
    -
      assert (Hwfex: well_formed (ex , subst_ctx AC p)).
      { unfold well_formed. simpl.
        pose proof (Hwf' := Hwf).
        unfold well_formed in Hwf. simpl in Hwf.
        apply andb_prop in Hwf. destruct Hwf as [Hwfp Hwfc].
        apply (@wp_sctx _ AC p) in Hwfp. rewrite Hwfp. simpl. clear Hwfp.
        unfold well_formed_closed. unfold well_formed_closed in Hwfc. simpl in Hwfc. simpl.
        split_and!.
        + apply wcmu_sctx. destruct_and!. assumption.
        + apply wcex_sctx. destruct_and!. assumption.          
      }

      assert(Hxfr1: evar_is_fresh_in x (subst_ctx AC p)).
      { simpl in Hx.
        eapply evar_is_fresh_in_richer.
        2: { apply Hx. }
        solve_free_evars_inclusion 5.
      }

      simpl in Hx.
      pose proof (Hxfr1' := Hxfr1).
      rewrite -> evar_is_fresh_in_subst_ctx in Hxfr1'.
      destruct Hxfr1' as [Hxfrp HxAC].
      
      assert(Hwf': well_formed (exists_quantify x (subst_ctx AC (evar_open 0 x p)))).
      {
        unfold exists_quantify.
        clear -HxAC Hwf.
        apply wf_ex_eq_sctx_eo.
        apply Hwf.
      }

      (* TODO automate this *)
      assert (Hwfeo: well_formed (evar_open 0 x p)).
      {
        unfold well_formed.
        unfold well_formed,well_formed_closed in Hwf. apply andb_prop in Hwf. simpl in Hwf.
        rewrite wfp_evar_open.
        { apply Hwf. }
        unfold well_formed_closed.
        destruct_and!.
        split_and!; auto.
      }
      
      
      (* TODO automate this. The problem is that [well_formed_app] and others do not have [= true];
         that is why [auto] does not work. But [auto] is not suitable for this anyway.
         A better way would be to create some `simpl_well_formed` tuple, that might use the type class
         mechanism for extension...
       *)
      assert(Hwf'p0: well_formed (exists_quantify x (p0 $ subst_ctx AC (evar_open 0 x p)))).
      {
        unfold exists_quantify.
        apply wf_ex_evar_quantify.
        apply well_formed_app; auto.
      }
      
      apply pf_iff_iff in IHAC; auto.
           
      destruct IHAC as [IH1 IH2].
      apply pf_iff_split; auto.
      + pose proof (H := IH1).
        eapply Framing_right in IH1.
        eapply syllogism_intro. 4: apply IH1.
        all:auto.
        remember (subst_ctx AC (evar_open 0 x p)) as p'.
        unfold exists_quantify.
        simpl. rewrite [evar_quantify x 0 p0]evar_quantify_fresh.
        { eapply evar_is_fresh_in_app_l. apply Hx. }
        apply Prop_ex_right. all: subst; auto.
      + clear IH1.

        eapply Framing_right in IH2.
        eapply syllogism_intro. 5: eapply IH2. all: auto.

        apply Ex_gen; auto.
        2: {
          unfold exists_quantify.
          simpl.
          rewrite free_evars_evar_quantify.
          unfold evar_is_fresh_in in Hx. simpl in Hx. clear -Hx.
          set_solver.
        }
        
        apply Framing_right; auto.
        unfold evar_open.
        rewrite subst_ctx_bevar_subst.
        unfold exists_quantify. simpl.
        fold (evar_open 0 x (subst_ctx AC p)).
        erewrite evar_quantify_evar_open by assumption.
        apply Ex_quan; auto.
  Defined.
  


  Lemma and_of_negated_iff_not_impl Γ p1 p2:
    well_formed p1 ->
    well_formed p2 ->
    Γ ⊢ (! (! p1 ---> p2) <---> ! p1 and ! p2).
  Proof.
    intros wfp1 wfp2.
    apply conj_intro_meta; auto 10.
    - toMyGoal.
      { auto 10. }
      mgIntro. mgIntro.
      mgApply 0.
      mgIntro.
      unfold patt_or.
      mgAdd (@not_not_elim Σ Γ p2 ltac:(auto)).
      mgApply 0.
      mgApply 2.
      mgAdd (@not_not_intro Σ Γ (! p1) ltac:(auto)).
      mgApply 0.
      mgExactn 4.
    - toMyGoal.
      { auto 10. }
      mgIntro. mgIntro.
      unfold patt_and.
      mgApply 0.
      unfold patt_or.
      mgIntro.
      mgAdd (@not_not_intro Σ Γ p2 ltac:(auto)).
      mgApply 0.
      mgApply 2.
      mgAdd (@not_not_elim Σ Γ (! p1) ltac:(auto)).
      mgApply 0.
      mgExactn 4.
  Defined.

  Lemma and_impl_2 Γ p1 p2:
    well_formed p1 ->
    well_formed p2 ->
    Γ ⊢ (! (p1 ---> p2) <---> p1 and ! p2).
  Proof.
    intros wfp1 wfp2.
    apply conj_intro_meta; auto.
    - toMyGoal.
      { auto 10. }
      mgIntro. mgIntro.
      mgApply 0.
      mgIntro.
      unfold patt_or.
      mgAdd (@not_not_elim Σ Γ p2 ltac:(auto)).
      mgApply 0.
      mgApply 2.
      mgAdd (@not_not_intro Σ Γ p1 ltac:(auto)).
      mgApply 0.
      mgExactn 4.
    - toMyGoal.
      { auto 10. }
      mgIntro. mgIntro.
      mgApply 0.
      unfold patt_or.
      mgIntro.
      mgAdd (@not_not_intro Σ Γ p2 ltac:(auto)).
      mgApply 0.
      mgApply 2.
      mgAdd (@not_not_elim Σ Γ p1 ltac:(auto)).
      mgApply 0.
      mgExactn 4.
  Defined.

  Lemma conj_intro_meta_partial (Γ : Theory) (A B : Pattern) :
    well_formed A → well_formed B → Γ ⊢ A → Γ ⊢ B ---> (A and B).
  Proof.
    intros WFA WFB H.
    eapply (Modus_ponens _ _ _ _ _).
    - exact H.
    - apply conj_intro; auto.
    Unshelve. all: auto.
  Defined.

  Lemma and_impl_patt (A B C : Pattern) Γ:
    well_formed A → well_formed B → well_formed C →
    Γ ⊢ A -> Γ ⊢ ((A and B) ---> C) -> Γ ⊢ (B ---> C).
  Proof.
    intros WFA WFB WFC H H0.
    eapply syllogism_intro with (B0 := patt_and A B); auto.
    apply conj_intro_meta_partial; auto.
  Defined.

  Lemma conj_intro2 (Γ : Theory) (A B : Pattern) :
    well_formed A -> well_formed B -> Γ ⊢ (A ---> (B ---> (B and A))).
  Proof.
    intros WFA WFB. eapply reorder_meta; auto.
    apply conj_intro; auto.
  Defined.

  Lemma conj_intro_meta_partial2 (Γ : Theory) (A B : Pattern):
    well_formed A → well_formed B → Γ ⊢ A → Γ ⊢ B ---> (B and A).
  Proof.
    intros WFA WFB H.
    eapply (Modus_ponens _ _ _ _ _).
    - exact H.
    - apply conj_intro2; auto.
    Unshelve. all: auto.
  Defined.

  Lemma and_impl_patt2  (A B C : Pattern) Γ:
    well_formed A → well_formed B → well_formed C →
    Γ ⊢ A -> Γ ⊢ ((B and A) ---> C) -> Γ ⊢ (B ---> C).
  Proof.
    intros WFA WFB WFC H H0.
    eapply syllogism_intro with (B0 := patt_and B A); auto.
    pose conj_intro_meta_partial2; auto.
  Defined.

  Lemma patt_and_comm_meta (A B : Pattern) Γ:
    well_formed A → well_formed B
  ->
    Γ ⊢ A and B -> Γ ⊢ B and A.
  Proof.
    intros WFA WFB H.
    apply pf_conj_elim_r_meta in H as P1.
    apply pf_conj_elim_l_meta in H as P2. all: auto.
    apply conj_intro_meta; auto.
  Defined.

  Lemma MyGoal_applyMeta Γ r r':
    Γ ⊢ (r' ---> r) ->
    forall l,
    @mkMyGoal Σ Γ l r' ->
    @mkMyGoal Σ Γ l r.
  Proof.
    intros Himp l H.
    unfold of_MyGoal in *. simpl in *.
    intros wfr wfl.
    eapply prf_weaken_conclusion_iter_meta_meta.
    4: apply Himp.
    4: apply H.
    all: try assumption.
    1,2: pose proof (wfrr' := proved_impl_wf _ _ Himp); wf_auto2.
  Defined.

End FOL_helpers.


Tactic Notation "mgApplyMeta" uconstr(t) :=
  eapply (@MyGoal_applyMeta _ _ _ _ t).

Lemma MyGoal_left {Σ : Signature} Γ l x y:
  @mkMyGoal Σ Γ l x ->
  @mkMyGoal Σ Γ l (patt_or x y).
Proof.
  intros H.
  unfold of_MyGoal in *. simpl in *.
  intros wfxy wfl.
  eapply prf_weaken_conclusion_iter_meta_meta.
  4: apply disj_left_intro.
  6: apply H.
  { assumption. }
  all: abstract (wf_auto2).
Defined.

Lemma MyGoal_right {Σ : Signature} Γ l x y:
  @mkMyGoal Σ Γ l y ->
  @mkMyGoal Σ Γ l (patt_or x y).
Proof.
  intros H.
  unfold of_MyGoal in *. simpl in *.
  intros wfxy wfl.
  eapply prf_weaken_conclusion_iter_meta_meta.
  4: apply disj_right_intro.
  6: apply H.
  { assumption. }
  all: abstract (wf_auto2).
Defined.


Ltac mgLeft := apply MyGoal_left.
Ltac mgRight := apply MyGoal_right.

Example ex_mgLeft {Σ : Signature} Γ a:
  well_formed a ->
  Γ ⊢ a ---> (a or a).
Proof.
  intros wfa.
  toMyGoal.
  { auto. }
  mgIntro.
  mgLeft.
Abort.

Lemma MyGoal_applyMetaIn {Σ : Signature} Γ r r':
  Γ ⊢ (r ---> r') ->
  forall l₁ l₂ g,
    @mkMyGoal Σ Γ (l₁ ++ r'::l₂) g ->
    @mkMyGoal Σ Γ (l₁ ++ r::l₂ ) g.
Proof.
  intros Himp l₁ l₂ g H.
  unfold of_MyGoal in *. simpl in *.
  intros wfg Hwf.
  specialize (H wfg).
  eapply prf_strenghten_premise_iter_meta_meta.
  6: apply Himp.
  6: apply H.
  { abstract (apply wfapp_proj_1 in Hwf; exact Hwf). }
  { abstract (apply wfl₁hl₂_proj_l₂ in Hwf; exact Hwf). }
  { abstract (apply proved_impl_wf in Himp; wf_auto2). }
  { abstract (apply wfl₁hl₂_proj_h in Hwf; exact Hwf). }
  { exact wfg. }
  { abstract(
      pose proof (wfapp_proj_1 Hwf);
      pose proof (wfl₁hl₂_proj_l₂ Hwf);
      pose proof (wfl₁hl₂_proj_h Hwf);
      unfold wf;
      rewrite map_app;
      rewrite foldr_app;
      simpl;
      apply proved_impl_wf in Himp;
      apply well_formed_imp_proj2 in Himp;
      rewrite Himp;
      simpl;
      unfold wf in H1;
      rewrite H1;
      exact H0
    ).
 }
Defined.

Tactic Notation "mgApplyMeta" uconstr(t) "in" constr(n) :=
  eapply cast_proof_mg_hyps;
  [(let hyps := fresh "hyps" in
    rewrite <- (firstn_skipn n);
    rewrite [hyps in (hyps ++ _)]/=;
    rewrite [hyps in (_ ++ hyps)]/=;
    reflexivity
   )|];
  eapply (@MyGoal_applyMetaIn _ _ _ _ t);
  eapply cast_proof_mg_hyps;
  [(rewrite /app; reflexivity)|].

Local Example Private_ex_mgApplyMetaIn {Σ : Signature} Γ p q:
  well_formed p ->
  well_formed q ->
  Γ ⊢ p ---> (p or q).
Proof.
  intros wfp wfq.
  toMyGoal.
  { auto. }
  mgIntro.
  mgApplyMeta (@disj_left_intro Σ Γ p q ltac:(auto) ltac:(auto)) in 0.
  mgExactn 0.
Qed.

Lemma MyGoal_destructAnd {Σ : Signature} Γ g l₁ l₂ x y:
    @mkMyGoal Σ Γ (l₁ ++ x::y::l₂ ) g ->
    @mkMyGoal Σ Γ (l₁ ++ (x and y)::l₂) g .
Proof.
  intros H.
  unfold of_MyGoal. intros wfg Hwf. pose proof (wfg' := wfg). pose proof (Hwf' := Hwf).
  revert wfg' Hwf'.
  cut (of_MyGoal (@mkMyGoal Σ Γ (l₁ ++ (x and y)::l₂ ) g)).
  { auto. }
  simpl in wfg, Hwf.

  mgAssert (y) using first (length (l₁ ++ [x and y])).
  { abstract (
      apply wfapp_proj_2 in Hwf;
      unfold wf in Hwf;
      simpl in Hwf;
      apply andb_prop in Hwf;
      destruct Hwf as [wfxy _];
      wf_auto2
    ).
  }
  {
    replace (l₁ ++ (x and y) :: l₂) with ((l₁++ [x and y]) ++ l₂).
    2: { rewrite -app_assoc. reflexivity. }
    rewrite take_app.
    assert (well_formed x).
    {
      abstract (
        apply wfapp_proj_2 in Hwf;
        unfold wf in Hwf;
        simpl in Hwf;
        apply andb_prop in Hwf as [wfxy _];
        wf_auto2
      ).
    }
    mgApplyMeta (@pf_conj_elim_r Σ Γ x y ltac:(assumption) ltac:(assumption)).
    apply MyGoal_exactn.
  }

  eapply cast_proof_mg_hyps.
  {  
    replace (l₁ ++ (x and y) :: l₂) with ((l₁++ [x and y]) ++ l₂).
    2: { rewrite -app_assoc. reflexivity. }
    rewrite take_app. rewrite drop_app. reflexivity.
  }

  mgAssert (x) using first (length (l₁ ++ [x and y])).
  { abstract (
      apply wfapp_proj_2 in Hwf;
      unfold wf in Hwf;
      simpl in Hwf;
      apply andb_prop in Hwf;
      destruct Hwf as [wfxy _];
      wf_auto2
    ).
  }
  {
    replace (l₁ ++ (x and y) :: l₂) with ((l₁++ [x and y]) ++ l₂).
    2: { rewrite -app_assoc. reflexivity. }
    rewrite take_app.
    assert (well_formed x).
    {
      abstract (
        apply wfapp_proj_2 in Hwf;
        unfold wf in Hwf;
        simpl in Hwf;
        apply andb_prop in Hwf as [wfxy _];
        wf_auto2
      ).
    }
    mgApplyMeta (@pf_conj_elim_l Σ Γ x y ltac:(assumption) ltac:(assumption)).
    apply MyGoal_exactn.
  }

  eapply cast_proof_mg_hyps.
  {  
    replace (l₁ ++ (x and y) :: l₂) with ((l₁++ [x and y]) ++ l₂).
    2: { rewrite -app_assoc. reflexivity. }
    rewrite take_app. rewrite drop_app. reflexivity.
  }

  eapply cast_proof_mg_hyps.
  {
    rewrite -app_assoc. reflexivity.
  }

 apply myGoal_clear_hyp.  
 exact H.
Defined.

Tactic Notation "mgDestructAnd" constr(n) :=
  eapply cast_proof_mg_hyps;
  [(let hyps := fresh "hyps" in
    rewrite <- (firstn_skipn n);
    rewrite [hyps in (hyps ++ _)]/=;
    rewrite [hyps in (_ ++ hyps)]/=;
    reflexivity
   )|];
  apply MyGoal_destructAnd;
  eapply cast_proof_mg_hyps;
  [(rewrite /app; reflexivity)|].

Local Example ex_mgDestructAnd {Σ : Signature} Γ a b p q:
  well_formed a ->
  well_formed b ->
  well_formed p ->
  well_formed q ->
  Γ ⊢ p and q ---> a and b ---> q ---> a.
Proof.
  intros. toMyGoal.
  { auto. }
  do 3 mgIntro.
  mgDestructAnd 1.
  mgDestructAnd 0.
  mgExactn 2.
Qed.

Section FOL_helpers.
  
  Context {Σ : Signature}.
  
  Lemma and_of_equiv_is_equiv Γ p q p' q':
    well_formed p ->
    well_formed q ->
    well_formed p' ->
    well_formed q' ->
    Γ ⊢ (p <---> p') ->
    Γ ⊢ (q <---> q') ->
    Γ ⊢ ((p and q) <---> (p' and q')).
  Proof.
    intros wfp wfq wfp' wfq' pep' qeq'.
    pose proof (pip' := pep'). apply pf_conj_elim_l_meta in pip'; auto.
    pose proof (p'ip := pep'). apply pf_conj_elim_r_meta in p'ip; auto.
    pose proof (qiq' := qeq'). apply pf_conj_elim_l_meta in qiq'; auto.
    pose proof (q'iq := qeq'). apply pf_conj_elim_r_meta in q'iq; auto.
    
    apply conj_intro_meta; auto.
    - toMyGoal.
      { auto. }
      mgIntro. unfold patt_and.
      mgIntro. mgApply 0.
      mgDestructOr 1.
      + apply modus_tollens in pip'; auto 10.
        mgAdd pip'.
        mgLeft.
        mgApply 0.
        mgExactn 2.
      + apply modus_tollens in qiq'; auto 10.
        mgAdd qiq'.
        mgRight.
        mgApply 0.
        mgExactn 2.
    - toMyGoal.
      { auto. }
      mgIntro. unfold patt_and.
      mgIntro. mgApply 0.
      mgDestructOr 1.
      + mgLeft.
        apply modus_tollens in p'ip; auto.
        mgAdd p'ip.
        mgApply 0.
        mgExactn 2.
      + mgRight.
        apply modus_tollens in q'iq; auto.
        mgAdd q'iq.
        mgApply 0.
        mgExactn 2.
  Defined.
  

  Lemma or_of_equiv_is_equiv Γ p q p' q':
    well_formed p ->
    well_formed q ->
    well_formed p' ->
    well_formed q' ->
    Γ ⊢ (p <---> p') ->
    Γ ⊢ (q <---> q') ->
    Γ ⊢ ((p or q) <---> (p' or q')).
  Proof with auto.
    intros wfp wfq wfp' wfq' pep' qeq'.
    pose proof (pip' := pep'). apply pf_conj_elim_l_meta in pip'...
    pose proof (p'ip := pep'). apply pf_conj_elim_r_meta in p'ip...
    pose proof (qiq' := qeq'). apply pf_conj_elim_l_meta in qiq'...
    pose proof (q'iq := qeq'). apply pf_conj_elim_r_meta in q'iq...
    
    apply conj_intro_meta; auto.
    - toMyGoal.
      { auto. }
      mgIntro.
      mgDestructOr 0.
      + mgLeft. fromMyGoal. intros _ _. assumption.
      + mgRight. fromMyGoal. intros _ _. assumption.
    - toMyGoal.
      { auto. }
      mgIntro.
      mgDestructOr 0.
      + mgLeft. fromMyGoal. intros _ _. assumption.
      + mgRight. fromMyGoal. intros _ _. assumption.
  Defined.

End FOL_helpers.


(* TODO this should have a different name, and we should give the name [mgSplit] to a tactic
  that works with our goals *)
(*Ltac mgSplit := apply conj_intro_meta; auto.*)

Section FOL_helpers.

  Context {Σ : Signature}.

  
  Lemma impl_iff_notp_or_q Γ p q:
    well_formed p ->
    well_formed q ->
    Γ ⊢ ((p ---> q) <---> (! p or q)).
  Proof.
    intros wfp wfq.
    apply conj_intro_meta; auto.
    - toMyGoal.
      { wf_auto2. }
      mgIntro.
      mgAdd (@A_or_notA Σ Γ p wfp).
      mgDestructOr 0.
      + mgRight.
        mgApply 1.
        mgExactn 0.
      + mgLeft.
        mgExactn 0.
    - toMyGoal.
      { wf_auto2. }
      mgIntro. mgIntro. unfold patt_or.
      mgApply 0.
      mgApplyMeta (@not_not_intro _ _ p wfp).
      mgExactn 1.
  Defined.

  Lemma p_and_notp_is_bot Γ p:
    well_formed p ->
    Γ ⊢ (⊥ <---> p and ! p).
  Proof.
    intros wfp.
    apply conj_intro_meta; auto.
    - apply bot_elim; auto.
    - unfold patt_and.
      toMyGoal.
      { wf_auto2. }
      mgIntro.
      mgApply 0.
      mgAdd (@A_or_notA Σ Γ (! p) ltac:(auto)).
      mgExactn 0.
  Defined.

  Lemma weird_lemma Γ A B L R:
    well_formed A ->
    well_formed B ->
    well_formed L ->
    well_formed R ->
    Γ ⊢ (((L and A) ---> (B or R)) ---> (L ---> ((A ---> B) or R))).
  Proof.
    intros wfA wfB wfL wfR.
    toMyGoal.
    { wf_auto2. }
    mgIntro. mgIntro.
    mgAdd (@A_or_notA Σ Γ A wfA).
    mgDestructOr 0.
    - mgAssert ((B or R)).
      { wf_auto2. }
      { mgApply 1.
        unfold patt_and at 2.
        mgIntro.
        mgDestructOr 3.
        + mgApply 3. mgExactn 2.
        + mgApply 3. mgExactn 0.
      }
      mgDestructOr 3.
      + mgLeft. mgIntro. mgExactn 3.
      + mgRight. mgExactn 3.
    - mgLeft.
      mgIntro.
      mgApplyMeta (@bot_elim Σ _ B wfB).
      mgApply 0. mgExactn 3.
  Defined.

  Lemma weird_lemma_meta Γ A B L R:
    well_formed A ->
    well_formed B ->
    well_formed L ->
    well_formed R ->
    Γ ⊢ ((L and A) ---> (B or R)) ->
    Γ ⊢ (L ---> ((A ---> B) or R)).
  Proof.
    intros WFA WFB WFL WFR H.
    eapply Modus_ponens.
    4: apply weird_lemma.
    all: auto 10.
  Defined.

(*
  Theorem congruence_iff :
    forall C φ1 φ2 Γ, well_formed φ1 -> well_formed φ2 ->
     Γ ⊢ (φ1 <---> φ2)
    ->
     (* well_formed (subst_patctx C φ1) -> well_formed (subst_patctx C φ2) -> *)
     wf_PatCtx C ->
     Γ ⊢ (subst_patctx C φ1 <---> subst_patctx C φ2).
  Proof.
    induction C; intros φ1 φ2 Γ WF1 WF2 H WFC.
    * apply H.
    * simpl. simpl in WFC. apply andb_true_iff in WFC as [E1 E2].
      specialize (IHC φ1 φ2 Γ).
      apply pf_iff_iff in IHC. all: auto. destruct IHC as [m m0].
      pose proof (Framing_left Γ (subst_patctx C φ1) (subst_patctx C φ2) r m).
      pose proof (Framing_left Γ (subst_patctx C φ2) (subst_patctx C φ1) r m0).
      apply pf_iff_iff; auto.
      all: auto. 1-2: apply well_formed_app; auto.
      all: apply subst_patctx_wf; auto.
    * simpl. simpl in WFC. apply andb_true_iff in WFC as [E1 E2].
      specialize (IHC φ1 φ2 Γ).
      apply pf_iff_iff in IHC. all: auto. destruct IHC as [m m0].
      pose proof (Framing_right Γ (subst_patctx C φ1) (subst_patctx C φ2) l m).
      pose proof (Framing_right Γ (subst_patctx C φ2) (subst_patctx C φ1) l m0).
      apply pf_iff_iff; auto.
      all: auto. 1-2: apply well_formed_app; auto.
      all: apply subst_patctx_wf; auto.
    * simpl. simpl in WFC. apply andb_true_iff in WFC as [E1 E2].
      specialize (IHC φ1 φ2 Γ).
      apply pf_iff_iff in IHC. all: auto. 2-3: now apply subst_patctx_wf.
      destruct IHC as [m m0].
      simpl. remember (subst_patctx C φ1) as A. remember (subst_patctx C φ2) as B.
      apply pf_iff_iff; auto.
      1-2: try rewrite HeqA; try rewrite HeqB; apply well_formed_imp; auto;
           now apply subst_patctx_wf.
      split.
      - epose proof (@syllogism Σ Γ B A r _ _ _).
        epose proof (Modus_ponens Γ (B ---> A) ((A ---> r) ---> B ---> r)
                    ltac:(auto) ltac:(auto) _ _). auto.
      - epose proof (@syllogism Σ Γ A B r _ _ _).
        epose proof (Modus_ponens Γ (A ---> B) ((B ---> r) ---> A ---> r)
                    ltac:(auto) ltac:(auto) _ _). auto.
      Unshelve.
       all: assert (well_formed A) by (rewrite HeqA; now apply subst_patctx_wf).
       all: assert (well_formed B) by (rewrite HeqB; now apply subst_patctx_wf).
       all: auto.
    * simpl. simpl in WFC. apply andb_true_iff in WFC as [E1 E2].
      specialize (IHC φ1 φ2 Γ).
      apply pf_iff_iff in IHC. all: auto. all: auto. 2-3: now apply subst_patctx_wf.
      destruct IHC as [m m0].
      simpl. remember (subst_patctx C φ1) as A. remember (subst_patctx C φ2) as B.
      apply pf_iff_iff; auto.
      1-2: try rewrite HeqA; try rewrite HeqB; apply well_formed_imp; auto;
           now apply subst_patctx_wf.
      split.
      - epose proof (@prf_weaken_conclusion Σ Γ l A B _ _ _).
        epose proof (Modus_ponens Γ (A ---> B) ((l ---> A) ---> l ---> B)
                    ltac:(auto) ltac:(auto) _ _). auto.
      - epose proof (@prf_weaken_conclusion Σ Γ l B A _ _ _).
        epose proof (Modus_ponens Γ (B ---> A) ((l ---> B) ---> l ---> A)
                    ltac:(auto) ltac:(auto) _ _). auto.
      Unshelve.
       all: assert (well_formed A) by (rewrite HeqA; now apply subst_patctx_wf).
       all: assert (well_formed B) by (rewrite HeqB; now apply subst_patctx_wf).
       all: auto.
    * simpl. simpl in WFC.
      specialize (IHC _ _ Γ WF1 WF2 H).
      simpl. unfold exists_quantify.
      pose proof (Ex_quan Γ (evar_quantify x 0 (subst_patctx C φ1)) x).
      pose proof (Ex_quan Γ (evar_quantify x 0 (subst_patctx C φ2)) x).
      unfold instantiate in H0, H1.
      fold (evar_open 0 x (evar_quantify x 0 (subst_patctx C φ1))) in H0.
      fold (evar_open 0 x (evar_quantify x 0 (subst_patctx C φ2))) in H1.
      erewrite -> evar_open_evar_quantify in H0, H1. 2-3: shelve.
      apply pf_iff_proj1 in IHC as IH1. apply pf_iff_proj2 in IHC as IH2.
      all: auto.
      eapply syllogism_intro in H0. 5: exact IH2. all: auto.
      eapply syllogism_intro in H1. 5: exact IH1. all: auto.
      apply (Ex_gen _ _ _ x) in H0. apply (Ex_gen _ _ _ x) in H1.
      all: auto. 2-3: shelve.
      unfold exists_quantify in H0, H1.
      apply pf_iff_iff; auto.
     Unshelve.
     all: try apply evar_quantify_well_formed; auto.
     all: try apply subst_patctx_wf; auto.
     1-2: simpl; apply evar_quantify_not_free.
     + eapply subst_patctx_wf in WFC. 2: exact WF2.
       apply andb_true_iff in WFC as [E1 E2].
       unfold well_formed_closed in *. destruct_and!. assumption.
     + eapply subst_patctx_wf in WFC. 2: exact WF1.
       apply andb_true_iff in WFC as [E1 E2].
       unfold well_formed_closed in *. destruct_and!. assumption.
  Defined.
*)
  Lemma imp_trans_mixed_meta Γ A B C D :
    well_formed A -> well_formed B -> well_formed C -> well_formed D ->
    Γ ⊢ (C ---> A) -> Γ ⊢ (B ---> D)
  ->
    Γ ⊢ ((A ---> B) ---> C ---> D).
  Proof.
    intros WFA WFB WFC WFD H H0.
    epose proof (@prf_weaken_conclusion Σ Γ A B D WFA WFB WFD).
    eapply Modus_ponens in H1; auto.
    epose proof (@prf_strenghten_premise Σ Γ A C D WFA WFC WFD).
    eapply Modus_ponens in H2; auto.
    epose proof (@syllogism_intro Σ Γ _ _ _ _ _ _ H1 H2). auto.
    Unshelve. all: auto.
  Defined.
(*
  Theorem congruence_iff_helper :
    forall sz ψ more, le (Syntax.size ψ) sz ->
     forall φ1 φ2 x Γ (MF : mu_free ψ), well_formed φ1 -> well_formed φ2 ->
     Γ ⊢ (φ1 <---> φ2)
    ->
     well_formed ψ ->
     Γ ⊢ (free_evar_subst' more ψ φ1 x <---> free_evar_subst' more ψ φ2 x).
  Proof.
    unfold free_evar_subst.
    induction sz; destruct ψ; intros more Hsz φ1 φ2 x' Γ MF WF1 WF2 H WFψ.
    6, 8, 9, 10: simpl in Hsz; lia.
    all: try apply pf_iff_equiv_refl; auto.
    1-2: cbn; break_match_goal; auto.
    * rewrite nest_ex_aux_wfc_ex.
      { unfold well_formed, well_formed_closed in WF1.
        destruct_and!. assumption. }
      rewrite nest_ex_aux_wfc_ex.
      { unfold well_formed, well_formed_closed in WF2.
        destruct_and!. assumption. }
      assumption.

    * apply pf_iff_equiv_refl; auto.
    * rewrite nest_ex_aux_wfc_ex.
      { unfold well_formed, well_formed_closed in WF1.
        destruct_and!. assumption. }
      rewrite nest_ex_aux_wfc_ex.
      { unfold well_formed, well_formed_closed in WF2.
        destruct_and!. assumption. }
      assumption.
    * apply pf_iff_equiv_refl; auto.
    * simpl in MF, Hsz.
      apply well_formed_app_1 in WFψ as WF1'.
      apply well_formed_app_2 in WFψ as WF2'.
      apply andb_true_iff in MF as [MF1 MF2].
      specialize (IHsz ψ1 more ltac:(lia) φ1 φ2 x' Γ MF1 WF1 WF2 H WF1') as IHψ1.
      specialize (IHsz ψ2 more ltac:(lia) φ1 φ2 x' Γ MF2 WF1 WF2 H WF2') as IHψ2.
      apply pf_iff_iff in IHψ1. apply pf_iff_iff in IHψ2.
      destruct IHψ1 as [H0 H1], IHψ2 as [H2 H3].
      pose proof (Framing_left Γ (free_evar_subst' more ψ1 φ1 x') (free_evar_subst' more ψ1 φ2 x') (free_evar_subst' more ψ2 φ1 x') H0) as Trans1.
      pose proof (Framing_right Γ (free_evar_subst' more ψ2 φ1 x') (free_evar_subst' more ψ2 φ2 x') (free_evar_subst' more ψ1 φ2 x') H2) as Trans2.
      epose proof (@syllogism_intro Σ Γ _ _ _ _ _ _ Trans1 Trans2).
      clear Trans1 Trans2. 2-5: shelve.

      pose proof (Framing_right Γ (free_evar_subst' more ψ2 φ2 x') (free_evar_subst' more ψ2 φ1 x') (free_evar_subst' more ψ1 φ2 x') H3) as Trans1.
      pose proof (Framing_left Γ _ _ (free_evar_subst' more ψ2 φ1 x') H1) as Trans2.
      epose proof (@syllogism_intro Σ Γ _ _ _ _ _ _ Trans1 Trans2).
      apply pf_iff_iff; auto.
      Unshelve.
      1-3, 8-10: apply well_formed_app.
      all: now apply well_formed_free_evar_subst.
    * simpl in MF, Hsz.
      apply well_formed_app_1 in WFψ as WF1'.
      apply well_formed_app_2 in WFψ as WF2'.
      apply andb_true_iff in MF as [MF1 MF2].
      specialize (IHsz ψ1 more ltac:(lia) φ1 φ2 x' Γ MF1 WF1 WF2 H WF1') as IHψ1.
      specialize (IHsz ψ2 more ltac:(lia) φ1 φ2 x' Γ MF2 WF1 WF2 H WF2') as IHψ2.
      apply pf_iff_iff in IHψ1. apply pf_iff_iff in IHψ2. destruct IHψ1, IHψ2.
      apply pf_iff_iff. 1, 2, 4-7: shelve.
      split.
      - simpl. apply imp_trans_mixed_meta; auto.
      - simpl. apply imp_trans_mixed_meta; auto.
      Unshelve.
      1, 2: apply well_formed_imp.
      all: now apply well_formed_free_evar_subst.
    * simpl in MF, Hsz. apply wf_ex_to_wf_body in WFψ as H3'.
      remember (fresh_evar (ψ $ φ1 $ φ2 $ patt_free_evar x')) as fx.
      unfold fresh_evar in Heqfx. simpl in Heqfx.
      pose (@set_evar_fresh_is_fresh' _ (free_evars ψ ∪ (free_evars φ1 ∪ (free_evars φ2 ∪ {[x']})))).
      rewrite <- Heqfx in n.
      apply sets.not_elem_of_union in n. destruct n as [n1 n2].
      apply sets.not_elem_of_union in n2. destruct n2 as [n2 n3].
      apply sets.not_elem_of_union in n3. destruct n3 as [n3 n4].
      apply sets.not_elem_of_singleton_1 in n4.
      epose proof (H3' fx _).
      cbn.
      epose proof (IHsz (evar_open 0 fx ψ) (S more) _ φ1 φ2 x' Γ _ WF1 WF2 H H0).
      pose proof (Ex_quan Γ (free_evar_subst' (S more) ψ φ1 x') fx) as H2.
      pose proof (Ex_quan Γ (free_evar_subst' (S more) ψ φ2 x') fx) as H3.
      unfold instantiate in *.
      fold (evar_open 0 fx (free_evar_subst ψ φ1 x')) in H2.
      fold (evar_open 0 fx (free_evar_subst ψ φ2 x')) in H3.
      do 2 rewrite <- evar_open_free_evar_subst_swap in H1; auto.
      apply pf_iff_iff in H1; auto. 2-3: shelve. destruct H1 as [IH1 IH2].
      eapply syllogism_intro in H2. 5: exact IH2. 2-4: shelve.
      eapply syllogism_intro in H3. 5: exact IH1. 2-4: shelve.
      apply (Ex_gen _ _ _ fx) in H2. apply (Ex_gen _ _ _ fx) in H3.
      2-7: shelve.
      unfold exists_quantify in H3, H2. simpl in H2, H3.
      erewrite -> evar_quantify_evar_open in H2, H3; auto.
      2-3: shelve.
      apply pf_iff_iff; auto.
      Unshelve.

      all: auto.
      simpl in WFψ.

      all: try replace (ex , free_evar_subst' (S more) ψ φ1 x') with (free_evar_subst' more (ex, ψ) φ1 x') by reflexivity.
      all: try replace (ex , free_evar_subst' (S more) ψ φ2 x') with (free_evar_subst' more (ex, ψ) φ2 x') by reflexivity.
      all: try apply well_formed_free_evar_subst; auto.
      
      { rewrite <- evar_open_size. simpl in H. lia. }
      { now apply mu_free_evar_open. }
      1, 4, 5, 7: eapply well_formed_free_evar_subst with (x := x') (q := φ1) in WFψ as HE1; auto; simpl in HE1; apply wf_ex_to_wf_body in HE1; apply (HE1 fx).
      5-7, 9: eapply well_formed_free_evar_subst with (x := x') (q := φ2) in WFψ as HE1; auto; simpl in HE1; apply wf_ex_to_wf_body in HE1; apply (HE1 fx).
      all: simpl; eapply not_elem_of_larger_impl_not_elem_of.
      all: try apply free_evars_free_evar_subst.
   all: apply sets.not_elem_of_union; auto.
   * inversion MF.
  Defined.
*)
  Lemma and_weaken A B C Γ:
    well_formed A -> well_formed B -> well_formed C ->
    Γ ⊢ (B ---> C)
   ->
    Γ ⊢ ((A and B) ---> (A and C)).
  Proof.
    intros WFA WFB WFC H.
    epose proof (@and_impl' Σ Γ A B (A and C) _ _ _). eapply Modus_ponens. 4: exact H0.
    1-2: shelve.
    apply reorder_meta; auto.
    epose proof (@prf_strenghten_premise Σ Γ C B (A ---> A and C) _ _ _).
    eapply Modus_ponens. 4: eapply Modus_ponens. 7: exact H1. all: auto 10.
    apply conj_intro2.
    Unshelve.
    all: unfold patt_and, patt_or, patt_not; auto 10.
  Defined.

  Lemma impl_and Γ A B C D: 
    well_formed A -> well_formed B -> well_formed C -> well_formed D
   ->
    Γ ⊢ (A ---> B) ->
    Γ ⊢ (C ---> D) ->
    Γ ⊢ (A and C) ---> (B and D).
  Proof.
    intros WFA WFB WFC WFD H H0.
    pose proof (@conj_intro Σ Γ B D WFB WFD).
    epose proof (@prf_strenghten_premise Σ Γ B A (D ---> B and D) WFB WFA _).
    eapply Modus_ponens in H2; auto. 2: shelve.
    eapply Modus_ponens in H2; auto.
    apply reorder_meta in H2; auto.
    epose proof (@prf_strenghten_premise Σ Γ D C (A ---> B and D) WFD WFC _).
    eapply Modus_ponens in H3; auto. 2: shelve.
    eapply Modus_ponens in H3; auto.
    apply reorder_meta in H3; auto.
    epose proof (@and_impl' _ _ _ _ _ _ _ _).
    eapply Modus_ponens in H4. 4: exact H3. all: auto.
    Unshelve.
    all: unfold patt_and, patt_or, patt_not; auto 10.
  Defined.

  Lemma and_drop A B C Γ:
    well_formed A -> well_formed B -> well_formed C ->
    Γ ⊢ ((A and B) ---> C)
   ->
    Γ ⊢ ((A and B) ---> (A and C)).
  Proof.
    intros WFA WFB WFC H.
    pose proof (@pf_conj_elim_l Σ Γ A B WFA WFB).
    epose proof (@impl_and Γ (A and B) A (A and B) C _ _ _ _ H0 H).
    epose proof (@and_impl _ _ _ _ _ _ _ _).
    eapply Modus_ponens in H2. 4: exact H1. 2-3: shelve.
    epose proof (@prf_contraction _ _ _ _ _ _).
    eapply Modus_ponens in H3. 4: exact H2. auto.
    Unshelve. all: unfold patt_and, patt_or, patt_not; auto 20.
  Defined.


  Lemma universal_generalization Γ ϕ x:
    well_formed ϕ ->
    Γ ⊢ ϕ ->
    Γ ⊢ patt_forall (evar_quantify x 0 ϕ).
  Proof.
    intros wfϕ Hϕ.
    unfold patt_forall.
    unfold patt_not at 1.
    replace (! evar_quantify x 0 ϕ)
      with (evar_quantify x 0 (! ϕ))
      by reflexivity.
    apply Ex_gen; auto.
    2: { simpl. set_solver. }
    toMyGoal.
    { wf_auto2. }
    mgIntro. mgAdd Hϕ.
    mgApply 1. mgExactn 0.
  Defined.

  Hint Resolve evar_quantify_well_formed.

  Lemma forall_variable_substitution Γ ϕ x:
    well_formed ϕ ->
    Γ ⊢ (all, evar_quantify x 0 ϕ) ---> ϕ.
  Proof.
    intros wfϕ.
   
    unfold patt_forall.
    replace (! evar_quantify x 0 ϕ)
      with (evar_quantify x 0 (! ϕ))
      by reflexivity.
    apply double_neg_elim_meta; auto 10.
    toMyGoal.
    { wf_auto2. }
    mgIntro.
    mgIntro.
    mgApply 0.
    mgIntro.
    mgApply 2.
    pose proof (Htmp := Ex_quan Γ (evar_quantify x 0 (!ϕ)) x).
    rewrite /instantiate in Htmp.
    rewrite bevar_subst_evar_quantify_free_evar in Htmp.
    {
      apply wfc_ex_implies_not_bevar_occur.
      unfold well_formed,well_formed_closed in wfϕ. destruct_and!. simpl.
      split_and; auto.
    }
    specialize (Htmp ltac:(wf_auto2)).
    mgAdd Htmp.
    mgApply 0.
    mgIntro.
    mgApply 2.
    mgExactn 4.
  Defined.

End FOL_helpers.

  
Section FOL_helpers.

  Context {Σ : Signature}.

  Lemma mu_monotone Γ ϕ₁ ϕ₂ X:
    well_formed ϕ₁ ->
    well_formed ϕ₂ ->
    svar_has_negative_occurrence X ϕ₁ = false ->
    svar_has_negative_occurrence X ϕ₂ = false ->
    Γ ⊢ ϕ₁ ---> ϕ₂ ->
    Γ ⊢ (patt_mu (svar_quantify X 0 ϕ₁)) ---> (patt_mu (svar_quantify X 0 ϕ₂)).
  Proof.
    intros wfϕ₁ wfϕ₂ nonegϕ₁ nonegϕ₂ Himp.
    apply Knaster_tarski.
    { wf_auto2. }

    pose proof (Htmp := Svar_subst Γ (ϕ₁ ---> ϕ₂) (mu, svar_quantify X 0 ϕ₂) X).
    feed specialize Htmp.
    { auto. }
    { unfold well_formed, well_formed_closed in *. destruct_and!.
      simpl. split_and!; auto.
    }
    { assumption. }
    unfold free_svar_subst in Htmp.
    simpl in Htmp.

    pose proof (Hpf := Pre_fixp Γ (svar_quantify X 0 ϕ₂)).
    simpl in Hpf.

    unshelve (eapply (@cast_proof Σ Γ _ _) in Hpf).
    3: { 
    erewrite bound_to_free_set_variable_subst.
      5: { apply svar_quantify_not_free. }
      4: {
       apply svar_quantify_closed_mu.
       unfold well_formed, well_formed_closed in *. destruct_and!. auto.
      }
      3: {
         apply svar_quantify_closed_mu.
         unfold well_formed, well_formed_closed in *. destruct_and!. auto.
      }
      2: lia.
      reflexivity.
    }

    2: abstract (wf_auto2).

    eapply (@cast_proof Σ Γ) in Hpf.
    2: {
      rewrite svar_open_svar_quantify.
      { unfold well_formed, well_formed_closed in *. destruct_and!. auto. }
      reflexivity.
    }


    assert(well_formed_positive (free_svar_subst' 0 ϕ₂ (mu , svar_quantify X 0 ϕ₂) X) = true).
    {
      unfold well_formed, well_formed_closed in *. destruct_and!. simpl; split_and?.
      apply wfp_free_svar_subst; auto.
      { apply svar_quantify_closed_mu. auto. }
      { simpl. split_and!.
        2: apply well_formed_positive_svar_quantify; assumption.
        apply no_negative_occurrence_svar_quantify; auto.
      }
    }

    assert(well_formed_closed_mu_aux (free_svar_subst' 0 ϕ₂ (mu , svar_quantify X 0 ϕ₂) X) 0 = true).
    {
      unfold well_formed, well_formed_closed in *. destruct_and!. simpl; split_and?; auto.
      replace 0 with (0 + 0) at 3 by lia.
      apply wfc_mu_free_svar_subst; auto.
      simpl.
      apply svar_quantify_closed_mu. assumption.
    }
    
    assert(well_formed_closed_ex_aux (free_svar_subst' 0 ϕ₂ (mu , svar_quantify X 0 ϕ₂) X) 0 = true).
    {
      unfold well_formed, well_formed_closed in *. destruct_and!. simpl; split_and?; auto.
      replace 0 with (0 + 0) at 3 by lia.
      apply wfc_ex_free_svar_subst; auto.
      simpl.
      apply svar_quantify_closed_ex. assumption.
    }

    assert(well_formed_positive (free_svar_subst' 0 ϕ₁ (mu , svar_quantify X 0 ϕ₂) X) = true).
    {
      unfold well_formed, well_formed_closed in *. destruct_and!. simpl; split_and?.
      apply wfp_free_svar_subst; auto.
      { apply svar_quantify_closed_mu. auto. }
      { simpl. split_and!.
        2: apply well_formed_positive_svar_quantify; assumption.
        apply no_negative_occurrence_svar_quantify; auto.
      }
    }

    assert(well_formed_closed_mu_aux (free_svar_subst' 0 ϕ₁ (mu , svar_quantify X 0 ϕ₂) X) 0 = true).
    {
      unfold well_formed, well_formed_closed in *. destruct_and!. simpl; split_and?; auto.
      replace 0 with (0 + 0) at 3 by lia.
      apply wfc_mu_free_svar_subst; auto.
      simpl.
      apply svar_quantify_closed_mu. assumption.
    }
    
    assert(well_formed_closed_ex_aux (free_svar_subst' 0 ϕ₁ (mu , svar_quantify X 0 ϕ₂) X) 0 = true).
    {
      unfold well_formed, well_formed_closed in *. destruct_and!. simpl; split_and?; auto.
      replace 0 with (0 + 0) at 3 by lia.
      apply wfc_ex_free_svar_subst; auto.
      simpl.
      apply svar_quantify_closed_ex. assumption.
    }
    
    epose proof (Hsi := @syllogism_intro Σ _ _ _ _ _ _ _ Htmp Hpf).
    simpl.

    eapply (@cast_proof Σ Γ).
    1: {
      erewrite bound_to_free_set_variable_subst with (X0 := X)(more := ?[more]).
      5: { apply svar_quantify_not_free. }
      4: {
           apply svar_quantify_closed_mu.
           unfold well_formed, well_formed_closed in *. destruct_and!. auto.
      }
      3: {
           apply svar_quantify_closed_mu.
           unfold well_formed, well_formed_closed in *. destruct_and!. auto.
      }
      2: lia.
      reflexivity.
    }

    eapply (@cast_proof Σ Γ).
    1: {
      rewrite svar_open_svar_quantify.
      { unfold well_formed, well_formed_closed in *. destruct_and!. auto. }
      reflexivity.
    }
    instantiate (more := 0).
    assumption.
    Unshelve.
    all: abstract(wf_auto2).
  Defined.


  (* These [Local Private_*] lemmas are not generally useful, but we use them to keep the body
     of [Private_prf_equiv_congruence] reasonably small. Because we want to reason about the body, too.
     The lemmas are mostly placeholders for `wf_auto`.
   *)


  Lemma prf_equiv_of_impl_of_equiv Γ a b a' b':
    well_formed a = true ->
    well_formed b = true ->
    well_formed a' = true ->
    well_formed b' = true ->
    Γ ⊢ (a <---> a') ->
    Γ ⊢ (b <---> b') ->
    Γ ⊢ (a ---> b) <---> (a' ---> b')
  .
  Proof.
    intros wfa wfb wfa' wfb' Haa' Hbb'.
    unshelve(epose proof (Haa'1 := @pf_conj_elim_l_meta _ _ _ _ _ _ Haa')); auto.
    unshelve(epose proof (Haa'2 := @pf_conj_elim_r_meta _ _ _ _ _ _ Haa')); auto.
    unshelve(epose proof (Hbb'1 := @pf_conj_elim_l_meta _ _ _ _ _ _ Hbb')); auto.
    unshelve(epose proof (Hbb'2 := @pf_conj_elim_r_meta _ _ _ _ _ _ Hbb')); auto.

    apply pf_iff_equiv_trans with (B := (a ---> b')); auto.
      + apply conj_intro_meta; subst; auto 10.
        * toMyGoal.
          { wf_auto2. }
          mgIntro. mgIntro.
          mgAdd Hbb'1.
          mgApply 0.
          mgApply 1.
          mgExactn 2.
        * toMyGoal.
          { wf_auto2. }
          mgIntro. mgIntro.
          mgAdd Hbb'2.
          mgApply 0.
          mgApply 1.
          mgExactn 2.
      + apply conj_intro_meta; auto.
        * toMyGoal.
          { wf_auto2. }
          mgIntro. mgIntro.
          mgAdd Haa'2.
          mgApply 1.
          mgApply 0.
          mgExactn 2.
        * toMyGoal.
          { wf_auto2. }
          mgIntro. mgIntro.
          mgAdd Haa'1.
          mgApply 1.
          mgApply 0.
          mgExactn 2.
  Defined.

  Lemma prf_equiv_of_impl_of_equiv_indifferent
        P Γ a b a' b'
        (wfa : well_formed a = true)
        (wfb : well_formed b = true)
        (wfa' : well_formed a' = true)
        (wfb' : well_formed b' = true)
        (aiffa' : Γ ⊢ a <---> a')
        (biffb' : Γ ⊢ b <---> b'):
    indifferent_to_prop P ->
    indifferent_to_cast P ->
    P _ _ aiffa' = false ->
    P _ _ biffb' = false ->
    P _ _ (@prf_equiv_of_impl_of_equiv Γ a b a' b' wfa wfb wfa' wfb' aiffa' biffb') = false.
  Proof.
    intros Hp. pose proof (Hp' := Hp). destruct Hp' as [Hp1 [Hp2 [Hp3 Hmp]]].
    intros Hc H1 H2.
    unfold prf_equiv_of_impl_of_equiv.
    rewrite pf_iff_equiv_trans_indifferent; auto.
    - rewrite conj_intro_meta_indifferent; auto.
      + pose proof (Htmp := MyGoal_intro_indifferent). simpl in Htmp.
        specialize (Htmp P Γ []). simpl in Htmp. rewrite Htmp; clear Htmp; auto.
        intros wf3 wf4.
        pose proof (Htmp := MyGoal_intro_indifferent).
        specialize (Htmp P Γ [a ---> b]). simpl in Htmp. rewrite Htmp; clear Htmp; auto.
        intros wf5 wf6.
        rewrite (@MyGoal_add_indifferent Σ P Γ [a ---> b; a]); auto.
        { rewrite pf_conj_elim_l_meta_indifferent; auto. }
        intros wf7 wf8.
        rewrite cast_proof_mg_hyps_indifferent; [assumption|].
        rewrite MyGoal_weakenConclusion_indifferent;[assumption|idtac|reflexivity].
        intros wf9 wf10.
        rewrite cast_proof_mg_hyps_indifferent;[assumption|].        
        rewrite MyGoal_weakenConclusion_indifferent;[assumption|idtac|reflexivity].
        intros wf11 wf12.
        rewrite cast_proof_mg_hyps_indifferent;[assumption|].
        rewrite MyGoal_exactn_indifferent;[assumption|reflexivity].
      + pose proof (Htmp := MyGoal_intro_indifferent).
        specialize (Htmp P Γ []). simpl in Htmp. rewrite Htmp; clear Htmp; auto.
        intros wf3 wf4.
        pose proof (Htmp := MyGoal_intro_indifferent).
        specialize (Htmp P Γ [a ---> b']). simpl in Htmp. rewrite Htmp; clear Htmp; auto.
        intros wf5 wf6.
        rewrite (@MyGoal_add_indifferent Σ P Γ [a ---> b'; a]); auto.
        { rewrite pf_conj_elim_r_meta_indifferent; auto. }
        intros wf7 wf8.
        rewrite cast_proof_mg_hyps_indifferent;[assumption|].
        rewrite MyGoal_weakenConclusion_indifferent;[assumption|idtac|reflexivity].
        intros wf9 wf10.
        rewrite cast_proof_mg_hyps_indifferent;[assumption|].
        rewrite MyGoal_weakenConclusion_indifferent;[assumption|idtac|reflexivity].      
        intros wf11 wf12.
        rewrite cast_proof_mg_hyps_indifferent;[assumption|].
        rewrite MyGoal_exactn_indifferent;[assumption|reflexivity].
    - rewrite conj_intro_meta_indifferent; auto.
      + pose proof (Htmp := MyGoal_intro_indifferent).
        specialize (Htmp P Γ []). simpl in Htmp. rewrite Htmp; clear Htmp; auto.
        intros wf3 wf4.
        pose proof (Htmp := MyGoal_intro_indifferent).
        specialize (Htmp P Γ [a ---> b']). simpl in Htmp. rewrite Htmp; clear Htmp; auto.
        intros wf5 wf6.
        rewrite (@MyGoal_add_indifferent Σ P Γ [a ---> b'; a']); auto.
        { rewrite pf_conj_elim_r_meta_indifferent; auto. }
        intros wf7 wf8.
        rewrite cast_proof_mg_hyps_indifferent;[assumption|].
        rewrite MyGoal_weakenConclusion_indifferent;[assumption|idtac|reflexivity].
        intros wf9 wf10.
        rewrite cast_proof_mg_hyps_indifferent;[assumption|].
        rewrite MyGoal_weakenConclusion_indifferent;[assumption|idtac|reflexivity].
        intros wf11 wf12.
        rewrite cast_proof_mg_hyps_indifferent;[assumption|].
        rewrite MyGoal_exactn_indifferent;[assumption|reflexivity].
      + pose proof (Htmp := MyGoal_intro_indifferent).
        specialize (Htmp P Γ []). simpl in Htmp. rewrite Htmp; clear Htmp; auto.
        intros wf3 wf4.
        pose proof (Htmp := MyGoal_intro_indifferent).
        specialize (Htmp P Γ [a' ---> b']). simpl in Htmp. rewrite Htmp; clear Htmp; auto.
        intros wf5 wf6.
        rewrite (@MyGoal_add_indifferent Σ P Γ [a' ---> b'; a]); auto.
        { rewrite pf_conj_elim_l_meta_indifferent; auto. }
        intros wf7 wf8.
        rewrite cast_proof_mg_hyps_indifferent;[assumption|].
        rewrite MyGoal_weakenConclusion_indifferent;[assumption|idtac|reflexivity].
        intros wf9 wf10.
        rewrite cast_proof_mg_hyps_indifferent;[assumption|].        
        rewrite MyGoal_weakenConclusion_indifferent;[assumption|idtac|reflexivity].      
        intros wf11 wf12.
        rewrite cast_proof_mg_hyps_indifferent;[assumption|].
        rewrite MyGoal_exactn_indifferent;[assumption|reflexivity].
  Qed.


  Lemma pf_evar_open_free_evar_subst_equiv_sides Γ x n ϕ p q E:
    x <> E ->
    well_formed p = true ->
    well_formed q = true ->
    Γ ⊢ free_evar_subst' n (evar_open n x ϕ) p E <---> free_evar_subst' n (evar_open n x ϕ) q E ->
    Γ ⊢ evar_open n x (free_evar_subst' n ϕ p E) <---> evar_open n x (free_evar_subst' n ϕ q E).
  Proof.
    intros Hx wfp wfq H.
    unshelve (eapply (@cast_proof Σ Γ _ _ _ H)).
    rewrite -> evar_open_free_evar_subst_swap by assumption.
    rewrite -> evar_open_free_evar_subst_swap by assumption.
    reflexivity.
  Defined.


  Definition evar_fresh_dep (S : EVarSet) : {x : evar & x ∉ S} :=
    @existT evar (fun x => x ∉ S) (evar_fresh (elements S)) (@set_evar_fresh_is_fresh' Σ S).

  Definition svar_fresh_dep (S : SVarSet) : {X : svar & X ∉ S} :=
    @existT svar (fun x => x ∉ S) (svar_fresh (elements S)) (@set_svar_fresh_is_fresh' _ S).

  Lemma pf_impl_ex_free_evar_subst_twice Γ n ϕ p q E:
    well_formed (ex, ϕ) = true ->
    well_formed p = true ->
    well_formed q = true ->
    Γ ⊢ ex , free_evar_subst' 0 ϕ p E ---> ex , free_evar_subst' 0 ϕ q E ->
    Γ ⊢ ex , free_evar_subst' n ϕ p E ---> ex , free_evar_subst' n ϕ q E.
  Proof.
    intros wfϕ wfp wfq H.
    unshelve (eapply (@cast_proof Σ Γ _ _ _ H)).
    abstract (
      replace n with (0 + n) by reflexivity;
      repeat rewrite -free_evar_subst_nest_ex_1;
      rewrite -> nest_ex_aux_wfc_ex by wf_auto;
      rewrite -> nest_ex_aux_wfc_ex by wf_auto;
      reflexivity
    ).
  Defined.

  Lemma strip_exists_quantify_l Γ x P Q :
    x ∉ free_evars P ->
    well_formed_closed_ex_aux P 1 ->
    Γ ⊢ (exists_quantify x (evar_open 0 x P) ---> Q) ->
    Γ ⊢ ex , P ---> Q.
  Proof.
    intros Hx HwfcP H.
    unshelve (eapply (@cast_proof Σ Γ _ _ _ H)).
    abstract (
      unfold exists_quantify;
      rewrite -> evar_quantify_evar_open by assumption;
      reflexivity
    ).
  Defined.

  Lemma strip_exists_quantify_r Γ x P Q :
    x ∉ free_evars Q ->
    well_formed_closed_ex_aux Q 1 ->
    Γ ⊢ P ---> (exists_quantify x (evar_open 0 x Q)) ->
    Γ ⊢ P ---> ex, Q.
  Proof.
    intros Hx HwfcP H.
    unshelve (eapply (@cast_proof Σ Γ _ _ _ H)).
    abstract (
      unfold exists_quantify;
      rewrite -> evar_quantify_evar_open by assumption;
      reflexivity
    ).
  Defined.

  Lemma pf_iff_free_evar_subst_svar_open_to_bsvar_subst_free_evar_subst Γ ϕ p q E X:
    well_formed_closed_mu_aux p 0 = true ->
    well_formed_closed_mu_aux q 0 = true ->
    Γ ⊢ free_evar_subst' 0 (svar_open 0 X ϕ) p E <---> free_evar_subst' 0 (svar_open 0 X ϕ) q E ->
    Γ ⊢ bsvar_subst (free_evar_subst' 0 ϕ p E) (patt_free_svar X) 0 <--->
        bsvar_subst (free_evar_subst' 0 ϕ q E) (patt_free_svar X) 0.
  Proof.
    intros wfp wfq H.
    unshelve (eapply (@cast_proof _ _ _ _ _ H)).

    abstract (
      unfold svar_open in H;
      rewrite <- free_evar_subst_bsvar_subst;
      [idtac|wf_auto| unfold evar_is_fresh_in; simpl; clear; set_solver];
      rewrite <- free_evar_subst_bsvar_subst;
      [idtac|wf_auto|unfold evar_is_fresh_in; simpl; clear; set_solver];
      reflexivity
   ).
  Defined.

  Lemma pf_iff_mu_remove_svar_quantify_svar_open Γ ϕ p q E X:
    well_formed_closed_mu_aux (free_evar_subst' 0 ϕ p E) 1 ->
    well_formed_closed_mu_aux (free_evar_subst' 0 ϕ q E) 1 ->
    X ∉ free_svars (free_evar_subst' 0 ϕ p E) ->
    X ∉ free_svars (free_evar_subst' 0 ϕ q E) ->
    Γ ⊢ mu , svar_quantify X 0 (svar_open 0 X (free_evar_subst' 0 ϕ p E)) <--->
        mu , svar_quantify X 0 (svar_open 0 X (free_evar_subst' 0 ϕ q E)) ->
    Γ ⊢ mu , free_evar_subst' 0 ϕ p E <---> mu , free_evar_subst' 0 ϕ q E.
  Proof.
    intros wfp' wfq' Xfrp Xfrq H.
    unshelve (eapply (@cast_proof _ _ _ _ _ H)).
    abstract (
      rewrite -{1}[free_evar_subst' 0 ϕ p E](@svar_quantify_svar_open _ X 0); [assumption|];
      rewrite -{1}[free_evar_subst' 0 ϕ q E](@svar_quantify_svar_open _ X 0); [assumption|];
      reflexivity
    ).
  Defined.


End FOL_helpers.

  Add Search Blacklist "_elim".
  Add Search Blacklist "_graph_rect".
  Add Search Blacklist "_graph_mut".
  Add Search Blacklist "FunctionalElimination_".


Section FOL_helpers.

  Context {Σ : Signature}.

  Definition pf_ite {P : Prop} (dec: {P} + {~P}) (Γ : Theory) (ϕ : Pattern)
    (pf1: P -> Γ ⊢ ϕ)
    (pf2: (~P) -> Γ ⊢ ϕ) :
    Γ ⊢ ϕ :=
    match dec with
    | left pf => pf1 pf
    | right pf => pf2 pf
    end.

  Equations? eq_prf_equiv_congruence
               Γ p q
               (wfp : well_formed p)
               (wfq : well_formed q)
               (EvS : EVarSet)
               (SvS : SVarSet)
               E ψ
               (wfψ : well_formed ψ)
               (pf : Γ ⊢ (p <---> q)) :
                   Γ ⊢ (((free_evar_subst' 0 ψ p E) <---> (free_evar_subst' 0 ψ q E)))
               by wf (size' ψ) lt
  :=
  @eq_prf_equiv_congruence  Γ p q wfp wfq EvS SvS E (patt_bound_evar n) wfψ pf
  := (@pf_iff_equiv_refl Σ Γ (patt_bound_evar n) wfψ) ;

  @eq_prf_equiv_congruence Γ p q wfp wfq EvS SvS E (patt_bound_svar n) wfψ pf
  := (@pf_iff_equiv_refl Σ Γ (patt_bound_svar n) wfψ) ;

  @eq_prf_equiv_congruence Γ p q wfp wfq EvS SvS E (patt_free_evar x) wfψ pf
  := @pf_ite _ (decide (E = x)) Γ
      ((free_evar_subst' 0 (patt_free_evar x) p E) <---> (free_evar_subst' 0 (patt_free_evar x) q E))
      (fun e => _)
      (fun (_ : E <> x) => _ ) ;

  @eq_prf_equiv_congruence Γ p q wfp wfq EvS SvS E (patt_free_svar X) wfψ pf
  := (@pf_iff_equiv_refl Σ Γ (patt_free_svar X) wfψ) ;

  @eq_prf_equiv_congruence Γ p q wfp wfq EvS SvS E (patt_bott) wfψ pf
  := (@pf_iff_equiv_refl Σ Γ patt_bott wfψ) ;

  @eq_prf_equiv_congruence Γ p q wfp wfq EvS SvS E (patt_sym s) wfψ pf
  := (@pf_iff_equiv_refl Σ Γ (patt_sym s) wfψ) ;

  @eq_prf_equiv_congruence Γ p q wfp wfq EvS SvS E (ϕ₁ ---> ϕ₂) wfψ pf
  with (@eq_prf_equiv_congruence Γ p q wfp wfq EvS SvS E ϕ₁ (@well_formed_imp_proj1 Σ _ _ wfψ) pf) => {
    | pf₁ with (@eq_prf_equiv_congruence Γ p q wfp wfq EvS SvS E ϕ₂ (@well_formed_imp_proj2 Σ _ _ wfψ) pf) => {
      | pf₂ := @prf_equiv_of_impl_of_equiv
                 Σ Γ
                 (free_evar_subst' 0 ϕ₁ p E)
                 (free_evar_subst' 0 ϕ₂ p E)
                 (free_evar_subst' 0 ϕ₁ q E)
                 (free_evar_subst' 0 ϕ₂ q E)
                 _ _ _ _ (*
                 (@well_formed_free_evar_subst Σ _ _ wfp (well_formed_imp_proj1 _ _ wfψ))
                 (@well_formed_free_evar_subst Σ _ _ wfp (well_formed_imp_proj2 _ _ wfψ))
                 (@well_formed_free_evar_subst Σ _ _ wfq (well_formed_imp_proj1 _ _ wfψ))
                 (@well_formed_free_evar_subst Σ _ _ wfq (well_formed_imp_proj2 _ _ wfψ)) *)
                 pf₁ pf₂
      }
  } ;

  @eq_prf_equiv_congruence Γ p q wfp wfq EvS SvS E (ϕ₁ $ ϕ₂) wfψ pf
  with (@eq_prf_equiv_congruence Γ p q wfp wfq EvS SvS E ϕ₁ (@well_formed_imp_proj1 Σ _ _ wfψ) pf) => {
  | pf₁ with (@eq_prf_equiv_congruence Γ p q wfp wfq EvS SvS E ϕ₂ (@well_formed_imp_proj2 Σ _ _ wfψ) pf) => {
    | pf₂ := (@pf_iff_equiv_trans Σ Γ _ (free_evar_subst' 0 ϕ₁ q E $ free_evar_subst' 0 ϕ₂ p E) _ _ _ _
               (@conj_intro_meta Σ Γ _ _ _ _
                 (Framing_left Γ _ _ _ _ (@pf_conj_elim_l_meta Σ _ _ _ _ _ pf₁))
                 (Framing_left Γ _ _ _ _ (@pf_conj_elim_r_meta Σ _ _ _ _ _ pf₁))
               )
               (@conj_intro_meta Σ Γ _ _ _ _
                 (Framing_right Γ _ _ _ _ (@pf_conj_elim_l_meta Σ _ _ _ _ _ pf₂))
                 (Framing_right Γ _ _ _ _ (@pf_conj_elim_r_meta Σ _ _ _ _ _ pf₂))
               )
             )
    }
  } ;

  @eq_prf_equiv_congruence Γ p q wfp wfq EvS SvS E (ex, ϕ') wfψ pf
  with (evar_fresh_dep ((EvS ∪ (free_evars (ex, ϕ')) ∪ {[ E ]} ∪ (free_evars p) ∪ (free_evars q)))) => {
  | (existT x frx) with (@eq_prf_equiv_congruence Γ p q wfp wfq EvS SvS E (evar_open 0 x ϕ') (@wf_evar_open_from_wf_ex Σ x ϕ' wfψ) pf) => {
    | IH with (@pf_evar_open_free_evar_subst_equiv_sides Σ Γ x 0 ϕ' p q E _ wfp wfq IH)=> {
      | IH' with ((@pf_iff_proj1 Σ _ _ _ _ _ IH'),(@pf_iff_proj2 Σ _ _ _ _ _ IH')) => {
        | (IH1, IH2) with ((@syllogism_intro Σ Γ _ _ _ _ _ _ IH1 (Ex_quan _ _ x _)),(@syllogism_intro Σ Γ _ _ _ _ _ _ IH2 (Ex_quan _ _ x _))) => {
          | (IH3, IH4) with ((Ex_gen Γ _ _ x _ _ IH3 _),(Ex_gen Γ _ _ x _ _ IH4 _)) => {
            | (IH3', IH4')
               :=
                @pf_iff_split Σ Γ (ex, free_evar_subst' 1 ϕ' p E) (ex, free_evar_subst' 1 ϕ' q E) _ _
                  (@pf_impl_ex_free_evar_subst_twice Σ Γ 1 ϕ' p q E wfψ wfp wfq
                    (@strip_exists_quantify_l Σ Γ x _ _ _ _ IH3')
                  )
                  (@pf_impl_ex_free_evar_subst_twice Σ Γ 1 ϕ' q p E wfψ wfq wfp
                    (@strip_exists_quantify_l Σ Γ x _ _ _ _ IH4')
                  )
            }
          }
        }
      }
    }
  } ;

  @eq_prf_equiv_congruence Γ p q wfp wfq EvS SvS E (mu, ϕ') wfψ pf
  with (svar_fresh_dep (SvS ∪ (free_svars (mu, ϕ')) ∪ (free_svars p) ∪ (free_svars q)
                      ∪ (free_svars (free_evar_subst' 0 ϕ' p E))
                      ∪ (free_svars (free_evar_subst' 0 ϕ' q E)))) => {
  | (existT X frX ) with (@eq_prf_equiv_congruence Γ p q wfp wfq EvS SvS E (svar_open 0 X ϕ') (@wf_svar_open_from_wf_mu Σ X ϕ' wfψ) pf) => {
    | IH with (@pf_iff_free_evar_subst_svar_open_to_bsvar_subst_free_evar_subst Σ Γ ϕ' p q E X _ _ IH) => {
      | IH' with ((@pf_iff_proj1 Σ _ _ _ _ _ IH'),(@pf_iff_proj2 Σ _ _ _ _ _ IH')) => {
        | (IH1, IH2) :=
            (@pf_iff_mu_remove_svar_quantify_svar_open Σ Γ ϕ' p q E X _ _ _ _
              (@pf_iff_split Σ Γ _ _ _ _
                (@mu_monotone Σ Γ _ _ X _ _ _ _ _)
                (@mu_monotone Σ Γ _ _ X _ _ _ _ _)
              )
            )
        }
      }
    }
  }
  .
  Proof.
    2: {
      unshelve (eapply (@cast_proof _ _ _ _ _ (@pf_iff_equiv_refl Σ Γ (patt_free_evar x) ltac:(auto)))).
      abstract (
        unfold free_evar_subst'; case_match; [congruence|]; reflexivity
      ).
    }
    1: {
      unshelve (eapply (@cast_proof _ _ _ _ _ pf)).
      abstract (
        unfold free_evar_subst'; case_match; [|congruence];
        rewrite !nest_ex_aux_0; reflexivity
      ).
    }
    all: try assumption.
    all: unfold is_true in *.
    all: abstract (wf_auto2).
  Defined.

  Lemma prf_equiv_congruence Γ p q C:
    PC_wf C ->
    Γ ⊢ (p <---> q) ->
    Γ ⊢ (((emplace C p) <---> (emplace C q))).
  Proof.
    intros wfC Hiff.
    pose proof (proved_impl_wf _ _ Hiff).
    assert (well_formed p) by wf_auto2.
    assert (well_formed q) by wf_auto2.
    destruct C as [pcEvar pcPattern].
    apply (
        @eq_prf_equiv_congruence Γ p q ltac:(assumption) ltac:(assumption)
          (free_evars pcPattern ∪ free_evars p ∪ free_evars q)
          (free_svars pcPattern ∪ free_svars p ∪ free_svars q)
      ); simpl;  assumption.
  Defined.

  Lemma uses_svar_subst_eq_prf_equiv_congruence
        Γ p q E ψ EvS SvS SvS'
        (wfp: well_formed p)
        (wfq: well_formed q)
        (wfψ: well_formed ψ)
        (pf : Γ ⊢ (p <---> q)):
    SvS ⊆ SvS' ->
    uses_svar_subst SvS pf = false ->
    uses_svar_subst SvS (@eq_prf_equiv_congruence Γ p q wfp wfq EvS SvS' E ψ wfψ pf) = false.
  Proof.
    intros Hsub H.

    apply (@eq_prf_equiv_congruence_elim
     (fun Γ p q wfp wfq EvS SvS' E ψ wfψ pf result
      => SvS ⊆ SvS' ->
         uses_svar_subst SvS pf = false ->
         uses_svar_subst SvS result = false)
    ).
    - clear. intros Γ p q wfp wfq EvS SvS' E x wfψ pf Hsub Hpf.
      unfold pf_ite.
      destruct (decide (E = x)).
      + unfold eq_prf_equiv_congruence_obligation_1.
        rewrite indifferent_to_cast_uses_svar_subst.
        exact Hpf.
      + unfold eq_prf_equiv_congruence_obligation_2.
        rewrite indifferent_to_cast_uses_svar_subst.
        reflexivity.
    - clear. intros Γ p q wfp wfq EvS SvS' E X wfψ pf Hsub Hpf.
      reflexivity.
    - clear. intros Γ p q wfp wfq EvS SvS' E X wfψ pf Hsub Hpf.
      reflexivity.
    - clear. intros Γ p q wfp wfq EvS SvS' E X wfψ pf Hsub Hpf.
      reflexivity.
    - clear. intros Γ p q wfp wfq EvS SvS' E X wfψ pf Hsub Hpf.
      reflexivity.
    - clear. intros Γ p q wfp wfq EvS SvS' E wfψ pf Hsub Hpf.
      reflexivity.
    - clear. intros Γ p q wfp wfq EvS SvS' E ϕ₁ ϕ₂ wfψ pf pf₁ pf₂.
      intros Heq1 Hind1 Heq2 Hind2 Hsub Hpf.
      subst pf₁. subst pf₂.
      specialize (Hind1 Hsub Hpf). specialize (Hind2 Hsub Hpf).
      pose proof (indifferent_to_prop_uses_svar_subst).
      rewrite pf_iff_equiv_trans_indifferent; auto.
      + rewrite conj_intro_meta_indifferent; auto.
        { simpl. rewrite Hind2. reflexivity. }
        { simpl. rewrite Hind2. reflexivity. }
      + rewrite conj_intro_meta_indifferent; auto.
        { simpl. rewrite Hind1. reflexivity. }
        { simpl. rewrite Hind1. reflexivity. }
    - clear. intros Γ p q wfp wfq EvS SvS' E ϕ₁ ϕ₂ wfψ pf pf₁ pf₂.
      intros Heq1 Hind1 Heq2 Hind2 Hsub Hpf.
      rewrite prf_equiv_of_impl_of_equiv_indifferent; subst; auto.
      { apply indifferent_to_prop_uses_svar_subst. }
      { apply indifferent_to_cast_uses_svar_subst. }
    - clear. intros Γ p q wfp wfq EvS SvS' E ϕ' x frx wfψ pf IH IH' IH1 IH2 IH3 IH4 IH3' IH4'.
      intros.
      inversion Heq; subst; clear Heq.
      inversion Heq0; subst; clear Heq0.
      inversion Heq1; subst; clear Heq1.

      specialize (Hind ltac:(assumption) ltac:(assumption)).
      rewrite pf_iff_split_indifferent.
      { apply indifferent_to_prop_uses_svar_subst. }
      + unfold pf_impl_ex_free_evar_subst_twice.
        rewrite indifferent_to_cast_uses_svar_subst.
        unfold strip_exists_quantify_l.
        rewrite indifferent_to_cast_uses_svar_subst.
        simpl.
        unfold pf_evar_open_free_evar_subst_equiv_sides.
        rewrite indifferent_to_cast_uses_svar_subst.
        rewrite Hind.
        reflexivity.
      + unfold pf_impl_ex_free_evar_subst_twice.
        rewrite indifferent_to_cast_uses_svar_subst.
        unfold strip_exists_quantify_l.
        rewrite indifferent_to_cast_uses_svar_subst.
        simpl.
        unfold pf_evar_open_free_evar_subst_equiv_sides.
        rewrite indifferent_to_cast_uses_svar_subst.
        rewrite Hind.
        reflexivity.
      + reflexivity.
    - clear. intros Γ p q wfp wfq EvS SvS' E ϕ' X frX wfψ pf Ih IH' IH1 IH2.
      intros.
      unfold pf_iff_mu_remove_svar_quantify_svar_open.
      rewrite indifferent_to_cast_uses_svar_subst.
      inversion Heq; subst; clear Heq.
      specialize (Hind ltac:(assumption) ltac:(assumption)).
      rewrite pf_iff_split_indifferent.
      { apply indifferent_to_prop_uses_svar_subst. }
      3: { reflexivity. }
      + unfold mu_monotone.
        simpl.
        rewrite indifferent_to_cast_uses_svar_subst.
        rewrite indifferent_to_cast_uses_svar_subst.
        rewrite syllogism_intro_indifferent.
        { apply indifferent_to_prop_uses_svar_subst. }
        simpl.
        { case_match. clear -frX e H. set_solver.
          unfold pf_iff_free_evar_subst_svar_open_to_bsvar_subst_free_evar_subst.
          rewrite indifferent_to_cast_uses_svar_subst.
          rewrite Hind. reflexivity.
        }
        2: reflexivity.
        rewrite indifferent_to_cast_uses_svar_subst.
        rewrite indifferent_to_cast_uses_svar_subst.
        simpl. reflexivity.
      + unfold mu_monotone.
        simpl.
        rewrite indifferent_to_cast_uses_svar_subst.
        rewrite indifferent_to_cast_uses_svar_subst.
        rewrite syllogism_intro_indifferent.
        { apply indifferent_to_prop_uses_svar_subst. }
        simpl.
        { case_match. clear -frX e H. set_solver.
          unfold pf_iff_free_evar_subst_svar_open_to_bsvar_subst_free_evar_subst.
          rewrite indifferent_to_cast_uses_svar_subst.
          rewrite Hind. reflexivity.
        }
        2: reflexivity.
        rewrite indifferent_to_cast_uses_svar_subst.
        rewrite indifferent_to_cast_uses_svar_subst.
        simpl. reflexivity.
    - assumption.
    - assumption.
  Qed.


  Lemma uses_ex_gen_eq_prf_equiv_congruence
        Γ p q E ψ EvS EvS' SvS
        (wfp: well_formed p)
        (wfq: well_formed q)
        (wfψ: well_formed ψ)
        (pf : Γ ⊢ (p <---> q)):
    EvS ⊆ EvS' ->
    uses_ex_gen EvS pf = false ->
    uses_ex_gen EvS (@eq_prf_equiv_congruence Γ p q wfp wfq EvS' SvS E ψ wfψ pf) = false.
  Proof.
    intros Hsub H.
    apply  (@eq_prf_equiv_congruence_elim
     (fun Γ p q wfp wfq EvS' SvS E ψ wfψ pf result
      => EvS ⊆ EvS' -> uses_ex_gen EvS pf = false -> uses_ex_gen EvS result = false)
    ).
    - clear. intros Γ p q wfp wfq EvS' SvS E x wfψ pf Hsub Hpf.
      unfold pf_ite.
      destruct (decide (E = x)).
      + unfold eq_prf_equiv_congruence_obligation_1.
        rewrite indifferent_to_cast_uses_ex_gen.
        exact Hpf.
      + unfold eq_prf_equiv_congruence_obligation_2.
        rewrite indifferent_to_cast_uses_ex_gen.
        reflexivity.
    - clear. intros Γ p q wfp wfq EvS' SvS E X wfψ pf Hsub Hpf.
      reflexivity.
    - clear. intros Γ p q wfp wfq EvS' SvS E X wfψ pf Hsub Hpf.
      reflexivity.
    - clear. intros Γ p q wfp wfq EvS' SvS E X wfψ pf Hsub Hpf.
      reflexivity.
    - clear. intros Γ p q wfp wfq EvS' SvS E X wfψ pf Hsub Hpf.
      reflexivity.
    - clear. intros Γ p q wfp wfq EvS' SvS E wfψ pf Hsub Hpf.
      reflexivity.
    - clear. intros Γ p q wfp wfq EvS' SvS E ϕ₁ ϕ₂ wfψ pf pf₁ pf₂.
      intros Heq1 Hind1 Heq2 Hind2 Hsub Hpf.
      subst pf₁. subst pf₂.
      specialize (Hind1 Hsub Hpf). specialize (Hind2 Hsub Hpf).
      pose proof (indifferent_to_prop_uses_ex_gen).
      rewrite pf_iff_equiv_trans_indifferent; auto.
      + rewrite conj_intro_meta_indifferent; auto.
        { simpl. rewrite Hind2. reflexivity. }
        { simpl. rewrite Hind2. reflexivity. }
      + rewrite conj_intro_meta_indifferent; auto.
        { simpl. rewrite Hind1. reflexivity. }
        { simpl. rewrite Hind1. reflexivity. }
    - clear. intros Γ p q wfp wfq EvS' SvS E ϕ₁ ϕ₂ wfψ pf pf₁ pf₂.
      intros Heq1 Hind1 Heq2 Hind2 Hsub Hpf.
      rewrite prf_equiv_of_impl_of_equiv_indifferent; subst; auto.
      { apply indifferent_to_prop_uses_ex_gen. }
      { apply indifferent_to_cast_uses_ex_gen. }
    - clear. intros Γ p q wfp wfq EvS' SvS E ϕ' x frx wfψ pf IH IH' IH1 IH2 IH3 IH4 IH3' IH4'.
      intros.
      inversion Heq; subst; clear Heq.
      inversion Heq0; subst; clear Heq0.
      inversion Heq1; subst; clear Heq1.

      specialize (Hind ltac:(assumption) ltac:(assumption)).
      rewrite pf_iff_split_indifferent.
      { apply indifferent_to_prop_uses_ex_gen. }
      + unfold pf_impl_ex_free_evar_subst_twice.
        rewrite indifferent_to_cast_uses_ex_gen.
        unfold strip_exists_quantify_l.
        rewrite indifferent_to_cast_uses_ex_gen.
        simpl.
        unfold pf_evar_open_free_evar_subst_equiv_sides.
        rewrite indifferent_to_cast_uses_ex_gen.
        rewrite Hind.
        case_match.
        { clear -frx e H.  set_solver. }
        reflexivity.
      + unfold pf_impl_ex_free_evar_subst_twice.
        rewrite indifferent_to_cast_uses_ex_gen.
        unfold strip_exists_quantify_l.
        rewrite indifferent_to_cast_uses_ex_gen.
        simpl.
        unfold pf_evar_open_free_evar_subst_equiv_sides.
        rewrite indifferent_to_cast_uses_ex_gen.
        rewrite Hind.
        case_match.
        { clear -frx e H. set_solver. }
        reflexivity.
      + reflexivity.
    - clear. intros Γ p q wfp wfq EvS' SvS E ϕ' X frX wfψ pf Ih IH' IH1 IH2.
      intros.
      unfold pf_iff_mu_remove_svar_quantify_svar_open.
      rewrite indifferent_to_cast_uses_ex_gen.
      inversion Heq; subst; clear Heq.
      specialize (Hind ltac:(assumption) ltac:(assumption)).
      rewrite pf_iff_split_indifferent.
      { apply indifferent_to_prop_uses_ex_gen. }
      3: { reflexivity. }
      + unfold mu_monotone.
        simpl.
        rewrite indifferent_to_cast_uses_ex_gen.
        rewrite indifferent_to_cast_uses_ex_gen.
        rewrite syllogism_intro_indifferent.
        { apply indifferent_to_prop_uses_ex_gen. }
        simpl.
        { unfold pf_iff_free_evar_subst_svar_open_to_bsvar_subst_free_evar_subst.
          rewrite indifferent_to_cast_uses_ex_gen.
          rewrite Hind. reflexivity.
        }
        2: reflexivity.
        rewrite indifferent_to_cast_uses_ex_gen.
        rewrite indifferent_to_cast_uses_ex_gen.
        simpl. reflexivity.
      + unfold mu_monotone.
        simpl.
        rewrite indifferent_to_cast_uses_ex_gen.
        rewrite indifferent_to_cast_uses_ex_gen.
        rewrite syllogism_intro_indifferent.
        { apply indifferent_to_prop_uses_ex_gen. }
        simpl.
        { unfold pf_iff_free_evar_subst_svar_open_to_bsvar_subst_free_evar_subst.
          rewrite indifferent_to_cast_uses_ex_gen.
          rewrite Hind. reflexivity.
        }
        2: reflexivity.
        rewrite indifferent_to_cast_uses_ex_gen.
        rewrite indifferent_to_cast_uses_ex_gen.
        simpl. reflexivity.
    - assumption.
    - assumption.
  Qed.

  Lemma uses_kt_nomu_eq_prf_equiv_congruence
        Γ p q E ψ EvS SvS
        (wfp: well_formed p)
        (wfq: well_formed q)
        (wfψ: well_formed ψ)
        (pf : Γ ⊢ (p <---> q)):
    mu_free ψ ->
    uses_kt pf = false ->
    uses_kt (@eq_prf_equiv_congruence Γ p q wfp wfq EvS SvS E ψ wfψ pf) = false.
  Proof.
    intros Hmfψ H.
    apply  (@eq_prf_equiv_congruence_elim
     (fun Γ p q wfp wfq EvS SvS E ψ wfψ pf result
      => mu_free ψ -> uses_kt pf = false -> uses_kt result = false)
    ).
    - clear. intros Γ p q wfp wfq EvS SvS E x wfψ pf Hmfψ Hpf.
      unfold pf_ite.
      destruct (decide (E = x)).
      + unfold eq_prf_equiv_congruence_obligation_1.
        rewrite indifferent_to_cast_uses_kt.
        exact Hpf.
      + unfold eq_prf_equiv_congruence_obligation_2.
        rewrite indifferent_to_cast_uses_kt.
        reflexivity.
    - clear. intros Γ p q wfp wfq EvS SvS E X wfψ pf Hmfψ Hpf.
      reflexivity.
    - clear. intros Γ p q wfp wfq EvS SvS E X wfψ pf Hmfψ Hpf.
      reflexivity.
    - clear. intros Γ p q wfp wfq EvS SvS E X wfψ pf Hmfψ Hpf.
      reflexivity.
    - clear. intros Γ p q wfp wfq EvS SvS E X wfψ pf Hmfψ Hpf.
      reflexivity.
    - clear. intros Γ p q wfp wfq EvS SvS E wfψ pf Hmfψ Hpf.
      reflexivity.
    - clear. intros Γ p q wfp wfq EvS SvS E ϕ₁ ϕ₂ wfψ pf pf₁ pf₂.
      intros Heq1 Hind1 Heq2 Hind2 Hmfψ Hpf.
      simpl in Hmfψ. apply andb_prop in Hmfψ. destruct Hmfψ as [Hmfϕ₁ Hmfϕ₂].
      subst pf₁. subst pf₂.
      specialize (Hind1 Hmfϕ₂ Hpf). specialize (Hind2 Hmfϕ₁ Hpf).
      pose proof (indifferent_to_prop_uses_kt).
      rewrite pf_iff_equiv_trans_indifferent; auto.
      + rewrite conj_intro_meta_indifferent; auto.
        { simpl. rewrite Hind2. reflexivity. }
        { simpl. rewrite Hind2. reflexivity. }
      + rewrite conj_intro_meta_indifferent; auto.
        { simpl. rewrite Hind1. reflexivity. }
        { simpl. rewrite Hind1. reflexivity. }
    - clear. intros Γ p q wfp wfq EvS SvS E ϕ₁ ϕ₂ wfψ pf pf₁ pf₂.
      intros Heq1 Hind1 Heq2 Hind2 Hmf Hpf.
      simpl in Hmf. apply andb_prop in Hmf as [Hmf1 Hmf2].
      rewrite prf_equiv_of_impl_of_equiv_indifferent; subst; auto.
      { apply indifferent_to_prop_uses_kt. }
      { apply indifferent_to_cast_uses_kt. }
    - clear. intros Γ p q wfp wfq EvS SvS E ϕ' x frx wfψ pf IH IH' IH1 IH2 IH3 IH4 IH3' IH4'.
      intros.
      inversion Heq; subst; clear Heq.
      inversion Heq0; subst; clear Heq0.
      inversion Heq1; subst; clear Heq1.
      simpl in H.

      feed specialize Hind.
      { apply mu_free_evar_open. assumption. }
      { assumption. }

      rewrite pf_iff_split_indifferent.
      { apply indifferent_to_prop_uses_kt. }
      + unfold pf_impl_ex_free_evar_subst_twice.
        rewrite indifferent_to_cast_uses_kt.
        unfold strip_exists_quantify_l.
        rewrite indifferent_to_cast_uses_kt.
        simpl.
        unfold pf_evar_open_free_evar_subst_equiv_sides.
        rewrite indifferent_to_cast_uses_kt.
        rewrite Hind.
        reflexivity.
      + unfold pf_impl_ex_free_evar_subst_twice.
        rewrite indifferent_to_cast_uses_kt.
        unfold strip_exists_quantify_l.
        rewrite indifferent_to_cast_uses_kt.
        simpl.
        unfold pf_evar_open_free_evar_subst_equiv_sides.
        rewrite indifferent_to_cast_uses_kt.
        rewrite Hind.
        reflexivity.
      + reflexivity.
    - clear. intros Γ p q wfp wfq EvS SvS E ϕ' X frX wfψ pf Ih IH' IH1 IH2.
      intros. simpl in H. congruence.
    - assumption.
    - assumption.
  Qed.



End FOL_helpers.

Lemma ex_quan_monotone {Σ : Signature} Γ x ϕ₁ ϕ₂:
  well_formed ϕ₁ = true ->
  well_formed ϕ₂ = true ->
  Γ ⊢ ϕ₁ ---> ϕ₂ ->
  Γ ⊢ (exists_quantify x ϕ₁) ---> (exists_quantify x ϕ₂).
Proof.
  intros wfϕ₁ wfϕ₂ H.
  apply Ex_gen.
  { assumption. }
  { unfold exists_quantify. apply wf_ex_evar_quantify. assumption. }
  2: { simpl. rewrite free_evars_evar_quantify. clear. set_solver. }

  unfold exists_quantify.
  eapply syllogism_intro. 4: apply H.
  { auto. }
  { auto. }
  { apply wf_ex_evar_quantify. assumption. }
  clear H wfϕ₁ ϕ₁.

  replace ϕ₂ with (instantiate (ex, evar_quantify x 0 ϕ₂) (patt_free_evar x)) at 1.
  2: { unfold instantiate. Search bevar_subst evar_quantify.
       rewrite bevar_subst_evar_quantify_free_evar.
       apply wfc_ex_implies_not_bevar_occur. wf_auto. reflexivity.
  }
  apply Ex_quan.
  abstract (wf_auto2).
Defined.

Lemma ex_quan_monotone_nowf {Σ : Signature} Γ x ϕ₁ ϕ₂:
  Γ ⊢ ϕ₁ ---> ϕ₂ ->
  Γ ⊢ (exists_quantify x ϕ₁) ---> (exists_quantify x ϕ₂).
Proof.
  intros H.
  pose proof (Hwf := proved_impl_wf _ _ H).
  pose proof (well_formed_imp_proj1 Hwf).
  pose proof (well_formed_imp_proj2 Hwf).
  apply ex_quan_monotone; assumption.
Defined.

Lemma ex_quan_and_proj1 {Σ : Signature} Γ x ϕ₁ ϕ₂:
  well_formed ϕ₁ = true ->
  well_formed ϕ₂ = true ->
  Γ ⊢ (exists_quantify x (ϕ₁ and ϕ₂)) ---> (exists_quantify x ϕ₁).
Proof.
  intros wfϕ₁ wfϕ₂.
  apply ex_quan_monotone; auto.
  toMyGoal.
  { wf_auto2. }
  mgIntro.
  mgDestructAnd 0. auto. mgExactn 0; auto.
Defined.

Lemma ex_quan_and_proj2 {Σ : Signature} Γ x ϕ₁ ϕ₂:
  well_formed ϕ₁ = true ->
  well_formed ϕ₂ = true ->
  Γ ⊢ (exists_quantify x (ϕ₁ and ϕ₂)) ---> (exists_quantify x ϕ₂).
Proof.
  intros wfϕ₁ wfϕ₂.
  apply ex_quan_monotone; auto.
  toMyGoal.
  { wf_auto2. }
  mgIntro.
  mgDestructAnd 0.
  mgExactn 1.
Defined.

Lemma lhs_to_and {Σ : Signature} Γ a b c:
  well_formed a ->
  well_formed b ->
  well_formed c ->
  Γ ⊢ (a and b) ---> c ->
  Γ ⊢ a ---> b ---> c.
Proof.
  intros wfa wfb wfc H.
  toMyGoal.
  { wf_auto2. }
  do 2 mgIntro. mgApplyMeta H; auto.
  fromMyGoal. intros _ _. apply conj_intro; auto.
Defined.

Lemma lhs_from_and {Σ : Signature} Γ a b c:
  well_formed a ->
  well_formed b ->
  well_formed c ->
  Γ ⊢ a ---> b ---> c ->
  Γ ⊢ (a and b) ---> c.
Proof.
  intros wfa wfb wfc H.
  toMyGoal.
  { wf_auto2. }
  mgIntro.
  mgAssert (b).
  { wf_auto2. }
  { fromMyGoal. intros _ _. apply pf_conj_elim_r; auto. }
  mgAssert (a) using first 1.
  { wf_auto2. }
  { fromMyGoal. intros _ _. apply pf_conj_elim_l; auto. }
  mgAdd H.
  mgAssert ((b ---> c)).
  { wf_auto2. }
  { mgApply 0. mgExactn 2. }
  mgApply 4.
  mgExactn 3.
Defined.

Lemma prf_conj_split {Σ : Signature} Γ a b l:
  well_formed a ->
  well_formed b ->
  wf l ->
  Γ ⊢ (foldr patt_imp a l) ---> (foldr patt_imp b l) ---> (foldr patt_imp (a and b) l).
Proof.
  intros wfa wfb wfl.
  induction l.
  - simpl. apply conj_intro; auto.
  - simpl. pose proof (wfl' := wfl). unfold wf in wfl'. simpl in wfl'. apply andb_prop in wfl' as [wfa0 wfl'].
    specialize (IHl wfl').
    toMyGoal.
    { wf_auto2. }
    do 3 mgIntro.
    mgAssert ((foldr patt_imp a l)).
    { wf_auto2. }
    { mgApply 0. mgExactn 2. }
    mgAssert ((foldr patt_imp b l)).
    { wf_auto2. }
    { mgApply 1. mgExactn 2. }
    mgClear 2. mgClear 1. mgClear 0.
    fromMyGoal. intros _ _. apply IHl.
Defined.

Lemma prf_conj_split_meta {Σ : Signature} Γ a b l:
  well_formed a ->
  well_formed b ->
  wf l ->
  Γ ⊢ (foldr patt_imp a l) -> 
  Γ ⊢ (foldr patt_imp b l) ---> (foldr patt_imp (a and b) l).
Proof.
  intros. eapply Modus_ponens. 4: apply prf_conj_split. all: auto 10.
Defined.

Lemma prf_conj_split_meta_meta {Σ : Signature} Γ a b l:
  well_formed a ->
  well_formed b ->
  wf l ->
  Γ ⊢ (foldr patt_imp a l) -> 
  Γ ⊢ (foldr patt_imp b l) ->
  Γ ⊢ (foldr patt_imp (a and b) l).
Proof.
  intros. eapply Modus_ponens. 4: apply prf_conj_split_meta. all: auto 10.
Defined.

Lemma MyGoal_splitAnd {Σ : Signature} Γ a b l:
  @mkMyGoal Σ Γ l a ->
  @mkMyGoal Σ Γ l b ->
  @mkMyGoal Σ Γ l (a and b).
Proof.
  intros Ha Hb.
  unfold of_MyGoal in *. simpl in *.
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

Ltac mgSplitAnd := apply MyGoal_splitAnd.

Local Lemma ex_mgSplitAnd {Σ : Signature} Γ a b c:
  well_formed a ->
  well_formed b ->
  well_formed c ->
  Γ ⊢ a ---> b ---> c ---> (a and b).
Proof.
  intros wfa wfb wfc.
  toMyGoal.
  { wf_auto2. }
  mgIntro. mgIntro. mgIntro.
  mgSplitAnd.
  - mgExactn 0.
  - mgExactn 1.
Qed.

(* Hints *)
#[export]
 Hint Resolve A_impl_A : core.


Lemma prf_local_goals_equiv_impl_full_equiv {Σ : Signature} Γ g₁ g₂ l:
  well_formed g₁ ->
  well_formed g₂ ->
  wf l ->
  Γ ⊢ (foldr patt_imp (g₁ <---> g₂) l) --->
      ((foldr patt_imp g₁ l) <---> (foldr patt_imp g₂ l)).
Proof.
  intros wfg₁ wfg₂ wfl.
  induction l; simpl.
  - apply A_impl_A; wf_auto2.
  - pose proof (wfl' := wfl). unfold wf in wfl'. simpl in wfl'. apply andb_prop in wfl' as [wfa wfl'].
    specialize (IHl wfl').
    toMyGoal.
    { wf_auto2. }
    mgIntro. mgSplitAnd.
    + unshelve (mgApplyMeta (@P2 _ _ _ _ _ _ _ _)).
      1-3: wf_auto2.
      (* TODO we need some [mgRevert] tactic *)
      fromMyGoal. intros _ _. toMyGoal.
      { wf_auto2. }
      unshelve(mgApplyMeta (@P2 _ _ _ _ _ _ _ _)).
      1-3: wf_auto2.
      mgIntro. mgClear 0. mgIntro.
      mgApplyMeta IHl in 0. unfold patt_iff at 1. mgDestructAnd 0.
      mgExactn 0.
    + unshelve (mgApplyMeta (@P2 _ _ _ _ _ _ _ _)).
      1-3: wf_auto2.
      fromMyGoal. intros _ _. toMyGoal.
      { wf_auto2. }
      unshelve (mgApplyMeta (@P2 _ _ _ _ _ _ _ _)).
      1-3: wf_auto2.
      mgIntro. mgClear 0. mgIntro.
      mgApplyMeta IHl in 0. unfold patt_iff at 1. mgDestructAnd 0.
      mgExactn 1.
Defined.

Lemma prf_local_goals_equiv_impl_full_equiv_meta {Σ : Signature} Γ g₁ g₂ l:
  well_formed g₁ ->
  well_formed g₂ ->
  wf l ->
  Γ ⊢ (foldr patt_imp (g₁ <---> g₂) l) ->
  Γ ⊢ ((foldr patt_imp g₁ l) <---> (foldr patt_imp g₂ l)).
Proof.
  intros wfg₁ wfg₂ wfl H.
  eapply Modus_ponens.
  4: apply prf_local_goals_equiv_impl_full_equiv; auto.
  all: auto.
Defined.

Lemma prf_local_goals_equiv_impl_full_equiv_meta_proj1 {Σ : Signature} Γ g₁ g₂ l:
  well_formed g₁ ->
  well_formed g₂ ->
  wf l ->
  Γ ⊢ (foldr patt_imp (g₁ <---> g₂) l) ->
  Γ ⊢ (foldr patt_imp g₁ l) ->
  Γ ⊢ (foldr patt_imp g₂ l).
Proof.
  intros wfg₁ wfg₂ wfl H1 H2.
  eapply Modus_ponens.
  4: eapply pf_iff_proj1.
  6: apply prf_local_goals_equiv_impl_full_equiv_meta.
  9: apply H1.
  all: auto.
Defined.

Lemma prf_local_goals_equiv_impl_full_equiv_meta_proj2 {Σ : Signature} Γ g₁ g₂ l:
  well_formed g₁ ->
  well_formed g₂ ->
  wf l ->
  Γ ⊢ (foldr patt_imp (g₁ <---> g₂) l) ->
  Γ ⊢ (foldr patt_imp g₂ l) ->
  Γ ⊢ (foldr patt_imp g₁ l).
Proof.
  intros wfg₁ wfg₂ wfl H1 H2.
  eapply Modus_ponens.
  4: eapply pf_iff_proj2.
  6: apply prf_local_goals_equiv_impl_full_equiv_meta.
  9: apply H1.
  all: auto.
Defined.

Lemma prf_equiv_congruence_iter {Σ : Signature} (Γ : Theory) (p q : Pattern) (C : PatternCtx) l:
  PC_wf C ->
  wf l ->
  Γ ⊢ p <---> q ->
  Γ ⊢ (foldr patt_imp (emplace C p) l) <---> (foldr patt_imp (emplace C q) l).
Proof.
  intros wfC wfl Himp.
  induction l; simpl in *.
  - apply prf_equiv_congruence; assumption.
  - pose proof (wfal := wfl). unfold wf in wfl. simpl in wfl. apply andb_prop in wfl as [wfa wfl].
    specialize (IHl wfl).
    pose proof (proved_impl_wf _ _ IHl).
    toMyGoal.
    { wf_auto2. }
    unfold patt_iff.
    mgSplitAnd.
    + mgIntro. mgIntro.
      mgAssert ((foldr patt_imp (emplace C p) l)).
      { wf_auto2. }
      { mgApply 0. mgExactn 1. }
      apply pf_iff_proj1 in IHl.
      2,3: wf_auto2.
      mgApplyMeta IHl.
      mgExactn 2.
    + mgIntro. mgIntro.
      mgAssert ((foldr patt_imp (emplace C q) l)).
      { wf_auto2. }
      { mgApply 0. mgExactn 1. }
      apply pf_iff_proj2 in IHl.
      2,3: wf_auto2.
      mgApplyMeta IHl.
      mgExactn 2.
Defined.

Lemma MyGoal_rewriteIff {Σ : Signature} (Γ : Theory) (p q : Pattern) (C : PatternCtx) l:
  Γ ⊢ p <---> q ->
  @mkMyGoal Σ Γ l (emplace C q) ->
  @mkMyGoal Σ Γ l (emplace C p).
Proof.
  intros Hpiffq H.
  unfold of_MyGoal in *. simpl in *.
  intros wfcp wfl.
  feed specialize H.
  { abstract (
      pose proof (Hwfiff := proved_impl_wf _ _ Hpiffq);
      unfold emplace;
      apply well_formed_free_evar_subst_0;[wf_auto2|];
      fold (PC_wf C);
      eapply wf_emplaced_impl_wf_context;
      apply wfcp
    ).
  }
  { exact wfl. }

  eapply Modus_ponens.
  4: apply pf_iff_proj2.
  4: abstract (wf_auto2).
  5: apply prf_equiv_congruence_iter.
  7: apply Hpiffq.
  3: apply H.
  5: exact wfl.
  4: eapply wf_emplaced_impl_wf_context;
     apply wfcp.
  1,3: apply proved_impl_wf in H; exact H.
  1: abstract (apply proved_impl_wf in H; wf_auto2).
Defined.

Ltac2 mutable ml_debug_rewrite := false.

(* Calls [cont] for every subpattern [a] of pattern [phi], giving the match context as an argument *)
Ltac2 for_each_match := fun (a : constr) (phi : constr) (cont : Pattern.context -> unit) =>
  try (
      if ml_debug_rewrite then
           Message.print (
               Message.concat
                 (Message.of_string "Trying to match ")
                 (Message.of_constr a)
             )
        else ();
      match! phi with
      | context ctx [ ?x ]
        => if ml_debug_rewrite then
             Message.print (
                 Message.concat
                   (Message.of_string " against ")
                   (Message.of_constr x)
               )
           else ();
           (if Constr.equal x a then
              if ml_debug_rewrite then
                Message.print (Message.of_string "Success.")
              else () ;
              cont ctx
            else ());
           fail (* backtrack *)
      end
    ); ().

(* Calls [cont] for [n]th subpatern [a] of pattern [phi]. *)
Ltac2 for_nth_match :=
  fun (n : int) (a : constr) (phi : constr) (cont : Pattern.context -> unit) =>
    if ml_debug_rewrite then
      Message.print (Message.of_string "for_nth_match")
    else () ;
    let curr : int ref := {contents := 0} in
    let found : bool ref := {contents := false} in
    for_each_match a phi
    (fun ctx =>
      if (found.(contents))
      then ()
      else
        curr.(contents) := Int.add 1 (curr.(contents)) ;
        if (Int.equal (curr.(contents)) n) then 
          cont ctx
        else ()
    )
.

Local Ltac reduce_free_evar_subst_step_2 star :=
      lazymatch goal with
      | [ |- context ctx [free_evar_subst' ?more ?p ?q star]]
        =>
          rewrite -> (@free_evar_subst_no_occurrence _ more star p q) by (
            apply count_evar_occurrences_0;
            unfold star;
            eapply evar_is_fresh_in_richer';
            [|apply set_evar_fresh_is_fresh'];
            simpl; clear; set_solver
          )
      end.

Local Ltac reduce_free_evar_subst_2 star :=
  unfold free_evar_subst;
  repeat (reduce_free_evar_subst_step_2 star).

Local Ltac solve_fresh_contradictions_2 star :=
  unfold fresh_evar; simpl;
  match goal with
  | h: star = ?x |- _
    => let hcontra := fresh "Hcontra" in
       assert (hcontra: x <> star) by (unfold star,fresh_evar; clear h; simpl; solve_fresh_neq);
       rewrite -> h in hcontra;
       contradiction
  end.

Local Ltac clear_obvious_equalities_2 :=
  repeat (
      match goal with
      | [ h: ?x = ?x |- _ ] => clear h
      end
    ).


Ltac simplify_emplace_2 star :=
  unfold emplace;
  simpl;
  unfold free_evar_subst;
  simpl;
  repeat break_match_goal;
  clear_obvious_equalities_2; try contradiction;
  try (solve_fresh_contradictions_2 star);
  repeat (rewrite nest_ex_aux_0);
  reduce_free_evar_subst_2 star.

(* Returns [n]th matching logic context [C] (of type [PatternCtx]) such that
   [emplace C a = phi].
 *)

Ltac2 Type HeatResult := {
  star_ident : ident ;
  pc : constr ;
  ctx : Pattern.context ;
  ctx_pat : constr ;
  equality : ident ;
}.

Ltac2 heat :=
  fun (n : int) (a : constr) (phi : constr) : HeatResult =>
    let found : (Pattern.context option) ref := { contents := None } in
     for_nth_match n a phi
     (fun ctx =>
        found.(contents) := Some ctx; ()
     );
    match found.(contents) with
    | None => Control.backtrack_tactic_failure "Cannot heat"
    | Some ctx
      => (
         let fr := constr:(fresh_evar $phi) in
         let star_ident := Fresh.in_goal ident:(star) in
         set ($star_ident := $fr);
         let star_hyp := Control.hyp star_ident in
         let ctxpat := Pattern.instantiate ctx constr:(patt_free_evar $star_hyp) in
         let pc := constr:((@Build_PatternCtx _ $star_hyp $ctxpat)) in
         let heq1 := Fresh.in_goal ident:(heq1) in
         assert(heq1 : ($phi = (@emplace _ $pc $a))) 
         > [ abstract(
             (ltac1:(star |- simplify_emplace_2 star) (Ltac1.of_ident star_ident);
             reflexivity
             ))
           | ()
           ];
         { star_ident := star_ident; pc := pc; ctx := ctx; ctx_pat := ctxpat; equality := heq1 }
         )
    end
.

Ltac2 mgRewrite (hiff : constr) (atn : int) :=
  lazy_match! Constr.type hiff with
  | @ML_proof_system _ _ (?a <---> ?a')
    =>
    lazy_match! goal with
    | [ |- of_MyGoal (@mkMyGoal ?sgm ?g ?l ?p)]
      => let hr : HeatResult := heat atn a p in
         if ml_debug_rewrite then
           Message.print (Message.of_constr (hr.(ctx_pat)))
         else () ;
         let heq := Control.hyp (hr.(equality)) in
         let pc := (hr.(pc)) in
         eapply (@cast_proof_mg_goal _ $g) >
           [ rewrite $heq; reflexivity | ()];
         Std.clear [hr.(equality)];
         apply (@MyGoal_rewriteIff $sgm $g _ _ $pc $l $hiff);
         lazy_match! goal with
         | [ |- of_MyGoal (@mkMyGoal ?sgm ?g ?l ?p)]
           =>
             let heq2 := Fresh.in_goal ident:(heq2) in
             let plugged := Pattern.instantiate (hr.(ctx)) a' in
             assert(heq2: ($p = $plugged))
             > [
                 abstract (ltac1:(star |- simplify_emplace_2 star) (Ltac1.of_ident (hr.(star_ident)));
                 reflexivity
                 )
               | ()
               ];
             let heq2_pf := Control.hyp heq2 in
             eapply (@cast_proof_mg_goal _ $g) >
               [ rewrite $heq2_pf; reflexivity | ()];
             Std.clear [heq2 ; (hr.(star_ident))]
         end
    end
  end.

Ltac2 rec constr_to_int (x : constr) : int :=
  match! x with
  | 0 => 0
  | (S ?x') => Int.add 1 (constr_to_int x')
  end.


Tactic Notation "mgRewrite" constr(Hiff) "at" constr(atn) :=
  (let ff := ltac2:(hiff atn |-
                      mgRewrite
                        (Option.get (Ltac1.to_constr(hiff)))
                        (constr_to_int (Option.get (Ltac1.to_constr(atn))))
                   ) in
   ff Hiff atn).

Lemma pf_iff_equiv_sym_nowf {Σ : Signature} Γ A B :
  Γ ⊢ (A <---> B) ->
  Γ ⊢ (B <---> A).
Proof.
  intros H.
  pose proof (wf := proved_impl_wf _ _ H).
  assert (well_formed A) by wf_auto2.
  assert (well_formed B) by wf_auto2.
  apply pf_iff_equiv_sym; assumption.
Defined.

Tactic Notation "mgRewrite" "->" constr(Hiff) "at" constr(atn) :=
  mgRewrite Hiff at atn.

Tactic Notation "mgRewrite" "<-" constr(Hiff) "at" constr(atn) :=
  mgRewrite (@pf_iff_equiv_sym_nowf _ _ _ _ Hiff) at atn.


Local Example ex_prf_rewrite_equiv_2 {Σ : Signature} Γ a a' b x:
  well_formed a ->
  well_formed a' ->
  well_formed b ->
  Γ ⊢ a <---> a' ->
  Γ ⊢ (a $ a $ b $ a ---> (patt_free_evar x)) <---> (a $ a' $ b $ a' ---> (patt_free_evar x)).
Proof.
  intros wfa wfa' wfb Hiff.
  toMyGoal.
  { abstract(wf_auto2). }
  mgRewrite Hiff at 2.
  mgRewrite <- Hiff at 3.
  fromMyGoal. intros _ _.
  apply pf_iff_equiv_refl; abstract(wf_auto2).
Defined.

Lemma top_holds {Σ : Signature} Γ:
  Γ ⊢ Top.
Proof.
  apply false_implies_everything.
  { wf_auto2. }
Defined.

Lemma phi_iff_phi_top {Σ : Signature} Γ ϕ :
  well_formed ϕ ->
  Γ ⊢ ϕ <---> (ϕ <---> Top).
Proof.
  intros wfϕ.
  toMyGoal.
  { wf_auto2. }
  mgSplitAnd; mgIntro.
  - mgSplitAnd.
    + mgIntro. mgClear 0. mgClear 0.
      fromMyGoal. intros _ _.
      apply top_holds. (* TODO: we need something like [mgExactMeta top_holds] *)
    + fromMyGoal. intros _ _.
      apply P1; wf_auto2.
  - mgDestructAnd 0.
    mgApply 1.
    mgClear 0.
    mgClear 0.
    fromMyGoal. intros _ _.
    apply top_holds.
Defined.

Lemma not_phi_iff_phi_bott {Σ : Signature} Γ ϕ :
  well_formed ϕ ->
  Γ ⊢ (! ϕ ) <---> (ϕ <---> ⊥).
Proof.
  intros wfϕ.
  toMyGoal.
  { wf_auto2. }
  mgSplitAnd; mgIntro.
  - mgSplitAnd.
    + mgExactn 0.
    + mgClear 0. fromMyGoal. intros _ _.
      apply false_implies_everything.
      { wf_auto2. }
  - mgDestructAnd 0.
    mgExactn 0.
Defined.


Lemma not_not_iff {Σ : Signature} (Γ : Theory) (A : Pattern) :
  well_formed A ->
  Γ ⊢ A <---> ! ! A.
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

(* prenex-exists-and-left *)
Lemma prenex_exists_and_1 {Σ : Signature} (Γ : Theory) ϕ₁ ϕ₂:
  well_formed (ex, ϕ₁) ->
  well_formed ϕ₂ ->
  Γ ⊢ ((ex, ϕ₁) and ϕ₂) ---> (ex, (ϕ₁ and ϕ₂)).
Proof.
  intros wfϕ₁ wfϕ₂.
  toMyGoal.
  { wf_auto2. }
  mgIntro. mgDestructAnd 0.
  fromMyGoal. intros _ _.

  remember (fresh_evar (ϕ₂ ---> (ex, (ϕ₁ and ϕ₂)))) as x.
  apply strip_exists_quantify_l with (x0 := x).
  { subst x. eapply evar_is_fresh_in_richer'.
    2: { apply set_evar_fresh_is_fresh'. }
    simpl. clear. set_solver.
  }
  { wf_auto2. }
  apply Ex_gen.
  { wf_auto2. }
  { wf_auto2. }
  2: { subst x. apply set_evar_fresh_is_fresh. }
  
  apply lhs_to_and.
  { wf_auto2. }
  { wf_auto2. }
  { wf_auto2. }

  eapply cast_proof.
  {
    replace (evar_open 0 x ϕ₁ and ϕ₂)
            with (evar_open 0 x (ϕ₁ and ϕ₂)).
    2: {
      unfold evar_open. simpl_bevar_subst.
      rewrite [bevar_subst ϕ₂ _ _]bevar_subst_not_occur.
      { apply wfc_ex_implies_not_bevar_occur.
        wf_auto2.
      }
      reflexivity.
    }
    reflexivity.
  }
  apply Ex_quan.
  wf_auto2.
Defined.

(* prenex-exists-and-right *)
Lemma prenex_exists_and_2 {Σ : Signature} (Γ : Theory) ϕ₁ ϕ₂:
  well_formed (ex, ϕ₁) ->
  well_formed ϕ₂ ->
  Γ ⊢ (ex, (ϕ₁ and ϕ₂)) ---> ((ex, ϕ₁) and ϕ₂).
Proof.
  intros wfϕ₁ wfϕ₂.
  toMyGoal.
  { wf_auto2. }
  mgIntro.
  mgSplitAnd.
  - fromMyGoal. intros _ _.
    remember (fresh_evar (ϕ₁ and ϕ₂)) as x.
    apply strip_exists_quantify_l with (x0 := x).
    { subst x. apply set_evar_fresh_is_fresh. }
    (* TODO: make wf_auto2 solve this *)
    { simpl. rewrite !andbT. split_and!.
      + wf_auto2.
      + wf_auto2.
    }
    apply strip_exists_quantify_r with (x0 := x).
    { subst x. eapply evar_is_fresh_in_richer'.
      2: { apply set_evar_fresh_is_fresh'. }
      simpl. clear. set_solver.
    }
    { wf_auto2. }
    apply ex_quan_monotone.
    { wf_auto2. }
    { wf_auto2. }
    unfold evar_open. simpl_bevar_subst.
    rewrite [bevar_subst ϕ₂ _ _]bevar_subst_not_occur.
    { apply wfc_ex_aux_implies_not_bevar_occur.
      wf_auto2.
    }
    toMyGoal.
    { wf_auto2. }
    mgIntro. mgDestructAnd 0. mgExactn 0.
  - fromMyGoal. intros _ _.
    remember (fresh_evar (ϕ₁ and ϕ₂)) as x.
    eapply cast_proof.
    {
      rewrite -[ϕ₁ and ϕ₂](@evar_quantify_evar_open Σ x 0).
      { subst x. apply set_evar_fresh_is_fresh. }
      reflexivity.
    }
    apply Ex_gen.
    { wf_auto2. }
    { wf_auto2. }
    2: { subst x. eapply evar_is_fresh_in_richer'.
         2: { apply set_evar_fresh_is_fresh. }
         solve_free_evars_inclusion 0.
    }
    unfold evar_open.
    simpl_bevar_subst.
    rewrite [bevar_subst ϕ₂ _ _]bevar_subst_not_occur.
    { apply wfc_ex_implies_not_bevar_occur.
      wf_auto2.
    }
    toMyGoal.
    { wf_auto2. }
    mgIntro.
    mgDestructAnd 0.
    mgExactn 1.
Defined.

Lemma prenex_exists_and_iff {Σ : Signature} (Γ : Theory) ϕ₁ ϕ₂:
  well_formed (ex, ϕ₁) ->
  well_formed ϕ₂ ->
  Γ ⊢ (ex, (ϕ₁ and ϕ₂)) <---> ((ex, ϕ₁) and ϕ₂).
Proof.
  intros wfϕ₁ wfϕ₂.
  apply conj_intro_meta.
  { wf_auto2. }
  { wf_auto2. }
  - apply prenex_exists_and_2; assumption.
  - apply prenex_exists_and_1; assumption.
Defined.

Lemma patt_and_comm {Σ : Signature} Γ p q:
  well_formed p ->
  well_formed q ->
  Γ ⊢ (p and q) <---> (q and p).
Proof.
  intros wfp wfq.
  toMyGoal.
  { wf_auto2. }
  mgSplitAnd; mgIntro; mgDestructAnd 0; mgSplitAnd.
  - mgExactn 1.
  - mgExactn 0.
  - mgExactn 1.
  - mgExactn 0.
Defined.

(* We need to come up with tactics that make this easier. *)
Local Example ex_mt {Σ : Signature} Γ ϕ₁ ϕ₂:
  well_formed ϕ₁ ->
  well_formed ϕ₂ ->
  Γ ⊢ (! ϕ₁ ---> ! ϕ₂) ---> (ϕ₂ ---> ϕ₁).
Proof.
  intros wfϕ₁ wfϕ₂.
  toMyGoal.
  { wf_auto2. }
  mgIntro. mgIntro.
  unfold patt_not.
  mgAssert (((ϕ₁ ---> ⊥) ---> ⊥)).
  { wf_auto2. }
  { mgIntro. Check modus_ponens.
    mgAssert ((ϕ₂ ---> ⊥)).
    { wf_auto2. }
    { mgApply 0. mgExactn 2. }
    mgApply 3.
    mgExactn 1.
  }
  mgApplyMeta (@not_not_elim Σ Γ ϕ₁ ltac:(wf_auto2)).
  mgExactn 2.
Defined.

Lemma well_formed_foldr_and {Σ : Signature} (x : Pattern) (xs : list Pattern):
  well_formed x ->
  wf xs ->
  well_formed (foldr patt_and x xs).
Proof.
  intros wfx wfxs.
  induction xs; simpl.
  - assumption.
  - feed specialize IHxs.
    { unfold wf in wfxs. simpl in wfxs. destruct_and!. assumption. }
    apply well_formed_and.
    { unfold wf in wfxs. simpl in wfxs. destruct_and!. assumption. }
    assumption.
Qed.


Lemma lhs_and_to_imp {Σ : Signature} Γ (g x : Pattern) (xs : list Pattern):
  well_formed g ->
  well_formed x ->
  wf xs ->
  Γ ⊢ (foldr patt_and x xs ---> g) ---> (foldr patt_imp g (x :: xs)).
Proof.
  intros wfg wfx wfxs.
  induction xs; simpl.
  - apply A_impl_A.
    { wf_auto2. }
  - pose proof (wfaxs := wfxs).
    unfold wf in wfxs.
    simpl in wfxs.
    apply andb_prop in wfxs as [wfa wfxs].
    fold (wf xs) in wfxs.
    specialize (IHxs wfxs).
    simpl in IHxs.
    assert (Hwffa: well_formed (foldr patt_and x xs)).
    { apply well_formed_foldr_and; assumption. }
    toMyGoal.
    { wf_auto2. }
    do 3 mgIntro.
    mgAdd IHxs.
    mgAssert (((foldr patt_and x xs ---> g) ---> foldr patt_imp g xs)).
    { wf_auto2. }
    { mgIntro.
      mgAssert ((x ---> foldr patt_imp g xs)).
      { wf_auto2. }
      { mgApply 0. mgExactn 4. }
      mgClear 0.
      mgApply 4.
      mgExactn 1.
    }
    mgClear 0.
    mgApply 3.
    mgClear 3.
    mgIntro.
    mgApply 0.
    mgSplitAnd.
    + mgExactn 2.
    + mgExactn 3.
Defined.

Lemma lhs_and_to_imp_meta {Σ : Signature} Γ (g x : Pattern) (xs : list Pattern):
  well_formed g ->
  well_formed x ->
  wf xs ->
  Γ ⊢ (foldr patt_and x xs ---> g) ->
  Γ ⊢ (foldr patt_imp g (x :: xs)).
Proof.
  intros wfg wfx wfxs H.
  eapply Modus_ponens.
  4: apply lhs_and_to_imp.
  all: try assumption.
  { apply proved_impl_wf in H. exact H. }
  { apply proved_impl_wf in H. wf_auto2. }
Defined.



Lemma lhs_and_to_imp_r {Σ : Signature} Γ (g x : Pattern) (xs : list Pattern):
  well_formed g ->
  well_formed x ->
  wf xs ->
  forall (r : ImpReshapeS g (x::xs)),
     Γ ⊢ ((foldr (patt_and) x xs) ---> g) ->
     Γ ⊢ untagPattern (irs_flattened r) .
Proof.
  intros wfg wfx wfxs r H.
  eapply cast_proof.
  { rewrite irs_pf; reflexivity. }
  clear r.
  apply lhs_and_to_imp_meta; assumption.
Defined.


Local Example ex_match {Σ : Signature} Γ a b c d:
  well_formed a ->
  well_formed b ->
  well_formed c ->
  well_formed d ->
  Γ ⊢ a ---> (b ---> (c ---> d)).
Proof.
  intros wfa wfb wfc wfd.
  apply lhs_and_to_imp_r.
Abort.

Lemma forall_gen {Σ : Signature} Γ ϕ₁ ϕ₂ x:
  evar_is_fresh_in x ϕ₁ ->
  Γ ⊢ ϕ₁ ---> ϕ₂ ->
  Γ ⊢ ϕ₁ ---> all, (evar_quantify x 0 ϕ₂).
Proof.
  intros Hfr Himp.
  pose proof (Hwf := proved_impl_wf _ _ Himp).
  pose proof (wfϕ₁ := well_formed_imp_proj1 Hwf).
  pose proof (wfϕ₂ := well_formed_imp_proj2 Hwf).
  toMyGoal.
  { wf_auto2. }
  mgIntro.
  mgApplyMeta (@not_not_intro Σ Γ ϕ₁ ltac:(wf_auto2)) in 0.
  fromMyGoal. intros _ _.
  apply modus_tollens.
  { wf_auto2. }
  { wf_auto2. }

  eapply cast_proof.
  {
    replace (! evar_quantify x 0 ϕ₂)
            with (evar_quantify x 0 (! ϕ₂))
                 by reflexivity.
    reflexivity.
  }
  apply Ex_gen.
  { wf_auto2. }
  { wf_auto2. }
  2: { simpl. unfold evar_is_fresh_in in Hfr. clear -Hfr. set_solver. }
  apply modus_tollens; assumption.
Defined.

Lemma forall_elim {Σ : Signature} Γ ϕ x:
  well_formed (ex, ϕ) ->
  evar_is_fresh_in x ϕ ->
  Γ ⊢ (all, ϕ) ->
  Γ ⊢ (evar_open 0 x ϕ).
Proof.
  intros wfϕ frϕ H.
  eapply Modus_ponens.
  4: apply (@forall_variable_substitution Σ Γ _ x).
  { wf_auto2. }
  { wf_auto2. }
  2: { wf_auto2. }
  rewrite evar_quantify_evar_open; assumption.
Defined.

Lemma prenex_forall_imp {Σ : Signature} Γ ϕ₁ ϕ₂:
  well_formed (ex, ϕ₁) ->
  well_formed ϕ₂ ->
  Γ ⊢ (all, (ϕ₁ ---> ϕ₂)) ->
  Γ ⊢ (ex, ϕ₁) ---> (ϕ₂).
Proof.
  intros wfϕ₁ wfϕ₂ H.
  remember (fresh_evar (ϕ₁ ---> ϕ₂)) as x.
  apply (@strip_exists_quantify_l Σ Γ x).
  { subst x.
    eapply evar_is_fresh_in_richer'.
    2: { apply set_evar_fresh_is_fresh'. }
    simpl. set_solver.
  }
  { wf_auto2. }
  apply Ex_gen.
  1,2: wf_auto2.
  2: {
    subst x.
    eapply evar_is_fresh_in_richer'.
    2: { apply set_evar_fresh_is_fresh'. }
    simpl. set_solver.
  }

  eapply cast_proof.
  {
    rewrite -[HERE in evar_open _ _ _ ---> HERE](@evar_open_not_occur Σ 0 x ϕ₂).
    {
      apply wfc_ex_aux_implies_not_bevar_occur.
      wf_auto2.
    }
    reflexivity.
  }
  eapply forall_elim with (x0 := x) in H.
  2: wf_auto2.
  2: { subst x. apply set_evar_fresh_is_fresh. }
  unfold evar_open in *. simpl in *. exact H.
Defined.

Lemma evar_fresh_in_foldr {Σ : Signature} x g l:
  evar_is_fresh_in x (foldr patt_imp g l) <-> evar_is_fresh_in x g /\ evar_is_fresh_in_list x l.
Proof.
  induction l; simpl; split; intros H.
  - split;[assumption|]. unfold evar_is_fresh_in_list. apply Forall_nil. exact I.
  - destruct H as [H _]. exact H.
  - unfold evar_is_fresh_in_list,evar_is_fresh_in in *. simpl in *.
    split;[set_solver|].
    apply Forall_cons.
    destruct IHl as [IHl1 IHl2].
    split;[set_solver|].
    apply IHl1. set_solver.
  - unfold evar_is_fresh_in_list,evar_is_fresh_in in *. simpl in *.
    destruct IHl as [IHl1 IHl2].
    destruct H as [H1 H2].
    inversion H2; subst.
    specialize (IHl2 (conj H1 H4)).
    set_solver.
Qed.

Lemma Ex_gen_lifted {Σ : Signature} (Γ : Theory) (ϕ₁ : Pattern) (l : list Pattern) (g : Pattern) (x : evar):
  evar_is_fresh_in x g ->
  evar_is_fresh_in_list x l ->
  bevar_occur ϕ₁ 0 = false ->
  @mkMyGoal Σ Γ (ϕ₁::l) g -> 
 @mkMyGoal Σ Γ ((exists_quantify x ϕ₁)::l) g.
Proof.
  intros xfrg xfrl Hno0 H.
  mgExtractWF H1 H2.
  fromMyGoal. intros _ _.
  pose proof (H1' := H1).
  unfold wf in H1. simpl in H1. apply andb_prop in H1. destruct H1 as [H11 H12].
  apply wf_ex_quan_impl_wf in H11. 2: assumption.
  unfold of_MyGoal in H. simpl in H.
  specialize (H H2).
  feed specialize H.
  {
    unfold wf. simpl. rewrite H11 H12. reflexivity.
  }
  apply Ex_gen.
  { wf_auto2. }
  { wf_auto2. }
  { assumption. }
  simpl.
  apply evar_fresh_in_foldr.
  split; assumption.
Defined.

(* Weakening under existential *)
Local Example ex_exists {Σ : Signature} Γ ϕ₁ ϕ₂ ϕ₃:
  well_formed (ex, ϕ₁) ->
  well_formed (ex, ϕ₂) ->
  well_formed ϕ₃ ->
  Γ ⊢ (all, (ϕ₁ and ϕ₃ ---> ϕ₂)) ->
  Γ ⊢ (ex, ϕ₁) ---> ϕ₃ ---> (ex, ϕ₂).
Proof.
  intros wfϕ₁ wfϕ₂ wfϕ₃ H.
  toMyGoal.
  { wf_auto2. }
  mgIntro.
  remember (evar_fresh (elements (free_evars ϕ₁ ∪ free_evars ϕ₂ ∪ free_evars (ex, ϕ₃)))) as x.
  rewrite -[ϕ₁](@evar_quantify_evar_open Σ x 0).
  { subst x.
    eapply evar_is_fresh_in_richer'. 2: apply set_evar_fresh_is_fresh'. clear. set_solver.
  }
  mgIntro.
  apply Ex_gen_lifted.
  { subst x. eapply evar_is_fresh_in_richer'. 2: apply set_evar_fresh_is_fresh'. clear. set_solver. }
  { constructor. 2: apply Forall_nil; exact I.
    subst x.
    eapply evar_is_fresh_in_richer'. 2: apply set_evar_fresh_is_fresh'. clear. set_solver.
  }
  { apply bevar_occur_evar_open_2. }

Abort.

(* This is an example and belongs to the end of this file.
   Its only purpose is only to show as many tactics as possible.\
 *)
   Lemma ex_and_of_equiv_is_equiv_2 {Σ : Signature} Γ p q p' q':
    well_formed p ->
    well_formed q ->
    well_formed p' ->
    well_formed q' ->
    Γ ⊢ (p <---> p') ->
    Γ ⊢ (q <---> q') ->
    Γ ⊢ ((p and q) <---> (p' and q')).
  Proof.
    intros wfp wfq wfp' wfq' pep' qeq'.
    pose proof (pip' := pep'). apply pf_conj_elim_l_meta in pip'; auto.
    pose proof (p'ip := pep'). apply pf_conj_elim_r_meta in p'ip; auto.
    pose proof (qiq' := qeq'). apply pf_conj_elim_l_meta in qiq'; auto.
    pose proof (q'iq := qeq'). apply pf_conj_elim_r_meta in q'iq; auto.

    toMyGoal.
    { wf_auto2. }
    unfold patt_iff.
    mgSplitAnd.
    - mgIntro.
      mgDestructAnd 0.
      mgSplitAnd.
      + mgApplyMeta pip'.
        mgExactn 0.
      + mgApplyMeta qiq' in 1.
        mgExactn 1.
    - mgIntro.
      unfold patt_and at 2.
      unfold patt_not at 1.
      mgIntro.
      mgDestructOr 1.
      + mgDestructAnd 0.
        unfold patt_not.
        mgApply 2.
        mgClear 2.
        mgClear 1.
        fromMyGoal. intros _ _.
        exact p'ip.
      + mgAdd q'iq.
        mgDestructAnd 1.
        mgAssert (q).
        { wf_auto2. }
        { mgApply 0. mgExactn 2. }
        unfold patt_not at 1.
        mgApply 3.
        mgExactn 4.
  Defined.

  Lemma ex_or_of_equiv_is_equiv_2 {Σ : Signature} Γ p q p' q':
    well_formed p ->
    well_formed q ->
    well_formed p' ->
    well_formed q' ->
    Γ ⊢ (p <---> p') ->
    Γ ⊢ (q <---> q') ->
    Γ ⊢ ((p or q) <---> (p' or q')).
  Proof.
    intros wfp wfq wfp' wfq' pep' qeq'.

    pose proof (pip' := pep'). apply pf_conj_elim_l_meta in pip'; auto.
    pose proof (p'ip := pep'). apply pf_conj_elim_r_meta in p'ip; auto.
    pose proof (qiq' := qeq'). apply pf_conj_elim_l_meta in qiq'; auto.
    pose proof (q'iq := qeq'). apply pf_conj_elim_r_meta in q'iq; auto.

    toMyGoal.
    { wf_auto2. }
    unfold patt_iff.
    mgSplitAnd.
    - mgIntro.
      mgDestructOr 0.
      mgLeft.
      + mgApplyMeta pip'.
        mgExactn 0.
      + mgRight.
        mgApplyMeta qiq'.
        mgExactn 0.
    - mgIntro.
      mgDestructOr 0.
      mgLeft.
      + mgApplyMeta p'ip.
        mgExactn 0.
      + mgRight.
        mgApplyMeta q'iq.
        mgExactn 0. 
  Defined.
