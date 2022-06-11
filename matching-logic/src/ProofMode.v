From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Ltac2 Require Import Ltac2.

From Coq Require Import Ensembles Bool.
From Coq.Logic Require Import FunctionalExtensionality Eqdep_dec.
From Equations Require Import Equations.

Require Import Coq.Program.Tactics.

From MatchingLogic Require Import Syntax DerivedOperators_Syntax ProofSystem IndexManipulation wftactics.

From stdpp Require Import list tactics fin_sets.

From MatchingLogic.Utils Require Import stdpp_ext.

Import extralibrary.

Import
  MatchingLogic.Syntax.Notations
  MatchingLogic.DerivedOperators_Syntax.Notations
  MatchingLogic.ProofSystem.Notations
.

Set Default Proof Mode "Classic".

Open Scope ml_scope.


Record GenericProofInfo {Σ : Signature} :=
  mkGenericProofInfo
  {
    pi_generalized_evars : EVarSet ;
    pi_substituted_svars : SVarSet ;
    pi_uses_kt : bool ;
  }.

Notation "'ExGen' ':=' evs ',' 'SVSubst' := svs ',' 'KT' := bkt"
  := (@mkGenericProofInfo _ evs svs bkt) (at level 95, no associativity).

Inductive ProofInfo {Σ : Signature} := pi_Propositional | pi_Generic (gpi : GenericProofInfo).

(* A proof together with some properties of it. *)
Record ProofInfoMeaning
  {Σ : Signature}
  (Γ : Theory)
  (ϕ : Pattern)
  (pwi_pf : Γ ⊢ ϕ)
  (pi : ProofInfo)
  : Prop
  :=
mkProofInfoMeaning
{
  pwi_pf_prop : if pi is pi_Propositional then @propositional_only Σ Γ ϕ pwi_pf = true else True ;
  pwi_pf_ge : @uses_of_ex_gen Σ Γ ϕ pwi_pf ⊆ (if pi is (pi_Generic pi') then pi_generalized_evars pi' else ∅) ;
  pwi_pf_svs : @uses_of_svar_subst Σ Γ ϕ pwi_pf ⊆ (if pi is (pi_Generic pi') then pi_substituted_svars pi' else ∅) ;
  pwi_pf_kt : implb (@uses_kt Σ Γ ϕ pwi_pf) (if pi is (pi_Generic pi') then pi_uses_kt pi' else false) ;
}.

Class ProofInfoLe {Σ : Signature} (i₁ i₂ : ProofInfo) :=
{ pi_le :
  forall (Γ : Theory) (ϕ : Pattern) (pf : Γ ⊢ ϕ),
    @ProofInfoMeaning Σ Γ ϕ pf i₁ -> @ProofInfoMeaning Σ Γ ϕ pf i₂ ;
}.

(*
#[global]
Instance
*)
Lemma pile_refl {Σ : Signature} (i : ProofInfo) : ProofInfoLe i i.
Proof.
  constructor. intros Γ ϕ pf H. exact H.
Qed.

(*
#[global]
Instance
*)
Lemma pile_trans {Σ : Signature}
  (i₁ i₂ i₃ : ProofInfo) (PILE12 : ProofInfoLe i₁ i₂) (PILE23 : ProofInfoLe i₂ i₃)
: ProofInfoLe i₁ i₃.
Proof.
  destruct PILE12 as [PILE12].
  destruct PILE23 as [PILE23].
  constructor. intros Γ ϕ pf.
  specialize (PILE12 Γ ϕ pf).
  specialize (PILE23 Γ ϕ pf).
  tauto.
Qed.

Definition PropositionalReasoning {Σ} : ProofInfo := @pi_Propositional Σ.
Definition BasicReasoning {Σ} : ProofInfo := (pi_Generic (@mkGenericProofInfo Σ ∅ ∅ false)).


Lemma propositional_pi
  {Σ : Signature}
  (Γ : Theory)
  (ϕ : Pattern)
  (pf : Γ ⊢ ϕ)
  :
  propositional_only Γ ϕ pf = true ->
  @ProofInfoMeaning Σ Γ ϕ pf PropositionalReasoning.
Proof.
  intros H.
  split; simpl.
  { exact H. }
  { rewrite propositional_implies_no_uses_ex_gen_2;[exact H|]. set_solver. }
  { rewrite propositional_implies_no_uses_svar_2;[exact H|]. set_solver. }
  { rewrite propositional_implies_noKT;[exact H|]. reflexivity. }
Qed.

(*
#[global]
Instance
*)
Lemma pile_prop {Σ : Signature} (i : ProofInfo) : ProofInfoLe PropositionalReasoning i.
Proof.
  constructor.
  intros Γ ϕ pf Hpf.
  destruct i.
  { apply Hpf. }
  { destruct gpi; simpl;
    destruct Hpf; simpl in *;
    constructor; simpl;
    [(exact I)
    |(set_solver)
    |(set_solver)
    |(destruct (uses_kt pf); simpl in *; try congruence)
    ].
  }
Qed.

(* Originally, the notation was defined like this: *)
(*
Notation "Γ ⊢ ϕ 'using' pi"
:= (@ProofWithInfo _ Γ ϕ pi) (at level 95, no associativity).
*)
(* However, this overlaps with the old notation [Γ ⊢ ϕ] and makes it unusable alone.*)

Notation "G 'using' pi"
:= ({pf : G | @ProofInfoMeaning _ _ _ pf pi }) (at level 95, no associativity).


Record MyGoal {Σ : Signature} : Type := mkMyGoal
  { mgTheory : Theory;
    mgHypotheses: list Pattern;
    mgConclusion : Pattern ;
    mgInfo : ProofInfo ;
  }.

Definition MyGoal_from_goal
  {Σ : Signature} (Γ : Theory) (goal : Pattern) (pi : ProofInfo)
  :
  MyGoal
  := @mkMyGoal Σ Γ nil goal pi.

Coercion of_MyGoal {Σ : Signature} (MG : MyGoal) : Type :=
  well_formed (mgConclusion MG) ->
  wf (mgHypotheses MG) ->
  (mgTheory MG) ⊢ (fold_right patt_imp (mgConclusion MG) (mgHypotheses MG))
  using (mgInfo MG).

  (* This is useful only for printing. *)
  Notation "[ S , G ⊢ l ==> g ]  'using' pi "
  := (@mkMyGoal S G l g pi) (at level 95, no associativity, only printing).


Ltac toMyGoal :=
  lazymatch goal with
  | [ |- ?G ⊢ ?phi using ?pi]
    => cut (of_MyGoal (MyGoal_from_goal G phi pi));
       unfold MyGoal_from_goal;
       [(unfold of_MyGoal; simpl; let H := fresh "H" in intros H; apply H; clear H; [|reflexivity])|]
  end.

Ltac fromMyGoal := unfold of_MyGoal; simpl; intros _ _.

Section FOL_helpers.

  Context {Σ : Signature}.


  Lemma A_impl_A (Γ : Theory) (A : Pattern)  :
    (well_formed A) ->
    Γ ⊢ (A ---> A)
    using PropositionalReasoning.
  Proof. 
    intros WFA.
    pose (_1 := P2 Γ A (A ---> A) A ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2)).
    pose (_2 := P1 Γ A (A ---> A) ltac:(wf_auto2) ltac:(wf_auto2)).
    pose (_3 := Modus_ponens _ _ _ _2 _1).
    pose (_4 := P1 Γ A A ltac:(wf_auto2) ltac:(wf_auto2)).
    pose (_5 := Modus_ponens Γ _ _ _4 _3).
    exists _5.
    apply propositional_pi. reflexivity.
  Defined.

  Lemma P4m (Γ : Theory) (A B : Pattern) :
    well_formed A ->
    well_formed B ->
    Γ ⊢ ((A ---> B) ---> ((A ---> !B) ---> !A))
    using PropositionalReasoning.
  Proof.
    intros WFA WFB.
    pose (H1 := P2 Γ A B Bot ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2)).
    pose (H2 := (P2 Γ (A ---> B ---> Bot) (A ---> B) (A ---> Bot) ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2))).
    pose (H3 := Modus_ponens _ _ _ H1 H2).
    pose (H4 := (P1 Γ (((A ---> B ---> Bot) ---> A ---> B) ---> (A ---> B ---> Bot) ---> A ---> Bot)
      (A ---> B) ltac:(wf_auto2) ltac:(wf_auto2))).
    pose (H5 := Modus_ponens _ _ _ H3 H4).
    pose (H6 := (P2 Γ (A ---> B) ((A ---> B ---> Bot) ---> A ---> B) ((A ---> B ---> Bot) ---> A ---> Bot)
      ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2))).
    pose (H7 := Modus_ponens _ _ _ H5 H6).
    pose (H8 := (P1 Γ (A ---> B) (A ---> B ---> Bot) ltac:(wf_auto2) ltac:(wf_auto2))).
    pose (H9 := Modus_ponens _ _ _ H8 H7).
    exists H9.
    apply propositional_pi. reflexivity.
  Defined.

  Lemma P1 (Γ : Theory) (ϕ ψ : Pattern) :
    well_formed ϕ ->
    well_formed ψ ->
    Γ ⊢ ϕ ---> ψ ---> ϕ 
    using PropositionalReasoning.
  Proof.
    intros wfϕ wfψ.
    unshelve (eexists).
    { apply ProofSystem.P1. exact wfϕ. exact wfψ. }
    { abstract (
        (constructor; simpl;[(reflexivity)|(set_solver)|(set_solver)|(reflexivity)])
      ).
    }
  Defined.

  Lemma P2 (Γ : Theory) (ϕ ψ ξ : Pattern) :
    well_formed ϕ ->
    well_formed ψ ->
    well_formed ξ ->
    Γ ⊢ (ϕ ---> ψ ---> ξ) ---> (ϕ ---> ψ) ---> (ϕ ---> ξ)
    using PropositionalReasoning.
  Proof.
    intros wfϕ wfψ wfξ.
    unshelve (eexists).
    { apply ProofSystem.P2. exact wfϕ. exact wfψ. exact wfξ. }
    { abstract (
        (constructor; simpl;[(reflexivity)|(set_solver)|(set_solver)|(reflexivity)])
      ).
    }
  Defined.

  Lemma P3 (Γ : Theory) (ϕ : Pattern) :
    well_formed ϕ ->
    Γ ⊢ (((ϕ ---> ⊥) ---> ⊥) ---> ϕ)
    using PropositionalReasoning.
  Proof.
    intros wfϕ.
    unshelve (eexists).
    { apply ProofSystem.P3. exact wfϕ. }
    { abstract (
        (constructor; simpl;[(reflexivity)|(set_solver)|(set_solver)|(reflexivity)])
      ).
    }
  Defined.

  Lemma MP (Γ : Theory) (ϕ₁ ϕ₂ : Pattern) (i : ProofInfo) :
    Γ ⊢ ϕ₁ using i ->
    Γ ⊢ (ϕ₁ ---> ϕ₂) using i ->
    Γ ⊢ ϕ₂ using i.
  Proof.
    intros H1 H2.
    unshelve (eexists).
    {
      eapply (Modus_ponens _ _ _).
      { apply H1. }
      { apply H2. }
    }
    {
      abstract(
      simpl;
      destruct H1 as [pf1 Hpf1];
      destruct H2 as [pf2 Hpf2];
      destruct Hpf1,Hpf2;
      destruct i;
      [(
        constructor;
        [(simpl; rewrite pwi_pf_prop0; rewrite pwi_pf_prop1; reflexivity)
        | (simpl; set_solver)
        | (simpl; set_solver)
        | (simpl; destruct (uses_kt pf1),(uses_kt pf2); simpl in *; congruence)
        ]
      )|(
        constructor;
        [(exact I)
        | (simpl; set_solver)
        | (simpl; set_solver)
        | (simpl; destruct (uses_kt pf1),(uses_kt pf2); simpl in *; congruence)
        ]
      )]).
    }
  Defined.

  Arguments P1 _ (_%ml) (_%ml) _ _ : clear implicits.
  Arguments P2 _ (_%ml) (_%ml) (_%ml) _ _ _ : clear implicits.
  Arguments P3 _ (_%ml) _ : clear implicits.


  Lemma P4i (Γ : Theory) (A : Pattern) :
    well_formed A ->
    Γ ⊢ ((A ---> !A) ---> !A)
    using PropositionalReasoning.
  Proof.
    intros WFA.
    eapply MP.
    { apply (@A_impl_A _ A WFA). }
    { apply (@P4m _ A A WFA WFA). }
  Defined.

  Lemma reorder (Γ : Theory) (A B C : Pattern) :
    well_formed A ->
    well_formed B ->
    well_formed C ->
    Γ ⊢ ((A ---> B ---> C) ---> ( B ---> A ---> C))
    using PropositionalReasoning.
  Proof.
    intros WFA WFB WFC.
   
    pose (t1 := (MP
                    (P1 Γ ((A ---> B) ---> A ---> C) B ltac:(wf_auto2) ltac:(wf_auto2))
                    (P1 Γ (((A ---> B) ---> A ---> C) ---> B ---> (A ---> B) ---> A ---> C) (A ---> B ---> C) ltac:(wf_auto2) ltac:(wf_auto2)))).
  
    pose(ABC := (A ---> B ---> C)).
    
    eapply MP.
    - eapply MP.
      + apply(P1 _ B A ltac:(wf_auto2) ltac:(wf_auto2)).
      + apply(P1 _ (B ---> A ---> B) (A ---> B ---> C) ltac:(wf_auto2) ltac:(wf_auto2)).
    - eapply MP.
      + eapply MP.
        * eapply MP.
          -- eapply MP.
             ++ apply (@A_impl_A _ ABC ltac:(wf_auto2)).
             ++ eapply MP.
                ** eapply MP.
                   --- apply(P2 _ A B C ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2)).
                   --- unshelve (eapply(P1 _ _ (A ---> B ---> C) _ _)); wf_auto2.
                ** apply P2; wf_auto2.
          -- eapply MP.
             ++ apply t1.
             ++ apply(P2 _ ABC ((A ---> B) ---> (A ---> C)) (B ---> (A ---> B) ---> (A ---> C)) ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2)).
        * eapply MP.
          -- eapply MP.
             ++ apply(P2 _ B (A ---> B) (A ---> C) ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2)).
             ++ apply(P1 _ _ ABC); wf_auto2.
          -- apply P2; wf_auto2.
      + apply P2; wf_auto2.
  Defined.

  Lemma liftPi (Γ : Theory) (ϕ : Pattern) (i₁ i₂ : ProofInfo)
    {pile : ProofInfoLe i₁ i₂}
    :
    Γ ⊢ ϕ using i₁ ->
    Γ ⊢ ϕ using i₂.
  Proof.
      intros [pf Hpf].
      apply pile in Hpf.
      exists pf.
      exact Hpf.
  Qed.


  (* This lemma is the reason why we could make P1,P2,P3 specialized to PropositionalReasoning *)
  Lemma usePropositionalReasoning (Γ : Theory) (ϕ : Pattern) (i : ProofInfo) :
    Γ ⊢ ϕ using PropositionalReasoning ->
    Γ ⊢ ϕ using i.
  Proof.
    intros [pf Hpf].
    exists pf.
    (* [abstract] does not really work here *)
    abstract(
    destruct i;
    [(unfold PropositionalReasoning in Hpf; simpl in Hpf; apply Hpf)
    |(destruct gpi; simpl;
      destruct Hpf; simpl in *;
      constructor; simpl;
      [(exact I)
      |(set_solver)
      |(set_solver)
      |(destruct (uses_kt pf); simpl in *; try congruence)
      ]
    )]).
  Qed.

  Lemma reorder_meta (Γ : Theory) (A B C : Pattern) (i : ProofInfo) :
    well_formed A ->
    well_formed B ->
    well_formed C ->  
    Γ ⊢ (A ---> B ---> C) using i ->
    Γ ⊢ (B ---> A ---> C) using i.
  Proof.
    intros H H0 H1 H2.
    eapply MP. apply H2.
    apply usePropositionalReasoning.
    apply reorder; wf_auto2.
  Defined.

  Lemma syllogism (Γ : Theory) (A B C : Pattern) :
    well_formed A ->
    well_formed B ->
    well_formed C ->
    Γ ⊢ ((A ---> B) ---> (B ---> C) ---> (A ---> C))
    using PropositionalReasoning.
  Proof.
    intros WFA WFB WFC.
    apply reorder_meta;[wf_auto2|wf_auto2|wf_auto2|].
    eapply MP.
    - apply(P1 _ (B ---> C) A); wf_auto2.
    - eapply MP.
      + eapply MP.
        * apply (P2 _ A B C); wf_auto2.
        * apply (P1 _ ((A ---> B ---> C) ---> (A ---> B) ---> A ---> C) (B ---> C)); wf_auto2.
      + apply P2; wf_auto2.
  Defined.
  
  Lemma syllogism_meta (Γ : Theory) (A B C : Pattern) (i : ProofInfo) :
    well_formed A ->
    well_formed B ->
    well_formed C ->
    Γ ⊢ (A ---> B) using i ->
    Γ ⊢ (B ---> C) using i ->
    Γ ⊢ (A ---> C) using i.
  Proof.
    intros H H0 H1 H2 H3.
    eapply MP.
    - exact H2.
    - eapply MP.
      + exact H3.
      + apply reorder_meta;[wf_auto2|wf_auto2|wf_auto2|].
        apply usePropositionalReasoning.
        apply syllogism; wf_auto2.
  Defined.
  
  Lemma modus_ponens (Γ : Theory) (A B : Pattern) :
    well_formed A ->
    well_formed B ->
    Γ ⊢ (A ---> (A ---> B) ---> B)
    using PropositionalReasoning.
  Proof.
    intros WFA WFB.
    eapply MP.
    - apply (P1 _ A (A ---> B) ltac:(wf_auto2) ltac:(wf_auto2)).
    - eapply MP.
      + eapply MP.
        * apply (@A_impl_A _ (A ---> B) ltac:(wf_auto2)).
        * eapply (P2 _ (A ---> B) A B ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2)).
      + apply reorder_meta;[wf_auto2|wf_auto2|wf_auto2|].
        apply syllogism; wf_auto2.
  Defined.

  Lemma not_not_intro (Γ : Theory) (A : Pattern) :
    well_formed A ->
    Γ ⊢ (A ---> !(!A))
    using PropositionalReasoning.
  Proof.
    intros WFA.
    apply modus_ponens; wf_auto2.
  Defined.

  Lemma P4 (Γ : Theory) (A B : Pattern)  :
    well_formed A ->
    well_formed B -> 
    Γ ⊢ (((! A) ---> (! B)) ---> (B ---> A))
    using PropositionalReasoning.
  Proof.
    intros WFA WFB.
    pose proof (m := P3 Γ A ltac:(wf_auto2)).
    pose proof (m0 := P1 Γ (((A ---> Bot) ---> Bot) ---> A) B ltac:(wf_auto2) ltac:(wf_auto2)).
    pose proof (m1 := P2 Γ B ((A ---> Bot) ---> Bot) A ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2)).
    pose proof (m2 := MP m m0).
    pose proof (m3 := MP m2 m1).
    pose proof (m4 := P1 Γ ((B ---> (A ---> Bot) ---> Bot) ---> B ---> A) ((A ---> Bot) ---> (B ---> Bot)) ltac:(wf_auto2) ltac:(wf_auto2) ).
    pose proof (m5 := MP m3 m4).
    pose proof (m6 := P2 Γ ((A ---> Bot) ---> (B ---> Bot)) (B ---> (A ---> Bot) ---> Bot) (B ---> A) ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2)).
    pose proof (m7 := MP m5 m6).
    pose proof (m8 := @reorder Γ (A ---> Bot) (B) Bot ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2)).
    apply (MP m8 m7).
  Defined.

  Lemma conj_intro (Γ : Theory) (A B : Pattern) :
    well_formed A ->
    well_formed B ->
    Γ ⊢ (A ---> B ---> (A and B))
    using PropositionalReasoning.
  Proof.
    intros WFA WFB.
    pose proof (tB := (@A_impl_A Γ B ltac:(wf_auto2))).
    epose proof (t1 := MP (P2 _ (!(!A) ---> !B) A Bot ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2)) (P1 _ _ B _ _)).
    epose proof (t2 := MP (reorder_meta _ _ _ (@P4 _ (!A) B ltac:(wf_auto2) ltac:(wf_auto2))) (P1 _ _ B _ _)).
    epose proof (t3'' := MP (P1 _ A (!(!A) ---> !B) _ _) (P1 _ _ B _ _)).
    epose proof (t4 := MP tB (MP t2 (P2 _ B B _ _ _ _))).
    epose proof (t5'' := 
            MP t4
                         (MP t1
                                       (P2 _ B ((!(!A) ---> !B) ---> !A)
                                           (((!(!A) ---> !B) ---> A) ---> !(!(!A) ---> !B)) _ _ _))).
    
    epose proof (tA := (P1 Γ A B) _ _).
    epose proof (tB' := MP tB
                              (P1 _ (B ---> B) A _ _)).
    epose proof (t3' := MP t3''
                              (P2 _ B A ((!(!A) ---> !B) ---> A) _ _ _)).
    epose proof (t3 := MP t3'
                             (P1 _ ((B ---> A) ---> B ---> (! (! A) ---> ! B) ---> A) A _ _)).
    epose proof (t5' := MP t5''
                              (P2 _ B ((!(!A) ---> !B) ---> A) (!(!(!A) ---> !B)) _ _ _)).
    epose proof (t5 := MP t5' 
                             (P1 _ ((B ---> (! (! A) ---> ! B) ---> A) ---> B ---> ! (! (! A) ---> ! B))
                                 A _ _)).
    epose proof (t6 := MP tA
                             (MP t3
                                           (P2 _ A (B ---> A) (B ---> (!(!A) ---> !B) ---> A) _ _ _))).
    epose proof (t7 := MP t6 
                             (MP t5 
                                           (P2 _ A (B ---> (!(!A) ---> !B) ---> A) (B ---> !(!(!A) ---> !B)) _ _ _))).
    apply t7.
    Unshelve.
    all: wf_auto2.
  Defined.

  Lemma conj_intro_meta (Γ : Theory) (A B : Pattern) (i : ProofInfo) :
    well_formed A ->
    well_formed B ->
    Γ ⊢ A using i ->
    Γ ⊢ B using i ->
    Γ ⊢ (A and B) using i.
  Proof.
    intros WFA WFB H H0.
    eapply MP.
    - exact H0.
    - eapply MP.
      + exact H.
      + apply usePropositionalReasoning.
        apply conj_intro; wf_auto2.
  Defined.
  
  Lemma syllogism_4_meta (Γ : Theory) (A B C D : Pattern) (i : ProofInfo) :
    well_formed A ->
    well_formed B ->
    well_formed C ->
    well_formed D ->
    Γ ⊢ (A ---> B ---> C) using i ->
    Γ ⊢ (C ---> D) using i ->
    Γ ⊢ (A ---> B ---> D) using i.
  Proof.
    intros WFA WFB WFC WFD H H0.
    eapply MP.
    - exact H.
    - eapply MP.
      + eapply MP.
        * eapply MP.
          -- eapply MP.
             ++ exact H0.
             ++ apply usePropositionalReasoning. 
                eapply (P1 _ (C ---> D) B _ _).
          -- apply usePropositionalReasoning.  
              eapply (P2 _ B C D _ _ _).
        * apply usePropositionalReasoning. 
          eapply (P1 _ ((B ---> C) ---> B ---> D) A _ _).
      + apply usePropositionalReasoning. 
        eapply (P2 _ A (B ---> C) (B ---> D) _ _ _).
        Unshelve.
        all: wf_auto2.
  Defined.

  Lemma bot_elim (Γ : Theory) (A : Pattern) :
    well_formed A ->
    Γ ⊢ (Bot ---> A)
    using PropositionalReasoning.
  Proof.
    intros WFA.
    eapply MP.
    - eapply MP.
      + eapply MP.
        * eapply MP.
          -- eapply (P1 _ Bot Bot _ _).
          -- eapply (P2 _ Bot Bot Bot _ _ _).
        * eapply (@P4 _ Bot Bot _ _).
      + eapply (P1 _ (Bot ---> Bot) (A ---> Bot) _ _).
    - eapply (@P4 _ A Bot _ _).
      Unshelve.
      all: wf_auto2.
  Defined.

  Lemma modus_ponens' (Γ : Theory) (A B : Pattern) :
    well_formed A ->
    well_formed B ->
    Γ ⊢ (A ---> (!B ---> !A) ---> B)
    using PropositionalReasoning.
  Proof.
    intros WFA WFB.
    apply reorder_meta;[wf_auto2|wf_auto2|wf_auto2|].
    apply P4; wf_auto2.
  Defined.

  Lemma disj_right_intro (Γ : Theory) (A B : Pattern) :
    well_formed A ->
    well_formed B ->
    Γ ⊢ (B ---> (A or B))
    using PropositionalReasoning.
  Proof.
    intros WFA WFB.
    apply usePropositionalReasoning.
    apply P1; wf_auto2.
  Defined.
  
  Lemma disj_left_intro (Γ : Theory) (A B : Pattern) :
    well_formed A ->
    well_formed B ->
    Γ ⊢ (A ---> (A or B))
    using PropositionalReasoning.
  Proof.
    intros WFA WFB.
    eapply syllogism_4_meta.
    5: { apply modus_ponens; wf_auto2. }
    5: { apply bot_elim; wf_auto2. }
    all: wf_auto2.
  Defined.

  Lemma disj_right_intro_meta (Γ : Theory) (A B : Pattern) (i : ProofInfo) :
    well_formed A ->
    well_formed B ->
    Γ ⊢ B using i ->
    Γ ⊢ (A or B) using i.
  Proof.
    intros HwfA HwfB HB.
    eapply MP.
    { exact HB. }
    {
      apply usePropositionalReasoning.
      apply disj_right_intro; wf_auto2.
    }
  Defined.

  Lemma disj_left_intro_meta (Γ : Theory) (A B : Pattern) (i : ProofInfo) :
    well_formed A ->
    well_formed B ->
    Γ ⊢ A using i ->
    Γ ⊢ (A or B) using i.
  Proof.
    intros HwfA HwfB HA.
    eapply MP.
    { exact HA. }
    apply usePropositionalReasoning.
    apply disj_left_intro; assumption.
  Defined.

  Lemma not_not_elim (Γ : Theory) (A : Pattern) :
    well_formed A ->
    Γ ⊢ (!(!A) ---> A)
    using PropositionalReasoning.
  Proof.
    intros WFA.
    apply P3. exact WFA.
  Defined.

  Lemma not_not_elim_meta Γ A (i : ProofInfo) :
    well_formed A ->
    Γ ⊢ (! ! A) using i ->
    Γ ⊢ A using i.
  Proof.
    intros wfA nnA.
    eapply MP.
    { apply nnA. }
    { apply usePropositionalReasoning. apply not_not_elim. exact wfA. }
  Defined.

  Lemma double_neg_elim (Γ : Theory) (A B : Pattern) :
    well_formed A ->
    well_formed B ->
    Γ ⊢ (((!(!A)) ---> (!(!B))) ---> (A ---> B))
    using PropositionalReasoning.
  Proof.
    intros WFA WFB.
    eapply syllogism_meta.
    5: apply P4.
    4: apply P4.
    all: wf_auto2.
  Defined.

  Lemma double_neg_elim_meta (Γ : Theory) (A B : Pattern) (i : ProofInfo) :
    well_formed A ->
    well_formed B -> 
    Γ ⊢ ((!(!A)) ---> (!(!B))) using i ->
    Γ ⊢ (A ---> B) using i.
  Proof.
    intros WFA WFB H.
    eapply MP.
    - exact H.
    - apply usePropositionalReasoning.
      apply double_neg_elim; wf_auto2.
  Defined.

  Lemma not_not_impl_intro (Γ : Theory) (A B : Pattern) :
    well_formed A ->
    well_formed B ->
    Γ ⊢ ((A ---> B) ---> ((! ! A) ---> (! ! B)))
    using PropositionalReasoning.
  Proof.
    intros WFA WFB.
    
    epose (S1 := @syllogism Γ (! ! A) A B _ _ _).
    
    epose (MP1 := MP (@not_not_elim _ A _) S1).
    
    epose(NNB := @not_not_intro Γ B _).

    epose(P1 := (P1 Γ (B ---> ! (! B)) (! ! A) _ _)).
    
    epose(MP2 := MP NNB P1).
    
    epose(P2' := (P2 Γ (! ! A) B (! !B) _ _ _)).
    
    epose(MP3 := MP MP2 P2').
    
    eapply @syllogism_meta with (B := (! (! A) ---> B)).
    - shelve.
    - shelve.
    - shelve.
    - assumption.
    - assumption.
      Unshelve.
      all: wf_auto2.
  Defined.

  Lemma contraposition (Γ : Theory) (A B : Pattern) : 
    well_formed A ->
    well_formed B -> 
    Γ ⊢ ((A ---> B) ---> ((! B) ---> (! A)))
    using PropositionalReasoning.
  Proof.
    intros WFA WFB.
    epose proof (@P4 Γ (! A) (! B) _ _) as m.
    apply syllogism_meta with (B := (! (! A) ---> ! (! B))).
    - shelve.
    - shelve.
    - shelve.
    - apply @not_not_impl_intro; wf_auto2.
    - exact m. (* apply (P4 _ _ _). shelve. shelve. *)
      Unshelve.
      all: wf_auto2.
  Defined.

  Lemma or_comm_meta (Γ : Theory) (A B : Pattern) (i : ProofInfo):
    well_formed A ->
    well_formed B ->
    Γ ⊢ (A or B) using i ->
    Γ ⊢ (B or A) using i.
  Proof.
    intros WFA WFB H. unfold patt_or in *.    
    epose proof (P4 := (@P4 Γ A (!B) _ _)).
    epose proof (NNI := @not_not_intro Γ B _).
    apply (usePropositionalReasoning i) in P4.
    apply (usePropositionalReasoning i) in NNI.
    epose proof (SI := @syllogism_meta Γ _ _ _ _ _ _ _ H NNI).
    eapply MP.
    - exact SI.
    - exact P4.
      Unshelve.
      all: wf_auto2.
  Defined.

  Lemma A_implies_not_not_A_alt (Γ : Theory) (A : Pattern) (i : ProofInfo) :
    well_formed A ->
    Γ ⊢ A using i ->
    Γ ⊢ (!( !A )) using i.
  Proof.
    intros WFA H. unfold patt_not.
    eapply MP.
    { apply H. }
    {
      apply usePropositionalReasoning.
      apply not_not_intro.
      exact WFA.
    }
  Defined.

  Lemma P5i (Γ : Theory) (A B : Pattern) :
    well_formed A ->
    well_formed B ->
    Γ ⊢ (! A ---> (A ---> B))
    using PropositionalReasoning.
  Proof.
    intros WFA WFB.
    eapply syllogism_meta.
    5: apply P4.
    4: apply P1.
    all: wf_auto2.
  Defined.

  Lemma false_implies_everything (Γ : Theory) (phi : Pattern) :
    well_formed phi ->
    Γ ⊢ (Bot ---> phi) using PropositionalReasoning.
  Proof.
    apply bot_elim.
  Defined.

  Lemma not_basic_in_prop : ~ProofInfoLe BasicReasoning pi_Propositional.
  Proof.
    intros [HContra].
    remember (evar_fresh []) as x.
    pose (pf := ProofSystem.P3 ∅ (patt_free_evar x) ltac:(wf_auto2)).
    pose (pf' := ProofSystem.Framing_left _ _ _ (patt_free_evar x) ltac:(wf_auto2) pf).
    specialize (HContra _ _ pf').
    feed specialize HContra.
    {
      constructor.
      {
        simpl. exact I.
      }
      {
        simpl. unfold pf'. set_solver.
      }
      {
        simpl. unfold pf'. set_solver.
      }
      {
        simpl. reflexivity.
      }
    }
    destruct HContra as [Contra1 Contra2 Contra3 Contra4].
    simpl in Contra1. congruence.
  Qed.

  Lemma not_exgen_x_in_prop (x : evar) :
    ~ ProofInfoLe (pi_Generic (ExGen := {[x]}, SVSubst := ∅, KT := false)) pi_Propositional.
  Proof.
    intros [HContra].

    remember (fresh_evar (patt_free_evar x)) as y.
    pose (pf1 := @A_impl_A ∅ (patt_free_evar y) ltac:(wf_auto2)).
    pose (pf2 := @Ex_gen Σ ∅ (patt_free_evar y) (patt_free_evar y) x ltac:(wf_auto2) ltac:(wf_auto2) (proj1_sig pf1) ltac:(simpl; rewrite elem_of_singleton; solve_fresh_neq)).
    specialize (HContra _ _ pf2).
    feed specialize HContra.
    {
      unfold pf2.
      constructor.
      { exact I. }
      { simpl. clear. set_solver. }
      { simpl. clear. set_solver. }
      { simpl. reflexivity. }
    }
    destruct HContra as [Hprop Hgen Hsvs Hkt].
    clear -Hgen.
    unfold pf2 in Hgen.
    simpl in Hgen.
    clear -Hgen.
    set_solver.
  Qed.

  Lemma Framing_left (Γ : Theory) (ϕ₁ ϕ₂ ψ : Pattern) (i : ProofInfo)
    {pile : ProofInfoLe BasicReasoning i}
    :
    well_formed ψ ->
    Γ ⊢ ϕ₁ ---> ϕ₂ using i ->
    Γ ⊢ ϕ₁ $ ψ ---> ϕ₂ $ ψ using i.
  Proof.
    intros wfψ [pf Hpf].
    unshelve (eexists).
    {
      apply ProofSystem.Framing_left.
      { exact wfψ. }
      exact pf.
    }
    {
      destruct i.
      {
        exfalso. apply not_basic_in_prop. apply pile.
      }
      destruct Hpf as [Hpf1 Hpf2 Hpf3 Hpf4].
      constructor; simpl.
      {
        exact I.
      }
      {
        assumption.
      }
      {
        assumption.
      }
      {
        assumption.
      }
    }
  Defined.

  Lemma Framing_right (Γ : Theory) (ϕ₁ ϕ₂ ψ : Pattern) (i : ProofInfo)
  {pile : ProofInfoLe BasicReasoning i}
  :
  well_formed ψ ->
  Γ ⊢ ϕ₁ ---> ϕ₂ using i ->
  Γ ⊢ ψ $ ϕ₁ ---> ψ $ ϕ₂ using i.
Proof.
  intros wfψ [pf Hpf].
  unshelve (eexists).
  {
    apply ProofSystem.Framing_right.
    { exact wfψ. }
    exact pf.
  }
  {
    destruct i.
    {
      exfalso. apply not_basic_in_prop. apply pile.
    }
    destruct Hpf as [Hpf1 Hpf2 Hpf3 Hpf4].
    constructor; simpl.
    {
      exact I.
    }
    {
      assumption.
    }
    {
      assumption.
    }
    {
      assumption.
    }
  }
Defined.

  Lemma Prop_bott_left (Γ : Theory) (ϕ : Pattern) :
    well_formed ϕ ->
    Γ ⊢ ⊥ $ ϕ ---> ⊥ using BasicReasoning.
  Proof.
    intros wfϕ.
    unshelve (eexists).
    {
      apply ProofSystem.Prop_bott_left. exact wfϕ.
    }
    {
      constructor; simpl.
      {
        exact I.
      }
      {
        set_solver.
      }
      {
        set_solver.
      }
      {
        reflexivity.
      }
    }
  Defined.

  Lemma Prop_bott_right (Γ : Theory) (ϕ : Pattern) :
    well_formed ϕ ->
    Γ ⊢ ϕ $ ⊥ ---> ⊥ using BasicReasoning.
  Proof.
    intros wfϕ.
    unshelve (eexists).
    {
      apply ProofSystem.Prop_bott_right. exact wfϕ.
    }
    {
      constructor; simpl.
      {
        exact I.
      }
      {
        set_solver.
      }
      {
        set_solver.
      }
      {
        reflexivity.
      }
    }
  Defined.

  Arguments Prop_bott_left _ (_%ml) _ : clear implicits.
  Arguments Prop_bott_right _ (_%ml) _ : clear implicits.



  (*Was an axiom in AML_definition.v*)
  (* TODO rename into Prop_bot_ctx *)
  Lemma Prop_bot (Γ : Theory) (C : Application_context) :
    Γ ⊢ ((subst_ctx C patt_bott) ---> patt_bott)
    using BasicReasoning.
  Proof.
    induction C; simpl.
    - apply usePropositionalReasoning.
      apply false_implies_everything.
      wf_auto2.
    - eapply syllogism_meta.
      5: { apply (Prop_bott_left Γ p ltac:(wf_auto2)). }
      4: { apply Framing_left. apply pile_refl. wf_auto2. exact IHC. }
      all: wf_auto2.
    - eapply syllogism_meta.
      5: { apply (Prop_bott_right Γ p ltac:(wf_auto2)). }
      4: { apply Framing_right. apply pile_refl. wf_auto2. exact IHC. }
      all: wf_auto2.
  Defined.

  (*Was an axiom in AML_definition.v*)
  Lemma Framing (Γ : Theory) (C : Application_context) (A B : Pattern) (i : ProofInfo)
    {pile : ProofInfoLe BasicReasoning i}
    :
    Γ ⊢ (A ---> B) using i ->
    Γ ⊢ ((subst_ctx C A) ---> (subst_ctx C B)) using i.
  Proof.
    intros H.
    pose proof H as [pf _].
    pose proof (HWF := @proved_impl_wf _ _ _ pf).
    assert (wfA: well_formed A) by wf_auto2.
    assert (wfB: well_formed B) by wf_auto2.
    clear pf HWF.
    move: wfA wfB H.

    induction C; intros WFA WFB H; simpl.
    - exact H.
    - apply Framing_left. apply _. wf_auto2.
      apply IHC. wf_auto2. wf_auto2. exact H.
    - apply Framing_right. apply _. wf_auto2.
      apply IHC. wf_auto2. wf_auto2. exact H.
  Defined.

  Lemma A_implies_not_not_A_ctx (Γ : Theory) (A : Pattern) (C : Application_context)
    (i : ProofInfo) {pile : ProofInfoLe BasicReasoning i}
    :
    well_formed A ->
    Γ ⊢ A using i ->
    Γ ⊢ (! (subst_ctx C ( !A ))) using i.
  Proof.
    intros WFA H.

    epose proof (ANNA := @A_implies_not_not_A_alt Γ _ i _ H).
    replace (! (! A)) with ((! A) ---> Bot) in ANNA by reflexivity.
    epose proof (EF := @Framing _ C (! A) Bot _ _ ANNA).
    epose proof (PB := Prop_bot Γ C).
    apply liftPi with (i₂ := i) in PB. 2: apply _.
    epose (TRANS := @syllogism_meta _ _ _ _ _ _ _ _ EF PB).
    apply TRANS.
    
    Unshelve.
    all: wf_auto2.
  Defined.

  Lemma A_implies_not_not_A_alt_Γ (Γ : Theory) (A : Pattern) (i : ProofInfo) :
    well_formed A ->
    Γ ⊢ A using i ->
    Γ ⊢ (!( !A )) using i.
  Proof.
    intros WFA H. unfold patt_not.
    eapply MP.
    { apply H. }
    { apply usePropositionalReasoning. apply not_not_intro. exact WFA. }
  Defined.

  Lemma ctx_bot_prop (Γ : Theory) (C : Application_context) (A : Pattern) 
    (i : ProofInfo)
    {pile : ProofInfoLe BasicReasoning i}
  :
    well_formed A ->
    Γ ⊢ (A ---> Bot) using i ->
    Γ ⊢ (subst_ctx C A ---> Bot) using i.
  Proof.
    intros WFA H.
    epose proof (FR := @Framing Γ C A Bot _ _ H).
    epose proof (BPR := @Prop_bot Γ C).
    apply liftPi with (i₂ := i) in BPR. 2: apply _.
    epose proof (TRANS := @syllogism_meta _ _ _ _ _ _ _ _ FR BPR).
    exact TRANS.
    Unshelve.
    all: wf_auto2.
  Defined.

  Lemma exclusion (G : Theory) (A : Pattern) (i : ProofInfo) :
    well_formed A ->
    G ⊢ A using i ->
    G ⊢ (A ---> Bot) using i ->
    G ⊢ Bot using i.
  Proof.
    intros WFA H H0.
    eapply MP.
    apply H.
    apply H0.
  Defined.

  Lemma modus_tollens Γ A B (i : ProofInfo) :
    Γ ⊢ (A ---> B) using i ->
    Γ ⊢ (!B ---> !A) using i.
  Proof.
    intros H.
    pose proof (wf := proved_impl_wf _ _ (proj1_sig H)).
    assert (wfA : well_formed A) by wf_auto2.
    assert (wfB : well_formed B) by wf_auto2.

    eapply MP.
    2: { apply usePropositionalReasoning. apply contraposition; wf_auto2. }
    apply H.
  Defined.
  
  Lemma A_impl_not_not_B Γ A B :
    well_formed A ->
    well_formed B ->
    Γ ⊢ ((A ---> ! !B) ---> (A ---> B))
    using PropositionalReasoning.
  Proof.
    intros WFA WFB.

    assert (H0 : Γ ⊢ (! !B ---> B) using PropositionalReasoning).
    {
      apply not_not_elim. wf_auto2.
    }

    assert (H1 : Γ ⊢ ((A ---> ! !B) ---> (! !B ---> B) ---> (A ---> B)) using PropositionalReasoning).
    {
      apply syllogism; wf_auto2.
    }

    eapply MP.
    2: { 
      apply reorder_meta.
      4: apply H1.
      all: wf_auto2.
    }
    apply H0.
  Defined.

  Lemma prf_weaken_conclusion Γ A B B' :
    well_formed A ->
    well_formed B ->
    well_formed B' ->
    Γ ⊢ ((B ---> B') ---> ((A ---> B) ---> (A ---> B')))
    using PropositionalReasoning.
  Proof.
    intros wfA wfB wfB'.
    apply reorder_meta;[wf_auto2|wf_auto2|wf_auto2|].
    apply syllogism; wf_auto2.
  Defined.

  Lemma prf_weaken_conclusion_meta Γ A B B' (i : ProofInfo) :
    well_formed A ->
    well_formed B ->
    well_formed B' ->
    Γ ⊢ (B ---> B') using i ->
    Γ ⊢ ((A ---> B) ---> (A ---> B')) using i.
  Proof.
    intros wfA wfB wfB' BimpB'.
    assert (H1: Γ ⊢ ((A ---> B) ---> (B ---> B') ---> (A ---> B')) using i).
    {
      apply usePropositionalReasoning. apply syllogism; wf_auto2.
    }
    apply reorder_meta in H1;[|wf_auto2|wf_auto2|wf_auto2].
    eapply MP. 2: apply H1. apply BimpB'.
  Defined.

  Lemma prf_weaken_conclusion_iter Γ l g g'
          (wfl : wf l) (wfg : well_formed g) (wfg' : well_formed g') :
    Γ ⊢ ((g ---> g') ---> (fold_right patt_imp g l ---> fold_right patt_imp g' l))
    using PropositionalReasoning.
  Proof.
    induction l.
    - apply A_impl_A. wf_auto2.
    - pose proof (wfl' := wfl).
      apply andb_prop in wfl.
      fold (map well_formed) in wfl.
      destruct wfl as [wfa wfl].
      (* I do not know how to fold it, so I just assert & clear. *)
      assert (wfl'' : wf l) by apply wfl.
      clear wfl.
      specialize (IHl wfl'').
      simpl in *.
      eapply syllogism_meta.
      5: eapply prf_weaken_conclusion.
      4: apply IHl.
      all: wf_auto2.
  Defined.

  Lemma prf_weaken_conclusion_iter_meta Γ l g g' (i : ProofInfo):
    wf l ->
    well_formed g ->
    well_formed g' ->
    Γ ⊢ (g ---> g') using i ->
    Γ ⊢ ((fold_right patt_imp g l) ---> (fold_right patt_imp g' l)) using i.
  Proof.
    intros wfl wfg wfg' gimpg'.
    eapply MP.
    2: { apply usePropositionalReasoning. apply prf_weaken_conclusion_iter; wf_auto2. }
    1: { apply gimpg'. }
  Defined.

  Lemma prf_weaken_conclusion_iter_meta_meta Γ l g g' (i : ProofInfo):
    wf l ->
    well_formed g ->
    well_formed g' ->
    Γ ⊢ (g ---> g') using i ->
    Γ ⊢ (fold_right patt_imp g l) using i ->
    Γ ⊢ (fold_right patt_imp g' l) using i.
  Proof.
    intros wfl wfg wfg' gimpg' H.
    eapply MP.
    { apply gimpg'. }
    eapply MP.
    { apply H. }
    apply reorder_meta;[wf_auto2|wf_auto2|wf_auto2|].
    apply usePropositionalReasoning.
    apply prf_weaken_conclusion_iter.
    all: wf_auto2.
  Defined.

  Lemma prf_weaken_conclusion_meta_meta Γ A B B' (i : ProofInfo) :
    well_formed A ->
    well_formed B ->
    well_formed B' ->
    Γ ⊢ (B ---> B') using i ->
    Γ ⊢ (A ---> B) using i ->
    Γ ⊢ (A ---> B') using i.
  Proof.
    intros WFA WFB WFB' H H0.
    eapply MP. 2: apply prf_weaken_conclusion_meta. 1: apply H0.
    4: apply H. all: wf_auto2.
  Defined.

  Lemma prf_strenghten_premise Γ A A' B :
    well_formed A ->
    well_formed A' ->
    well_formed B ->
    Γ ⊢ ((A' ---> A) ---> ((A ---> B) ---> (A' ---> B))) using PropositionalReasoning.
  Proof.
    intros wfA wfA' wfB.
    apply syllogism; wf_auto2.
  Defined.

  Lemma prf_strenghten_premise_iter Γ l₁ l₂ h h' g :
    wf l₁ -> wf l₂ ->
    well_formed h ->
    well_formed h' ->
    well_formed g ->
    Γ ⊢ (h' ---> h) --->
        foldr patt_imp g (l₁ ++ h::l₂) --->
        foldr patt_imp g (l₁ ++ h'::l₂)
    using PropositionalReasoning.
  Proof.
    intros wfl₁ wfl₂ wfh wfh' wfg.
    induction l₁.
    - simpl. apply prf_strenghten_premise. all: wf_auto2.
    - pose proof (wfal₁ := wfl₁).
      remember (foldr patt_imp g (h::l₂)) as g1.
      remember (foldr patt_imp g (h'::l₂)) as g2.
      unfold wf in wfl₁. simpl in wfl₁. apply andb_prop in wfl₁.
      destruct wfl₁ as [wfa wfl₁].
      specialize (IHl₁ wfl₁).
      remember (foldr patt_imp g (l₁ ++ h::l₂)) as b.
      remember (foldr patt_imp g (l₁ ++ h'::l₂)) as b'.

      assert (prf: Γ ⊢ ((b ---> b') ---> ((a ---> b) ---> (a ---> b'))) using PropositionalReasoning).
      { apply prf_weaken_conclusion; subst; wf_auto2. }

      subst.
      eapply syllogism_meta.
      5: { apply prf. }
      4: { apply IHl₁. }
      all: wf_auto2.
  Defined.

  Lemma prf_strenghten_premise_meta Γ A A' B (i : ProofInfo) :
    well_formed A ->
    well_formed A' ->
    well_formed B ->
    Γ ⊢ (A' ---> A) using i ->
    Γ ⊢ ((A ---> B) ---> (A' ---> B)) using i.
  Proof.
    intros wfA wfA' wfB A'impA.
    assert (H1: Γ ⊢ ((A' ---> A) ---> (A ---> B) ---> (A' ---> B)) using i).
    {
      apply usePropositionalReasoning. apply syllogism; wf_auto2.
    }
    eapply MP. 2: apply H1. apply A'impA.
  Defined.

  Lemma prf_strenghten_premise_meta_meta Γ A A' B (i : ProofInfo) :
    well_formed A ->
    well_formed A' ->
    well_formed B ->
    Γ ⊢ (A' ---> A) using i ->
    Γ ⊢ (A ---> B) using i ->
    Γ ⊢ (A' ---> B) using i.
  Proof.
    intros wfA wfA' wfB A'impA AimpB.
    eapply MP. 2: apply prf_strenghten_premise_meta. 1: apply AimpB.
    4: apply A'impA. all: wf_auto2.
  Defined.

  Lemma prf_strenghten_premise_iter_meta Γ l₁ l₂ h h' g (i : ProofInfo) :
    wf l₁ -> wf l₂ ->
    well_formed h ->
    well_formed h' ->
    well_formed g ->
    Γ ⊢ (h' ---> h) using i ->
    Γ ⊢ foldr patt_imp g (l₁ ++ h::l₂) --->
         foldr patt_imp g (l₁ ++ h'::l₂)
    using i.  
  Proof.
    intros WFl₁ WFl₂ WFh WFh' WFg H.
    eapply MP.
    2: { apply usePropositionalReasoning. apply prf_strenghten_premise_iter; wf_auto2. }
    exact H.
  Defined.

  Lemma prf_strenghten_premise_iter_meta_meta Γ l₁ l₂ h h' g (i : ProofInfo) :
    wf l₁ -> wf l₂ ->
    well_formed h ->
    well_formed h' ->
    well_formed g ->
    Γ ⊢ (h' ---> h) using i ->
    Γ ⊢ foldr patt_imp g (l₁ ++ h::l₂) using i ->
    Γ ⊢ foldr patt_imp g (l₁ ++ h'::l₂) using i.  
  Proof.
    intros WFl₁ WFl₂ WFh WFh' WFg H H0.
    eapply MP.
    2: eapply prf_strenghten_premise_iter_meta.
    7: eassumption. 1: assumption. all: wf_auto2.
  Defined.

  (*
  (* TODO rename *)
  Lemma rewrite_under_implication Γ g g' (i : ProofInfo):
    well_formed g ->
    well_formed g' ->
    Γ ⊢ ((g ---> g') ---> g) using i ->
    Γ ⊢ ((g ---> g') ---> g') using i.
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
*)

  Local Example example_nested_const Γ a b c:
    well_formed a ->
    well_formed b ->
    well_formed c ->
    (* like P2 but nested a bit *)
    Γ ⊢ (a ---> (b ---> (c ---> a)))
    using PropositionalReasoning.
  Proof.
    intros wfa wfb wfc.
    assert (H1: Γ ⊢ ((c ---> a) ---> (b ---> (c ---> a))) using PropositionalReasoning).
    {
      apply P1; wf_auto2.
    }
    assert (H2: Γ ⊢ (a ---> (c ---> a)) using PropositionalReasoning).
    { apply P1; wf_auto2. }

    eapply (@syllogism_meta _ _ _ _ _ _ _ _ H2 H1).
    Unshelve. all: wf_auto2.
  Defined.

  (* This will form a base for the tactic 'exact 0' *)
  Lemma nested_const Γ a l:
    well_formed a ->
    wf l ->
    Γ ⊢ (a ---> (fold_right patt_imp a l))
    using PropositionalReasoning.
  Proof.
    intros wfa wfl.
    induction l; simpl.
    - apply A_impl_A. exact wfa.
    - pose proof (wfa0l := wfl).
      unfold wf in wfl. simpl in wfl. apply andb_prop in wfl. destruct wfl as [wfa0 wfl].
      specialize (IHl wfl).
      assert (H1 : Γ ⊢ ((foldr patt_imp a l) ---> (a0 ---> (foldr patt_imp a l))) using PropositionalReasoning).
      {
        apply P1; wf_auto2.
      }
      eapply syllogism_meta.
      5: apply H1. 4: assumption. all: wf_auto2.
  Defined.

  Lemma nested_const_middle Γ a l₁ l₂:
    well_formed a ->
    wf l₁ ->
    wf l₂ ->
    Γ ⊢ (fold_right patt_imp a (l₁ ++ a :: l₂))
    using PropositionalReasoning.
  Proof.
    intros wfa wfl₁ wfl₂.
    induction l₁; simpl.
    - apply nested_const; wf_auto2.
    - pose proof (wfa0l₁ := wfl₁).
      unfold wf in wfl₁. simpl in wfl₁. apply andb_prop in wfl₁. destruct wfl₁ as [wfa0 wfl₁].
      specialize (IHl₁ wfl₁). simpl in IHl₁.
      eapply MP. 2: apply P1. 1: apply IHl₁. all: wf_auto2.
  Defined.

  Lemma prf_reorder_iter Γ a b g l₁ l₂:
    well_formed a ->
    well_formed b ->
    well_formed g ->
    wf l₁ ->
    wf l₂ ->
    Γ ⊢ ((fold_right patt_imp g (l₁ ++ [a;b] ++ l₂)) --->
         (fold_right patt_imp g (l₁ ++ [b;a] ++ l₂)))
    using PropositionalReasoning.
  Proof.
    intros wfa wfb wfg wfl₁ wfl₂.
    induction l₁; simpl in *.
    - apply reorder; wf_auto2.
    - pose proof (wfa0l₁ := wfl₁).
      unfold wf in wfl₁. apply andb_prop in wfl₁. destruct wfl₁ as [wfa0 wfl₁].
      specialize (IHl₁ wfl₁).
      eapply prf_weaken_conclusion_meta.
      4: apply IHl₁.
      all: wf_auto2.
  Defined.

  Lemma prf_reorder_iter_meta Γ a b g l₁ l₂ (i : ProofInfo):
    well_formed a ->
    well_formed b ->
    well_formed g ->
    wf l₁ ->
    wf l₂ ->
    Γ ⊢ (fold_right patt_imp g (l₁ ++ [a;b] ++ l₂)) using i ->
    Γ ⊢ (fold_right patt_imp g (l₁ ++ [b;a] ++ l₂)) using i.
  Proof.
    (* TODO we should have a function/lemma for creating these "meta" variants. *)
    intros WFa WFb WFg Wfl1 Wfl2 H.
    eapply MP.
    2: { apply usePropositionalReasoning. apply prf_reorder_iter; wf_auto2. }
    exact H.
  Defined.
  
  Lemma A_impl_not_not_B_meta Γ A B (i : ProofInfo) :
    well_formed A ->
    well_formed B ->
    Γ ⊢ A ---> ! !B using i ->
    Γ ⊢ A ---> B using i.
  Proof.
    intros WFA WFB H.
    eapply MP.
    2: { apply usePropositionalReasoning. apply A_impl_not_not_B; wf_auto2. }
    exact H.
  Defined.

  Lemma pf_conj_elim_l Γ A B :
    well_formed A ->
    well_formed B ->
    Γ ⊢ A and B ---> A using PropositionalReasoning.
  Proof.
    intros WFA WFB. unfold patt_and. unfold patt_not at 1.

    assert (Γ ⊢ (! A ---> (! A or ! B)) using PropositionalReasoning).
    { apply disj_left_intro; wf_auto2. }

    assert (Γ ⊢ ((! A or ! B) ---> (! A or ! B ---> ⊥) ---> ⊥) using PropositionalReasoning).
    {
      apply modus_ponens; wf_auto2.
    }
    assert (Γ ⊢ (! A ---> ((! A or ! B ---> ⊥) ---> ⊥)) using PropositionalReasoning).
    { eapply syllogism_meta. 5: apply H0. 4: apply H. all: wf_auto2. }
    epose proof (reorder_meta _ _ _ H1).
    apply A_impl_not_not_B_meta;[wf_auto2|wf_auto2|].
    apply H2.
    Unshelve.
    all: wf_auto2.
  Defined.

  Lemma pf_conj_elim_r Γ A B :
    well_formed A ->
    well_formed B ->
    Γ ⊢ A and B ---> B using PropositionalReasoning.
  Proof.
    intros WFA WFB. unfold patt_and. unfold patt_not at 1.

    assert (Γ ⊢ (! B ---> (! A or ! B)) using PropositionalReasoning).
    { apply disj_right_intro; wf_auto2. }

    assert (Γ ⊢ ((! A or ! B) ---> (! A or ! B ---> ⊥) ---> ⊥) using PropositionalReasoning).
    { apply modus_ponens; wf_auto2. }

    assert (Γ ⊢ (! B ---> ((! A or ! B ---> ⊥) ---> ⊥)) using PropositionalReasoning).
    { eapply syllogism_meta. 5: apply H0. 4: apply H. all: wf_auto2. }
    epose proof (reorder_meta  _ _ _ H1).
    apply A_impl_not_not_B_meta;[wf_auto2|wf_auto2|].
    apply H2.
    Unshelve.
    all: wf_auto2.
  Defined.

  Lemma pf_conj_elim_l_meta Γ A B (i : ProofInfo) :
    well_formed A ->
    well_formed B ->
    Γ ⊢ A and B using i ->
    Γ ⊢ A using i.
  Proof.
    intros WFA WFB H.
    eapply MP.
    2: { apply usePropositionalReasoning. apply pf_conj_elim_l. wf_auto2. shelve. }
    1: apply H.
    Unshelve. all: wf_auto2.
  Defined.
  
  Lemma pf_conj_elim_r_meta Γ A B (i : ProofInfo) :
    well_formed A ->
    well_formed B ->
    Γ ⊢ A and B using i ->
    Γ ⊢ B using i.
  Proof.
    intros WFA WFB H.
    eapply MP.
    2: apply usePropositionalReasoning; apply pf_conj_elim_r.
    1: apply H.
    all: wf_auto2.
  Defined.

  Lemma A_or_notA Γ A :
    well_formed A ->
    Γ ⊢ A or ! A using PropositionalReasoning.
  Proof.
    intros wfA.
    unfold patt_or.
    apply A_impl_A. wf_auto2.
  Defined.

  Lemma P4m_meta (Γ : Theory) (A B : Pattern) (i : ProofInfo) :
    well_formed A ->
    well_formed B ->
    Γ ⊢ A ---> B using i ->
    Γ ⊢ A ---> !B using i ->
    Γ ⊢ !A using i.
  Proof.
    intros wfA wfB AimpB AimpnB.
    pose proof (H1 := @P4m Γ A B wfA wfB).
    assert (H2 : Γ ⊢ (A ---> ! B) ---> ! A using i).
    { eapply MP. 2: { apply usePropositionalReasoning; apply H1. } exact AimpB. }
    eapply MP. 2: { apply H2. } exact AimpnB.
  Defined.

End FOL_helpers.

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


Lemma reshape {Σ : Signature} (Γ : Theory) (g : Pattern) (xs: list Pattern) (i : ProofInfo) :
  forall (r : ImpReshapeS g (xs)),
     Γ ⊢ foldr (patt_imp) g (xs) using i ->
     Γ ⊢ (untagPattern (irs_flattened r)) using i.
Proof.
  intros r [pf Hpf].
  unshelve (eexists).
  {
    eapply cast_proof.
    { rewrite irs_pf; reflexivity. }
    exact pf.
  }
  {
    simpl.
    destruct Hpf as [Hpf1 Hpf2 Hpf3 Hpf4].
    constructor.
    {
      destruct i;[|exact I].
      rewrite indifferent_to_cast_propositional_only.
      exact Hpf1.
    }
    {
      rewrite elem_of_subseteq in Hpf2.
      rewrite elem_of_subseteq.
      intros x Hx.
      specialize (Hpf2 x).
      apply Hpf2. clear Hpf2.
      rewrite uses_of_ex_gen_correct in Hx.
      rewrite uses_of_ex_gen_correct.
      rewrite indifferent_to_cast_uses_ex_gen in Hx.
      exact Hx.
    }
    {
      rewrite elem_of_subseteq in Hpf3.
      rewrite elem_of_subseteq.
      intros x Hx.
      specialize (Hpf3 x).
      apply Hpf3. clear Hpf3.
      rewrite uses_of_svar_subst_correct in Hx.
      rewrite uses_of_svar_subst_correct.
      rewrite indifferent_to_cast_uses_svar_subst in Hx.
      exact Hx.
    }
    {
      rewrite indifferent_to_cast_uses_kt.
      apply Hpf4.
    }
  }
Defined.


Local Example ex_reshape {Σ : Signature} Γ a b c d:
  well_formed a ->
  well_formed b ->
  well_formed c ->
  well_formed d ->
  Γ ⊢ a ---> (b ---> (c ---> d)) using PropositionalReasoning.
Proof.
  intros wfa wfb wfc wfd.
  apply reshape.
  (* Now the goal has the right shape *)
Abort.

Local Example ex_toMyGoal {Σ : Signature} Γ (p : Pattern) :
  well_formed p ->
  Γ ⊢ p ---> p using PropositionalReasoning.
Proof.
  intros wfp.
  toMyGoal.
  { wf_auto2. }
  fromMyGoal. 
  apply A_impl_A. exact wfp.
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
  Γ ⊢ p ---> p using PropositionalReasoning.
Proof.
  intros wfp.
  toMyGoal.
  { auto. }
  mgExtractWF wfl wfg.
  (* These two asserts by assumption only test presence of the two hypotheses *)
  assert (wf []) by assumption.
  assert (well_formed (p ---> p)) by assumption.
Abort.

Lemma cast_proof' {Σ : Signature} (Γ : Theory) (ϕ ψ : Pattern) (i : ProofInfo) (e : ψ = ϕ) :
  Γ ⊢ ϕ using i ->
  Γ ⊢ ψ using i.
Proof.
  intros [pf Hpf].
  unshelve (eexists).
  {
    apply (cast_proof e).
    exact pf.
  }
  { abstract(
    destruct Hpf as [Hpf1 Hpf2 Hpf3 Hpf4];
    constructor; [
    (
      destruct i;[|exact I];
      rewrite indifferent_to_cast_propositional_only;
      exact Hpf1
    )|
    (
      rewrite elem_of_subseteq in Hpf2;
      rewrite elem_of_subseteq;
      intros x Hx;
      specialize (Hpf2 x);
      apply Hpf2; clear Hpf2;
      rewrite uses_of_ex_gen_correct in Hx;
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
      rewrite uses_of_svar_subst_correct in Hx;
      rewrite uses_of_svar_subst_correct;
      rewrite indifferent_to_cast_uses_svar_subst in Hx;
      exact Hx
    )|
    (
      rewrite indifferent_to_cast_uses_kt;
      apply Hpf4
    )]).
  }
Defined.

Lemma cast_proof_mg_hyps {Σ : Signature} Γ hyps hyps' (e : hyps = hyps') goal (i : ProofInfo) :
  @mkMyGoal Σ Γ hyps goal i ->
  @mkMyGoal Σ Γ hyps' goal i.
Proof.
  unfold of_MyGoal. simpl. intros H.
  intros wfg wfhyps'.
  feed specialize H.
  { exact wfg. }
  { rewrite e. exact wfhyps'. }
  unshelve (eapply (@cast_proof' Σ Γ _ _ i _ H)).
  rewrite e.
  reflexivity.
Defined.

Lemma cast_proof_mg_goal {Σ : Signature} Γ hyps goal goal' (e : goal = goal') (i : ProofInfo):
  @mkMyGoal Σ Γ hyps goal i ->
  @mkMyGoal Σ Γ hyps goal' i .
Proof.
  unfold of_MyGoal. simpl. intros H.
  intros wfgoal' wfhyps.
  feed specialize H.
  { rewrite e. exact wfgoal'. }
  { exact wfhyps. }
  unshelve (eapply (@cast_proof' Σ Γ _ _ i _ H)).
  rewrite e.
  reflexivity.
Defined.

Lemma cast_proof_mg_hyps_indifferent'
      Σ P Γ hyps hyps' (e : hyps = hyps') goal (i : ProofInfo)
      (pf : @mkMyGoal Σ Γ hyps goal i) wf1 wf2 wf3 wf4:
  indifferent_to_cast P ->
  P _ _ (proj1_sig (@cast_proof_mg_hyps Σ Γ hyps hyps' e goal i pf wf1 wf2)) = P _ _ (proj1_sig (pf wf3 wf4)).
Proof.
  intros Hp. simpl. unfold cast_proof_mg_hyps.
  unfold proj1_sig. unfold cast_proof'. destruct pf as [pf' Hpf'] eqn:Heqpf.
  rewrite Hp.
  apply f_equal. simpl in *.
  case_match. simpl in *.
  remember (pf wf1
  (eq_ind_r (λ pv : list Pattern, wf pv)
     wf2 e)).
  simpl in *.
  apply proj1_sig_eq in Heqpf. simpl in Heqpf. rewrite -Heqpf.
  apply proj1_sig_eq in Heqs0. rewrite Heqs0.
  apply proj1_sig_eq in Heqs. simpl in Heqs. rewrite -Heqs.
  f_equal. f_equal.
  { apply UIP_dec; apply bool_eqdec. }
  { apply UIP_dec. apply bool_eqdec. }
Qed.

Lemma cast_proof_mg_goal_indifferent
      Σ P Γ hyps goal goal' (e : goal = goal') (i : ProofInfo)
      (pf : @mkMyGoal Σ Γ hyps goal i) wf1 wf2 wf3 wf4:
  indifferent_to_cast P ->
  P _ _ (proj1_sig (@cast_proof_mg_goal Σ Γ hyps goal goal' e i pf wf1 wf2)) = P _ _ (proj1_sig (pf wf3 wf4)).
Proof.
  intros Hp. simpl. unfold cast_proof_mg_goal.
  unfold proj1_sig. unfold cast_proof'. destruct pf as [pf' Hpf'] eqn:Heqpf.
  rewrite Hp.
  apply f_equal. f_equal.
  apply proj1_sig_eq in Heqpf. simpl in Heqpf. rewrite -Heqpf. clear Heqpf. simpl.
  case_match. simpl in *.
  apply proj1_sig_eq in Heqs. simpl in Heqs. rewrite -Heqs.
  f_equal. f_equal.
  { apply UIP_dec; apply bool_eqdec. }
  { apply UIP_dec. apply bool_eqdec. }
Qed.

Lemma cast_proof_trans {Σ : Signature} Γ ϕ₁ ϕ₂ ϕ₃ (pf : Γ ⊢ ϕ₁) (e₂₁ : ϕ₂ = ϕ₁) (e₃₂ : ϕ₃ = ϕ₂):
  @cast_proof Σ Γ ϕ₂ ϕ₃ e₃₂ (@cast_proof Σ Γ ϕ₁ ϕ₂ e₂₁ pf ) = (@cast_proof Σ Γ ϕ₁ ϕ₃ (eq_trans e₃₂ e₂₁) pf ).
Proof.
  unfold cast_proof,eq_rec_r,eq_rec,eq_rect.
  repeat case_match.
  replace (eq_sym (eq_trans e₃₂ e₂₁)) with (@eq_refl _ ϕ₁) by (apply UIP_dec; intros x' y'; apply Pattern_eqdec).
  reflexivity.
Qed.

Lemma cast_proof_refl {Σ : Signature} Γ ϕ₁ (pf : Γ ⊢ ϕ₁):
  @cast_proof Σ Γ ϕ₁ ϕ₁ eq_refl pf = pf.
Proof.
  reflexivity.
Qed.

Lemma MyGoal_intro {Σ : Signature} (Γ : Theory) (l : list Pattern) (x g : Pattern)
  (i : ProofInfo) :
  @mkMyGoal Σ Γ (l ++ [x]) g i ->
  @mkMyGoal Σ Γ l (x ---> g) i.
Proof.
  intros H.
  unfold of_MyGoal in H. simpl in H.
  unfold of_MyGoal. simpl. intros wfxig wfl.

  feed specialize H.
  { abstract (apply well_formed_imp_proj2 in wfxig; exact wfxig). }
  { abstract (unfold wf; unfold wf in wfl; rewrite map_app foldr_app; simpl;
              apply well_formed_imp_proj1 in wfxig; rewrite wfxig; simpl; exact wfl).
  }
  unshelve (eapply (cast_proof' _ H)).
  { rewrite foldr_app. reflexivity. }
Defined.

Ltac simplLocalContext :=
  match goal with
    | [ |- @of_MyGoal ?Sgm (@mkMyGoal ?Sgm ?Ctx ?l ?g ?i) ]
      => eapply cast_proof_mg_hyps;[(rewrite {1}[l]/app; reflexivity)|]
  end.

#[global]
 Ltac mgIntro := apply MyGoal_intro; simplLocalContext.


 Lemma mgUsePropositionalReasoning
  {Σ : Signature} (Γ : Theory) (l : list Pattern) (g : Pattern) (i : ProofInfo) :
  @mkMyGoal Σ Γ l g PropositionalReasoning ->
  @mkMyGoal Σ Γ l g i.
Proof.
  intros H wf1 wf2.
  specialize (H wf1 wf2).
  apply usePropositionalReasoning.
  exact H.
Defined.

Ltac usePropositionalReasoning :=
  lazymatch goal with
  | [ |- of_MyGoal (@mkMyGoal _ _ _ _ _) ] => apply mgUsePropositionalReasoning
  | [ |- _ ⊢ _ using _ ] => apply usePropositionalReasoning
  end.

Local Example ex_mgIntro {Σ : Signature} Γ a (i : ProofInfo) :
  well_formed a ->
  Γ ⊢ a ---> a using i.
Proof.
  intros wfa.
  toMyGoal.
  { wf_auto2. }
  mgIntro.
  usePropositionalReasoning.
  fromMyGoal. apply A_impl_A; assumption.
Defined.

Lemma MyGoal_exactn {Σ : Signature} (Γ : Theory) (l₁ l₂ : list Pattern) (g : Pattern):
  @mkMyGoal Σ Γ (l₁ ++ g :: l₂) g PropositionalReasoning.
Proof.
  mgExtractWF wfl₁gl₂ wfg.
  fromMyGoal.
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

Tactic Notation "mgExactn" constr(n) :=
  usePropositionalReasoning;
  unshelve (eapply (@cast_proof_mg_hyps _ _ _ _ _ _ _));
  [shelve|(rewrite <- (firstn_skipn n); rewrite /firstn; rewrite /skipn; reflexivity)|idtac];
  apply MyGoal_exactn.


Local Example ex_mgExactn {Σ : Signature} Γ a b c:
  well_formed a = true ->
  well_formed b = true ->
  well_formed c = true ->
  Γ ⊢ a ---> b ---> c ---> b using PropositionalReasoning.
Proof.
  intros wfa wfb wfc.
  toMyGoal.
  { wf_auto2. }
  mgIntro. mgIntro. mgIntro.
  mgExactn 1.
Defined.

Section FOL_helpers.

  Context {Σ : Signature}.

  Lemma MyGoal_weakenConclusion' Γ l g g' (i : ProofInfo):
    Γ ⊢ g ---> g' using i ->
    @mkMyGoal Σ Γ l g i ->
    @mkMyGoal Σ Γ l g' i.
  Proof.
    intros Hgg' Hlg.
    (*mgExtractWF wfl wfgp.*)
    unfold of_MyGoal in *. simpl in *.
    intros wfg' wfl.
    pose proof (wfimp := proved_impl_wf _ _ (proj1_sig Hgg')).
    apply well_formed_imp_proj1 in wfimp.
    eapply prf_weaken_conclusion_iter_meta_meta.
    5: apply Hlg.
    4: apply Hgg'.
    all: assumption.
  Defined.

  Lemma prf_contraction Γ a b:
    well_formed a ->
    well_formed b ->
    Γ ⊢ ((a ---> a ---> b) ---> (a ---> b)) using PropositionalReasoning.
  Proof.
    intros wfa wfb.
    assert (H1 : Γ ⊢ (a ---> ((a ---> b) ---> b)) using PropositionalReasoning).
    {
      apply modus_ponens; assumption.
    }
    assert (H2 : Γ ⊢ ((a ---> ((a ---> b) ---> b)) ---> ((a ---> (a ---> b)) ---> (a ---> b))) using PropositionalReasoning).
    {
      apply P2; wf_auto2.
    }
    eapply MP. 2: apply H2. apply H1.
  Defined.

  Lemma prf_weaken_conclusion_under_implication Γ a b c:
    well_formed a ->
    well_formed b ->
    well_formed c ->
    Γ ⊢ ((a ---> b) ---> ((a ---> (b ---> c)) ---> (a ---> c))) using PropositionalReasoning.
  Proof.
    intros wfa wfb wfc.
    assert (H1 : Γ ⊢ ((a ---> (b ---> c)) ---> (b ---> (a ---> c))) using PropositionalReasoning).
    {
      apply reorder; wf_auto2.
    }
    assert (H2 : Γ ⊢ (((b ---> (a ---> c)) ---> (a ---> c)) ---> ((a ---> (b ---> c)) ---> (a ---> c))) using PropositionalReasoning).
    {
      apply prf_strenghten_premise_meta;[wf_auto2|wf_auto2|wf_auto2|].
      apply H1.
    }
    eapply prf_weaken_conclusion_meta_meta.
    4: apply H2. 1-3: wf_auto2. clear H1 H2.

    assert (H3 : Γ ⊢ ((a ---> b) ---> ((b ---> (a ---> c)) ---> (a ---> (a ---> c)))) using PropositionalReasoning).
    {
      apply syllogism; wf_auto2.
    }
    assert (H4 : Γ ⊢ ((a ---> (a ---> c)) ---> (a ---> c)) using PropositionalReasoning).
    {
      apply prf_contraction; wf_auto2.
    }
    assert (Hiter: ((a ---> b) ---> (b ---> a ---> c) ---> a ---> c)
                   = foldr patt_imp (a ---> c) [(a ---> b); (b ---> a ---> c)]) by reflexivity.
    
    eapply (@cast_proof' _ _ _ _ _ Hiter).
    
    eapply prf_weaken_conclusion_iter_meta_meta.
    5: apply H3. 4: apply H4. all: wf_auto2.
  Defined.

  Lemma prf_weaken_conclusion_under_implication_meta Γ a b c (i : ProofInfo):
    well_formed a ->
    well_formed b ->
    well_formed c ->
    Γ ⊢ (a ---> b) using i ->
    Γ ⊢ ((a ---> (b ---> c)) ---> (a ---> c)) using i.
  Proof.
    intros wfa wfb wfc H.
    eapply MP.
    2: { usePropositionalReasoning. apply prf_weaken_conclusion_under_implication; wf_auto2. }
    exact H.
  Defined.

  Lemma prf_weaken_conclusion_under_implication_meta_meta Γ a b c i:
    well_formed a ->
    well_formed b ->
    well_formed c ->
    Γ ⊢ a ---> b using i ->
    Γ ⊢ a ---> b ---> c using i ->
    Γ ⊢ a ---> c using i.
  Proof.
    intros wfa wfb wfc H1 H2.
    eapply MP.
    { apply H2. }
    { apply prf_weaken_conclusion_under_implication_meta.
      4: { apply H1. }
      all: wf_auto2.
    }
  Defined.

  Lemma prf_weaken_conclusion_iter_under_implication Γ l g g':
    wf l ->
    well_formed g ->
    well_formed g' ->
    Γ ⊢ (((g ---> g') ---> (foldr patt_imp g l)) ---> ((g ---> g') ---> (foldr patt_imp g' l)))
    using PropositionalReasoning.
  Proof.
    intros wfl wfg wfg'.
    pose proof (H1 := @prf_weaken_conclusion_iter Σ Γ l g g' wfl wfg wfg').
    remember ((g ---> g')) as a.
    remember (foldr patt_imp g l) as b.
    remember (foldr patt_imp g' l) as c.
    assert (well_formed a) by (subst; wf_auto2).
    assert (well_formed b) by (subst; wf_auto2).
    assert (well_formed c) by (subst; wf_auto2).
    pose proof (H2' := @prf_weaken_conclusion_under_implication Γ a b c ltac:(assumption) ltac:(assumption) ltac:(assumption)).
    apply reorder_meta in H2'. 2,3,4: subst;wf_auto2.
    eapply MP. 2: apply H2'. apply H1.
  Defined.

  Lemma prf_weaken_conclusion_iter_under_implication_meta Γ l g g' (i : ProofInfo):
    wf l ->
    well_formed g ->
    well_formed g' ->
    Γ ⊢ ((g ---> g') ---> (foldr patt_imp g l)) using i->
    Γ ⊢ ((g ---> g') ---> (foldr patt_imp g' l)) using i.
  Proof.
    intros wfl wfg wfg' H.
    eapply MP.
    2: { usePropositionalReasoning. apply prf_weaken_conclusion_iter_under_implication; wf_auto2. }
    { exact H. }
  Defined.
  
  Lemma MyGoal_weakenConclusion_under_first_implication Γ l g g' i:
    @mkMyGoal Σ Γ ((g ---> g') :: l) g i ->
    @mkMyGoal Σ Γ ((g ---> g') :: l) g' i .
  Proof.
    intros H. unfold of_MyGoal in *. simpl in *.
    intros wfg' wfgg'l.
    pose proof (Htmp := wfgg'l).
    unfold wf in Htmp. simpl in Htmp. apply andb_prop in Htmp. destruct Htmp as [wfgg' wfl].
    apply well_formed_imp_proj1 in wfgg'. specialize (H wfgg' wfgg'l).
    apply prf_weaken_conclusion_iter_under_implication_meta; assumption.
  Defined.

  Lemma prf_weaken_conclusion_iter_under_implication_iter Γ l₁ l₂ g g':
    wf l₁ ->
    wf l₂ ->
    well_formed g ->
    well_formed g' ->
    Γ ⊢ ((foldr patt_imp g (l₁ ++ (g ---> g') :: l₂)) --->
         (foldr patt_imp g' (l₁ ++ (g ---> g') :: l₂)))
    using PropositionalReasoning.
  Proof.
    intros wfl₁ wfl₂ wfg wfg'.
    induction l₁; simpl.
    - apply prf_weaken_conclusion_iter_under_implication; auto.
    - pose proof (wfal₁ := wfl₁). unfold wf in wfl₁. simpl in wfl₁. apply andb_prop in wfl₁.
      destruct wfl₁ as [wfa wfl₁]. specialize (IHl₁ wfl₁).
      eapply prf_weaken_conclusion_meta. 4: assumption. all: wf_auto2.
  Defined.

  Lemma prf_weaken_conclusion_iter_under_implication_iter_meta Γ l₁ l₂ g g' i:
    wf l₁ ->
    wf l₂ ->
    well_formed g ->
    well_formed g' ->
    Γ ⊢ (foldr patt_imp g (l₁ ++ (g ---> g') :: l₂)) using i ->
    Γ ⊢ (foldr patt_imp g' (l₁ ++ (g ---> g') :: l₂)) using i.
  Proof.
    intros wfl₁ wfl₂ wfg wfg' H.
    eapply MP.
    { apply H. }
    { usePropositionalReasoning. apply prf_weaken_conclusion_iter_under_implication_iter; wf_auto2. }
  Defined.

  Lemma MyGoal_weakenConclusion Γ l₁ l₂ g g' i:
    @mkMyGoal Σ Γ (l₁ ++ (g ---> g') :: l₂) g i ->
    @mkMyGoal Σ Γ (l₁ ++ (g ---> g') :: l₂) g' i.
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

End FOL_helpers.

Tactic Notation "mgApply" constr(n) :=
  unshelve (eapply (@cast_proof_mg_hyps _ _ _ _ _ _ _));
  [shelve|(rewrite <- (firstn_skipn n); rewrite /firstn; rewrite /skipn; reflexivity)|idtac];
  apply MyGoal_weakenConclusion;
  let hyps := fresh "hyps" in rewrite [hyps in @mkMyGoal _ _ hyps _]/app.

Local Example ex_mgApply {Σ : Signature} Γ a b:
  well_formed a ->
  well_formed b ->
  Γ ⊢ a ---> (a ---> b) ---> b using PropositionalReasoning.
Proof.
  intros wfa wfb.
  toMyGoal.
  { wf_auto2. }
  mgIntro. mgIntro.
  mgApply 1.
  fromMyGoal. apply P1; wf_auto2.
Defined.

Section FOL_helpers.

  Context {Σ : Signature}.
  
  Lemma Constructive_dilemma Γ p q r s:
    well_formed p ->
    well_formed q ->
    well_formed r ->
    well_formed s ->
    Γ ⊢ ((p ---> q) ---> (r ---> s) ---> (p or r) ---> (q or s)) using PropositionalReasoning.
  Proof.
    intros wfp wfq wfr wfs.
    unfold patt_or.

    toMyGoal.
    { wf_auto2. }

    mgIntro. mgIntro. mgIntro. mgIntro.
    mgApply 1.
    mgApply 2.
    mgIntro.
    mgApply 3.
    mgApply 0.
    mgExactn 4.
  Defined.

  Lemma prf_add_assumption Γ a b i :
    well_formed a ->
    well_formed b ->
    Γ ⊢ b using i ->
    Γ ⊢ (a ---> b) using i.
  Proof.
    intros wfa wfb H.
    eapply MP.
    { apply H. }
    { usePropositionalReasoning. apply P1; wf_auto2. }
  Defined.

  Lemma prf_impl_distr_meta Γ a b c i:
    well_formed a ->
    well_formed b ->
    well_formed c ->
    Γ ⊢ (a ---> (b ---> c)) using i ->
    Γ ⊢ ((a ---> b) ---> (a ---> c)) using i.
  Proof.
    intros wfa wfb wfc H.
    eapply MP.
    { apply H. }
    { usePropositionalReasoning. apply P2; wf_auto2. }
  Defined.

  Lemma prf_add_lemma_under_implication Γ l g h:
    wf l ->
    well_formed g ->
    well_formed h ->
    Γ ⊢ ((foldr patt_imp h l) --->
         ((foldr patt_imp g (l ++ [h])) --->
          (foldr patt_imp g l)))
    using PropositionalReasoning.
  Proof.
    intros wfl wfg wfh.
    induction l; simpl.
    - apply modus_ponens; auto.
    - pose proof (wfal := wfl).
      unfold wf in wfl. apply andb_prop in wfl. destruct wfl as [wfa wfl].
      specialize (IHl wfl).
      assert (H1: Γ ⊢ a --->
                      foldr patt_imp h l --->
                      foldr patt_imp g (l ++ [h]) --->
                      foldr patt_imp g l
              using PropositionalReasoning).
      { apply prf_add_assumption; wf_auto2. }

      assert (H2 : Γ ⊢ (a ---> foldr patt_imp h l) --->
                       (a ---> foldr patt_imp g (l ++ [h]) --->
                       foldr patt_imp g l)
              using PropositionalReasoning).
      { apply prf_impl_distr_meta;[wf_auto2|wf_auto2|wf_auto2|]. apply H1. }

      assert (H3 : Γ ⊢ ((a ---> foldr patt_imp g (l ++ [h]) ---> foldr patt_imp g l)
                          ---> ((a ---> foldr patt_imp g (l ++ [h])) ---> (a ---> foldr patt_imp g l)))
              using PropositionalReasoning).
      { apply P2; wf_auto2. }

      eapply prf_weaken_conclusion_meta_meta.
      4: apply H3. 4: apply H2. all: wf_auto2.
  Defined.

  Lemma prf_add_lemma_under_implication_meta Γ l g h i:
    wf l ->
    well_formed g ->
    well_formed h ->
    Γ ⊢ (foldr patt_imp h l) using i ->
    Γ ⊢ ((foldr patt_imp g (l ++ [h])) ---> (foldr patt_imp g l)) using i.
  Proof.
    intros WFl WFg WGh H.
    eapply MP.
    { apply H. }
    { usePropositionalReasoning. apply prf_add_lemma_under_implication. all: wf_auto2. }
  Defined.

  Lemma prf_add_lemma_under_implication_meta_meta Γ l g h i:
    wf l ->
    well_formed g ->
    well_formed h ->
    Γ ⊢ (foldr patt_imp h l) using i ->
    Γ ⊢ (foldr patt_imp g (l ++ [h])) using i ->
    Γ ⊢ (foldr patt_imp g l) using i.
  Proof.
    intros WFl WFg WGh H H0.
    eapply MP.
    { apply H0. }
    { apply prf_add_lemma_under_implication_meta. 4: apply H. all: wf_auto2. }
  Defined.

  Lemma myGoal_assert Γ l g h i:
    well_formed h ->
    @mkMyGoal Σ Γ l h i ->
    @mkMyGoal Σ Γ (l ++ [h]) g i ->
    @mkMyGoal Σ Γ l g i.
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

  Lemma prf_add_lemma_under_implication_generalized Γ l1 l2 g h:
    wf l1 ->
    wf l2 ->
    well_formed g ->
    well_formed h ->
    Γ ⊢ ((foldr patt_imp h l1) ---> ((foldr patt_imp g (l1 ++ [h] ++ l2)) ---> (foldr patt_imp g (l1 ++ l2))))
    using PropositionalReasoning.
  Proof.
    intros wfl1 wfl2 wfg wfh.
    induction l1; simpl.
    - apply modus_ponens; wf_auto2.
    - pose proof (wfal1 := wfl1).
      unfold wf in wfl1. simpl in wfl1. apply andb_prop in wfl1. destruct wfl1 as [wfa wfl1].
      specialize (IHl1 wfl1).
      assert (H1: Γ ⊢ a ---> foldr patt_imp h l1 ---> foldr patt_imp g (l1 ++ [h] ++ l2) ---> foldr patt_imp g (l1 ++ l2) using PropositionalReasoning).
      { apply prf_add_assumption; wf_auto2. }
      assert (H2 : Γ ⊢ (a ---> foldr patt_imp h l1) ---> (a ---> foldr patt_imp g (l1 ++ [h] ++ l2) ---> foldr patt_imp g (l1 ++ l2)) using PropositionalReasoning).
      { apply prf_impl_distr_meta;[wf_auto2|wf_auto2|wf_auto2|]. exact H1. }
      assert (H3 : Γ ⊢ ((a ---> foldr patt_imp g (l1 ++ [h] ++ l2) ---> foldr patt_imp g (l1 ++ l2))
                          ---> ((a ---> foldr patt_imp g (l1 ++ [h] ++ l2)) ---> (a ---> foldr patt_imp g (l1 ++ l2)))) using PropositionalReasoning).
      { apply P2; wf_auto2. }

      eapply prf_weaken_conclusion_meta_meta.
      4: apply H3. 4: assumption. all: wf_auto2.
  Defined.
  
  Lemma prf_add_lemma_under_implication_generalized_meta Γ l1 l2 g h i:
    wf l1 ->
    wf l2 ->
    well_formed g ->
    well_formed h ->
    Γ ⊢ (foldr patt_imp h l1) using i ->
    Γ ⊢ ((foldr patt_imp g (l1 ++ [h] ++ l2)) ---> (foldr patt_imp g (l1 ++ l2))) using i.
  Proof.
    intros WFl1 WFl2 WFg WGh H.
    eapply MP.
    { apply H. }
    { usePropositionalReasoning.
      apply prf_add_lemma_under_implication_generalized; wf_auto2.
    }
  Defined.
  
  Lemma prf_add_lemma_under_implication_generalized_meta_meta Γ l1 l2 g h i:
    wf l1 ->
    wf l2 ->
    well_formed g ->
    well_formed h ->
    Γ ⊢ (foldr patt_imp h l1) using i ->
    Γ ⊢ (foldr patt_imp g (l1 ++ [h] ++ l2)) using i ->
    Γ ⊢ (foldr patt_imp g (l1 ++ l2)) using i.
  Proof.
    intros WFl1 WFl2 WFg WGh H H0.
    eapply MP.
    { apply H0. }
    { apply prf_add_lemma_under_implication_generalized_meta.
      5: apply H. all: wf_auto2.
    }
  Defined.

  Lemma myGoal_assert_generalized Γ l1 l2 g h i:
    well_formed h ->
    @mkMyGoal Σ Γ l1 h i ->
    @mkMyGoal Σ Γ (l1 ++ [h] ++ l2) g i ->
    @mkMyGoal Σ Γ (l1 ++ l2) g i.
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

End FOL_helpers.

Tactic Notation "mgAssert" "(" constr(t) ")" :=
  match goal with
  | |- @of_MyGoal ?Sgm (@mkMyGoal ?Sgm ?Ctx ?l ?g ?i) =>
    let Hwf := fresh "Hwf" in
    assert (Hwf : well_formed t);
    [idtac|
      let H := fresh "H" in
      assert (H : @mkMyGoal Sgm Ctx l t i);
      [ | (eapply (@myGoal_assert Sgm Ctx l g t i Hwf H); rewrite [_ ++ _]/=; clear H)]
    ]
  end.

Local Example ex_mgAssert {Σ : Signature} Γ a:
  well_formed a ->
  Γ ⊢ (a ---> a ---> a) using PropositionalReasoning.
Proof.
  intros wfa.
  toMyGoal.
  { wf_auto2. }
  mgIntro. mgIntro.
  mgAssert (a).
  { wf_auto2. }
  { mgExactn 1. }
  { mgExactn 2. }
Qed.

Tactic Notation "mgAssert" "(" constr(t) ")" "using" "first" constr(n) :=
  lazymatch goal with
  | |- @of_MyGoal ?Sgm (@mkMyGoal ?Sgm ?Ctx ?l ?g ?i) =>
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
      assert (H : @mkMyGoal Sgm Ctx l1 t i) ;
      [
        (eapply cast_proof_mg_hyps; [(rewrite Heql1; reflexivity)|]);  clear l1 l2 Heql1 Heql2
      | apply (cast_proof_mg_hyps Heql1) in H;
        eapply (@myGoal_assert_generalized Sgm Ctx (take n l) (drop n l) g t i Hwf H);
        rewrite [_ ++ _]/=; clear l1 l2 Heql1 Heql2 H] 
    ]
  end.

Local Example ex_assert_using {Σ : Signature} Γ p q a b:
  well_formed a = true ->
  well_formed b = true ->
  well_formed p = true ->
  well_formed q = true ->
  Γ ⊢ a ---> p and q ---> b ---> ! ! q using PropositionalReasoning.
Proof.
  intros wfa wfb wfp wfq.
  toMyGoal.
  { wf_auto2. }
  do 3 mgIntro.
  mgAssert (p) using first 2.
  { wf_auto2. }
  { admit. }
  { admit. }
Abort.


Section FOL_helpers.

  Context {Σ : Signature}.
  
  Lemma P4i' (Γ : Theory) (A : Pattern) :
    well_formed A →
    Γ ⊢ ((!A ---> A) ---> A) using PropositionalReasoning.
  Proof.
    intros wfA.
    assert (H1: Γ ⊢ ((! A ---> ! ! A) ---> ! ! A) using PropositionalReasoning).
    { apply P4i. wf_auto2. }
    assert (H2: Γ ⊢ ((! A ---> A) ---> (! A ---> ! ! A)) using PropositionalReasoning).
    { eapply prf_weaken_conclusion_meta. 
      4: apply not_not_intro.
      all: wf_auto2.
    }
    
    eapply prf_strenghten_premise_meta_meta. 4: apply H2.
    4: eapply prf_weaken_conclusion_meta_meta. 7: apply not_not_elim.
    8: { apply H1. }
    all: wf_auto2.
  Defined.

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
    Γ ⊢ ((p ---> r) ---> (q ---> r) ---> (p or q) ---> r)
    using PropositionalReasoning.
  Proof.
    intros wfp wfq wfr.
    pose proof (H1 := @Constructive_dilemma Σ Γ p r q r wfp wfr wfq wfr).
    assert (Γ ⊢ ((r or r) ---> r) using PropositionalReasoning).
    { unfold patt_or. apply P4i'. wf_auto2. }
    eapply cast_proof' in H1.
    2: { rewrite -> tofold. do 3 rewrite -> consume. reflexivity. }
    eapply prf_weaken_conclusion_iter_meta_meta in H1. 5: apply H.
    { apply H1. }
    all: wf_auto2.
  Defined.

  Lemma prf_disj_elim_meta Γ p q r i:
    well_formed p ->
    well_formed q ->
    well_formed r ->
    Γ ⊢ (p ---> r) using i ->
    Γ ⊢ ((q ---> r) ---> (p or q) ---> r) using i.
  Proof.
    intros WFp WHq WFr H.
    eapply MP. apply H. usePropositionalReasoning. apply prf_disj_elim.
    all: wf_auto2.
  Defined.
  
  Lemma prf_disj_elim_meta_meta Γ p q r i:
    well_formed p ->
    well_formed q ->
    well_formed r ->
    Γ ⊢ (p ---> r) using i ->
    Γ ⊢ (q ---> r) using i ->
    Γ ⊢ ((p or q) ---> r) using i.
  Proof.
    intros WFp WHq WFr H H0.
    eapply MP. apply H0. apply prf_disj_elim_meta. 4: apply H.
    all: wf_auto2.
  Defined.

  Lemma prf_disj_elim_meta_meta_meta Γ p q r i:
    well_formed p ->
    well_formed q ->
    well_formed r ->
    Γ ⊢ (p ---> r) using i ->
    Γ ⊢ (q ---> r) using i ->
    Γ ⊢ (p or q) using i ->
    Γ ⊢ r using i.
  Proof.
    intros WFp WHq WFr H H0 H1.
    eapply MP. apply H1.
    apply prf_disj_elim_meta_meta.
    all: assumption.
  Defined.
  
  Lemma prf_add_proved_to_assumptions Γ l a g i:
    wf l ->
    well_formed a ->
    well_formed g ->
    Γ ⊢ a using i->
    Γ ⊢ ((foldr patt_imp g (a::l)) ---> (foldr patt_imp g l)) using i.
  Proof.
    intros wfl wfa wfg Ha.
    induction l.
    - simpl.
      pose proof (@modus_ponens Σ Γ _ _ wfa wfg).
      eapply MP. apply Ha. usePropositionalReasoning. apply H.
    - pose proof (wfa0l := wfl).
      unfold wf in wfl. simpl in wfl. apply andb_prop in wfl. destruct wfl as [wfa0 wfl].
      specialize (IHl wfl).
      simpl in IHl. simpl.
      (* < change a0 and a in the LHS > *)
      assert (H : Γ ⊢ (a ---> a0 ---> foldr patt_imp g l) ---> (a0 ---> a ---> foldr patt_imp g l) using PropositionalReasoning).
      { apply reorder; wf_auto2. }

      eapply cast_proof'.
      { rewrite -> tofold. rewrite -> consume. reflexivity. }
      pose proof (H0 := @prf_strenghten_premise_iter_meta_meta Σ Γ [] []).
      simpl in H0. simpl.
      specialize (H0 (a0 ---> a ---> foldr patt_imp g l) (a ---> a0 ---> foldr patt_imp g l)).
      specialize (H0 (a0 ---> foldr patt_imp g l)). simpl in H0. simpl.
      simpl. apply H0. all: try_wfauto2.
      { usePropositionalReasoning. apply H. }
      clear H0 H.
      (* </change a0 and a > *)
      assert (Γ ⊢ ((a ---> a0 ---> foldr patt_imp g l) ---> (a0 ---> foldr patt_imp g l)) using i).
      { eapply MP. 2: { usePropositionalReasoning. apply modus_ponens; wf_auto2. } apply Ha. }
      
      eapply prf_strenghten_premise_meta_meta. 5: apply H. all: try_wfauto2.
      usePropositionalReasoning.
      apply reorder; wf_auto2.
  Defined.

  Lemma prf_add_proved_to_assumptions_meta Γ l a g i:
    wf l ->
    well_formed a ->
    well_formed g ->
    Γ ⊢ a using i ->
    Γ ⊢ (foldr patt_imp g (a::l)) using i ->
    Γ ⊢ (foldr patt_imp g l) using i.
  Proof.
    intros WFl WFa WFg H H0.
    eapply MP.
    apply H0.
    eapply prf_add_proved_to_assumptions.
    4: apply H.
    all: wf_auto2.
  Defined.
  
  Lemma MyGoal_add Γ l g h i:
    Γ ⊢ h using i ->
    @mkMyGoal Σ Γ (h::l) g i ->
    @mkMyGoal Σ Γ l g i.
  Proof.
    intros H H0.
    unfold of_MyGoal in *. simpl in *.
    intros wfg wfl.
    apply prf_add_proved_to_assumptions_meta with (a := h).
    5: apply H0.
    all: try assumption.
    { abstract (pose (tmp := proj1_sig H); apply proved_impl_wf in tmp; exact tmp). }
    { abstract (
          unfold wf;
          simpl;
          pose (tmp := proj1_sig H);
          apply proved_impl_wf in tmp;
          rewrite tmp;
          simpl;
          exact wfl
      ).
    }
  Defined.

End FOL_helpers.

Tactic Notation "mgAdd" constr(n) :=
  match goal with
  | |- @of_MyGoal ?Sgm (@mkMyGoal ?Sgm ?Ctx ?l ?g ?i) =>
    apply (@MyGoal_add Sgm Ctx l g _ i n)
  end.

Section FOL_helpers.
  
  Context {Σ : Signature}.
  
  Local Example ex_mgAdd Γ l g h i:
    wf l ->
    well_formed g ->
    well_formed h ->
    Γ ⊢ (h ---> g) using i ->
    Γ ⊢ h using i ->
    Γ ⊢ g using i.
  Proof.
    intros WFl WFg WFh H H0. toMyGoal.
    { wf_auto2. }
    mgAdd H0.
    mgAdd H.
    mgApply 0.    
    mgExactn 1.
  Defined.


  Lemma prf_clear_hyp Γ l1 l2 g h:
    wf l1 ->
    wf l2 ->
    well_formed g ->
    well_formed h ->
    Γ ⊢ (foldr patt_imp g (l1 ++ l2)) ---> (foldr patt_imp g (l1 ++ [h] ++ l2))
    using PropositionalReasoning.
  Proof.
    intros wfl1 wfl2 wfg wfh.
    induction l1; simpl.
    - apply P1; wf_auto2.
    - unfold wf in wfl1. simpl in wfl1. apply andb_prop in wfl1. destruct wfl1 as [wfa wfl1].
      specialize (IHl1 wfl1).

      assert (H1: Γ ⊢ a ---> foldr patt_imp g (l1 ++ l2) ---> foldr patt_imp g (l1 ++ [h] ++ l2) using PropositionalReasoning).
      {
        toMyGoal.
        { wf_auto2. }
        mgAdd IHl1.
        mgIntro. mgExactn 0.
      }
      apply prf_impl_distr_meta; try_wfauto2. apply H1.
  Defined.

  Lemma prf_clear_hyp_meta Γ l1 l2 g h i:
    wf l1 ->
    wf l2 ->
    well_formed g ->
    well_formed h ->
    Γ ⊢ (foldr patt_imp g (l1 ++ l2)) using i ->
    Γ ⊢ (foldr patt_imp g (l1 ++ [h] ++ l2)) using i.
  Proof.
    intros. eapply MP.
    apply H3.
    usePropositionalReasoning.
    apply prf_clear_hyp; wf_auto2.
  Defined.  

  (* TODO move somewhere else *)
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

  Lemma myGoal_clear_hyp Γ l1 l2 g h i:
    @mkMyGoal Σ Γ (l1 ++ l2) g i ->
    @mkMyGoal Σ Γ (l1 ++ h::l2) g i.
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
  | |- @of_MyGoal ?Sgm (@mkMyGoal ?Sgm ?Ctx ?l ?g ?i) =>
    let l1 := fresh "l1" in
    let l2 := fresh "l2" in
    let Heql1 := fresh "Heql1" in
    let Heql2 := fresh "Heql2" in
    eapply cast_proof_mg_hyps;
    [(rewrite -[l](take_drop n); reflexivity)|];
    remember (take n l) as l1 eqn:Heql1 in |-;
    remember (drop n l) as l2 eqn:Heql2 in |-;
    eapply cast_proof_mg_hyps;
    [(rewrite -Heql1; rewrite -Heql2; reflexivity)|];
    simpl in Heql1; simpl in Heql2;
    let a := fresh "a" in
    let Hd := fresh "Hd" in
    destruct l2 as [|a l2''] eqn:Hd in *|-;[congruence|];
    eapply cast_proof_mg_hyps;
    [(rewrite -> Hd at 1; reflexivity)|];
    let Heqa := fresh "Heqa" in
    let Heql2' := fresh "Heql2'" in
    inversion Heql2 as [[Heqa Heql2'] ]; clear Heql2;
    apply myGoal_clear_hyp;
    eapply cast_proof_mg_hyps;
    [(try(rewrite -> Heql1 at 1); try(rewrite -> Heql2' at 1); reflexivity)|];
    clear Hd Heql2' Heqa l2 l2'' a Heql1 l1;
    eapply cast_proof_mg_hyps;[rewrite {1}[_ ++ _]/=; reflexivity|]
  end.

Local Example ex_mgClear {Σ : Signature} Γ a b c:
  well_formed a ->
  well_formed b ->
  well_formed c ->
  Γ ⊢ a ---> (b ---> (c ---> b)) using PropositionalReasoning.
Proof.
  intros wfa wfb wfc.
  toMyGoal.
  { wf_auto2. }
  repeat mgIntro.
  mgClear 2.
  mgClear 0.
  mgExactn 0.
Defined.

Section FOL_helpers.
  
  Context {Σ : Signature}.
  
  Lemma not_concl Γ p q:
    well_formed p ->
    well_formed q ->
    Γ ⊢ (p ---> (q ---> ((p ---> ! q) ---> ⊥))) using PropositionalReasoning.
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
  Lemma helper Γ p q r:
    well_formed p ->
    well_formed q ->
    well_formed r ->
    Γ ⊢ (p ---> (q ---> ((p ---> (q ---> r)) ---> r))) using PropositionalReasoning.
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

  Lemma reorder_last_to_head Γ g x l:
    wf l ->
    well_formed g ->
    well_formed x ->
    Γ ⊢ ((foldr patt_imp g (x::l)) ---> (foldr patt_imp g (l ++ [x]))) using PropositionalReasoning.
  Proof.
    intros wfl wfg wfx.
    induction l.
    - simpl. apply A_impl_A. wf_auto2.
    - pose proof (wfal := wfl).
      unfold wf in wfl. simpl in wfl. apply andb_prop in wfl. destruct wfl as [wfa wfl].
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

  Lemma reorder_last_to_head_meta Γ g x l i:
    wf l ->
    well_formed g ->
    well_formed x ->
    Γ ⊢ (foldr patt_imp g (x::l)) using i ->
    Γ ⊢ (foldr patt_imp g (l ++ [x])) using i.
  Proof.
    intros WFl WFG WFx H.
    eapply MP.
    apply H.
    usePropositionalReasoning.
    apply reorder_last_to_head; wf_auto2.
  Defined.
  
  (* Iterated modus ponens.
     For l = [x₁, ..., xₙ], it says that
     Γ ⊢ ((x₁ -> ... -> xₙ -> (x₁ -> ... -> xₙ -> r)) -> r)
  *)
  Lemma modus_ponens_iter Γ l r:
    wf l ->
    well_formed r ->
    Γ ⊢ (foldr patt_imp r (l ++ [foldr patt_imp r l])) using PropositionalReasoning.
  Proof.
    intros wfl wfr.
    induction l.
    - simpl. apply A_impl_A. exact wfr.
    - pose proof (wfal := wfl).
      unfold wf in wfl. simpl in wfl. apply andb_prop in wfl. destruct wfl as [wfa wfl].
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
  
  Lemma and_impl Γ p q r:
    well_formed p ->
    well_formed q ->
    well_formed r ->
    Γ ⊢ ((p and q ---> r) ---> (p ---> (q ---> r))) using PropositionalReasoning.
  Proof.
    intros wfp wfq wfr.
    toMyGoal.
    { wf_auto2. }
    repeat mgIntro.
    unfold patt_and. mgApply 0.
    mgIntro. unfold patt_or at 2.
    mgAssert ((! ! p)).
    { wf_auto2. }
    {
      mgAdd (@not_not_intro Σ Γ p wfp).
      mgApply 0.
      mgExactn 2.
    }
    mgAssert ((! q)).
    { wf_auto2. }
    {
      mgApply 3. mgExactn 4.
    }
    mgApply 5. mgExactn 2.
  Defined.
  
  Lemma and_impl' Γ p q r:
    well_formed p ->
    well_formed q ->
    well_formed r ->
    Γ ⊢ ((p ---> (q ---> r)) ---> ((p and q) ---> r)) using PropositionalReasoning.
  Proof.
    intros wfp wfq wfr.
    toMyGoal.
    { wf_auto2. }
    repeat mgIntro.
    mgAssert (p).
    { wf_auto2. }
    {
      mgAdd (@pf_conj_elim_l Σ Γ p q wfp wfq).
      mgApply 0.
      mgExactn 2.
    }
    mgAssert (q).
    { wf_auto2. }
    {
      mgAdd (@pf_conj_elim_r Σ Γ p q wfp wfq).
      mgApply 0.
      mgExactn 2.
    }
    (* This pattern is basically an "apply ... in" *)
    mgAssert ((q ---> r)).
    { wf_auto2. }
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
              (fold_right patt_imp r (l ++ [p or q]))))
    using PropositionalReasoning.
  Proof.
    intros wfl wfp wfq wfr.
    induction l.
    - simpl. apply prf_disj_elim; wf_auto2.
    - pose proof (wfal := wfl).
      unfold wf in wfl. simpl in wfl. apply andb_prop in wfl. destruct wfl as [wfa wfl].
      specialize (IHl wfl).
      simpl in *.
      toMyGoal.
      { wf_auto2. }
      repeat mgIntro.
      mgAdd IHl.
      mgAssert ((foldr patt_imp r (l ++ [p]))).
      { wf_auto2. }
      { mgApply 1. mgExactn 3. }
      mgAssert ((foldr patt_imp r (l ++ [q]))).
      { wf_auto2. }
      { mgApply 2. mgExactn 3. }
      mgAssert ((foldr patt_imp r (l ++ [q]) ---> foldr patt_imp r (l ++ [p or q]))).
      { wf_auto2. }
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
              (fold_right patt_imp r (l₁ ++ [p or q] ++ l₂))))
    using PropositionalReasoning.  
  Proof.
    intros wfl₁ wfl₂ wfp wfq wfr.
    move: l₁ wfl₁.
    induction l₂; intros l₁ wfl₁.
    - simpl. apply prf_disj_elim_iter; wf_auto2.
    - pose proof (wfal₂ := wfl₂).
      unfold wf in wfl₂. simpl in wfl₂. apply andb_prop in wfl₂. destruct wfl₂ as [wfa wfl₂].

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

  Lemma prf_disj_elim_iter_2_meta Γ l₁ l₂ p q r i:
    wf l₁ ->
    wf l₂ ->
    well_formed p ->
    well_formed q ->
    well_formed r ->
    Γ ⊢ (fold_right patt_imp r (l₁ ++ [p] ++ l₂)) using i ->
    Γ ⊢ ((fold_right patt_imp r (l₁ ++ [q] ++ l₂))
              --->                                                                
              (fold_right patt_imp r (l₁ ++ [p or q] ++ l₂))) using i.
            
  Proof.
    intros WFl1 WFl2 WFp WFq WFr H.
    eapply MP.
    apply H.
    usePropositionalReasoning.
    apply prf_disj_elim_iter_2; wf_auto2.
  Defined.
  
  Lemma prf_disj_elim_iter_2_meta_meta Γ l₁ l₂ p q r i:
    wf l₁ ->
    wf l₂ ->
    well_formed p ->
    well_formed q ->
    well_formed r ->
    Γ ⊢ (fold_right patt_imp r (l₁ ++ [p] ++ l₂)) using i ->
    Γ ⊢ (fold_right patt_imp r (l₁ ++ [q] ++ l₂)) using i ->
    Γ ⊢ (fold_right patt_imp r (l₁ ++ [p or q] ++ l₂)) using i.
  Proof.
    intros WFl1 WFl2 WFp WFq WFr H H0.
    eapply MP.
    2: { apply prf_disj_elim_iter_2_meta; try_wfauto2. apply H. }
    apply H0.
  Defined.

  Lemma MyGoal_disj_elim Γ l₁ l₂ p q r i:
    @mkMyGoal Σ Γ (l₁ ++ [p] ++ l₂) r i ->
    @mkMyGoal Σ Γ (l₁ ++ [q] ++ l₂) r i ->
    @mkMyGoal Σ Γ (l₁ ++ [p or q] ++ l₂) r i.
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

Tactic Notation "mgDestructOr" constr(n) :=
  match goal with
  | |- @of_MyGoal ?Sgm (@mkMyGoal ?Sgm ?Ctx ?l ?g ?i) =>
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
  
  Local Example exd Γ a b p q c i:
    well_formed a ->
    well_formed b ->
    well_formed p ->
    well_formed q ->
    well_formed c ->
    Γ ⊢ (a ---> p ---> b ---> c) using i ->
    Γ ⊢ (a ---> q ---> b ---> c) using i->
    Γ ⊢ (a ---> (p or q) ---> b ---> c) using i.
  Proof.
    intros WFa WFb WFp WFq WFc H H0.
    toMyGoal.
    { wf_auto2. } 
    repeat mgIntro.
    mgDestructOr 1.
    - fromMyGoal. apply H.
    - fromMyGoal. apply H0.
  Defined.

  Lemma pf_iff_split Γ A B i:
    well_formed A ->
    well_formed B ->
    Γ ⊢ A ---> B using i ->
    Γ ⊢ B ---> A using i ->
    Γ ⊢ A <---> B using i.
  Proof.
    intros wfA wfB AimplB BimplA.
    unfold patt_iff.
    apply conj_intro_meta; try_wfauto2; assumption.
  Defined.
  
  Lemma pf_iff_proj1 Γ A B i:
    well_formed A ->
    well_formed B ->
    Γ ⊢ A <---> B using i ->
    Γ ⊢ A ---> B using i.
  Proof.
    intros WFA WFB H. unfold patt_iff in H.
    apply pf_conj_elim_l_meta in H; try_wfauto2; assumption.
  Defined.

  Lemma pf_iff_proj2 Γ A B i:
    well_formed A ->
    well_formed B ->
    Γ ⊢ (A <---> B) using i ->
    Γ ⊢ (B ---> A) using i.
  Proof.
    intros WFA WFB H. unfold patt_iff in H.
    apply pf_conj_elim_r_meta in H; try_wfauto2; assumption.
  Defined.

  Lemma pf_iff_iff Γ A B i:
    well_formed A ->
    well_formed B ->
    prod ((Γ ⊢ (A <---> B) using i) -> (prod (Γ ⊢ (A ---> B) using i) (Γ ⊢ (B ---> A) using i)))
    ( (prod (Γ ⊢ (A ---> B) using i)  (Γ ⊢ (B ---> A) using i)) -> (Γ ⊢ (A <---> B) using i)).
  Proof.
    intros WFA WFB.
    split; intros H.
    {
      pose proof (H1 := pf_iff_proj1 WFA WFB H).
      pose proof (H2 := pf_iff_proj2 WFA WFB H).
      split; assumption.
    }
    {
      destruct H as [H1 H2].
      apply pf_iff_split; assumption.
    }
  Defined.

  Lemma pf_iff_equiv_refl Γ A :
    well_formed A ->
    Γ ⊢ (A <---> A) using PropositionalReasoning.
  Proof.
    intros WFA.
    apply pf_iff_split; try_wfauto2; apply A_impl_A; assumption.
  Defined.

  Lemma pf_iff_equiv_sym Γ A B i:
    well_formed A ->
    well_formed B ->
    Γ ⊢ (A <---> B) using i ->
    Γ ⊢ (B <---> A) using i.
  Proof.
    intros wfA wfB H.
    pose proof (H2 := H).
    apply pf_iff_proj2 in H2; try_wfauto2.
    rename H into H1.
    apply pf_iff_proj1 in H1; try_wfauto2.
    apply pf_iff_split; try_wfauto2; assumption.
  Defined.

  Lemma pf_iff_equiv_trans Γ A B C i:
    well_formed A ->
    well_formed B ->
    well_formed C ->
    Γ ⊢ (A <---> B) using i ->
    Γ ⊢ (B <---> C) using i ->
    Γ ⊢ (A <---> C) using i.
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

  Lemma prf_conclusion Γ a b i:
    well_formed a ->
    well_formed b ->
    Γ ⊢ b using i ->
    Γ ⊢ (a ---> b) using i.
  Proof.
    intros WFa WFb H. eapply MP.
    apply H.
    usePropositionalReasoning.
    apply P1; wf_auto2.
  Defined.
    
  Lemma prf_prop_bott_iff Γ AC:
    Γ ⊢ ((subst_ctx AC patt_bott) <---> patt_bott) using BasicReasoning.
  Proof.
    induction AC; simpl.
    - usePropositionalReasoning. apply pf_iff_equiv_refl; auto.
    - apply pf_iff_iff in IHAC; auto.
      destruct IHAC as [IH1 IH2].
      apply pf_iff_split; try_wfauto2.
      + pose proof (H := IH1).
        eapply Framing_left in H.
        eassert (Γ ⊢ (⊥ $ ?[psi] ---> ⊥) using BasicReasoning).
        { apply Prop_bott_left. shelve. }
        eapply syllogism_meta. 5: apply H0. 4: apply H. all: try_wfauto2. apply pile_refl.
      + usePropositionalReasoning. apply bot_elim; wf_auto2.
    - apply pf_iff_iff in IHAC; auto.
      destruct IHAC as [IH1 IH2].
      apply pf_iff_split; try_wfauto2.
      + pose proof (H := IH1).
        eapply Framing_right in H.
        eassert (Γ ⊢ ( ?[psi] $ ⊥ ---> ⊥) using BasicReasoning).
        { apply Prop_bott_right. shelve. }
        eapply syllogism_meta. 5: apply H0. 4: apply H. all: try_wfauto2. apply pile_refl.
      + usePropositionalReasoning. apply bot_elim; wf_auto2.
        Unshelve. all: wf_auto2.
  Defined.

  Lemma Prop_disj_left (Γ : Theory) (ϕ₁ ϕ₂ ψ : Pattern) :
    well_formed ϕ₁ ->
    well_formed ϕ₂ ->
    well_formed ψ ->
    Γ ⊢ (ϕ₁ or ϕ₂) $ ψ ---> (ϕ₁ $ ψ) or (ϕ₂ $ ψ) using BasicReasoning.
  Proof.
    intros wfϕ₁ wfϕ₂ wfψ.
    unshelve (eexists).
    {
      apply Prop_disj_left; assumption.
    }
    {
      abstract (
        constructor; simpl;
        [(exact I)|(set_solver)|(set_solver)|(reflexivity)]
      ).
    }
  Defined.
  
  Lemma Prop_disj_right (Γ : Theory) (ϕ₁ ϕ₂ ψ : Pattern) :
    well_formed ϕ₁ ->
    well_formed ϕ₂ ->
    well_formed ψ ->
    Γ ⊢ ψ $ (ϕ₁ or ϕ₂)  ---> (ψ $ ϕ₁) or (ψ $ ϕ₂) using BasicReasoning.
  Proof.
    intros wfϕ₁ wfϕ₂ wfψ.
    unshelve (eexists).
    {
      apply Prop_disj_right; assumption.
    }
    {
      abstract (
        constructor; simpl;
        [(exact I)|(set_solver)|(set_solver)|(reflexivity)]
      ).
    }
  Defined.

  Lemma prf_prop_or_iff Γ AC p q:
    well_formed p ->
    well_formed q ->
    Γ ⊢ ((subst_ctx AC (p or q)) <---> ((subst_ctx AC p) or (subst_ctx AC q))) using BasicReasoning.
  Proof.
    intros wfp wfq.
    induction AC; simpl.
    - usePropositionalReasoning. apply pf_iff_equiv_refl; wf_auto2.
    - apply pf_iff_iff in IHAC; try_wfauto2.
      destruct IHAC as [IH1 IH2].
      apply pf_iff_split; try_wfauto2.
      + pose proof (H := IH1).
        eapply Framing_left in H. 2: apply pile_refl.
        eapply syllogism_meta. 4: apply H.
        all: try_wfauto2.
        remember (subst_ctx AC p) as p'.
        remember (subst_ctx AC q) as q'.
        apply Prop_disj_left. all: subst; wf_auto2.
      + eapply prf_disj_elim_meta_meta; try_wfauto2.
        * apply Framing_left; try_wfauto2. apply pile_refl.
          eapply prf_weaken_conclusion_meta_meta. 4: apply IH2. all: try_wfauto2.
          usePropositionalReasoning.
          apply disj_left_intro; wf_auto2.
        * apply Framing_left; try_wfauto2. apply pile_refl.
          eapply prf_weaken_conclusion_meta_meta. 4: apply IH2. all: try_wfauto2.
          usePropositionalReasoning.
          apply disj_right_intro; wf_auto2.
    - apply pf_iff_iff in IHAC; try_wfauto2.
      destruct IHAC as [IH1 IH2].
      apply pf_iff_split; try_wfauto2.
      + pose proof (H := IH1).
        eapply Framing_right in H.
        eapply syllogism_meta. 4: apply H.
        all: try_wfauto2.
        remember (subst_ctx AC p) as p'.
        remember (subst_ctx AC q) as q'.
        apply Prop_disj_right. all: subst; wf_auto2. apply pile_refl.
      + eapply prf_disj_elim_meta_meta; try_wfauto2.
        * apply Framing_right; try_wfauto2. apply pile_refl.
          eapply prf_weaken_conclusion_meta_meta. 4: apply IH2. all: try_wfauto2.
          usePropositionalReasoning.
          apply disj_left_intro; wf_auto2.
        * apply Framing_right; try_wfauto2. apply pile_refl.
          eapply prf_weaken_conclusion_meta_meta. 4: apply IH2. all: try_wfauto2.
          usePropositionalReasoning.
          apply disj_right_intro; wf_auto2.
  Defined.

  Lemma Ex_quan (Γ : Theory) (ϕ : Pattern) (y : evar) :
    well_formed (patt_exists ϕ) ->
    Γ ⊢ (instantiate (patt_exists ϕ) (patt_free_evar y) ---> (patt_exists ϕ))
    using BasicReasoning.
  Proof.
    intros Hwf.
    unshelve (eexists).
    {
      apply ProofSystem.Ex_quan. apply Hwf.
    }
    {
      abstract (
        constructor; simpl;
        [( exact I )
        |( set_solver )
        |( set_solver )
        |( reflexivity )
        ]
      ).
    }
  Defined.

  Lemma hypothesis (Γ : Theory) (axiom : Pattern) :
    well_formed axiom ->
    (axiom ∈ Γ) ->
    Γ ⊢ axiom
    using BasicReasoning.
  Proof.
    intros Hwf Hin.
    unshelve (eexists).
    {
      apply ProofSystem.hypothesis. apply Hwf. apply Hin.
    }
    {
      abstract (
        constructor; simpl;
        [( exact I )
        |( set_solver )
        |( set_solver )
        |( reflexivity )
        ]
      ).
    }
  Defined.

  Lemma Singleton_ctx (Γ : Theory) (C1 C2 : Application_context) (ϕ : Pattern) (x : evar) :
    well_formed ϕ ->
    Γ ⊢ (! ((subst_ctx C1 (patt_free_evar x and ϕ)) and
               (subst_ctx C2 (patt_free_evar x and (! ϕ)))))
    using BasicReasoning.
  Proof.
    intros Hwf.
    unshelve (eexists).
    {
      apply ProofSystem.Singleton_ctx. apply Hwf.
    }
    {
      abstract (
        constructor; simpl;
        [( exact I )
        |( set_solver )
        |( set_solver )
        |( reflexivity )
        ]
      ).
    }
  Defined.

  Lemma Existence (Γ : Theory) :
    Γ ⊢ (ex , patt_bound_evar 0) using BasicReasoning.
  Proof.
    unshelve (eexists).
    {
      apply ProofSystem.Existence.
    }
    {
      abstract (
        constructor; simpl;
        [( exact I )
        |( set_solver )
        |( set_solver )
        |( reflexivity )
        ]
      ).
    }
  Defined.

  Lemma pile_impl_allows_gen_x x gpi svs kt:
    ProofInfoLe (pi_Generic (ExGen := {[x]}, SVSubst := svs, KT := kt)) (pi_Generic gpi) ->
    x ∈ pi_generalized_evars gpi.
  Proof.
    intros [H].
    pose (H1 := @A_impl_A Σ ∅ patt_bott ltac:(wf_auto2)).
    pose (H2 := @prf_add_assumption Σ ∅ (patt_free_evar x) (patt_bott ---> patt_bott) PropositionalReasoning ltac:(wf_auto2) ltac:(wf_auto2) H1).
    pose (H3 := @ProofSystem.Ex_gen Σ ∅ (patt_free_evar x) (patt_bott ---> patt_bott) x ltac:(wf_auto2) ltac:(wf_auto2) (proj1_sig H2) ltac:(simpl; set_solver)).
    pose proof (H' := H ∅ _ H3).
    feed specialize H'.
    {
      constructor; simpl.
      {
        exact I.
      }
      {
        case_match.
        cut ((uses_of_ex_gen ∅ ((⊥ ---> ⊥) ---> patt_free_evar x ---> ⊥ ---> ⊥) x0) = ∅).
        {
          set_solver.
        }
        destruct p as [Hp1 Hp2 Hp3 Hp4]. simpl in *.
        apply propositional_implies_no_uses_ex_gen_2.
        apply Hp1.
      }
      {
        case_match.
        cut (uses_of_svar_subst ∅ ((⊥ ---> ⊥) ---> patt_free_evar x ---> ⊥ ---> ⊥) x0 = ∅).
        {
          set_solver.
        }
        destruct p as [Hp1 Hp2 Hp3 Hp4]. simpl in *.
        apply propositional_implies_no_uses_svar_2.
        apply Hp1.
      }
      {
        case_match.
        cut (uses_kt x0 = false).
        {
          intros H''. rewrite H''. simpl. reflexivity.
        }
        destruct p as [Hp1 Hp2 Hp3 Hp4]. simpl in *.
        apply propositional_implies_noKT.
        apply Hp1.
      }
    }
    inversion H'. simpl in *. clear -pwi_pf_ge0. set_solver.
  Qed.

  Lemma Ex_gen (Γ : Theory) (ϕ₁ ϕ₂ : Pattern) (x : evar) (i : ProofInfo)
    {pile : ProofInfoLe (pi_Generic
            {| pi_generalized_evars := {[x]};
               pi_substituted_svars := ∅;
               pi_uses_kt := false ;
            |}) i} :
    x ∉ free_evars ϕ₂ ->
    Γ ⊢ ϕ₁ ---> ϕ₂ using i ->
    Γ ⊢ (exists_quantify x ϕ₁ ---> ϕ₂) using i.
  Proof.
    intros Hfev [pf Hpf].
    unshelve (eexists).
    {
      apply ProofSystem.Ex_gen.
      { pose proof (pf' := pf). apply proved_impl_wf in pf'.  wf_auto2. }
      { pose proof (pf' := pf). apply proved_impl_wf in pf'.  wf_auto2. }
      { exact pf. }
      { exact Hfev. }
    }
    {
      simpl.
      pose proof (Hnot := not_exgen_x_in_prop).
      specialize (Hnot x).
      constructor; simpl.
      {
        destruct i;[|exact I].
        contradiction.
      }
      {
        destruct i;[contradiction|].
        rewrite union_subseteq.
        split.
        {
          rewrite -elem_of_subseteq_singleton.
          eapply pile_impl_allows_gen_x.
          apply pile.
        }
        {
          inversion Hpf.
          apply pwi_pf_ge0.
        }
      }
      {
        destruct i;[contradiction|].
        inversion Hpf.
        apply pwi_pf_svs0.
      }
      {
        destruct i;[contradiction|].
        inversion Hpf.
        apply pwi_pf_kt0.
      }
    }
  Defined.

  Lemma pile_basic_generic eg svs kt:
    ProofInfoLe BasicReasoning (pi_Generic (ExGen := eg, SVSubst := svs, KT := kt)).
  Proof.
    constructor.
    intros Γ ϕ pf Hpf.
    destruct Hpf as [Hpf1 Hpf2 Hpf3 Hpf4]. simpl in *.
    constructor; simpl.
    { exact I. }
    { set_solver. }
    { set_solver. }
    { unfold implb in Hpf4. case_match.
      { inversion Hpf4. }
      simpl. reflexivity.
    }
  Qed.

  Lemma Prop_ex_left (Γ : Theory) (ϕ ψ : Pattern) :
    well_formed (ex, ϕ) ->
    well_formed ψ ->
    Γ ⊢ (ex , ϕ) $ ψ ---> ex , ϕ $ ψ
    using BasicReasoning.
  Proof.
    intros wfϕ wfψ.
    unshelve (eexists).
    {
      apply ProofSystem.Prop_ex_left.
      { exact wfϕ. }
      { exact wfψ. }
    }
    {
      constructor; simpl.
      { exact I. }
      { set_solver. }
      { set_solver. }
      { reflexivity. }
    }
  Defined.

  Lemma Prop_ex_right (Γ : Theory) (ϕ ψ : Pattern) :
    well_formed (ex, ϕ) ->
    well_formed ψ ->
    Γ ⊢ ψ $ (ex , ϕ) ---> ex , ψ $ ϕ
    using BasicReasoning.
  Proof.
    intros wfϕ wfψ.
    unshelve (eexists).
    {
      apply ProofSystem.Prop_ex_right.
      { exact wfϕ. }
      { exact wfψ. }
    }
    {
      constructor; simpl.
      { exact I. }
      { set_solver. }
      { set_solver. }
      { reflexivity. }
    }
  Defined.

  Lemma useBasicReasoning (Γ : Theory) (ϕ : Pattern) (gpi : GenericProofInfo) :
    Γ ⊢ ϕ using BasicReasoning ->
    Γ ⊢ ϕ using (pi_Generic gpi).
  Proof.
    intros [pf Hpf].
    exists pf.
    destruct Hpf as [Hpf1 Hpf2 Hpf3 Hpf4].
    simpl in *.
    constructor.
    { exact I. }
    { set_solver. }
    { set_solver. }
    { destruct (uses_kt pf); simpl in *.
      { inversion Hpf4. }
      reflexivity.
    }
  Qed.

  Lemma mgUseBasicReasoning
    (Γ : Theory) (l : list Pattern) (g : Pattern) (gpi : GenericProofInfo) :
    @mkMyGoal Σ Γ l g BasicReasoning ->
    @mkMyGoal Σ Γ l g (pi_Generic gpi).
  Proof.
    intros H wf1 wf2.
    specialize (H wf1 wf2).
    apply useBasicReasoning.
    exact H.
  Defined.

  End FOL_helpers.

  Ltac useBasicReasoning :=
    lazymatch goal with
    | [ |- of_MyGoal (@mkMyGoal _ _ _ _ _) ] => apply mgUseBasicReasoning
    | [ |- _ ⊢ _ using _ ] => apply useBasicReasoning
    end.

Section FOL_helpers.
  
  Context {Σ : Signature}.
    

  Lemma prf_prop_ex_iff Γ AC p x:
    evar_is_fresh_in x (subst_ctx AC p) ->
    well_formed (patt_exists p) = true ->
    Γ ⊢ ((subst_ctx AC (patt_exists p)) <---> (exists_quantify x (subst_ctx AC (evar_open 0 x p))))
    using (pi_Generic
    {| pi_generalized_evars := {[x]};
       pi_substituted_svars := ∅;
       pi_uses_kt := false ;
    |}).
  Proof.
    intros Hx Hwf.

    induction AC; simpl.
    - simpl in Hx.
      unfold exists_quantify.
      erewrite evar_quantify_evar_open; auto. 2: now do 2 apply andb_true_iff in Hwf as [_ Hwf].
      usePropositionalReasoning.
      apply pf_iff_equiv_refl. exact Hwf.
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
        eapply syllogism_meta. 4: apply IH1.
        all:auto.
        2: { apply pile_basic_generic. }
        remember (subst_ctx AC (evar_open 0 x p)) as p'.
        unfold exists_quantify.
        simpl. rewrite [evar_quantify x 0 p0]evar_quantify_fresh.
        { eapply evar_is_fresh_in_app_r. apply Hx. }
        useBasicReasoning.
        apply Prop_ex_left. wf_auto2. wf_auto2.
      + clear IH1.

        eapply Framing_left in IH2.
        eapply syllogism_meta. 5: eapply IH2. all: auto.
        2: { apply pile_basic_generic. }
        apply Ex_gen; auto.
        { apply pile_refl. }
        1: {
          unfold exists_quantify.
          simpl.
          rewrite free_evars_evar_quantify.
          unfold evar_is_fresh_in in Hx. simpl in Hx. clear -Hx.
          set_solver.
        }
        
        apply Framing_left; auto.
        1: {
          apply pile_basic_generic.
        }
        unfold evar_open.
        rewrite subst_ctx_bevar_subst.
        unfold exists_quantify. simpl.
        fold (evar_open 0 x (subst_ctx AC p)).
        rewrite -> evar_quantify_evar_open; auto.
        2: now do 2 apply andb_true_iff in Hwfex as [_ Hwfex].
        useBasicReasoning.
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
        eapply syllogism_meta. 4: apply IH1.
        all:auto.
        remember (subst_ctx AC (evar_open 0 x p)) as p'.
        unfold exists_quantify.
        simpl. rewrite [evar_quantify x 0 p0]evar_quantify_fresh.
        { eapply evar_is_fresh_in_app_l. apply Hx. }
        2: { apply pile_basic_generic. }
        useBasicReasoning.
        apply Prop_ex_right. wf_auto2. wf_auto2.
      + clear IH1.

        eapply Framing_right in IH2.
        eapply syllogism_meta. 5: eapply IH2. all: auto.
        2: { apply pile_basic_generic. }

        apply Ex_gen; auto.
        { apply pile_refl. }
        1: {
          unfold exists_quantify.
          simpl.
          rewrite free_evars_evar_quantify.
          unfold evar_is_fresh_in in Hx. simpl in Hx. clear -Hx.
          set_solver.
        }
        
        apply Framing_right; auto.
        { apply pile_basic_generic. }
        unfold evar_open.
        rewrite subst_ctx_bevar_subst.
        unfold exists_quantify. simpl.
        fold (evar_open 0 x (subst_ctx AC p)).
        erewrite evar_quantify_evar_open; auto.
        2: now do 2 apply andb_true_iff in Hwfex as [_ Hwfex].
        useBasicReasoning.
        apply Ex_quan; auto.
  Defined.
  
  Lemma and_of_negated_iff_not_impl Γ p1 p2:
    well_formed p1 ->
    well_formed p2 ->
    Γ ⊢ (! (! p1 ---> p2) <---> ! p1 and ! p2)
    using PropositionalReasoning.
  Proof.
    intros wfp1 wfp2.
    apply conj_intro_meta.
    { wf_auto2. }
    { wf_auto2. }
    - toMyGoal.
      { wf_auto2. }
      mgIntro. mgIntro.
      mgApply 0.
      mgIntro.
      unfold patt_or.
      mgAdd (@not_not_elim Σ Γ p2 ltac:(wf_auto2)).
      mgApply 0.
      mgApply 2.
      mgAdd (@not_not_intro Σ Γ (! p1) ltac:(wf_auto2)).
      mgApply 0.
      mgExactn 4.
    - toMyGoal.
      { wf_auto2. }
      mgIntro. mgIntro.
      unfold patt_and.
      mgApply 0.
      unfold patt_or.
      mgIntro.
      mgAdd (@not_not_intro Σ Γ p2 ltac:(wf_auto2)).
      mgApply 0.
      mgApply 2.
      mgAdd (@not_not_elim Σ Γ (! p1) ltac:(wf_auto2)).
      mgApply 0.
      mgExactn 4.
  Defined.

  Lemma and_impl_2 Γ p1 p2:
    well_formed p1 ->
    well_formed p2 ->
    Γ ⊢ (! (p1 ---> p2) <---> p1 and ! p2)
    using PropositionalReasoning.
  Proof.
    intros wfp1 wfp2.
    apply conj_intro_meta.
    { wf_auto2. }
    { wf_auto2. }
    - toMyGoal.
      { wf_auto2. }
      mgIntro. mgIntro.
      mgApply 0.
      mgIntro.
      unfold patt_or.
      mgAdd (@not_not_elim Σ Γ p2 ltac:(wf_auto2)).
      mgApply 0.
      mgApply 2.
      mgAdd (@not_not_intro Σ Γ p1 ltac:(wf_auto2)).
      mgApply 0.
      mgExactn 4.
    - toMyGoal.
      { wf_auto2. }
      mgIntro. mgIntro.
      mgApply 0.
      unfold patt_or.
      mgIntro.
      mgAdd (@not_not_intro Σ Γ p2 ltac:(wf_auto2)).
      mgApply 0.
      mgApply 2.
      mgAdd (@not_not_elim Σ Γ p1 ltac:(wf_auto2)).
      mgApply 0.
      mgExactn 4.
  Defined.

  Lemma conj_intro_meta_partial (Γ : Theory) (A B : Pattern) (i : ProofInfo) :
    well_formed A → well_formed B →
    Γ ⊢ A using i →
    Γ ⊢ B ---> (A and B) using i.
  Proof.
    intros WFA WFB H.
    eapply MP.
    - exact H.
    - usePropositionalReasoning. apply conj_intro.
      { wf_auto2. }
      { wf_auto2. }
  Defined.

  Lemma and_impl_patt (A B C : Pattern) Γ (i : ProofInfo):
    well_formed A → well_formed B → well_formed C →
    Γ ⊢ A using i ->
    Γ ⊢ ((A and B) ---> C) using i ->
    Γ ⊢ (B ---> C) using i.
  Proof.
    intros WFA WFB WFC H H0.
    eapply syllogism_meta with (B0 := patt_and A B).
    { wf_auto2. }
    { wf_auto2. }
    { wf_auto2. }
    2: { exact H0. }
    apply conj_intro_meta_partial.
    { wf_auto2. }
    { wf_auto2. }
    exact H.
  Defined.

  Lemma conj_intro2 (Γ : Theory) (A B : Pattern) :
    well_formed A -> well_formed B ->
    Γ ⊢ (A ---> (B ---> (B and A)))
    using PropositionalReasoning.
  Proof.
    intros WFA WFB. eapply reorder_meta.
    { wf_auto2. }
    { wf_auto2. }
    { wf_auto2. }
    apply conj_intro.
    { wf_auto2. }
    { wf_auto2. }
  Defined.

  Lemma conj_intro_meta_partial2 (Γ : Theory) (A B : Pattern) (i : ProofInfo):
    well_formed A → well_formed B →
    Γ ⊢ A using i →
    Γ ⊢ B ---> (B and A) using i.
  Proof.
    intros WFA WFB H.
    eapply MP.
    - exact H.
    - usePropositionalReasoning. apply conj_intro2.
      { wf_auto2. }
      { wf_auto2. }
  Defined.

  Lemma and_impl_patt2  (A B C : Pattern) Γ (i : ProofInfo):
    well_formed A → well_formed B → well_formed C →
    Γ ⊢ A using i ->
    Γ ⊢ ((B and A) ---> C) using i ->
    Γ ⊢ (B ---> C) using i.
  Proof.
    intros WFA WFB WFC H H0.
    eapply syllogism_meta with (B0 := patt_and B A).
    { wf_auto2. }
    { wf_auto2. }
    { wf_auto2. }
    2: exact H0.
    apply conj_intro_meta_partial2.
    { wf_auto2. }
    { wf_auto2. }
    exact H.
  Defined.


  Lemma patt_and_comm_meta (A B : Pattern) (Γ : Theory) (i : ProofInfo) :
    well_formed A → well_formed B
    ->
    Γ ⊢ A and B using i ->
    Γ ⊢ B and A using i.
  Proof.
    intros WFA WFB H.
    apply pf_conj_elim_r_meta in H as P1.
    apply pf_conj_elim_l_meta in H as P2. all: try_wfauto2.
    apply conj_intro_meta; assumption.
  Defined.

  Lemma MyGoal_applyMeta Γ r r' i:
    Γ ⊢ (r' ---> r) using i ->
    forall l,
    @mkMyGoal Σ Γ l r' i ->
    @mkMyGoal Σ Γ l r i.
  Proof.
    intros Himp l H.
    unfold of_MyGoal in *. simpl in *.
    intros wfr wfl.
    eapply prf_weaken_conclusion_iter_meta_meta.
    4: apply Himp.
    4: apply H.
    all: try assumption.
    1,2: pose proof (wfrr' := proved_impl_wf _ _ (proj1_sig Himp)); wf_auto2.
  Defined.

End FOL_helpers.


Tactic Notation "mgApplyMeta" uconstr(t) :=
  eapply (@MyGoal_applyMeta _ _ _ _ _ t).

Lemma MyGoal_left {Σ : Signature} Γ l x y i:
  @mkMyGoal Σ Γ l x i ->
  @mkMyGoal Σ Γ l (patt_or x y) i.
Proof.
  intros H.
  unfold of_MyGoal in *. simpl in *.
  intros wfxy wfl.
  eapply prf_weaken_conclusion_iter_meta_meta.
  4: { usePropositionalReasoning. apply disj_left_intro. wf_auto2. wf_auto2. }
  { wf_auto2. }
  { wf_auto2. }
  { wf_auto2. }
  apply H.
  { wf_auto2. }
  { assumption. }
Defined.

Lemma MyGoal_right {Σ : Signature} Γ l x y i:
  @mkMyGoal Σ Γ l y i ->
  @mkMyGoal Σ Γ l (patt_or x y) i.
Proof.
  intros H.
  unfold of_MyGoal in *. simpl in *.
  intros wfxy wfl.
  eapply prf_weaken_conclusion_iter_meta_meta.
  4: { usePropositionalReasoning. apply disj_right_intro. wf_auto2. wf_auto2. }
  { wf_auto2. }
  { wf_auto2. }
  { wf_auto2. }
  apply H.
  { wf_auto2. }
  { assumption. }
Defined.

Ltac mgLeft := apply MyGoal_left.
Ltac mgRight := apply MyGoal_right.

Example ex_mgLeft {Σ : Signature} Γ a:
  well_formed a ->
  Γ ⊢ a ---> (a or a)
  using PropositionalReasoning.
Proof.
  intros wfa.
  toMyGoal.
  { wf_auto2. }
  mgIntro.
  mgLeft.
Abort.

Lemma MyGoal_applyMetaIn {Σ : Signature} Γ r r' i:
  Γ ⊢ (r ---> r') using i ->
  forall l₁ l₂ g,
    @mkMyGoal Σ Γ (l₁ ++ r'::l₂) g i ->
    @mkMyGoal Σ Γ (l₁ ++ r::l₂ ) g i.
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
  { abstract (pose proof (Himp' := proj1_sig Himp); apply proved_impl_wf in Himp'; wf_auto2). }
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
      pose proof (Himp' := proj1_sig Himp);
      apply proved_impl_wf in Himp';
      apply well_formed_imp_proj2 in Himp';
      rewrite Himp';
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
  eapply (@MyGoal_applyMetaIn _ _ _ _ _ t);
  eapply cast_proof_mg_hyps;
  [(rewrite /app; reflexivity)|].

Local Example Private_ex_mgApplyMetaIn {Σ : Signature} Γ p q:
  well_formed p ->
  well_formed q ->
  Γ ⊢ p ---> (p or q)
  using PropositionalReasoning.
Proof.
  intros wfp wfq.
  toMyGoal.
  { wf_auto2. }
  mgIntro.
  mgApplyMeta (@disj_left_intro Σ Γ p q ltac:(wf_auto2) ltac:(wf_auto2)) in 0.
  mgExactn 0.
Defined.

Lemma MyGoal_destructAnd {Σ : Signature} Γ g l₁ l₂ x y i:
    @mkMyGoal Σ Γ (l₁ ++ x::y::l₂ ) g i ->
    @mkMyGoal Σ Γ (l₁ ++ (x and y)::l₂) g i .
Proof.
  intros H.
  unfold of_MyGoal. intros wfg Hwf. pose proof (wfg' := wfg). pose proof (Hwf' := Hwf).
  revert wfg' Hwf'.
  cut (of_MyGoal (@mkMyGoal Σ Γ (l₁ ++ (x and y)::l₂ ) g i)).
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
    eapply cast_proof_mg_hyps.
    { replace (l₁ ++ (x and y) :: l₂) with ((l₁++ [x and y]) ++ l₂).
      2: { rewrite -app_assoc. reflexivity. }
      rewrite take_app.
      reflexivity.
    }
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
    usePropositionalReasoning.
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
    eapply cast_proof_mg_hyps.
    {
      replace (l₁ ++ (x and y) :: l₂) with ((l₁++ [x and y]) ++ l₂).
      2: { rewrite -app_assoc. reflexivity. }
      rewrite take_app.
      reflexivity.
    }
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
    usePropositionalReasoning.
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
  Γ ⊢ p and q ---> a and b ---> q ---> a
  using PropositionalReasoning.
Proof.
  intros. toMyGoal.
  { wf_auto2. }
  do 3 mgIntro.
  mgDestructAnd 1.
  mgDestructAnd 0.
  mgExactn 2.
Defined.

Section FOL_helpers.
  
  Context {Σ : Signature}.
  
  Lemma and_of_equiv_is_equiv Γ p q p' q' i:
    well_formed p ->
    well_formed q ->
    well_formed p' ->
    well_formed q' ->
    Γ ⊢ (p <---> p') using i ->
    Γ ⊢ (q <---> q') using i ->
    Γ ⊢ ((p and q) <---> (p' and q')) using i.
  Proof.
    intros wfp wfq wfp' wfq' pep' qeq'.
    pose proof (pip' := pep'). apply pf_conj_elim_l_meta in pip'; auto.
    pose proof (p'ip := pep'). apply pf_conj_elim_r_meta in p'ip; auto.
    pose proof (qiq' := qeq'). apply pf_conj_elim_l_meta in qiq'; auto.
    pose proof (q'iq := qeq'). apply pf_conj_elim_r_meta in q'iq; auto.
    
    apply conj_intro_meta; auto.
    - toMyGoal.
      { wf_auto2. }
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
      { wf_auto2. }
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

  Lemma or_of_equiv_is_equiv Γ p q p' q' i:
    well_formed p ->
    well_formed q ->
    well_formed p' ->
    well_formed q' ->
    Γ ⊢ (p <---> p') using i ->
    Γ ⊢ (q <---> q') using i ->
    Γ ⊢ ((p or q) <---> (p' or q')) using i.
  Proof with try_wfauto2.
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
      + mgLeft. fromMyGoal. assumption.
      + mgRight. fromMyGoal. assumption.
    - toMyGoal.
      { auto. }
      mgIntro.
      mgDestructOr 0.
      + mgLeft. fromMyGoal. assumption.
      + mgRight. fromMyGoal. assumption.
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
    Γ ⊢ ((p ---> q) <---> (! p or q))
    using PropositionalReasoning.
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
    Γ ⊢ (⊥ <---> p and ! p)
    using PropositionalReasoning.
  Proof.
    intros wfp.
    apply conj_intro_meta; auto.
    - apply bot_elim; auto.
    - unfold patt_and.
      toMyGoal.
      { wf_auto2. }
      mgIntro.
      mgApply 0.
      mgAdd (@A_or_notA Σ Γ (! p) ltac:(wf_auto2)).
      mgExactn 0.
  Defined.

  Lemma weird_lemma Γ A B L R:
    well_formed A ->
    well_formed B ->
    well_formed L ->
    well_formed R ->
    Γ ⊢ (((L and A) ---> (B or R)) ---> (L ---> ((A ---> B) or R)))
    using PropositionalReasoning.
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

  Lemma weird_lemma_meta Γ A B L R i:
    well_formed A ->
    well_formed B ->
    well_formed L ->
    well_formed R ->
    Γ ⊢ ((L and A) ---> (B or R)) using i ->
    Γ ⊢ (L ---> ((A ---> B) or R)) using i.
  Proof.
    intros WFA WFB WFL WFR H.
    eapply MP.
    2: { usePropositionalReasoning. apply weird_lemma; assumption. }
    exact H.
  Defined.

  Lemma imp_trans_mixed_meta Γ A B C D i :
    well_formed A -> well_formed B -> well_formed C -> well_formed D ->
    Γ ⊢ (C ---> A) using i ->
    Γ ⊢ (B ---> D) using i ->
    Γ ⊢ ((A ---> B) ---> C ---> D) using i.
  Proof.
    intros WFA WFB WFC WFD H H0.
    epose proof (H1 := @prf_weaken_conclusion Σ Γ A B D WFA WFB WFD).
    eapply usePropositionalReasoning in H1.
    eapply MP in H1.
    2: { exact H0. }
    epose proof (H2 := @prf_strenghten_premise Σ Γ A C D WFA WFC WFD).
    eapply usePropositionalReasoning in H2.
    eapply MP in H2.
    2: { exact H. }
    epose proof (H3 := @syllogism_meta Σ Γ _ _ _ i _ _ _ H1 H2).
    exact H3.
    Unshelve. all: wf_auto2.
  Defined.

  Lemma and_weaken A B C Γ i:
    well_formed A -> well_formed B -> well_formed C ->
    Γ ⊢ (B ---> C) using i ->
    Γ ⊢ ((A and B) ---> (A and C)) using i.
  Proof.
    intros WFA WFB WFC H.
    epose proof (H0 := @and_impl' Σ Γ A B (A and C) _ _ _).
    eapply MP. 2: { usePropositionalReasoning. exact H0. }
    apply reorder_meta.
    1-3: wf_auto2.
    epose proof (H1 := @prf_strenghten_premise Σ Γ C B (A ---> A and C) _ _ _).
    eapply MP.
    2: eapply MP.
    3: { usePropositionalReasoning. exact H1. }
    2: { exact H. }
    usePropositionalReasoning.
    apply conj_intro2; assumption.
    Unshelve.
    all: wf_auto2.
  Defined.

  Lemma impl_and Γ A B C D i: 
    well_formed A -> well_formed B -> well_formed C -> well_formed D ->
    Γ ⊢ (A ---> B) using i ->
    Γ ⊢ (C ---> D) using i ->
    Γ ⊢ (A and C) ---> (B and D) using i.
  Proof.
    intros WFA WFB WFC WFD H H0.
    toMyGoal.
    { wf_auto2. }
    {
      mgAdd H.
      mgAdd H0.
      mgIntro.
      mgDestructAnd 2.
      mgIntro.
      mgDestructOr 4.
      {
        mgApply 4.
        mgApply 1.
        mgExactn 2.
      }
      {
        mgApply 4.
        mgApply 0.
        mgExactn 3.
      }
    }
  Defined.

  Lemma and_drop A B C Γ i:
    well_formed A -> well_formed B -> well_formed C ->
    Γ ⊢ ((A and B) ---> C) using i ->
    Γ ⊢ ((A and B) ---> (A and C)) using i.
  Proof.
    intros WFA WFB WFC H.
    toMyGoal.
    { wf_auto2. }
    mgAdd H.
    mgIntro.
    mgIntro.
    mgDestructOr 2.
    {
      mgDestructAnd 1.
      mgApply 3.
      mgExactn 1.
    }
    {
      mgApply 2.
      mgApply 0.
      mgExactn 1.
    }
  Defined.

  Lemma universal_generalization Γ ϕ x (i : ProofInfo) :
    ProofInfoLe (pi_Generic (ExGen := {[x]}, SVSubst := ∅, KT := false)) i ->
    well_formed ϕ ->
    Γ ⊢ ϕ using i ->
    Γ ⊢ patt_forall (evar_quantify x 0 ϕ) using i.
  Proof.
    intros pile wfϕ Hϕ.
    unfold patt_forall.
    unfold patt_not at 1.
    replace (! evar_quantify x 0 ϕ)
      with (evar_quantify x 0 (! ϕ))
      by reflexivity.
    apply Ex_gen.
    { exact pile. }
    { simpl. set_solver. }
    toMyGoal.
    { wf_auto2. }
    mgIntro. mgAdd Hϕ.
    mgApply 1. mgExactn 0.
  Defined.

  (*Hint Resolve evar_quantify_well_formed.*)

  Lemma forall_variable_substitution Γ ϕ x:
    well_formed ϕ ->
    Γ ⊢ (all, evar_quantify x 0 ϕ) ---> ϕ
    using (pi_Generic (ExGen := {[x]}, SVSubst := ∅, KT := false)).
  Proof.
    intros wfϕ.
   
    unfold patt_forall.
    replace (! evar_quantify x 0 ϕ)
      with (evar_quantify x 0 (! ϕ))
      by reflexivity.
    apply double_neg_elim_meta.
    { wf_auto2. }
    { wf_auto2. }
    toMyGoal.
    { wf_auto2. }
    mgIntro.
    mgIntro.
    mgApply 0.
    mgIntro.
    mgApply 2.
    pose proof (Htmp := @Ex_quan Σ Γ (evar_quantify x 0 (!ϕ)) x).
    rewrite /instantiate in Htmp.
    rewrite bevar_subst_evar_quantify_free_evar in Htmp.
    {
      simpl. split_and!. now do 2 apply andb_true_iff in wfϕ as [_ wfϕ]. reflexivity.
    }
    specialize (Htmp ltac:(wf_auto2)).
    useBasicReasoning.
    mgAdd Htmp.
    mgApply 0.
    mgIntro.
    mgApply 2.
    mgExactn 4.
  Defined.

End FOL_helpers.

Lemma not_kt_in_prop {Σ : Signature} :
  ~ ProofInfoLe (pi_Generic (ExGen := ∅, SVSubst := ∅, KT := true)) pi_Propositional.
Proof.
  intros [HContra].
  specialize (HContra ∅).
  pose (pf1 := @A_impl_A Σ ∅ patt_bott ltac:(wf_auto2)).
  pose (pf2 := @ProofSystem.Knaster_tarski Σ ∅ (patt_bound_svar 0) patt_bott ltac:(wf_auto2) (proj1_sig pf1)).
  specialize (HContra _ pf2).
  feed specialize HContra.
  {
    unfold pf2. simpl. constructor; simpl.
    { exact I. }
    { set_solver. }
    { set_solver. }
    { reflexivity. }
  }
  destruct HContra as [HC1 HC2 HC3 HC4].
  unfold pf2 in HC4.
  simpl in HC4.
  congruence.
Qed.

Lemma pile_impl_uses_kt {Σ : Signature} gpi evs svs:
  ProofInfoLe (pi_Generic (ExGen := evs, SVSubst := svs, KT := true)) (pi_Generic gpi) ->
  pi_uses_kt gpi.
Proof.
  intros [H].
  specialize (H ∅).
  pose (pf1 := @A_impl_A Σ ∅ patt_bott ltac:(wf_auto2)).
  pose (pf2 := @ProofSystem.Knaster_tarski Σ ∅ (patt_bound_svar 0) patt_bott ltac:(wf_auto2) (proj1_sig pf1)).
  specialize (H _ pf2).
  feed specialize H.
  {
    constructor; simpl.
    { exact I. }
    { set_solver. }
    { set_solver. }
    reflexivity.
  }
  destruct H as [H1 H2 H3 H4].
  unfold pf2 in H4. simpl in H4. exact H4.
Qed.


Lemma Knaster_tarski {Σ : Signature}
  (Γ : Theory) (ϕ ψ : Pattern)  (i : ProofInfo)
  {pile : ProofInfoLe (pi_Generic
        {| pi_generalized_evars := ∅;
           pi_substituted_svars := ∅;
           pi_uses_kt := true ;
        |}) i} :
well_formed (mu, ϕ) ->
Γ ⊢ (instantiate (mu, ϕ) ψ) ---> ψ using i ->
Γ ⊢ mu, ϕ ---> ψ using i.
Proof.
intros Hfev [pf Hpf].
unshelve (eexists).
{
  apply ProofSystem.Knaster_tarski.
  { exact Hfev. }
  { exact pf. }
}
{
  simpl.
  pose proof (Hnot := not_kt_in_prop).
  constructor; simpl.
  {
    destruct i;[|exact I].
    contradiction.
  }
  {
    destruct i;[contradiction|].
    destruct Hpf as [Hpf1 Hpf2 Hpf3 Hpf4].
    apply Hpf2.
  }
  {
    destruct i;[contradiction|].
    destruct Hpf as [Hpf1 Hpf2 Hpf3 Hpf4].
    apply Hpf3.
  }
  {
    destruct i;[contradiction|].
    destruct Hpf as [Hpf1 Hpf2 Hpf3 Hpf4].
    pose proof (Hpile := @pile_impl_uses_kt _ _ _ _ pile).
    exact Hpile.
  }
}
Defined.

Lemma pile_evs_subseteq {Σ : Signature} evs1 evs2 svs kt:
  evs1 ⊆ evs2 ->
  ProofInfoLe
    (pi_Generic (ExGen := evs1, SVSubst := svs, KT := kt))
    (pi_Generic (ExGen := evs2, SVSubst := svs, KT := kt)).
Proof.
  intros Hsub.
  constructor.
  intros Γ ϕ pf Hpf.
  destruct Hpf as [Hpf1 Hpf2 Hpf3 Hpf4].
  constructor; simpl in *.
  { exact Hpf1. }
  { clear -Hsub Hpf2. set_solver. }
  { exact Hpf3. }
  { exact Hpf4. }
Qed.

Lemma pile_svs_subseteq {Σ : Signature} evs svs1 svs2 kt:
  svs1 ⊆ svs2 ->
  ProofInfoLe
    (pi_Generic (ExGen := evs, SVSubst := svs1, KT := kt))
    (pi_Generic (ExGen := evs, SVSubst := svs2, KT := kt)).
Proof.
  intros Hsub.
  constructor.
  intros Γ ϕ pf Hpf.
  destruct Hpf as [Hpf1 Hpf2 Hpf3 Hpf4].
  constructor; simpl in *.
  { exact Hpf1. }
  { exact Hpf2. }
  { clear -Hsub Hpf3. set_solver. }
  { exact Hpf4. }
Qed.


Lemma pile_kt_impl {Σ : Signature} evs svs kt1 kt2:
  kt1 ==> kt2 ->
  ProofInfoLe
    (pi_Generic (ExGen := evs, SVSubst := svs, KT := kt1))
    (pi_Generic (ExGen := evs, SVSubst := svs, KT := kt2)).
Proof.
  intros Hsub.
  constructor.
  intros Γ ϕ pf Hpf.
  destruct Hpf as [Hpf1 Hpf2 Hpf3 Hpf4].
  constructor; simpl in *.
  { exact Hpf1. }
  { exact Hpf2. }
  { exact Hpf3. }
  { unfold implb in *.  destruct (uses_kt pf),kt1; simpl in *; try reflexivity.
    { exact Hsub. }
    { inversion Hpf4. }
  }
Qed.

Lemma not_svs_in_prop {Σ : Signature} (X : svar) :
  ~ ProofInfoLe (pi_Generic (ExGen := ∅, SVSubst := {[X]}, KT := false)) pi_Propositional.
Proof.
  intros [HContra].
  specialize (HContra ∅).
  pose (pf1 := @A_impl_A Σ ∅ (patt_free_svar X) ltac:(wf_auto2)).
  pose (pf2 := @ProofSystem.Svar_subst Σ ∅ (patt_free_svar X ---> patt_free_svar X) patt_bott X ltac:(wf_auto2) ltac:(wf_auto2) (proj1_sig pf1)).
  specialize (HContra _ pf2).
  feed specialize HContra.
  {
    unfold pf2. simpl. constructor; simpl.
    { exact I. }
    { set_solver. }
    { set_solver. }
    { reflexivity. }
  }
  destruct HContra as [HC1 HC2 HC3 HC4].
  simpl in *.
  clear -HC1.
  congruence.
Qed.


Lemma not_generic_in_prop {Σ : Signature} evs svs kt :
  ~ ProofInfoLe (pi_Generic (ExGen := evs, SVSubst := svs, KT := kt)) pi_Propositional.
Proof.
  intros [HContra].
  specialize (HContra ∅).
  pose (pf := @ProofSystem.Pre_fixp Σ ∅ (patt_bound_svar 0) ltac:(wf_auto2)).
  specialize (HContra _ pf).
  feed specialize HContra.
  {
    unfold pf. simpl. constructor; simpl.
    { exact I. }
    { set_solver. }
    { set_solver. }
    { reflexivity. }
  }
  destruct HContra as [HC1 HC2 HC3 HC4].
  simpl in *.
  clear -HC1.
  congruence.
Qed.

Lemma pile_impl_allows_svsubst_X {Σ : Signature} gpi evs X kt:
  ProofInfoLe (pi_Generic (ExGen := evs, SVSubst := {[X]}, KT := kt)) (pi_Generic gpi) ->
  X ∈ pi_substituted_svars gpi.
Proof.
  intros [H].
  specialize (H ∅).
  pose (pf1 := @A_impl_A Σ ∅ (patt_free_svar X) ltac:(wf_auto2)).
  pose (pf2 := @ProofSystem.Svar_subst Σ ∅ (patt_free_svar X ---> patt_free_svar X) patt_bott X ltac:(wf_auto2) ltac:(wf_auto2) (proj1_sig pf1)).
  specialize (H _ pf2).
  feed specialize H.
  {
    constructor; simpl.
    { exact I. }
    { set_solver. }
    { set_solver. }
    reflexivity.
  }
  destruct H as [H1 H2 H3 H4].
  simpl in *.
  clear -H3. set_solver.
Qed.

Lemma Svar_subst {Σ : Signature}
  (Γ : Theory) (ϕ ψ : Pattern) (X : svar)  (i : ProofInfo)
  {pile : ProofInfoLe (pi_Generic
        {| pi_generalized_evars := ∅;
           pi_substituted_svars := {[X]};
           pi_uses_kt := false ;
        |}) i} :
  well_formed ψ ->
  Γ ⊢ ϕ using i ->
  Γ ⊢ (free_svar_subst ϕ ψ X) using i.
Proof.
  intros wfψ [pf Hpf].
  unshelve (eexists).
  {
   apply ProofSystem.Svar_subst.
   { pose proof (Hwf := @proved_impl_wf _ _ _ pf). exact Hwf. }
   { exact wfψ. }
   { exact pf. }
  }
{
  simpl.
  pose proof (Hnot := @not_svs_in_prop Σ X).
  constructor; simpl.
  {
    destruct i;[|exact I].
    contradiction.
  }
  {
    destruct i;[contradiction|].
    destruct Hpf as [Hpf1 Hpf2 Hpf3 Hpf4].
    apply Hpf2.
  }
  {
    destruct i;[contradiction|].
    destruct Hpf as [Hpf1 Hpf2 Hpf3 Hpf4].
    pose proof (Hpile := @pile_impl_allows_svsubst_X _ _ _ _ _ pile).
    clear -Hpile Hpf3.
    set_solver.
  }
  {
    destruct i;[contradiction|].
    destruct Hpf as [Hpf1 Hpf2 Hpf3 Hpf4].
    exact Hpf4.
  }
}
Defined.

Lemma Pre_fixp {Σ : Signature}
  (Γ : Theory) (ϕ : Pattern) :
  well_formed (patt_mu ϕ) ->
  Γ ⊢ (instantiate (patt_mu ϕ) (patt_mu ϕ) ---> (patt_mu ϕ))
  using BasicReasoning.
Proof.
  intros wfϕ.
  unshelve (eexists).
  {
    apply ProofSystem.Pre_fixp.
    { exact wfϕ. }
  }
  {
    simpl.
    constructor; simpl.
    { exact I. }
    { set_solver. }
    { set_solver. }
    { reflexivity. }
  }
Defined.

Section FOL_helpers.

  Context {Σ : Signature}.

  Lemma mu_monotone Γ ϕ₁ ϕ₂ X (i : ProofInfo):
    ProofInfoLe (pi_Generic (ExGen := ∅, SVSubst := {[X]}, KT := true)) i ->
    svar_has_negative_occurrence X ϕ₁ = false ->
    svar_has_negative_occurrence X ϕ₂ = false ->
    Γ ⊢ ϕ₁ ---> ϕ₂ using i->
    Γ ⊢ (patt_mu (svar_quantify X 0 ϕ₁)) ---> (patt_mu (svar_quantify X 0 ϕ₂))
    using i.
  Proof.
    intros pile nonegϕ₁ nonegϕ₂ Himp.
    pose proof (wfϕ12 := @proved_impl_wf _ _ _ (proj1_sig Himp)).
    assert(wfϕ₁ : well_formed ϕ₁) by wf_auto2.
    assert(wfϕ₂ : well_formed ϕ₂) by wf_auto2.

    apply Knaster_tarski.
    { eapply pile_trans. 2: apply pile. apply pile_svs_subseteq. set_solver. }
    { wf_auto2. }

    pose proof (Htmp := @Svar_subst Σ Γ (ϕ₁ ---> ϕ₂) (mu, svar_quantify X 0 ϕ₂) X i).
    feed specialize Htmp.
    { eapply pile_trans. 2: apply pile. apply pile_kt_impl. simpl. reflexivity. }
    { wf_auto2. }
    { exact Himp. }
    unfold free_svar_subst in Htmp.
    simpl in Htmp.
    fold free_svar_subst in Htmp.

    pose proof (Hpf := @Pre_fixp Σ Γ (svar_quantify X 0 ϕ₂)).
    simpl in Hpf.

    unshelve (eapply (@cast_proof' Σ Γ _ _) in Hpf).
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

    eapply (@cast_proof' Σ Γ) in Hpf.
    2: {
      rewrite svar_open_svar_quantify.
      { unfold well_formed, well_formed_closed in *. destruct_and!. auto. }
      reflexivity.
    }


    assert(well_formed_positive (free_svar_subst ϕ₂ (mu , svar_quantify X 0 ϕ₂) X) = true).
    {
      unfold well_formed, well_formed_closed in *. destruct_and!. simpl; split_and?.
      apply wfp_free_svar_subst; auto.
      { apply svar_quantify_closed_mu. auto. }
      { simpl. split_and!.
        2: apply well_formed_positive_svar_quantify; assumption.
        apply no_negative_occurrence_svar_quantify; auto.
      }
    }

    assert(well_formed_closed_mu_aux (free_svar_subst ϕ₂ (mu , svar_quantify X 0 ϕ₂) X) 0 = true).
    {
      unfold well_formed, well_formed_closed in *. destruct_and!. simpl; split_and?; auto.
      replace 0 with (0 + 0) at 3 by lia.
      apply wfc_mu_free_svar_subst; auto.
      simpl.
      apply svar_quantify_closed_mu. assumption.
    }
    
    assert(well_formed_closed_ex_aux (free_svar_subst ϕ₂ (mu , svar_quantify X 0 ϕ₂) X) 0 = true).
    {
      unfold well_formed, well_formed_closed in *. destruct_and!. simpl; split_and?; auto.
      replace 0 with (0 + 0) at 3 by lia.
      apply wfc_ex_free_svar_subst; auto.
      simpl.
      apply svar_quantify_closed_ex. assumption.
    }

    assert(well_formed_positive (free_svar_subst ϕ₁ (mu , svar_quantify X 0 ϕ₂) X) = true).
    {
      unfold well_formed, well_formed_closed in *. destruct_and!. simpl; split_and?.
      apply wfp_free_svar_subst; auto.
      { apply svar_quantify_closed_mu. auto. }
      { simpl. split_and!.
        2: apply well_formed_positive_svar_quantify; assumption.
        apply no_negative_occurrence_svar_quantify; auto.
      }
    }

    assert(well_formed_closed_mu_aux (free_svar_subst ϕ₁ (mu , svar_quantify X 0 ϕ₂) X) 0 = true).
    {
      unfold well_formed, well_formed_closed in *. destruct_and!. simpl; split_and?; auto.
      replace 0 with (0 + 0) at 3 by lia.
      apply wfc_mu_free_svar_subst; auto.
      simpl.
      apply svar_quantify_closed_mu. assumption.
    }
    
    assert(well_formed_closed_ex_aux (free_svar_subst ϕ₁ (mu , svar_quantify X 0 ϕ₂) X) 0 = true).
    {
      unfold well_formed, well_formed_closed in *. destruct_and!. simpl; split_and?; auto.
      replace 0 with (0 + 0) at 3 by lia.
      apply wfc_ex_free_svar_subst; auto.
      simpl.
      apply svar_quantify_closed_ex. assumption.
    }
    
    (* i = pi_Generic gpi *)
    destruct i.
    {
      exfalso.
      apply not_kt_in_prop.
      eapply pile_trans.
      2: { apply pile. }
      apply pile_svs_subseteq.
      set_solver.
    }
    apply useBasicReasoning with (gpi0 := gpi) in Hpf.
    epose proof (Hsi := @syllogism_meta Σ _ _ _ _ _ _ _ _ Htmp Hpf).
    simpl.

    eapply (@cast_proof' Σ Γ).
    1: {
      erewrite bound_to_free_set_variable_subst with (X0 := X).
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

    eapply (@cast_proof' Σ Γ).
    1: {
      rewrite svar_open_svar_quantify.
      { unfold well_formed, well_formed_closed in *. destruct_and!. auto. }
      reflexivity.
    }
    apply Hsi.
    Unshelve.
    all: abstract(wf_auto2).
  Defined.


  (* These [Local Private_*] lemmas are not generally useful, but we use them to keep the body
     of [Private_prf_equiv_congruence] reasonably small. Because we want to reason about the body, too.
     The lemmas are mostly placeholders for `wf_auto`.
   *)


  Lemma prf_equiv_of_impl_of_equiv Γ a b a' b' i:
    well_formed a = true ->
    well_formed b = true ->
    well_formed a' = true ->
    well_formed b' = true ->
    Γ ⊢ (a <---> a') using i ->
    Γ ⊢ (b <---> b') using i ->
    Γ ⊢ (a ---> b) <---> (a' ---> b') using i
  .
  Proof.
    intros wfa wfb wfa' wfb' Haa' Hbb'.
    unshelve(epose proof (Haa'1 := @pf_conj_elim_l_meta _ _ _ _ _ _ _ Haa')).
    { wf_auto2. }
    { wf_auto2. }
    unshelve(epose proof (Haa'2 := @pf_conj_elim_r_meta _ _ _ _ _ _ _ Haa')).
    { wf_auto2. }
    { wf_auto2. }
    unshelve(epose proof (Hbb'1 := @pf_conj_elim_l_meta _ _ _ _ _ _ _ Hbb')).
    { wf_auto2. }
    { wf_auto2. }
    unshelve(epose proof (Hbb'2 := @pf_conj_elim_r_meta _ _ _ _ _ _ _ Hbb')).
    { wf_auto2. }
    { wf_auto2. }

    apply pf_iff_equiv_trans with (B := (a ---> b')).
    1-3: wf_auto2.
      + apply conj_intro_meta.
        1-2: wf_auto2.
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
      + apply conj_intro_meta.
        1-2: wf_auto2.
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

  Lemma pf_evar_open_free_evar_subst_equiv_sides Γ x n ϕ p q E i:
    x <> E ->
    well_formed p = true ->
    well_formed q = true ->
    Γ ⊢ free_evar_subst (evar_open n x ϕ) p E <---> free_evar_subst (evar_open n x ϕ) q E using i ->
    Γ ⊢ evar_open n x (free_evar_subst ϕ p E) <---> evar_open n x (free_evar_subst ϕ q E) using i.
  Proof.
    intros Hx wfp wfq H.
    unshelve (eapply (@cast_proof' Σ Γ _ _ _ _ H)).
    rewrite -> evar_open_free_evar_subst_swap by assumption.
    rewrite -> evar_open_free_evar_subst_swap by assumption.
    reflexivity.
  Defined.

  Lemma strip_exists_quantify_l Γ x P Q i :
    x ∉ free_evars P ->
    well_formed_closed_ex_aux P 1 ->
    Γ ⊢ (exists_quantify x (evar_open 0 x P) ---> Q) using i ->
    Γ ⊢ ex , P ---> Q using i.
  Proof.
    intros Hx HwfcP H.
    unshelve (eapply (@cast_proof' Σ Γ _ _ _ _ H)).
    abstract (
      unfold exists_quantify;
      rewrite -> evar_quantify_evar_open by assumption;
      reflexivity
    ).
  Defined.

  Lemma strip_exists_quantify_r Γ x P Q i :
    x ∉ free_evars Q ->
    well_formed_closed_ex_aux Q 1 ->
    Γ ⊢ P ---> (exists_quantify x (evar_open 0 x Q)) using i ->
    Γ ⊢ P ---> ex, Q using i.
  Proof.
    intros Hx HwfcP H.
    unshelve (eapply (@cast_proof' Σ Γ _ _ _ _ H)).
    abstract (
      unfold exists_quantify;
      rewrite -> evar_quantify_evar_open by assumption;
      reflexivity
    ).
  Defined.

  Lemma pf_iff_free_evar_subst_svar_open_to_bsvar_subst_free_evar_subst Γ ϕ p q E X i:
    well_formed_closed_mu_aux p 0 = true ->
    well_formed_closed_mu_aux q 0 = true ->
    Γ ⊢ free_evar_subst (svar_open 0 X ϕ) p E <---> free_evar_subst (svar_open 0 X ϕ) q E using i ->
    Γ ⊢ bsvar_subst (free_evar_subst ϕ p E) (patt_free_svar X) 0 <--->
        bsvar_subst (free_evar_subst ϕ q E) (patt_free_svar X) 0 using i.
  Proof.
    intros wfp wfq H.
    unshelve (eapply (@cast_proof' _ _ _ _ _ _ H)).

    abstract (
      unfold svar_open in H;
      rewrite <- free_evar_subst_bsvar_subst;
      [idtac|wf_auto| unfold evar_is_fresh_in; simpl; clear; set_solver];
      rewrite <- free_evar_subst_bsvar_subst;
      [idtac|wf_auto|unfold evar_is_fresh_in; simpl; clear; set_solver];
      reflexivity
   ).
  Defined.

  Lemma pf_iff_mu_remove_svar_quantify_svar_open Γ ϕ p q E X i :
    well_formed_closed_mu_aux (free_evar_subst ϕ p E) 1 ->
    well_formed_closed_mu_aux (free_evar_subst ϕ q E) 1 ->
    X ∉ free_svars (free_evar_subst ϕ p E) ->
    X ∉ free_svars (free_evar_subst ϕ q E) ->
    Γ ⊢ mu , svar_quantify X 0 (svar_open 0 X (free_evar_subst ϕ p E)) <--->
        mu , svar_quantify X 0 (svar_open 0 X (free_evar_subst ϕ q E)) using i ->
    Γ ⊢ mu , free_evar_subst ϕ p E <---> mu , free_evar_subst ϕ q E using i.
  Proof.
    intros wfp' wfq' Xfrp Xfrq H.
    unshelve (eapply (@cast_proof' _ _ _ _ _ _ H)).
    abstract (
      rewrite -{1}[free_evar_subst ϕ p E](@svar_quantify_svar_open _ X 0); [assumption| auto | auto];
      rewrite -{1}[free_evar_subst ϕ q E](@svar_quantify_svar_open _ X 0); [assumption| auto | auto];
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

  Fixpoint maximal_exists_depth_of_evar_in_pattern' (depth : nat) (E : evar) (ψ : Pattern) : nat :=
    match ψ with
    | patt_bott => 0
    | patt_sym _ => 0
    | patt_bound_evar _ => 0
    | patt_bound_svar _ => 0
    | patt_free_svar _ => 0
    | patt_free_evar E' =>
      match (decide (E' = E)) with
      | left _ => depth
      | right _ => 0
      end
    | patt_imp ψ₁ ψ₂
      => Nat.max
        (maximal_exists_depth_of_evar_in_pattern' depth E ψ₁)
        (maximal_exists_depth_of_evar_in_pattern' depth E ψ₂)
    | patt_app ψ₁ ψ₂
      => Nat.max
        (maximal_exists_depth_of_evar_in_pattern' depth E ψ₁)
        (maximal_exists_depth_of_evar_in_pattern' depth E ψ₂)
    | patt_exists ψ' =>
      maximal_exists_depth_of_evar_in_pattern' (S depth) E ψ'
    | patt_mu ψ' =>
      maximal_exists_depth_of_evar_in_pattern' depth E ψ'
    end.

  Definition maximal_exists_depth_of_evar_in_pattern (E : evar) (ψ : Pattern) : nat :=
    maximal_exists_depth_of_evar_in_pattern' 0 E ψ.

  Definition pf_ite {P : Prop} (i : ProofInfo) (dec: {P} + {~P}) (Γ : Theory) (ϕ : Pattern)
    (pf1: P -> Γ ⊢ ϕ using i)
    (pf2: (~P) -> Γ ⊢ ϕ using i) :
    Γ ⊢ ϕ using i :=
    match dec with
    | left pf => pf1 pf
    | right pf => pf2 pf
    end.

  Lemma evar_fresh_seq_max (EvS : EVarSet) (n1 n2 : nat) :
    (@list_to_set evar EVarSet _ _ _ (evar_fresh_seq EvS n1)) ⊆ (list_to_set (evar_fresh_seq EvS (n1 `max` n2))).
  Proof.
    move: EvS n2.
    induction n1; intros EvS n2.
    {
      simpl. set_solver.
    }
    {
      simpl.
      destruct n2.
      {
        simpl. set_solver.
      }
      {
        simpl.
        cut (@list_to_set evar EVarSet _ _ _ (evar_fresh_seq ({[evar_fresh_s EvS]} ∪ EvS) n1)
        ⊆ list_to_set (evar_fresh_seq ({[evar_fresh_s EvS]} ∪ EvS) (n1 `max` n2))).
        {
          set_solver.
        }
        specialize (IHn1 ({[evar_fresh_s EvS]} ∪ EvS) n2).
        apply IHn1.
      }
    }
  Qed.

  Lemma medoeip_evar_open depth E n x ψ:
    E <> x ->
    maximal_exists_depth_of_evar_in_pattern' depth E (evar_open n x ψ)
    = maximal_exists_depth_of_evar_in_pattern' depth E ψ.
  Proof.
    intros HEnex.
    unfold evar_open.
    move: depth n.
    induction ψ; intros depth n'; simpl; try reflexivity.
    {
      case_match; simpl; try reflexivity.
      case_match; try reflexivity. subst. contradiction.
    }
    {
      rewrite IHψ1. rewrite IHψ2. reflexivity.
    }
    {
      rewrite IHψ1. rewrite IHψ2. reflexivity.
    }
    {
      rewrite IHψ. reflexivity.
    }
    {
      rewrite IHψ. reflexivity.
    }
  Qed.

  Lemma medoeip_svar_open depth E n X ψ:
    maximal_exists_depth_of_evar_in_pattern' depth E (svar_open n X ψ)
    = maximal_exists_depth_of_evar_in_pattern' depth E ψ.
  Proof.
    unfold svar_open.
    move: depth n.
    induction ψ; intros depth n'; simpl; try reflexivity.
    {
      case_match; simpl; try reflexivity.
    }
    {
      rewrite IHψ1. rewrite IHψ2. reflexivity.
    }
    {
      rewrite IHψ1. rewrite IHψ2. reflexivity.
    }
    {
      rewrite IHψ. reflexivity.
    }
    {
      rewrite IHψ. reflexivity.
    }
  Qed.

  Lemma medoeip_notin E ψ depth:
    E ∉ free_evars ψ ->
    maximal_exists_depth_of_evar_in_pattern' depth E ψ = 0.
  Proof.
    intros Hnotin.
    move: E depth Hnotin.
    induction ψ; intros E depth Hnotin; simpl in *; try reflexivity.
    { case_match. set_solver. reflexivity. }
    { rewrite IHψ1. set_solver. rewrite IHψ2. set_solver. reflexivity. }
    { rewrite IHψ1. set_solver. rewrite IHψ2. set_solver. reflexivity. }
    { rewrite IHψ. exact Hnotin. reflexivity. }
    { rewrite IHψ. exact Hnotin. reflexivity. }
  Qed.

  Lemma medoeip_S_in E ψ depth:
    E ∈ free_evars ψ ->
    maximal_exists_depth_of_evar_in_pattern' (S depth) E ψ
    = S (maximal_exists_depth_of_evar_in_pattern' depth E ψ).
  Proof.
    intros Hin.
    move: E depth Hin.
    induction ψ; intros E depth Hin; simpl in *.
    { case_match. reflexivity. set_solver. }
    { set_solver. }
    { set_solver. }
    { set_solver. }
    { set_solver. }
    {
      destruct (decide (E ∈ free_evars ψ1)),(decide (E ∈ free_evars ψ2)).
      {
        rewrite IHψ1. assumption. rewrite IHψ2. assumption. simpl. reflexivity.
      }
      {
        rewrite IHψ1. assumption.
        rewrite [maximal_exists_depth_of_evar_in_pattern' _ _ ψ2]medoeip_notin.
        { assumption. }
        rewrite [maximal_exists_depth_of_evar_in_pattern' _ _ ψ2]medoeip_notin.
        { assumption. }
        simpl.
        rewrite Nat.max_comm.
        simpl.
        reflexivity.
      }
      {
        rewrite IHψ2. assumption.
        rewrite [maximal_exists_depth_of_evar_in_pattern' _ _ ψ1]medoeip_notin.
        { assumption. }
        rewrite [maximal_exists_depth_of_evar_in_pattern' _ _ ψ1]medoeip_notin.
        { assumption. }
        simpl.
        reflexivity.
      }
      {
        exfalso. set_solver.
      }
    }
    { set_solver. }
    {
      destruct (decide (E ∈ free_evars ψ1)),(decide (E ∈ free_evars ψ2)).
      {
        rewrite IHψ1. assumption. rewrite IHψ2. assumption. simpl. reflexivity.
      }
      {
        rewrite IHψ1. assumption.
        rewrite [maximal_exists_depth_of_evar_in_pattern' _ _ ψ2]medoeip_notin.
        { assumption. }
        rewrite [maximal_exists_depth_of_evar_in_pattern' _ _ ψ2]medoeip_notin.
        { assumption. }
        simpl.
        rewrite Nat.max_comm.
        simpl.
        reflexivity.
      }
      {
        rewrite IHψ2. assumption.
        rewrite [maximal_exists_depth_of_evar_in_pattern' _ _ ψ1]medoeip_notin.
        { assumption. }
        rewrite [maximal_exists_depth_of_evar_in_pattern' _ _ ψ1]medoeip_notin.
        { assumption. }
        simpl.
        reflexivity.
      }
      {
        exfalso. set_solver.
      }     
    }
    {
      rewrite IHψ. assumption. reflexivity.
    }
    {
      rewrite IHψ. assumption. reflexivity.
    }
  Qed.


  Fixpoint maximal_mu_depth_of_evar_in_pattern' (depth : nat) (E : evar) (ψ : Pattern) : nat :=
    match ψ with
    | patt_bott => 0
    | patt_sym _ => 0
    | patt_bound_evar _ => 0
    | patt_bound_svar _ => 0
    | patt_free_svar _ => 0
    | patt_free_evar E' =>
      match (decide (E' = E)) with
      | left _ => depth
      | right _ => 0
      end
    | patt_imp ψ₁ ψ₂
      => Nat.max
        (maximal_mu_depth_of_evar_in_pattern' depth E ψ₁)
        (maximal_mu_depth_of_evar_in_pattern' depth E ψ₂)
    | patt_app ψ₁ ψ₂
      => Nat.max
        (maximal_mu_depth_of_evar_in_pattern' depth E ψ₁)
        (maximal_mu_depth_of_evar_in_pattern' depth E ψ₂)
    | patt_exists ψ' =>
      maximal_mu_depth_of_evar_in_pattern' depth E ψ'
    | patt_mu ψ' =>
      maximal_mu_depth_of_evar_in_pattern' (S depth) E ψ'
    end.

  Definition maximal_mu_depth_of_evar_in_pattern (E : evar) (ψ : Pattern) : nat :=
    maximal_mu_depth_of_evar_in_pattern' 0 E ψ.



  Lemma svar_fresh_seq_max (SvS : SVarSet) (n1 n2 : nat) :
    (@list_to_set svar SVarSet _ _ _ (svar_fresh_seq SvS n1)) ⊆ (list_to_set (svar_fresh_seq SvS (n1 `max` n2))).
  Proof.
    move: SvS n2.
    induction n1; intros SvS n2.
    {
      simpl. set_solver.
    }
    {
      simpl.
      destruct n2.
      {
        simpl. set_solver.
      }
      {
        simpl.
        cut (@list_to_set svar SVarSet _ _ _ (svar_fresh_seq ({[svar_fresh_s SvS]} ∪ SvS) n1)
        ⊆ list_to_set (svar_fresh_seq ({[svar_fresh_s SvS]} ∪ SvS) (n1 `max` n2))).
        {
          set_solver.
        }
        specialize (IHn1 ({[svar_fresh_s SvS]} ∪ SvS) n2).
        apply IHn1.
      }
    }
  Qed.


  Lemma pile_evs_svs_kt evs1 evs2 svs1 svs2 kt1 kt2:
    evs1 ⊆ evs2 ->
    svs1 ⊆ svs2 ->
    kt1 ==> kt2 ->
    ProofInfoLe
      (pi_Generic (ExGen := evs1, SVSubst := svs1, KT := kt1))
      (pi_Generic (ExGen := evs2, SVSubst := svs2, KT := kt2)).
  Proof.
    intros Hevs Hsvs Hkt.
    eapply pile_trans.
    {
      apply pile_evs_subseteq. apply Hevs.
    }
    eapply pile_trans.
    {
      apply pile_svs_subseteq. apply Hsvs.
    }
    apply pile_kt_impl.
    apply Hkt.
  Qed.

  Lemma mmdoeip_svar_open depth E n X ψ:
    maximal_mu_depth_of_evar_in_pattern' depth E (svar_open n X ψ)
    = maximal_mu_depth_of_evar_in_pattern' depth E ψ.
  Proof.
    unfold svar_open.
    move: depth n.
    induction ψ; intros depth n'; simpl; try reflexivity.
    {
      case_match; simpl; try reflexivity.
    }
    {
      rewrite IHψ1. rewrite IHψ2. reflexivity.
    }
    {
      rewrite IHψ1. rewrite IHψ2. reflexivity.
    }
    {
      rewrite IHψ. reflexivity.
    }
    {
      rewrite IHψ. reflexivity.
    }
  Qed.

  Lemma mmdoeip_evar_open depth E n x ψ:
  E <> x ->
  maximal_mu_depth_of_evar_in_pattern' depth E (evar_open n x ψ)
  = maximal_mu_depth_of_evar_in_pattern' depth E ψ.
Proof.
  intros Hne.
  unfold evar_open.
  move: depth n.
  induction ψ; intros depth n'; simpl; try reflexivity.
  {
    case_match; simpl; try reflexivity.
    case_match; simpl; try reflexivity.
    subst. contradiction.
  }
  {
    rewrite IHψ1. rewrite IHψ2. reflexivity.
  }
  {
    rewrite IHψ1. rewrite IHψ2. reflexivity.
  }
  {
    rewrite IHψ. reflexivity.
  }
  {
    rewrite IHψ. reflexivity.
  }
Qed.


  Lemma mmdoeip_notin E ψ depth:
    E ∉ free_evars ψ ->
    maximal_mu_depth_of_evar_in_pattern' depth E ψ = 0.
  Proof.
    intros Hnotin.
    move: E depth Hnotin.
    induction ψ; intros E depth Hnotin; simpl in *; try reflexivity.
    { case_match. set_solver. reflexivity. }
    { rewrite IHψ1. set_solver. rewrite IHψ2. set_solver. reflexivity. }
    { rewrite IHψ1. set_solver. rewrite IHψ2. set_solver. reflexivity. }
    { rewrite IHψ. exact Hnotin. reflexivity. }
    { rewrite IHψ. exact Hnotin. reflexivity. }
  Qed.

  Lemma mmdoeip_S_in E ψ depth:
    E ∈ free_evars ψ ->
    maximal_mu_depth_of_evar_in_pattern' (S depth) E ψ
    = S (maximal_mu_depth_of_evar_in_pattern' depth E ψ).
  Proof.
    intros Hin.
    move: E depth Hin.
    induction ψ; intros E depth Hin; simpl in *.
    { case_match. reflexivity. set_solver. }
    { set_solver. }
    { set_solver. }
    { set_solver. }
    { set_solver. }
    {
      destruct (decide (E ∈ free_evars ψ1)),(decide (E ∈ free_evars ψ2)).
      {
        rewrite IHψ1. assumption. rewrite IHψ2. assumption. simpl. reflexivity.
      }
      {
      rewrite IHψ1. assumption.
      rewrite [maximal_mu_depth_of_evar_in_pattern' _ _ ψ2]mmdoeip_notin.
      { assumption. }
      rewrite [maximal_mu_depth_of_evar_in_pattern' _ _ ψ2]mmdoeip_notin.
      { assumption. }
      simpl.
      rewrite Nat.max_comm.
      simpl.
      reflexivity.
    }
    {
      rewrite IHψ2. assumption.
      rewrite [maximal_mu_depth_of_evar_in_pattern' _ _ ψ1]mmdoeip_notin.
      { assumption. }
      rewrite [maximal_mu_depth_of_evar_in_pattern' _ _ ψ1]mmdoeip_notin.
      { assumption. }
      simpl.
      reflexivity.
    }
    {
      exfalso. set_solver.
    }
  }
  { set_solver. }
  {
    destruct (decide (E ∈ free_evars ψ1)),(decide (E ∈ free_evars ψ2)).
    {
      rewrite IHψ1. assumption. rewrite IHψ2. assumption. simpl. reflexivity.
    }
    {
    rewrite IHψ1. assumption.
    rewrite [maximal_mu_depth_of_evar_in_pattern' _ _ ψ2]mmdoeip_notin.
    { assumption. }
    rewrite [maximal_mu_depth_of_evar_in_pattern' _ _ ψ2]mmdoeip_notin.
    { assumption. }
    simpl.
    rewrite Nat.max_comm.
    simpl.
    reflexivity.
  }
  {
    rewrite IHψ2. assumption.
    rewrite [maximal_mu_depth_of_evar_in_pattern' _ _ ψ1]mmdoeip_notin.
    { assumption. }
    rewrite [maximal_mu_depth_of_evar_in_pattern' _ _ ψ1]mmdoeip_notin.
    { assumption. }
    simpl.
    reflexivity.
  }
  {
    exfalso. set_solver.
  }
}
{
  rewrite IHψ. assumption. reflexivity.
}
{
  rewrite IHψ. assumption. reflexivity.
}
Qed.


  Lemma eq_prf_equiv_congruence
  Γ p q
  (wfp : well_formed p)
  (wfq : well_formed q)
  (EvS : EVarSet)
  (SvS : SVarSet)
  E ψ
  (wfψ : well_formed ψ)
  (p_sub_EvS : (free_evars p) ⊆ EvS)
  (q_sub_EvS : (free_evars q) ⊆ EvS)
  (ψ_sub_EvS : (free_evars ψ) ⊆ EvS)
  (E_in_EvS : E ∈ EvS)
  (p_sub_SvS : (free_svars p) ⊆ SvS)
  (q_sub_SvS : (free_svars q) ⊆ SvS)
  (ψ_sub_SvS : (free_svars ψ) ⊆ SvS)
  (exdepth : nat)
  (mudepth : nat)
  (i : ProofInfo)
  (pile : ProofInfoLe
   (pi_Generic
     (ExGen := list_to_set (evar_fresh_seq EvS (maximal_exists_depth_of_evar_in_pattern' exdepth E ψ)),
     SVSubst := list_to_set (svar_fresh_seq SvS (maximal_mu_depth_of_evar_in_pattern' mudepth E ψ)),
     KT := if decide (0 = (maximal_mu_depth_of_evar_in_pattern' mudepth E ψ)) is left _ then false else true)
    )
   i
  )
  (pf : Γ ⊢ (p <---> q) using i) :
      Γ ⊢ (((free_evar_subst ψ p E) <---> (free_evar_subst ψ q E))) using i.
  Proof.
    remember (size' ψ) as sz.
    assert (Hsz: size' ψ <= sz) by lia.
    clear Heqsz.

    move: ψ wfψ Hsz EvS SvS pile
      p_sub_EvS q_sub_EvS E_in_EvS ψ_sub_EvS
      p_sub_SvS q_sub_SvS ψ_sub_SvS
    .
    induction sz; intros ψ wfψ Hsz EvS SvS pile
      p_sub_EvS q_sub_EvS E_in_EvS ψ_sub_EvS p_sub_SvS q_sub_SvS ψ_sub_SvS;
      destruct ψ; simpl in Hsz; try lia; simpl.
    {
      destruct (decide (E = x)).
      {
        exact pf.
      }
      {
        usePropositionalReasoning.
        apply pf_iff_equiv_refl.
        wf_auto2.
      }
    }
    {
      usePropositionalReasoning.
      apply pf_iff_equiv_refl.
      wf_auto2.
    }
    {
      usePropositionalReasoning.
      apply pf_iff_equiv_refl.
      wf_auto2.
    }
    {
      usePropositionalReasoning.
      apply pf_iff_equiv_refl.
      wf_auto2.
    }
    {
      usePropositionalReasoning.
      apply pf_iff_equiv_refl.
      wf_auto2.
    }
    {
      pose proof (pf₁ := (IHsz ψ1 ltac:(wf_auto2) ltac:(lia)) EvS SvS).
      feed specialize pf₁.
      {
        eapply pile_trans.
        2: { apply pile. }
        simpl.
        apply pile_evs_svs_kt.
        {
          apply evar_fresh_seq_max.
        }
        {
          apply svar_fresh_seq_max.
        }
        {
          clear pf₁.
          repeat case_match; simpl; try reflexivity.
          {
            lia.
          }
          {
            lia.
          }
        }
      }
      { exact p_sub_EvS. }
      { exact q_sub_EvS. }
      { exact E_in_EvS. }
      {
        simpl in ψ_sub_EvS.
        clear -ψ_sub_EvS.
        set_solver.
      }
      { exact p_sub_SvS. }
      { exact q_sub_SvS. }
      { simpl in ψ_sub_SvS.
        clear -ψ_sub_SvS.
        set_solver.
      }
      pose proof (pf₂ := (IHsz ψ2 ltac:(wf_auto2) ltac:(lia)) EvS SvS).
      feed specialize pf₂.
      {
        eapply pile_trans.
        2: { apply pile. }
        simpl.
        apply pile_evs_svs_kt.
        {
          simpl.
          rewrite Nat.max_comm.
          apply evar_fresh_seq_max.
        }
        {
          rewrite Nat.max_comm.
          apply svar_fresh_seq_max.
        }
        {
          clear pf₂.
          repeat case_match; simpl; try reflexivity; try lia.
        }
      }
      { exact p_sub_EvS. }
      { exact q_sub_EvS. }
      { exact E_in_EvS. }
      {
        simpl in ψ_sub_EvS.
        clear -ψ_sub_EvS.
        set_solver.
      }
      { exact p_sub_SvS. }
      { exact q_sub_SvS. }
      { simpl in ψ_sub_SvS.
        clear -ψ_sub_SvS.
        set_solver.
      }

      eapply pf_iff_equiv_trans.
      5: { 
        apply conj_intro_meta.
        4: {
          apply Framing_right.
          {
            unfold BasicReasoning.
            eapply pile_trans.
            2: { apply pile. }
            simpl.
            apply pile_evs_svs_kt.
            { clear. set_solver. }
            { clear. set_solver. }
            { reflexivity. }
          }
          {
            wf_auto2.
          }
          {
            eapply pf_conj_elim_r_meta in pf₂.
            apply pf₂.
            { wf_auto2. }
            { wf_auto2. }
          }
        }
        3: {
          apply Framing_right.
          {
            eapply pile_trans.
            2: { apply pile. }
            apply pile_evs_svs_kt.
            { clear. set_solver. }
            { clear. set_solver. }
            { reflexivity. }
          }
          {
            wf_auto2.
          }
          {
            eapply pf_conj_elim_l_meta in pf₂.
            apply pf₂.
            { wf_auto2. }
            { wf_auto2. }
          }
        }
        {
          wf_auto2.
        }
        {
          wf_auto2.
        }
       }
       4: {
        apply conj_intro_meta.
        4: {
          apply Framing_left.
          {
            eapply pile_trans.
            2: { apply pile. }
            apply pile_evs_svs_kt.
            { clear. set_solver. }
            { clear. set_solver. }
            { reflexivity. }
          }
          {
            wf_auto2.
          }
          {
            eapply pf_conj_elim_r_meta in pf₁.
            apply pf₁.
            { wf_auto2. }
            { wf_auto2. }
          }
        }
        3: {
          apply Framing_left.
          {
            eapply pile_trans.
            2: { apply pile. }
            apply pile_evs_svs_kt.
            { clear. set_solver. }
            { clear. set_solver. }
            { reflexivity. }
          }
          {
            wf_auto2.
          }
          {
            eapply pf_conj_elim_l_meta in pf₁.
            apply pf₁.
            { wf_auto2. }
            { wf_auto2. }
          }
        }
        {
          wf_auto2.
        }
        {
          wf_auto2.
        }         
       }
       { wf_auto2. }
       { wf_auto2. }
       { wf_auto2. }
    }
    {
      usePropositionalReasoning.
      apply pf_iff_equiv_refl.
      wf_auto2.
    }
    {
      pose proof (pf₁ := (IHsz ψ1 ltac:(wf_auto2) ltac:(lia)) EvS SvS).
      feed specialize pf₁.
      {
        eapply pile_trans.
        2: { apply pile. }
        apply pile_evs_svs_kt.
        { 
          simpl.
          apply evar_fresh_seq_max.
        }
        {
          simpl.
          apply svar_fresh_seq_max.
        }
        {
          clear pf₁.
          repeat case_match; simpl; try reflexivity; simpl in *.
          lia.
        }
      }
      { exact p_sub_EvS. }
      { exact q_sub_EvS. }
      { exact E_in_EvS. }
      {
        simpl in ψ_sub_EvS.
        clear -ψ_sub_EvS.
        set_solver.
      }
      { exact p_sub_SvS. }
      { exact q_sub_SvS. }
      { simpl in ψ_sub_SvS.
        clear -ψ_sub_SvS.
        set_solver.
      }

      pose proof (pf₂ := (IHsz ψ2 ltac:(wf_auto2) ltac:(lia)) EvS SvS).
      feed specialize pf₂.
      {
        eapply pile_trans.
        2: { apply pile. }
        apply pile_evs_svs_kt.
        { 
          simpl.
          rewrite Nat.max_comm.
          apply evar_fresh_seq_max.
        }
        {
          simpl.
          rewrite Nat.max_comm.
          apply svar_fresh_seq_max.
        }
        {
          clear pf₂.
          repeat case_match; simpl in *; try reflexivity; lia.
        }
      }
      { exact p_sub_EvS. }
      { exact q_sub_EvS. }
      { exact E_in_EvS. }
      {
        simpl in ψ_sub_EvS.
        clear -ψ_sub_EvS.
        set_solver.
      }
      { exact p_sub_SvS. }
      { exact q_sub_SvS. }
      { simpl in ψ_sub_SvS.
        clear -ψ_sub_SvS.
        set_solver.
      }

      apply prf_equiv_of_impl_of_equiv.
      { wf_auto2. }
      { wf_auto2. }
      { wf_auto2. }
      { wf_auto2. }
      { apply pf₁. }
      { apply pf₂. }
    }
    {
      pose proof (frx := @set_evar_fresh_is_fresh' Σ EvS).
      remember (evar_fresh (elements EvS)) as x.

      (* i = pi_Generic gpi *)
      destruct i.
      {
        exfalso.
        eapply not_generic_in_prop.
        apply pile.
      }

      destruct (decide (E ∈ free_evars ψ)) as [HEinψ|HEnotinψ].
      2: {
        rewrite free_evar_subst_no_occurrence.
        {
          apply count_evar_occurrences_0.
          assumption.
        }
        rewrite free_evar_subst_no_occurrence.
        {
          apply count_evar_occurrences_0.
          assumption.
        }
        usePropositionalReasoning.
        apply pf_iff_equiv_refl.
        { wf_auto2. }
      }

      pose proof (IH := IHsz (evar_open 0 x ψ) ltac:(wf_auto2) ltac:(rewrite evar_open_size'; lia)).
      specialize (IH ({[x]} ∪ EvS) SvS).
      feed specialize IH.
      {
        simpl.
        eapply pile_trans.
        2: { apply pile. }
        assert (HxneE: x <> E).
        {
          clear -frx E_in_EvS. set_solver.
        }
        apply pile_evs_svs_kt.
        {
          simpl.
          rewrite medoeip_evar_open.
          { apply not_eq_sym. exact HxneE. }
          simpl.

          rewrite medoeip_S_in.
          { assumption. }
          remember (maximal_exists_depth_of_evar_in_pattern' exdepth E ψ) as n.
          simpl.
          unfold evar_fresh_s.
          rewrite -Heqx.
          clear. set_solver.
        }
        {
          simpl.
          rewrite mmdoeip_evar_open.
          { apply not_eq_sym. exact HxneE. }
          apply reflexivity.
        }
        {
          clear IH.
          repeat case_match; simpl in *; try reflexivity.
          pose proof (Htmp := n).
          rewrite mmdoeip_evar_open in Htmp.
          { apply not_eq_sym. exact HxneE. }
          lia.
        }
      }
      { clear -p_sub_EvS. set_solver. }
      { clear -q_sub_EvS. set_solver. }
      { clear -E_in_EvS. set_solver. }
      { clear -ψ_sub_EvS. Search free_evars evar_open.
        rewrite elem_of_subseteq.
        intros x0.
        rewrite free_evars_evar_open''.
        intros [[H1 H2]| H2].
        {
          subst. clear. set_solver.
        }
        {
          simpl in ψ_sub_EvS.
          set_solver.
        }
      }
      { exact p_sub_SvS. }
      { exact q_sub_SvS. }
      { simpl in ψ_sub_SvS.
        clear -ψ_sub_SvS.
        rewrite free_svars_evar_open.
        exact ψ_sub_SvS.
      }
      apply pf_evar_open_free_evar_subst_equiv_sides in IH.
      2: { set_solver. }
      2: { wf_auto2. }
      2: { wf_auto2. }
      unshelve (epose proof (IH1 := @pf_iff_proj1 Σ Γ _ _ _ _ _ IH)).
      { wf_auto2. }
      { wf_auto2. }
      unshelve (epose proof (IH2 := @pf_iff_proj2 Σ Γ _ _ _ _ _ IH)).
      { wf_auto2. }
      { wf_auto2. }

      (* TODO: remove the well-formedness constraints on this lemma*)
      apply pf_iff_split.
      { wf_auto2. }
      { wf_auto2. }
      {
        eapply strip_exists_quantify_l.
        3: {
          apply Ex_gen.
          3: {
            eapply syllogism_meta.
            5: {
              useBasicReasoning.
              apply Ex_quan.
              wf_auto2.
            }
            4: {
                apply IH1.
              }
            { wf_auto2. }
            { simpl. wf_auto2. apply wfc_ex_aux_bevar_subst. wf_auto2. wf_auto2. }
            { wf_auto2. }
          }
          {
            eapply pile_trans.
            2: { apply pile. }
            apply pile_evs_svs_kt.
            {
              simpl.
              rewrite medoeip_S_in.
              { assumption. }
              simpl.
              unfold evar_fresh_s.
              rewrite -Heqx.
              clear.
              set_solver.
            }
            {
              clear. set_solver.
            }
            {
              reflexivity.
            }
          }
          {
            simpl.
            pose proof (Htmp := @free_evars_free_evar_subst Σ ψ q E).
            set_solver.
          }
        }
        {
          simpl.
          pose proof (Htmp := @free_evars_free_evar_subst Σ ψ p E).
          set_solver.
        }
        {
          wf_auto2.
        }
      }
      (* this block is a symmetric version of the previous block*)
      {
        eapply strip_exists_quantify_l.
        3: {
          apply Ex_gen.
          3: {
            eapply syllogism_meta.
            5: {
              useBasicReasoning.
              apply Ex_quan.
              wf_auto2.
            }
            4: {
                apply IH2.
              }
            { wf_auto2. }
            { simpl. wf_auto2. apply wfc_ex_aux_bevar_subst. wf_auto2. wf_auto2. }
            { wf_auto2. }
          }
          {
            eapply pile_trans.
            2: { apply pile. }
            apply pile_evs_svs_kt.
            {
              simpl.
              rewrite medoeip_S_in.
              { assumption. }
              simpl.
              unfold evar_fresh_s.
              rewrite -Heqx.
              clear.
              set_solver.
            }
            {
              clear. set_solver.
            }
            {
              reflexivity.
            }
          }
          {
            simpl.
            pose proof (Htmp := @free_evars_free_evar_subst Σ ψ p E).
            set_solver.
          }
        }
        {
          simpl.
          pose proof (Htmp := @free_evars_free_evar_subst Σ ψ q E).
          set_solver.
        }
        {
          wf_auto2.
        }
      }
    }
    {
      pose proof (frX := @set_svar_fresh_is_fresh' Σ SvS).
      remember (svar_fresh (elements SvS)) as X.

      (* i = pi_Generic gpi *)
      destruct i.
      {
        exfalso.
        eapply not_generic_in_prop.
        apply pile.
      }

      destruct (decide (E ∈ free_evars ψ)) as [HEinψ|HEnotinψ].
      2: {
        rewrite free_evar_subst_no_occurrence.
        {
          apply count_evar_occurrences_0.
          assumption.
        }
        rewrite free_evar_subst_no_occurrence.
        {
          apply count_evar_occurrences_0.
          assumption.
        }
        usePropositionalReasoning.
        apply pf_iff_equiv_refl.
        { wf_auto2. }
      }

      pose proof (IH := IHsz (svar_open 0 X ψ) ltac:(wf_auto2) ltac:(rewrite svar_open_size'; lia)).
      specialize (IH EvS ({[X]} ∪ SvS)).
      feed specialize IH.
      {
        eapply pile_trans.
        2: { apply pile. }
        apply pile_evs_svs_kt.
        {
          simpl.
          rewrite medoeip_svar_open.
          apply reflexivity.
        }
        {
          simpl.
          rewrite mmdoeip_svar_open.
          rewrite mmdoeip_S_in.
          { exact HEinψ. }
          simpl.
          unfold svar_fresh_s.
          rewrite -HeqX.
          clear. set_solver.
        }
        {
          clear IH.
          repeat case_match; simpl in *; try reflexivity.
          pose proof (Htmp := n).
          rewrite mmdoeip_svar_open in Htmp.
          pose proof (Htmp2 := e).
          rewrite mmdoeip_S_in in Htmp2.
          { exact HEinψ. }
          inversion Htmp2.
        }
      }
      {
        exact p_sub_EvS.
      }
      {
        exact q_sub_EvS.
      }
      {
        exact E_in_EvS.
      }
      {
        rewrite free_evars_svar_open.
        simpl in ψ_sub_EvS.
        apply ψ_sub_EvS.
      }
      {
        clear -p_sub_SvS.
        set_solver.
      }
      {
        clear -q_sub_SvS.
        set_solver.
      }
      {
        rewrite elem_of_subseteq.
        intros X'.
        rewrite free_svars_svar_open''.
        intros [[H1 H2]|H1].
        {
          subst X'. clear. set_solver.
        }
        {
          simpl in ψ_sub_SvS.
          clear -H1 ψ_sub_SvS.
          set_solver.
        }
      }

      apply pf_iff_free_evar_subst_svar_open_to_bsvar_subst_free_evar_subst in IH.
      3: { wf_auto2. }
      2: { wf_auto2. }

      unshelve (epose proof (IH1 := @pf_iff_proj1 _ _ _ _ _ _ _ IH)).
      { wf_auto2. }
      { wf_auto2. }
      unshelve (epose proof (IH2 := @pf_iff_proj2 _ _ _ _ _ _ _ IH)).
      { wf_auto2. }
      { wf_auto2. }

      eapply pf_iff_mu_remove_svar_quantify_svar_open.
      5: {
        apply pf_iff_split.
        4: {
          apply mu_monotone.
          4: {
            unfold svar_open.
            apply IH2.
          }
          3: {
            wf_auto2. simpl in *.
            pose proof (Htmp := @free_svars_free_evar_subst Σ ψ E p).
            clear -Htmp ψ_sub_SvS p_sub_SvS frX.
            set_solver.
          }
          2: {
            wf_auto2. simpl in *.
            pose proof (Htmp := @free_svars_free_evar_subst Σ ψ E q).
            clear -Htmp ψ_sub_SvS q_sub_SvS frX.
            set_solver.
          }
          {
            eapply pile_trans.
            2: { apply pile. }
            apply pile_evs_svs_kt.
            {
              clear. set_solver.
            }
            {
              simpl.
              rewrite mmdoeip_S_in.
              { exact HEinψ. }
              simpl.
              unfold svar_fresh_s.
              rewrite -HeqX.
              clear. set_solver.
            }
            {
              repeat case_match; simpl in *; try reflexivity.
              pose proof (Htmp := e).
              rewrite mmdoeip_S_in in Htmp.
              { exact HEinψ. }
              inversion Htmp.
            }
          }
        }
        3: {
          apply mu_monotone.
          4: {
            unfold svar_open.
            apply IH1.
          }
          3: {
            wf_auto2. simpl in *.
            pose proof (Htmp := @free_svars_free_evar_subst Σ ψ E q).
            clear -Htmp ψ_sub_SvS q_sub_SvS frX.
            set_solver.
          }
          2: {
            wf_auto2. simpl in *.
            pose proof (Htmp := @free_svars_free_evar_subst Σ ψ E p).
            clear -Htmp ψ_sub_SvS p_sub_SvS frX.
            set_solver.
          }
          {
            eapply pile_trans.
            2: { apply pile. }
            apply pile_evs_svs_kt.
            {
              clear. set_solver.
            }
            {
              simpl.
              rewrite mmdoeip_S_in.
              { exact HEinψ. }
              simpl.
              unfold svar_fresh_s.
              rewrite -HeqX.
              clear. set_solver.
            }
            {
              repeat case_match; simpl in *; try reflexivity.
              pose proof (Htmp := e).
              rewrite mmdoeip_S_in in Htmp.
              { exact HEinψ. }
              inversion Htmp.
            }
          }          
        }
        {
          cut (X ∉ free_svars ψ.[[evar:E↦p]]).
          {
            wf_auto2.
          }
          pose proof (@free_svars_free_evar_subst Σ ψ E p).
          clear -H frX ψ_sub_SvS p_sub_SvS.
          set_solver.
        }
        {
          cut (X ∉ free_svars ψ.[[evar:E↦q]]).
          {
            wf_auto2.
          }
          pose proof (@free_svars_free_evar_subst Σ ψ E q).
          clear -H frX ψ_sub_SvS q_sub_SvS.
          set_solver.
        }
      }
      {
        wf_auto2.
      }
      {
        wf_auto2.
      }
      {
        pose proof (@free_svars_free_evar_subst Σ ψ E p).
        clear -H frX ψ_sub_SvS p_sub_SvS.
        set_solver.
      }
      {
        pose proof (@free_svars_free_evar_subst Σ ψ E q).
        clear -H frX ψ_sub_SvS q_sub_SvS.
        set_solver.
      }
    }
  Defined.

  Lemma prf_equiv_congruence Γ p q C
  (i : ProofInfo)
  (pile : ProofInfoLe
   (pi_Generic
     (ExGen := list_to_set (evar_fresh_seq (free_evars (pcPattern C) ∪ free_evars p ∪ free_evars q ∪ {[pcEvar C]}) (maximal_exists_depth_of_evar_in_pattern (pcEvar C) (pcPattern C))),
     SVSubst := list_to_set (svar_fresh_seq (free_svars (pcPattern C) ∪ free_svars p ∪ free_svars q) (maximal_mu_depth_of_evar_in_pattern (pcEvar C) (pcPattern C))),
     KT := if decide (0 = (maximal_mu_depth_of_evar_in_pattern (pcEvar C) (pcPattern C))) is left _ then false else true)
    )
   i
  ):
    PC_wf C ->
    Γ ⊢ (p <---> q) using i ->
    Γ ⊢ (((emplace C p) <---> (emplace C q))) using i.
  Proof.
    intros wfC Hiff.
    pose proof (proved_impl_wf _ _ (proj1_sig Hiff)).
    assert (well_formed p) by (abstract (wf_auto2)).
    assert (well_formed q) by (abstract (wf_auto2)).
    destruct C as [pcEvar pcPattern].
    apply @eq_prf_equiv_congruence
    with (EvS := (free_evars pcPattern ∪ free_evars p ∪ free_evars q ∪ {[pcEvar]}))
         (SvS := (free_svars pcPattern ∪ free_svars p ∪ free_svars q))
         (exdepth := 0)
         (mudepth := 0)
    .
    { assumption. }
    { assumption. }
    { abstract (simpl; wf_auto2). }
    { abstract (clear; set_solver). }
    { abstract (clear; set_solver). }
    { abstract (clear; set_solver). }
    { abstract (simpl; clear; set_solver). }
    { abstract (clear; set_solver). }
    { abstract (clear; set_solver). }
    { abstract (simpl; clear; set_solver). }
    { simpl. exact pile. }
    { exact Hiff. }
  Defined.
  Print prf_equiv_congruence.


End FOL_helpers.

Lemma ex_quan_monotone {Σ : Signature} Γ x ϕ₁ ϕ₂ (i : ProofInfo)
  (pile : ProofInfoLe (pi_Generic (ExGen := {[x]}, SVSubst := ∅, KT := false)) i) :
  Γ ⊢ ϕ₁ ---> ϕ₂ using i ->
  Γ ⊢ (exists_quantify x ϕ₁) ---> (exists_quantify x ϕ₂) using i.
Proof.
  intros H.
  pose proof (Hwf := @proved_impl_wf Σ Γ _ (proj1_sig H)).
  assert (wfϕ₁: well_formed ϕ₁ = true) by wf_auto2.
  assert (wfϕ₂: well_formed ϕ₂ = true) by wf_auto2.
  apply Ex_gen.
  { exact pile. }
  { simpl. rewrite free_evars_evar_quantify. clear. set_solver. }

  unfold exists_quantify.
  eapply syllogism_meta. 4: apply H.
  { wf_auto2. }
  { wf_auto2. }
  { wf_auto2. }
  clear H wfϕ₁ ϕ₁ Hwf.

  (* We no longer need to use [cast_proof] to avoid to ugly eq_sym terms;
     however, without [cast_proof'] the [replace] tactics does not work,
     maybe because of implicit parameters.
   *)
  eapply (cast_proof').
  {
    replace ϕ₂ with (instantiate (ex, evar_quantify x 0 ϕ₂) (patt_free_evar x)) at 1.
    2: { unfold instantiate.
       rewrite bevar_subst_evar_quantify_free_evar.
       now do 2 apply andb_true_iff in wfϕ₂ as [_ wfϕ₂].
       reflexivity.
    }
    reflexivity.
  }
        (* i = pi_Generic gpi *)
  destruct i.
  {
    exfalso.
    eapply not_generic_in_prop.
    apply pile.
  }
  
  useBasicReasoning.
  apply Ex_quan.
  abstract (wf_auto2).
Defined.

Lemma ex_quan_and_proj1 {Σ : Signature} Γ x ϕ₁ ϕ₂:
  well_formed ϕ₁ = true ->
  well_formed ϕ₂ = true ->
  Γ ⊢ (exists_quantify x (ϕ₁ and ϕ₂)) ---> (exists_quantify x ϕ₁)
  using (pi_Generic (ExGen := {[x]}, SVSubst := ∅, KT := false)).
Proof.
  intros wfϕ₁ wfϕ₂.
  apply ex_quan_monotone.
  { apply pile_refl. }
  toMyGoal.
  { wf_auto2. }
  mgIntro.
  mgDestructAnd 0. mgExactn 0.
Defined.

Lemma ex_quan_and_proj2 {Σ : Signature} Γ x ϕ₁ ϕ₂:
  well_formed ϕ₁ = true ->
  well_formed ϕ₂ = true ->
  Γ ⊢ (exists_quantify x (ϕ₁ and ϕ₂)) ---> (exists_quantify x ϕ₂)
  using (pi_Generic (ExGen := {[x]}, SVSubst := ∅, KT := false)).
Proof.
  intros wfϕ₁ wfϕ₂.
  apply ex_quan_monotone.
  { apply pile_refl. }
  toMyGoal.
  { wf_auto2. }
  mgIntro.
  mgDestructAnd 0.
  mgExactn 1.
Defined.

Lemma lhs_to_and {Σ : Signature} Γ a b c i:
  well_formed a ->
  well_formed b ->
  well_formed c ->
  Γ ⊢ (a and b) ---> c using i ->
  Γ ⊢ a ---> b ---> c using i.
Proof.
  intros wfa wfb wfc H.
  toMyGoal.
  { wf_auto2. }
  do 2 mgIntro. mgApplyMeta H.
  fromMyGoal.
  usePropositionalReasoning.
  apply conj_intro.
  { wf_auto2. }
  { wf_auto2. }
Defined.

Lemma lhs_from_and {Σ : Signature} Γ a b c i:
  well_formed a ->
  well_formed b ->
  well_formed c ->
  Γ ⊢ a ---> b ---> c using i ->
  Γ ⊢ (a and b) ---> c using i.
Proof.
  intros wfa wfb wfc H.
  toMyGoal.
  { wf_auto2. }
  mgIntro.
  mgAssert (b).
  { wf_auto2. }
  { fromMyGoal. usePropositionalReasoning. apply pf_conj_elim_r.
    wf_auto2. wf_auto2.
  }
  mgAssert (a) using first 1.
  { wf_auto2. }
  { fromMyGoal. usePropositionalReasoning. apply pf_conj_elim_l; wf_auto2. }
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
  Γ ⊢ (foldr patt_imp a l) ---> (foldr patt_imp b l) ---> (foldr patt_imp (a and b) l)
  using PropositionalReasoning.
Proof.
  intros wfa wfb wfl.
  induction l.
  - simpl. apply conj_intro; assumption.
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
    fromMyGoal. apply IHl.
Defined.

Lemma prf_conj_split_meta {Σ : Signature} Γ a b l (i : ProofInfo):
  well_formed a ->
  well_formed b ->
  wf l ->
  Γ ⊢ (foldr patt_imp a l) using i -> 
  Γ ⊢ (foldr patt_imp b l) ---> (foldr patt_imp (a and b) l) using i.
Proof.
  intros. eapply MP. 2: { usePropositionalReasoning. apply prf_conj_split; assumption. }
  exact H2.
Defined.

Lemma prf_conj_split_meta_meta {Σ : Signature} Γ a b l (i : ProofInfo):
  well_formed a ->
  well_formed b ->
  wf l ->
  Γ ⊢ (foldr patt_imp a l) using i -> 
  Γ ⊢ (foldr patt_imp b l) using i ->
  Γ ⊢ (foldr patt_imp (a and b) l) using i.
Proof.
  intros. eapply MP.
  2: {
    apply prf_conj_split_meta; assumption.
  }
  exact H3.
Defined.

Lemma MyGoal_splitAnd {Σ : Signature} Γ a b l i:
  @mkMyGoal Σ Γ l a i ->
  @mkMyGoal Σ Γ l b i ->
  @mkMyGoal Σ Γ l (a and b) i.
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
  Γ ⊢ a ---> b ---> c ---> (a and b)
  using PropositionalReasoning.
Proof.
  intros wfa wfb wfc.
  toMyGoal.
  { wf_auto2. }
  mgIntro. mgIntro. mgIntro.
  mgSplitAnd.
  - mgExactn 0.
  - mgExactn 1.
Defined.

Lemma prf_local_goals_equiv_impl_full_equiv {Σ : Signature} Γ g₁ g₂ l:
  well_formed g₁ ->
  well_formed g₂ ->
  wf l ->
  Γ ⊢ (foldr patt_imp (g₁ <---> g₂) l) --->
      ((foldr patt_imp g₁ l) <---> (foldr patt_imp g₂ l))
  using PropositionalReasoning.
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
      fromMyGoal. toMyGoal.
      { wf_auto2. }
      unshelve(mgApplyMeta (@P2 _ _ _ _ _ _ _ _)).
      1-3: wf_auto2.
      mgIntro. mgClear 0. mgIntro.
      mgApplyMeta IHl in 0. unfold patt_iff at 1. mgDestructAnd 0.
      mgExactn 0.
    + unshelve (mgApplyMeta (@P2 _ _ _ _ _ _ _ _)).
      1-3: wf_auto2.
      fromMyGoal. toMyGoal.
      { wf_auto2. }
      unshelve (mgApplyMeta (@P2 _ _ _ _ _ _ _ _)).
      1-3: wf_auto2.
      mgIntro. mgClear 0. mgIntro.
      mgApplyMeta IHl in 0. unfold patt_iff at 1. mgDestructAnd 0.
      mgExactn 1.
Defined.

Lemma prf_local_goals_equiv_impl_full_equiv_meta {Σ : Signature} Γ g₁ g₂ l i:
  well_formed g₁ ->
  well_formed g₂ ->
  wf l ->
  Γ ⊢ (foldr patt_imp (g₁ <---> g₂) l) using i ->
  Γ ⊢ ((foldr patt_imp g₁ l) <---> (foldr patt_imp g₂ l)) using i.
Proof.
  intros wfg₁ wfg₂ wfl H.
  eapply MP.
  2: { usePropositionalReasoning. apply prf_local_goals_equiv_impl_full_equiv; assumption. }
  exact H.
Defined.

Lemma prf_local_goals_equiv_impl_full_equiv_meta_proj1 {Σ : Signature} Γ g₁ g₂ l i:
  well_formed g₁ ->
  well_formed g₂ ->
  wf l ->
  Γ ⊢ (foldr patt_imp (g₁ <---> g₂) l) using i ->
  Γ ⊢ (foldr patt_imp g₁ l) using i ->
  Γ ⊢ (foldr patt_imp g₂ l) using i.
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
  wf l ->
  Γ ⊢ (foldr patt_imp (g₁ <---> g₂) l) using i ->
  Γ ⊢ (foldr patt_imp g₂ l) using i ->
  Γ ⊢ (foldr patt_imp g₁ l) using i.
Proof.
  intros wfg₁ wfg₂ wfl H1 H2.
  eapply MP.
  2: eapply pf_iff_proj2.
  4: apply prf_local_goals_equiv_impl_full_equiv_meta.
  7: apply H1.
  1: exact H2.
  all: wf_auto2.
Defined.

Lemma prf_equiv_congruence_iter {Σ : Signature} (Γ : Theory) (p q : Pattern) (C : PatternCtx) l
  (i : ProofInfo)
  (pile : ProofInfoLe
  (pi_Generic
    (ExGen := list_to_set (evar_fresh_seq (free_evars (pcPattern C) ∪ free_evars p ∪ free_evars q ∪ {[pcEvar C]}) (maximal_exists_depth_of_evar_in_pattern (pcEvar C) (pcPattern C))),
      SVSubst := list_to_set (svar_fresh_seq (free_svars (pcPattern C) ∪ free_svars p ∪ free_svars q) (maximal_mu_depth_of_evar_in_pattern (pcEvar C) (pcPattern C))),
      KT := if decide (0 = (maximal_mu_depth_of_evar_in_pattern (pcEvar C) (pcPattern C))) is left _ then false else true)
    )
    i
  ):
  PC_wf C ->
  wf l ->
  Γ ⊢ p <---> q using i ->
  Γ ⊢ (foldr patt_imp (emplace C p) l) <---> (foldr patt_imp (emplace C q) l) using i.
Proof.
  intros wfC wfl Himp.
  induction l; simpl in *.
  - apply prf_equiv_congruence; assumption.
  - pose proof (wfal := wfl).
    unfold wf in wfl. simpl in wfl. apply andb_prop in wfl as [wfa wfl].
    specialize (IHl wfl).
    pose proof (Hwf1 := proved_impl_wf _ _ (proj1_sig IHl)).
    pose proof (Hwf2 := proved_impl_wf _ _ (proj1_sig Himp)).
    assert (well_formed (emplace C p)).
    {
      unfold emplace.
      wf_auto2.
    }
    assert (well_formed (emplace C q)).
    {
      unfold emplace.
      wf_auto2.
    }
    toMyGoal.
    { unfold emplace. wf_auto2. }
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

Lemma MyGoal_rewriteIff {Σ : Signature} (Γ : Theory) (p q : Pattern) (C : PatternCtx) l (i : ProofInfo):
  Γ ⊢ p <---> q using i ->
  @mkMyGoal Σ Γ l (emplace C q) i ->
  (ProofInfoLe
  (pi_Generic
     (ExGen := list_to_set
                 (evar_fresh_seq
                    (free_evars (pcPattern C) ∪ free_evars p ∪ free_evars q
                     ∪ {[pcEvar C]})
                    (maximal_exists_depth_of_evar_in_pattern 
                       (pcEvar C) (pcPattern C))),
      SVSubst := list_to_set
                   (svar_fresh_seq
                      (free_svars (pcPattern C) ∪ free_svars p
                       ∪ free_svars q)
                      (maximal_mu_depth_of_evar_in_pattern 
                         (pcEvar C) (pcPattern C))),
      KT := (if
              decide
                (0 =
                 maximal_mu_depth_of_evar_in_pattern (pcEvar C) (pcPattern C))
             is left _
             then false
             else true))) i) ->
  @mkMyGoal Σ Γ l (emplace C p) i.
Proof.
  intros Hpiffq H pile.
  unfold of_MyGoal in *. simpl in *.
  intros wfcp wfl.
  feed specialize H.
  { abstract (
      pose proof (Hwfiff := proved_impl_wf _ _ (proj1_sig Hpiffq));
      unfold emplace;
      apply well_formed_free_evar_subst_0;[wf_auto2|];
      fold (PC_wf C);
      eapply wf_emplaced_impl_wf_context;
      apply wfcp
    ).
  }
  { exact wfl. }

  eapply MP.
  2: apply pf_iff_proj2.
  2: abstract (wf_auto2).
  3: apply prf_equiv_congruence_iter.
  3: exact pile.
  5: apply Hpiffq.
  1: apply H.
  3: exact wfl.
  2: eapply wf_emplaced_impl_wf_context;
     apply wfcp.
  pose proof (@proved_impl_wf _ _ _ (proj1_sig H)).
  wf_auto2.
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
      | [ |- context ctx [free_evar_subst ?p ?q star] ]
        =>
          progress rewrite -> (@free_evar_subst_no_occurrence _ star p q) by (
            apply count_evar_occurrences_0;
            subst star;
            eapply evar_is_fresh_in_richer';
            [|apply set_evar_fresh_is_fresh'];
            simpl; clear; set_solver
          )
      end.

Local Ltac reduce_free_evar_subst_2 star :=
  (* unfold free_evar_subst; *)
  repeat (reduce_free_evar_subst_step_2 star).

Local Tactic Notation "solve_fresh_contradictions_2'" constr(star) constr(x) constr(h) :=
  let hcontra := fresh "Hcontra" in
  assert (hcontra: x <> star) by (subst star; unfold fresh_evar,evar_fresh_s; try clear h; simpl; solve_fresh_neq);
  rewrite -> h in hcontra;
  contradiction.

Local Ltac solve_fresh_contradictions_2 star :=
  unfold fresh_evar; simpl;
  match goal with
  | h: ?x = star |- _ =>
    let hprime := fresh "hprime" in
    pose proof (hprime := eq_sym h);
    solve_fresh_contradictions_2' star x hprime
  | h: star = ?x |- _
    => solve_fresh_contradictions_2' star x h
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
  (* unfold free_evar_subst; *)
  simpl;
  repeat break_match_goal;
  clear_obvious_equalities_2; try contradiction;
  try (solve_fresh_contradictions_2 star);
  (* repeat (rewrite nest_ex_aux_0); *)
  reduce_free_evar_subst_2 star.

(* Returns [n]th matching logic context [C] (of type [PatternCtx]) such that
   [emplace C a = phi].
 *)

 
 Ltac simplify_pile_side_condition_helper star :=
  subst star;
  unfold fresh_evar,evar_fresh_s;
  eapply evar_is_fresh_in_richer';
  [|apply set_evar_fresh_is_fresh'];
  clear; simpl; set_solver.

 Ltac simplify_pile_side_condition star :=
  cbn;
  simplify_emplace_2 star;
  repeat (rewrite (mmdoeip_notin, medoeip_notin);
  [(simplify_pile_side_condition_helper star)|]);
  simpl;
  repeat (
    lazymatch goal with
    | [H: context [maximal_mu_depth_of_evar_in_pattern' _ _ _] |- _ ]
      => rewrite mmdoeip_notin in H;
         [(simplify_pile_side_condition_helper star)|]
    | [H: context [maximal_exists_depth_of_evar_in_pattern' _ _ _] |- _ ]
      => rewrite medoeip_notin in H;
         [(simplify_pile_side_condition_helper star)|]
    end
  );
  simpl in *;
  try lia.

Ltac2 Type HeatResult := {
  star_ident : ident ;
  star_eq : ident ;
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
         let star_eq := Fresh.in_goal ident:(star_eq) in
         (*set ($star_ident := $fr);*)
         remember $fr as $star_ident eqn:star_eq;
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
         { star_ident := star_ident; star_eq := star_eq; pc := pc; ctx := ctx; ctx_pat := ctxpat; equality := heq1 }
         )
    end
.

Ltac2 mgRewrite (hiff : constr) (atn : int) :=
  lazy_match! Constr.type hiff with
  | _ ⊢ (?a <---> ?a') using _
    =>
    lazy_match! goal with
    | [ |- of_MyGoal (@mkMyGoal ?sgm ?g ?l ?p ?i)]
      => let hr : HeatResult := heat atn a p in
         if ml_debug_rewrite then
           Message.print (Message.of_constr (hr.(ctx_pat)))
         else () ;
         let heq := Control.hyp (hr.(equality)) in
         let pc := (hr.(pc)) in
         eapply (@cast_proof_mg_goal _ $g) >
           [ rewrite $heq; reflexivity | ()];
         Std.clear [hr.(equality)];
         apply (@MyGoal_rewriteIff $sgm $g _ _ $pc $l $i $hiff)  >
         [
         (lazy_match! goal with
         | [ |- of_MyGoal (@mkMyGoal ?sgm ?g ?l ?p _)]
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
             Std.clear [heq2 ; (hr.(star_ident)); (hr.(star_eq))]
         end)
         | (ltac1:(star |- simplify_pile_side_condition star) (Ltac1.of_ident (hr.(star_ident))))
         ]
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

Lemma pf_iff_equiv_sym_nowf {Σ : Signature} Γ A B i :
  Γ ⊢ (A <---> B) using i ->
  Γ ⊢ (B <---> A) using i.
Proof.
  intros H.
  pose proof (wf := proved_impl_wf _ _ (proj1_sig H)).
  assert (well_formed A) by wf_auto2.
  assert (well_formed B) by wf_auto2.
  apply pf_iff_equiv_sym; assumption.
Defined.

Tactic Notation "mgRewrite" "->" constr(Hiff) "at" constr(atn) :=
  mgRewrite Hiff at atn.

Tactic Notation "mgRewrite" "<-" constr(Hiff) "at" constr(atn) :=
  mgRewrite (@pf_iff_equiv_sym_nowf _ _ _ _ _ Hiff) at atn.

(* Ltac2 Set ml_debug_rewrite := true.*)
Local Example ex_prf_rewrite_equiv_2 {Σ : Signature} Γ a a' b x i
  (pile : ProofInfoLe BasicReasoning i):
  well_formed a ->
  well_formed a' ->
  well_formed b ->
  Γ ⊢ a <---> a' using i ->
  Γ ⊢ (a $ a $ b $ a ---> (patt_free_evar x)) <---> (a $ a' $ b $ a' ---> (patt_free_evar x)) using i.
Proof.
  intros wfa wfa' wfb Hiff.
  toMyGoal.
  { abstract(wf_auto2). }
  mgRewrite Hiff at 2.
  2: { apply pile. }
  mgRewrite <- Hiff at 3.
  2: { apply pile. }
  fromMyGoal.
  usePropositionalReasoning.
  apply pf_iff_equiv_refl. abstract(wf_auto2).
Defined.

Lemma top_holds {Σ : Signature} Γ:
  Γ ⊢ Top using PropositionalReasoning.
Proof.
  apply false_implies_everything.
  { wf_auto2. }
Defined.

Lemma phi_iff_phi_top {Σ : Signature} Γ ϕ :
  well_formed ϕ ->
  Γ ⊢ ϕ <---> (ϕ <---> Top)
  using PropositionalReasoning.
Proof.
  intros wfϕ.
  toMyGoal.
  { wf_auto2. }
  mgSplitAnd; mgIntro.
  - mgSplitAnd.
    + mgIntro. mgClear 0. mgClear 0.
      fromMyGoal.
      apply top_holds. (* TODO: we need something like [mgExactMeta top_holds] *)
    + fromMyGoal.
      apply P1; wf_auto2.
  - mgDestructAnd 0.
    mgApply 1.
    mgClear 0.
    mgClear 0.
    fromMyGoal.
    apply top_holds.
Defined.

Lemma not_phi_iff_phi_bott {Σ : Signature} Γ ϕ :
  well_formed ϕ ->
  Γ ⊢ (! ϕ ) <---> (ϕ <---> ⊥)
  using PropositionalReasoning.
Proof.
  intros wfϕ.
  toMyGoal.
  { wf_auto2. }
  mgSplitAnd; mgIntro.
  - mgSplitAnd.
    + mgExactn 0.
    + mgClear 0. fromMyGoal.
      apply false_implies_everything.
      { wf_auto2. }
  - mgDestructAnd 0.
    mgExactn 0.
Defined.

Lemma not_not_iff {Σ : Signature} (Γ : Theory) (A : Pattern) :
  well_formed A ->
  Γ ⊢ A <---> ! ! A
  using PropositionalReasoning.
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
  Γ ⊢ ((ex, ϕ₁) and ϕ₂) ---> (ex, (ϕ₁ and ϕ₂))
  using (pi_Generic (ExGen := {[fresh_evar (ϕ₂ ---> ex , (ϕ₁ and ϕ₂))]}, SVSubst := ∅, KT := false)).
Proof.
  intros wfϕ₁ wfϕ₂.
  toMyGoal.
  { wf_auto2. }
  mgIntro. mgDestructAnd 0.
  fromMyGoal.

  remember (fresh_evar (ϕ₂ ---> (ex, (ϕ₁ and ϕ₂)))) as x.
  apply strip_exists_quantify_l with (x0 := x).
  { subst x. eapply evar_is_fresh_in_richer'.
    2: { apply set_evar_fresh_is_fresh'. }
    simpl. clear. set_solver.
  }
  { wf_auto2. }
  apply Ex_gen.
  { apply pile_refl. }
  { wf_auto2. }
  
  apply lhs_to_and.
  { wf_auto2. }
  { wf_auto2. }
  { wf_auto2. }

  eapply cast_proof'.
  {
    replace (evar_open 0 x ϕ₁ and ϕ₂)
            with (evar_open 0 x (ϕ₁ and ϕ₂)).
    2: {
      unfold evar_open. simpl_bevar_subst.
      rewrite [bevar_subst ϕ₂ _ _]bevar_subst_not_occur.
      {
        wf_auto2.
      }
      reflexivity.
    }
    reflexivity.
  }
  useBasicReasoning.
  apply Ex_quan.
  wf_auto2.
Defined.

(* prenex-exists-and-right *)
Lemma prenex_exists_and_2 {Σ : Signature} (Γ : Theory) ϕ₁ ϕ₂:
  well_formed (ex, ϕ₁) ->
  well_formed ϕ₂ ->
  Γ ⊢ (ex, (ϕ₁ and ϕ₂)) ---> ((ex, ϕ₁) and ϕ₂)
  using (pi_Generic (ExGen := {[fresh_evar ((ϕ₁ and ϕ₂))]}, SVSubst := ∅, KT := false)).
Proof.
  intros wfϕ₁ wfϕ₂.
  toMyGoal.
  { wf_auto2. }
  mgIntro.
  mgSplitAnd.
  - fromMyGoal.
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
    { apply pile_refl. }

    unfold evar_open. simpl_bevar_subst.
    rewrite [bevar_subst ϕ₂ _ _]bevar_subst_not_occur.
    {
      wf_auto2.
    }
    toMyGoal.
    { wf_auto2. }
    mgIntro. mgDestructAnd 0. mgExactn 0.
  - fromMyGoal.
    remember (fresh_evar (ϕ₁ and ϕ₂)) as x.
    eapply cast_proof'.
    {
      rewrite -[ϕ₁ and ϕ₂](@evar_quantify_evar_open Σ x 0).
      { subst x. apply set_evar_fresh_is_fresh. }
      { cbn. split_and!; auto. wf_auto. wf_auto2. }
      reflexivity.
    }
    apply Ex_gen.
    { apply pile_refl. }
    { eapply evar_is_fresh_in_richer. 2: { subst x. apply set_evar_fresh_is_fresh'. }
      simpl. clear. set_solver.
    }

    unfold evar_open.
    simpl_bevar_subst.
    rewrite [bevar_subst ϕ₂ _ _]bevar_subst_not_occur.
    {
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
  Γ ⊢ (ex, (ϕ₁ and ϕ₂)) <---> ((ex, ϕ₁) and ϕ₂)
  using (pi_Generic (ExGen := {[fresh_evar ((ϕ₁ and ϕ₂))]}, SVSubst := ∅, KT := false)).
Proof.
  intros wfϕ₁ wfϕ₂.
  apply conj_intro_meta.
  { wf_auto2. }
  { wf_auto2. }
  - apply prenex_exists_and_2; assumption.
  - (* TODO we need a tactic to automate this change *)
    replace (fresh_evar (ϕ₁ and ϕ₂))
    with (fresh_evar (ϕ₂ ---> ex , (ϕ₁ and ϕ₂))).
    2: { cbn. unfold fresh_evar. apply f_equal. simpl. set_solver. }
   apply prenex_exists_and_1; assumption.
Defined.

Lemma patt_and_comm {Σ : Signature} Γ p q:
  well_formed p ->
  well_formed q ->
  Γ ⊢ (p and q) <---> (q and p)
  using PropositionalReasoning.
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
  Γ ⊢ (! ϕ₁ ---> ! ϕ₂) ---> (ϕ₂ ---> ϕ₁)
  using PropositionalReasoning.
Proof.
  intros wfϕ₁ wfϕ₂.
  toMyGoal.
  { wf_auto2. }
  mgIntro. mgIntro.
  unfold patt_not.
  mgAssert (((ϕ₁ ---> ⊥) ---> ⊥)).
  { wf_auto2. }
  { mgIntro.
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
  Γ ⊢ (foldr patt_and x xs ---> g) ---> (foldr patt_imp g (x :: xs))
  using PropositionalReasoning.
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

Lemma lhs_and_to_imp_meta {Σ : Signature} Γ (g x : Pattern) (xs : list Pattern) i:
  well_formed g ->
  well_formed x ->
  wf xs ->
  Γ ⊢ (foldr patt_and x xs ---> g) using i ->
  Γ ⊢ (foldr patt_imp g (x :: xs)) using i.
Proof.
  intros wfg wfx wfxs H.
  eapply MP.
  2: { usePropositionalReasoning. apply lhs_and_to_imp; assumption. }
  exact H.
Defined.



Lemma lhs_and_to_imp_r {Σ : Signature} Γ (g x : Pattern) (xs : list Pattern) i :
  well_formed g ->
  well_formed x ->
  wf xs ->
  forall (r : ImpReshapeS g (x::xs)),
     Γ ⊢ ((foldr (patt_and) x xs) ---> g) using i ->
     Γ ⊢ untagPattern (irs_flattened r) using i .
Proof.
  intros wfg wfx wfxs r H.
  eapply cast_proof'.
  { rewrite irs_pf; reflexivity. }
  clear r.
  apply lhs_and_to_imp_meta; assumption.
Defined.


Local Example ex_match {Σ : Signature} Γ a b c d:
  well_formed a ->
  well_formed b ->
  well_formed c ->
  well_formed d ->
  Γ ⊢ a ---> (b ---> (c ---> d)) using PropositionalReasoning.
Proof.
  intros wfa wfb wfc wfd.
  apply lhs_and_to_imp_r.
Abort.

Lemma forall_gen {Σ : Signature} Γ ϕ₁ ϕ₂ x (i : ProofInfo):
  evar_is_fresh_in x ϕ₁ ->
  ProofInfoLe (pi_Generic (ExGen := {[x]}, SVSubst := ∅, KT := false)) i ->
  Γ ⊢ ϕ₁ ---> ϕ₂ using i ->
  Γ ⊢ ϕ₁ ---> all, (evar_quantify x 0 ϕ₂) using i.
Proof.
  intros Hfr pile Himp.
  pose proof (Hwf := proved_impl_wf _ _ (proj1_sig Himp)).
  pose proof (wfϕ₁ := well_formed_imp_proj1 Hwf).
  pose proof (wfϕ₂ := well_formed_imp_proj2 Hwf).
  toMyGoal.
  { wf_auto2. }
  mgIntro.
  mgApplyMeta (@usePropositionalReasoning Σ Γ _ _ (@not_not_intro Σ Γ ϕ₁ ltac:(wf_auto2))) in 0.
  fromMyGoal.
  apply modus_tollens.

  eapply cast_proof'.
  {
    replace (! evar_quantify x 0 ϕ₂)
            with (evar_quantify x 0 (! ϕ₂))
                 by reflexivity.
    reflexivity.
  }
  apply Ex_gen.
  { exact pile. }
  { simpl. unfold evar_is_fresh_in in Hfr. clear -Hfr. set_solver. }
  apply modus_tollens; assumption.
Defined.

Lemma pile_evs_svs_kt_back {Σ : Signature} evs1 evs2 svs1 svs2 kt1 kt2:
ProofInfoLe
  (pi_Generic (ExGen := evs1, SVSubst := svs1, KT := kt1))
  (pi_Generic (ExGen := evs2, SVSubst := svs2, KT := kt2)) ->
  evs1 ⊆ evs2 /\ svs1 ⊆ svs2 /\ kt1 ==> kt2.
Proof.
  intros pile.
  repeat split.
  {
    destruct pile as [pile].
    rewrite elem_of_subseteq.
    intros x Hx.
    remember (fresh_evar (patt_free_evar x)) as y.
    pose (pf1 := @A_impl_A Σ ∅ (patt_free_evar y) ltac:(wf_auto2)).
    pose (pf2 := @ProofSystem.Ex_gen Σ ∅ (patt_free_evar y) (patt_free_evar y) x ltac:(wf_auto2) ltac:(wf_auto2) (proj1_sig pf1) ltac:(simpl; rewrite elem_of_singleton; solve_fresh_neq)).
    specialize (pile ∅ _ pf2).
    feed specialize pile.
    {
      constructor.
      { exact I. }
      { simpl. clear -Hx. set_solver. }
      { simpl. clear. set_solver. }
      { simpl. reflexivity. }
    }
    destruct pile as [Hm1 Hm2 Hm3 Hm4].
    simpl in *.
    clear -Hm2.
    set_solver.
  }
  {
    destruct pile as [pile].
    rewrite elem_of_subseteq.
    intros X HX.
    pose (pf1 := @A_impl_A Σ ∅ (patt_free_svar X) ltac:(wf_auto2)).
    pose (pf2 := @ProofSystem.Svar_subst Σ ∅ (patt_free_svar X ---> patt_free_svar X) patt_bott X ltac:(wf_auto2) ltac:(wf_auto2) (proj1_sig pf1)).
    specialize (pile ∅ _ pf2).
    feed specialize pile.
    {
      constructor; simpl.
      { exact I. }
      { clear. set_solver. }
      { clear -HX. set_solver. }
      { reflexivity. }
    }
    destruct pile as [Hp1 Hp2 Hp3 Hp4].
    simpl in *.
    clear -Hp3.
    set_solver.
  }
  {
    destruct pile as [pile].
    pose (pf1 := @A_impl_A Σ ∅ patt_bott ltac:(wf_auto2)).
    pose (pf2 := @ProofSystem.Knaster_tarski Σ ∅ (patt_bound_svar 0) patt_bott ltac:(wf_auto2) (proj1_sig pf1)).
    destruct kt1.
    2: { simpl. reflexivity. }
    specialize (pile ∅ _ pf2).
    feed specialize pile.
    {
      constructor; simpl.
      { exact I. }
      { clear. set_solver. }
      { clear. set_solver. }
      { reflexivity. }
    }
    destruct pile as [Hp1 Hp2 Hp3 Hp4].
    simpl in Hp4.
    rewrite Hp4.
    reflexivity.
  }
Qed.

Lemma useGenericReasoning {Σ : Signature} (Γ : Theory) (ϕ : Pattern) evs svs kt i:
  (ProofInfoLe (pi_Generic (ExGen := evs, SVSubst := svs, KT := kt)) i) ->
  Γ ⊢ ϕ using (pi_Generic (ExGen := evs, SVSubst := svs, KT := kt)) ->
  Γ ⊢ ϕ using i.
Proof.
  intros pile [pf Hpf].
  destruct i.
  {
    exfalso.
    eapply not_generic_in_prop.
    apply pile.
  }
  exists pf.
  destruct Hpf as [Hpf1 Hpf2 Hpf3 Hpf4].
  simpl in *.
  destruct gpi.
  pose proof (Htmp := @pile_evs_svs_kt_back Σ).
  specialize (Htmp evs pi_generalized_evars0 svs pi_substituted_svars0 kt pi_uses_kt0 pile).
  destruct Htmp as [Hevs [Hsvs Hkt] ].
  constructor; simpl.
  { exact I. }
  { clear -Hpf2 Hevs. set_solver. }
  { clear -Hpf3 Hsvs. set_solver. }
  { unfold implb in *. repeat case_match; try reflexivity; try assumption. inversion Hpf4. }
Qed.


Lemma mgUseGenericReasoning
{Σ : Signature} (Γ : Theory) (l : list Pattern) (g : Pattern) (i : ProofInfo) evs svs kt :
(ProofInfoLe (pi_Generic (ExGen := evs, SVSubst := svs, KT := kt)) i) ->
@mkMyGoal Σ Γ l g ((pi_Generic (ExGen := evs, SVSubst := svs, KT := kt))) ->
@mkMyGoal Σ Γ l g i.
Proof.
intros Hpile H wf1 wf2.
specialize (H wf1 wf2).
eapply useGenericReasoning.
2: exact H.
apply Hpile.
Defined.

Lemma forall_variable_substitution' {Σ : Signature} Γ ϕ x (i : ProofInfo):
  well_formed ϕ ->
  (ProofInfoLe (pi_Generic (ExGen := {[x]}, SVSubst := ∅, KT := false)) i) ->
  Γ ⊢ (all, evar_quantify x 0 ϕ) ---> ϕ using i.
Proof.
  intros wfϕ pile.
  destruct i.
  {
    exfalso.
    eapply not_generic_in_prop.
    apply pile.
  }
  pose proof (Htmp := @forall_variable_substitution Σ Γ ϕ x wfϕ).
  eapply useGenericReasoning. apply pile. apply Htmp.
Defined.

Lemma forall_elim {Σ : Signature} Γ ϕ x (i : ProofInfo):
  well_formed (ex, ϕ) ->
  evar_is_fresh_in x ϕ ->
  ProofInfoLe (pi_Generic (ExGen := {[x]}, SVSubst := ∅, KT := false)) i ->
  Γ ⊢ (all, ϕ) using i ->
  Γ ⊢ (evar_open 0 x ϕ) using i.
Proof.
  intros wfϕ frϕ pile H.
  destruct i.
  {
    exfalso.
    eapply not_generic_in_prop.
    apply pile.
  }
  destruct gpi.
  eapply MP.
  2: eapply forall_variable_substitution'.
  2: wf_auto2.
  2: apply pile.
  eapply cast_proof'.
  {
    rewrite evar_quantify_evar_open.
    { apply frϕ. }
    { wf_auto2. }
    reflexivity.
  }
  apply H.
Defined.

Lemma prenex_forall_imp {Σ : Signature} Γ ϕ₁ ϕ₂ i:
  well_formed (ex, ϕ₁) ->
  well_formed ϕ₂ ->
  ProofInfoLe (pi_Generic (ExGen := {[fresh_evar (ϕ₁ ---> ϕ₂)]}, SVSubst := ∅, KT := false)) i ->
  Γ ⊢ (all, (ϕ₁ ---> ϕ₂)) using i ->
  Γ ⊢ (ex, ϕ₁) ---> (ϕ₂) using i.
Proof.
  intros wfϕ₁ wfϕ₂ pile H.
  remember (fresh_evar (ϕ₁ ---> ϕ₂)) as x.
  apply (@strip_exists_quantify_l Σ Γ x).
  { subst x.
    eapply evar_is_fresh_in_richer'.
    2: { apply set_evar_fresh_is_fresh'. }
    simpl. set_solver.
  }
  { wf_auto2. }
  apply Ex_gen.
  { apply pile. }
  1: {
    subst x.
    eapply evar_is_fresh_in_richer'.
    2: { apply set_evar_fresh_is_fresh'. }
    simpl. set_solver.
  }

  eapply cast_proof'.
  {
    rewrite -[HERE in evar_open _ _ _ ---> HERE](@evar_open_not_occur Σ 0 x ϕ₂).
    {
      wf_auto2.
    }
    reflexivity.
  }
  eapply forall_elim with (x0 := x) in H.
  4: { apply pile. }
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

Lemma Ex_gen_lifted {Σ : Signature} (Γ : Theory) (ϕ₁ : Pattern) (l : list Pattern) (g : Pattern) (x : evar)
  (i : ProofInfo) :
  evar_is_fresh_in x g ->
  evar_is_fresh_in_list x l ->
  ProofInfoLe (pi_Generic (ExGen := {[x]}, SVSubst := ∅, KT := false)) i ->
  bevar_occur ϕ₁ 0 = false ->
  @mkMyGoal Σ Γ (ϕ₁::l) g i -> 
 @mkMyGoal Σ Γ ((exists_quantify x ϕ₁)::l) g i.
Proof.
  intros xfrg xfrl pile Hno0 H.
  mgExtractWF H1 H2.
  fromMyGoal.
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
  { apply pile. }
  2: { assumption. }
  simpl.
  apply evar_fresh_in_foldr.
  split; assumption.
Defined.

(* Weakening under existential *)
Local Example ex_exists {Σ : Signature} Γ ϕ₁ ϕ₂ ϕ₃ i:
  well_formed (ex, ϕ₁) ->
  well_formed (ex, ϕ₂) ->
  well_formed ϕ₃ ->
  ProofInfoLe (pi_Generic (ExGen := {[(evar_fresh (elements (free_evars ϕ₁ ∪ free_evars ϕ₂ ∪ free_evars (ex, ϕ₃))))]}, SVSubst := ∅, KT := false)) i ->
  Γ ⊢ (all, (ϕ₁ and ϕ₃ ---> ϕ₂)) using i ->
  Γ ⊢ (ex, ϕ₁) ---> ϕ₃ ---> (ex, ϕ₂) using i.
Proof.
  intros wfϕ₁ wfϕ₂ wfϕ₃ pile H.
  toMyGoal.
  { wf_auto2. }
  mgIntro.
  remember (evar_fresh (elements (free_evars ϕ₁ ∪ free_evars ϕ₂ ∪ free_evars (ex, ϕ₃)))) as x.
  rewrite -[ϕ₁](@evar_quantify_evar_open Σ x 0).
  { subst x.
    eapply evar_is_fresh_in_richer'. 2: apply set_evar_fresh_is_fresh'. clear. set_solver.
  }
  wf_auto2.
  mgIntro.
  apply Ex_gen_lifted.
  { subst x. eapply evar_is_fresh_in_richer'. 2: apply set_evar_fresh_is_fresh'. clear. set_solver. }
  { constructor. 2: apply Forall_nil; exact I.
    subst x.
    eapply evar_is_fresh_in_richer'. 2: apply set_evar_fresh_is_fresh'. clear. set_solver.
  }
  { wf_auto. }

Abort.

(* This is an example and belongs to the end of this file.
   Its only purpose is only to show as many tactics as possible.\
 *)
   Lemma ex_and_of_equiv_is_equiv_2 {Σ : Signature} Γ p q p' q' i:
    well_formed p ->
    well_formed q ->
    well_formed p' ->
    well_formed q' ->
    Γ ⊢ (p <---> p') using i ->
    Γ ⊢ (q <---> q') using i ->
    Γ ⊢ ((p and q) <---> (p' and q')) using i.
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
        fromMyGoal.
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

#[local]
Ltac tryExact l idx :=
  match l with
    | nil => idtac
    | (?a :: ?m) => try mgExactn idx; tryExact m (idx + 1)
  end.

#[global]
Ltac mgAssumption :=
  match goal with
    | [ |- @of_MyGoal ?Sgm (@mkMyGoal ?Sgm ?Ctx ?l ?g ?i) ] 
      =>
        tryExact l 0
  end.

Section FOL_helpers.

  Context {Σ : Signature}.

  Lemma MyGoal_revert (Γ : Theory) (l : list Pattern) (x g : Pattern) i :
      @mkMyGoal Σ Γ l (x ---> g) i ->
      @mkMyGoal Σ Γ (l ++ [x]) g i.
    Proof.
      intros H.
      unfold of_MyGoal in H. simpl in H.
      unfold of_MyGoal. simpl. intros wfxig wfl.

      feed specialize H.
      {
        abstract (
            apply wfapp_proj_2 in wfl;
            unfold wf in wfl;
            simpl in wfl;
            rewrite andbT in wfl;
            wf_auto2
          ).
      }
      {
        abstract (apply wfapp_proj_1 in wfl; exact wfl).
      }

      eapply cast_proof'.
      { rewrite foldr_app. simpl. reflexivity. }
      exact H.
    Defined.

End FOL_helpers.

#[global]
  Ltac mgRevert :=
    match goal with
    | |- @of_MyGoal ?Sgm (@mkMyGoal ?Sgm ?Ctx ?l ?g ?i)
      => eapply cast_proof_mg_hyps;
         [(rewrite -[l](take_drop (length l - 1)); rewrite [take _ _]/=; rewrite [drop _ _]/=; reflexivity)|];
         apply MyGoal_revert
    end.

#[local]
  Lemma ex_or_of_equiv_is_equiv_2 {Σ : Signature} Γ p q p' q' i:
    well_formed p ->
    well_formed q ->
    well_formed p' ->
    well_formed q' ->
    Γ ⊢ (p <---> p') using i ->
    Γ ⊢ (q <---> q') using i ->
    Γ ⊢ ((p or q) <---> (p' or q')) using i.
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


Lemma impl_eq_or {Σ : Signature} Γ a b:
  well_formed a ->
  well_formed b ->
  Γ ⊢( (a ---> b) <---> ((! a) or b) )
  using PropositionalReasoning.
Proof.
  intros wfa wfb.
  toMyGoal.
  { wf_auto2. }
  repeat mgIntro.
  mgDestructOr 0.
  - mgApply 0. mgIntro. mgClear 0. mgIntro.
    mgApplyMeta (@not_not_elim _ _ _ _) in 1.
    mgApply 0. mgAssumption.
  - mgApply 0. mgIntro. mgClear 0. mgIntro.
    mgDestructOr 0.
    + mgApplyMeta (@false_implies_everything _ _ _ _).
      mgApply 0. mgAssumption.
    + mgAssumption.
  Unshelve. all: assumption.
Qed.


Lemma nimpl_eq_and {Σ : Signature} Γ a b:
  well_formed a ->
  well_formed b ->
  Γ ⊢( ! (a ---> b) <---> (a and !b) )
  using PropositionalReasoning.
Proof.
  intros wfa wfb.
  toMyGoal.
  { wf_auto2. }
  repeat mgIntro.
  mgDestructOr 0.
  - mgApply 0. repeat mgIntro.
    mgApply 1. mgIntro.
    mgDestructOr 2.
    + mgApplyMeta (false_implies_everything _ _).
      mgApply 2. mgAssumption.
    + mgApplyMeta (@not_not_elim _ _ _ _) in 2.
      mgAssumption.
  - mgApply 0. repeat mgIntro.
    mgDestructAnd 1. mgApply 2. mgApply 3.
    mgAssumption.
  Unshelve. all: assumption.
Qed.


Lemma deMorgan_nand {Σ : Signature} Γ a b:
    well_formed a ->
    well_formed b ->
    Γ ⊢ ( !(a and b) <---> (!a or !b) )
    using PropositionalReasoning.
  Proof.
    intros wfa wfb.
    toMyGoal.
    { wf_auto2. }
    repeat mgIntro.
    mgDestructOr 0.
    - mgRevert. mgApplyMeta (@not_not_intro _ _ _ _). repeat mgIntro.
      mgApplyMeta (@not_not_elim _ _ _ _) in 1.
      mgApply 0. mgIntro.
      mgDestructOr 3.
      all: mgApply 3; mgAssumption.
    - mgRevert. mgApplyMeta (@not_not_intro _ _ _ _). repeat mgIntro.
      mgDestructAnd 1.
      mgDestructOr 0.
      all: mgApply 0; mgAssumption.
    Unshelve. all: auto.
  Qed.

Lemma deMorgan_nor {Σ : Signature} Γ a b:
    well_formed a ->
    well_formed b ->
    Γ ⊢ ( !(a or b) <---> (!a and !b))
    using PropositionalReasoning.
  Proof.
    intros wfa wfb.
    toMyGoal.
    { wf_auto2. }
    repeat mgIntro.
    mgDestructOr 0.
    - mgRevert. mgApplyMeta (@not_not_intro _ _ _ _). repeat mgIntro.
      mgApply 0.
      mgDestructOr 1.
      + mgApplyMeta (@not_not_elim _ _ _ _) in 1.
        mgLeft. mgAssumption.
      + mgApplyMeta (@not_not_elim _ _ _ _) in 1.
        mgRight. mgAssumption.
    - mgRevert. mgApplyMeta (@not_not_intro _ _ _ _). repeat mgIntro.
      mgDestructAnd 0.
      mgDestructOr 2.
      + mgApply 0. mgAssumption.
      + mgApply 1. mgAssumption.
    Unshelve. all: wf_auto2.
  Qed.

#[local]
Lemma not_not_eq {Σ : Signature} (Γ : Theory) (a : Pattern) :
  well_formed a ->
  Γ ⊢ (!(!a) <---> a)
  using PropositionalReasoning.
Proof.
  intros wfa.
  toMyGoal.
  { wf_auto2. }
  mgIntro.
  mgDestructOr 0.
  - mgApply 0. mgIntro.
    mgApplyMeta (@not_not_elim _ _ _ _) in 1.
    mgAssumption.
  - unfold patt_not. mgApply 0. repeat mgIntro.
    mgApply 2. mgAssumption.
  Unshelve.
  all: assumption.
Defined.

Check @usePropositionalReasoning.
#[local]
Ltac convertToNNF_rewrite_pat Ctx p i :=
  lazymatch p with
    | (! ! ?x) =>
        let H' := fresh "H" in
        pose proof (@not_not_eq _ Ctx x ltac:(wf_auto2)) as H';
        apply (@usePropositionalReasoning _ _ _ i) in H';
        repeat (mgRewrite H' at 1);
        clear H';
        convertToNNF_rewrite_pat Ctx x i
    | patt_not (patt_and ?x ?y) =>
        let H' := fresh "H" in
        pose proof (@deMorgan_nand _ Ctx x y ltac:(wf_auto2) ltac:(wf_auto2)) as H';
        apply (@usePropositionalReasoning _ _ _ i) in H';
        repeat (mgRewrite H' at 1);
        clear H';
        convertToNNF_rewrite_pat Ctx (!x or !y) i
    | patt_not (patt_or ?x ?y) =>
        let H' := fresh "H" in
        pose proof (@deMorgan_nor _ Ctx x y ltac:(wf_auto2) ltac:(wf_auto2)) as H';
        apply (@usePropositionalReasoning _ _ _ i) in H';
        repeat (mgRewrite H' at 1);
        clear H';
        convertToNNF_rewrite_pat Ctx (!x and !y) i
    | patt_not (?x ---> ?y) =>
        let H' := fresh "H" in
        pose proof (@nimpl_eq_and _ Ctx x y ltac:(wf_auto2) ltac:(wf_auto2)) as H';
        apply (@usePropositionalReasoning _ _ _ i) in H';
        repeat (mgRewrite H' at 1);
        clear H';
        convertToNNF_rewrite_pat Ctx (x and !y) i
    | (?x ---> ?y) =>
        let H' := fresh "H" in
        pose proof (@impl_eq_or _ Ctx x y ltac:(wf_auto2) ltac:(wf_auto2)) as H';
        apply (@usePropositionalReasoning _ _ _ i) in H';
        repeat (mgRewrite H' at 1);
        clear H';
        convertToNNF_rewrite_pat Ctx (!x or y) i
    | patt_and ?x ?y => convertToNNF_rewrite_pat Ctx x i; convertToNNF_rewrite_pat Ctx y i
    | patt_or ?x ?y => convertToNNF_rewrite_pat Ctx x i; convertToNNF_rewrite_pat Ctx y i
    | _ => idtac
  end.

#[local]
Ltac toNNF := 
  repeat mgRevert;
  match goal with
    | [ |- @of_MyGoal ?Sgm (@mkMyGoal ?Sgm ?Ctx ?ll ?g ?i) ] 
      =>
        mgApplyMeta (@usePropositionalReasoning _ _ _ i (@not_not_elim Sgm Ctx g ltac:(wf_auto2)));
        convertToNNF_rewrite_pat Ctx (!g) i
  end.

#[local] Example test_toNNF {Σ : Signature} Γ a b :
  well_formed a ->
  well_formed b ->
  Γ ⊢ ( (b and (a or b) and !b and ( a or a) and a) ---> ⊥)
  using BasicReasoning.
Proof.
  intros wfa wfb.
  toMyGoal.
  { wf_auto2. }
  toNNF;[|try apply pile_refl].
Abort.

#[local]
Ltac rfindContradictionTo a ll k n:=
  match ll with
    | ((! a) :: ?m) =>
        mgApply n; mgExactn k
    | (?b :: ?m) => 
        let nn := eval compute in ( n + 1 ) in
         (rfindContradictionTo a m k nn)
    | _ => fail
  end.

#[local]
Ltac findContradiction l k:=
    match l with
       | (?a :: ?m) => 
             match goal with
                | [ |- @of_MyGoal ?Sgm (@mkMyGoal ?Sgm ?Ctx ?ll ?g ?i) ] 
                  =>
                     try rfindContradictionTo a ll k 0;
                     let kk := eval compute in ( k + 1 ) in
                     (findContradiction m kk)
             end
       | _ => fail
    end.

#[local]
Ltac findContradiction_start :=
  match goal with
    | [ |- @of_MyGoal ?Sgm (@mkMyGoal ?Sgm ?Ctx ?l ?g ?i) ] 
      =>
        match goal with
          | [ |- @of_MyGoal ?Sgm (@mkMyGoal ?Sgm ?Ctx ?l ?g ?i) ] 
            =>
              findContradiction l 0
        end
  end.

#[local]
Ltac breakHyps l n:=
  let nn := eval compute in ( n + 1)
  in
  (
    match l with
    | ((?x and ?y) :: ?m) => 
        mgDestructAnd n
    | ((?x or ?y) :: ?m) => 
        mgDestructOr n
    | (?x :: ?m)  =>
        breakHyps m nn
    end
  )
.
#[local]
Ltac mgTautoBreak := repeat match goal with
| [ |- @of_MyGoal ?Sgm (@mkMyGoal ?Sgm ?Ctx ?l ?g ?i) ] 
  =>
    lazymatch g with
      | (⊥) =>
              breakHyps l 0
      | _ => mgApplyMeta (@usePropositionalReasoning _ _ _ i (@false_implies_everything _ _ g _))
    end
end.

Ltac try_solve_pile fallthrough :=
  lazymatch goal with
  | [ |- ProofInfoLe _ _] => try apply pile_refl; fallthrough
  | _ => idtac
  end.

#[global]
Ltac mgTauto :=
  unshelve(
    try (
      toNNF; (try_solve_pile shelve);
      repeat mgIntro;
      mgTautoBreak;
      findContradiction_start
    )
  )
.

#[local]
Lemma conj_right {Σ : Signature} Γ a b:
  well_formed a ->
  well_formed b ->
  Γ ⊢ ( (b and (a or b) and !b and ( a or a) and a) ---> ⊥)
  (* If we use mgTauto or mgRewrite, we cannot use the PropositionalReasoning annotation. *)
  using BasicReasoning.
Proof.
  intros wfa wfb.
  toMyGoal.
  { wf_auto2. }
  mgTauto.
Defined.

#[local]
Lemma condtradict_taut_2 {Σ : Signature} Γ a b:
  well_formed a ->
  well_formed b ->
  Γ ⊢ (a ---> ((! a) ---> b))
  using BasicReasoning.
Proof.
  intros wfa wfb.
  toMyGoal.
  { wf_auto2. }
  mgTauto.
Qed.

#[local]
Lemma taut {Σ : Signature} Γ a b c:
  well_formed a ->
  well_formed b ->
  well_formed c ->
  Γ ⊢ ((a ---> b) ---> ((b ---> c) ---> ((a or b)---> c)))
  using BasicReasoning.
Proof.
  intros wfa wfb wfc.
  toMyGoal.
  { wf_auto2. }
  mgTauto. (* Slow *)
Qed.

#[local]
Lemma condtradict_taut_1 {Σ : Signature} Γ a:
  well_formed a ->
  Γ ⊢ !(a and !a)
  using BasicReasoning.
Proof.
  intros wfa.
  toMyGoal.
  { wf_auto2. }
  mgTauto.
Qed.

#[local]
Lemma notnot_taut_1 {Σ : Signature} Γ a:
  well_formed a ->
  Γ ⊢ (! ! a ---> a)
  using BasicReasoning.
Proof.
  intros wfa.
  toMyGoal.
  { wf_auto2. }
  mgTauto.
Qed.

#[local]
Lemma Peirce_taut {Σ : Signature} Γ a b:
  well_formed a ->
  well_formed b ->
  Γ ⊢ ((((a ---> b) ---> a) ---> a))
  using BasicReasoning.
Proof.
  intros wfa wfb.
  toMyGoal.
  { wf_auto2. }
  mgTauto.
Qed.