From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Ltac2 Require Import Ltac2.

From Coq Require Import Ensembles Bool.
From Coq.Logic Require Import FunctionalExtensionality Eqdep_dec.
From Equations Require Import Equations.

Require Import Coq.Program.Tactics.

From MatchingLogic Require Import
    Syntax
    DerivedOperators_Syntax
    ProofSystem
    IndexManipulation
    wftactics
    ProofMode_base
.

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

Lemma P1 {Σ : Signature} (Γ : Theory) (ϕ ψ : Pattern) :
well_formed ϕ ->
well_formed ψ ->
Γ ⊢i ϕ ---> ψ ---> ϕ 
using BasicReasoning.
Proof.
intros wfϕ wfψ.
unshelve (eexists).
{ apply ProofSystem.P1. exact wfϕ. exact wfψ. }
{ abstract(solve_pim_simple). }
Defined.

Lemma P2 {Σ : Signature} (Γ : Theory) (ϕ ψ ξ : Pattern) :
well_formed ϕ ->
well_formed ψ ->
well_formed ξ ->
Γ ⊢i (ϕ ---> ψ ---> ξ) ---> (ϕ ---> ψ) ---> (ϕ ---> ξ)
using BasicReasoning.
Proof.
intros wfϕ wfψ wfξ.
unshelve (eexists).
{ apply ProofSystem.P2. exact wfϕ. exact wfψ. exact wfξ. }
{ abstract (solve_pim_simple). }
Defined.

Lemma P3 {Σ : Signature} (Γ : Theory) (ϕ : Pattern) :
well_formed ϕ ->
Γ ⊢i (((ϕ ---> ⊥) ---> ⊥) ---> ϕ)
using BasicReasoning.
Proof.
intros wfϕ.
unshelve (eexists).
{ apply ProofSystem.P3. exact wfϕ. }
{ abstract ( solve_pim_simple ). }
Defined.

Lemma MP {Σ : Signature} (Γ : Theory) (ϕ₁ ϕ₂ : Pattern) (i : ProofInfo) :
Γ ⊢i ϕ₁ using i ->
Γ ⊢i (ϕ₁ ---> ϕ₂) using i ->
Γ ⊢i ϕ₂ using i.
Proof.
intros H1 H2.
unshelve (eexists).
{
  eapply (ProofSystem.Modus_ponens _ _ _).
  { apply H1. }
  { apply H2. }
}
{
  abstract(
    simpl;
    destruct H1 as [pf1 Hpf1];
    destruct H2 as [pf2 Hpf2];
    destruct Hpf1,Hpf2;
    constructor; simpl;
    [set_solver|set_solver|(destruct (uses_kt pf1),(uses_kt pf2); simpl in *; congruence)|set_solver]
  ).
}
Defined.

Arguments P1 {Σ} _ (_%ml) (_%ml) _ _ .
Arguments P2 {Σ} _ (_%ml) (_%ml) (_%ml) _ _ _.
Arguments P3 {Σ} _ (_%ml) _.

  Lemma A_impl_A {Σ : Signature} (Γ : Theory) (A : Pattern)  :
    (well_formed A) ->
    Γ ⊢i (A ---> A)
    using BasicReasoning.
  Proof. 
    intros WFA.
    pose (_1 := P2 Γ A (A ---> A) A ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2)).
    pose (_2 := P1 Γ A (A ---> A) ltac:(wf_auto2) ltac:(wf_auto2)).
    pose (_3 := MP _2 _1).
    pose (_4 := P1 Γ A A ltac:(wf_auto2) ltac:(wf_auto2)).
    pose (_5 := MP _4 _3).
    exact _5.
  Defined.

  Lemma P4m  {Σ : Signature}(Γ : Theory) (A B : Pattern) :
    well_formed A ->
    well_formed B ->
    Γ ⊢i ((A ---> B) ---> ((A ---> !B) ---> !A))
    using BasicReasoning.
  Proof.
    intros WFA WFB.
    pose (H1 := P2 Γ A B Bot ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2)).
    pose (H2 := (P2 Γ (A ---> B ---> Bot) (A ---> B) (A ---> Bot) ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2))).
    pose (H3 := MP H1 H2).
    pose (H4 := (P1 Γ (((A ---> B ---> Bot) ---> A ---> B) ---> (A ---> B ---> Bot) ---> A ---> Bot)
      (A ---> B) ltac:(wf_auto2) ltac:(wf_auto2))).
    pose (H5 := MP  H3 H4).
    pose (H6 := (P2 Γ (A ---> B) ((A ---> B ---> Bot) ---> A ---> B) ((A ---> B ---> Bot) ---> A ---> Bot)
      ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2))).
    pose (H7 := MP H5 H6).
    pose (H8 := (P1 Γ (A ---> B) (A ---> B ---> Bot) ltac:(wf_auto2) ltac:(wf_auto2))).
    pose (H9 := MP H8 H7).
    exact H9.
  Defined.

  Lemma P4i {Σ : Signature} (Γ : Theory) (A : Pattern) :
    well_formed A ->
    Γ ⊢i ((A ---> !A) ---> !A)
    using BasicReasoning.
  Proof.
    intros WFA.
    eapply MP.
    { apply (@A_impl_A _ _ A WFA). }
    { apply (@P4m _ _ A A WFA WFA). }
  Defined.

  Lemma reorder {Σ : Signature} (Γ : Theory) (A B C : Pattern) :
    well_formed A ->
    well_formed B ->
    well_formed C ->
    Γ ⊢i ((A ---> B ---> C) ---> ( B ---> A ---> C))
    using BasicReasoning.
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
             ++ apply (@A_impl_A _ _ ABC ltac:(wf_auto2)).
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


  Lemma reorder_meta {Σ : Signature} (Γ : Theory) (A B C : Pattern) (i : ProofInfo) :
    well_formed A ->
    well_formed B ->
    well_formed C ->  
    Γ ⊢i (A ---> B ---> C) using i ->
    Γ ⊢i (B ---> A ---> C) using i.
  Proof.
    intros H H0 H1 H2.
    eapply MP. apply H2.
    apply useBasicReasoning.
    apply reorder; wf_auto2.
  Defined.

  Lemma syllogism {Σ : Signature} (Γ : Theory) (A B C : Pattern) :
    well_formed A ->
    well_formed B ->
    well_formed C ->
    Γ ⊢i ((A ---> B) ---> (B ---> C) ---> (A ---> C))
    using BasicReasoning.
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
  
  Lemma syllogism_meta {Σ : Signature} (Γ : Theory) (A B C : Pattern) (i : ProofInfo) :
    well_formed A ->
    well_formed B ->
    well_formed C ->
    Γ ⊢i (A ---> B) using i ->
    Γ ⊢i (B ---> C) using i ->
    Γ ⊢i (A ---> C) using i.
  Proof.
    intros H H0 H1 H2 H3.
    eapply MP.
    - exact H2.
    - eapply MP.
      + exact H3.
      + apply reorder_meta;[wf_auto2|wf_auto2|wf_auto2|].
        apply useBasicReasoning.
        apply syllogism; wf_auto2.
  Defined.
  
  Lemma modus_ponens {Σ : Signature} (Γ : Theory) (A B : Pattern) :
    well_formed A ->
    well_formed B ->
    Γ ⊢i (A ---> (A ---> B) ---> B)
    using BasicReasoning.
  Proof.
    intros WFA WFB.
    eapply MP.
    - apply (P1 _ A (A ---> B) ltac:(wf_auto2) ltac:(wf_auto2)).
    - eapply MP.
      + eapply MP.
        * apply (@A_impl_A _ _ (A ---> B) ltac:(wf_auto2)).
        * eapply (P2 _ (A ---> B) A B ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2)).
      + apply reorder_meta;[wf_auto2|wf_auto2|wf_auto2|].
        apply syllogism; wf_auto2.
  Defined.

  Lemma not_not_intro {Σ : Signature} (Γ : Theory) (A : Pattern) :
    well_formed A ->
    Γ ⊢i (A ---> !(!A))
    using BasicReasoning.
  Proof.
    intros WFA.
    apply modus_ponens; wf_auto2.
  Defined.

  Lemma P4 {Σ : Signature} (Γ : Theory) (A B : Pattern)  :
    well_formed A ->
    well_formed B -> 
    Γ ⊢i (((! A) ---> (! B)) ---> (B ---> A))
    using BasicReasoning.
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
    pose proof (m8 := @reorder _ Γ (A ---> Bot) (B) Bot ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2)).
    apply (MP m8 m7).
  Defined.

  Lemma conj_intro {Σ : Signature} (Γ : Theory) (A B : Pattern) :
    well_formed A ->
    well_formed B ->
    Γ ⊢i (A ---> B ---> (A and B))
    using BasicReasoning.
  Proof.
    intros WFA WFB.
    pose proof (tB := (@A_impl_A _ Γ B ltac:(wf_auto2))).
    epose proof (t1 := MP (P2 _ (!(!A) ---> !B) A Bot ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2)) (P1 _ _ B _ _)).
    epose proof (t2 := MP (reorder_meta _ _ _ (@P4 _ _ (!A) B ltac:(wf_auto2) ltac:(wf_auto2))) (P1 _ _ B _ _)).
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

  Lemma conj_intro_meta {Σ : Signature} (Γ : Theory) (A B : Pattern) (i : ProofInfo) :
    well_formed A ->
    well_formed B ->
    Γ ⊢i A using i ->
    Γ ⊢i B using i ->
    Γ ⊢i (A and B) using i.
  Proof.
    intros WFA WFB H H0.
    eapply MP.
    - exact H0.
    - eapply MP.
      + exact H.
      + apply useBasicReasoning.
        apply conj_intro; wf_auto2.
  Defined.
  
  Lemma syllogism_4_meta {Σ : Signature} (Γ : Theory) (A B C D : Pattern) (i : ProofInfo) :
    well_formed A ->
    well_formed B ->
    well_formed C ->
    well_formed D ->
    Γ ⊢i (A ---> B ---> C) using i ->
    Γ ⊢i (C ---> D) using i ->
    Γ ⊢i (A ---> B ---> D) using i.
  Proof.
    intros WFA WFB WFC WFD H H0.
    eapply MP.
    - exact H.
    - eapply MP.
      + eapply MP.
        * eapply MP.
          -- eapply MP.
             ++ exact H0.
             ++ apply useBasicReasoning. 
                eapply (P1 _ (C ---> D) B _ _).
          -- apply useBasicReasoning.  
              eapply (P2 _ B C D _ _ _).
        * apply useBasicReasoning. 
          eapply (P1 _ ((B ---> C) ---> B ---> D) A _ _).
      + apply useBasicReasoning. 
        eapply (P2 _ A (B ---> C) (B ---> D) _ _ _).
        Unshelve.
        all: wf_auto2.
  Defined.

  Lemma bot_elim {Σ : Signature} (Γ : Theory) (A : Pattern) :
    well_formed A ->
    Γ ⊢i (Bot ---> A)
    using BasicReasoning.
  Proof.
    intros WFA.
    eapply MP.
    - eapply MP.
      + eapply MP.
        * eapply MP.
          -- eapply (P1 _ Bot Bot _ _).
          -- eapply (P2 _ Bot Bot Bot _ _ _).
        * eapply (@P4 _ _ Bot Bot _ _).
      + eapply (P1 _ (Bot ---> Bot) (A ---> Bot) _ _).
    - eapply (@P4 _ _ A Bot _ _).
      Unshelve.
      all: wf_auto2.
  Defined.

  Lemma modus_ponens' {Σ : Signature} (Γ : Theory) (A B : Pattern) :
    well_formed A ->
    well_formed B ->
    Γ ⊢i (A ---> (!B ---> !A) ---> B)
    using BasicReasoning.
  Proof.
    intros WFA WFB.
    apply reorder_meta;[wf_auto2|wf_auto2|wf_auto2|].
    apply P4; wf_auto2.
  Defined.

  Lemma disj_right_intro {Σ : Signature} (Γ : Theory) (A B : Pattern) :
    well_formed A ->
    well_formed B ->
    Γ ⊢i (B ---> (A or B))
    using BasicReasoning.
  Proof.
    intros WFA WFB.
    apply useBasicReasoning.
    apply P1; wf_auto2.
  Defined.
  
  Lemma disj_left_intro {Σ : Signature} (Γ : Theory) (A B : Pattern) :
    well_formed A ->
    well_formed B ->
    Γ ⊢i (A ---> (A or B))
    using BasicReasoning.
  Proof.
    intros WFA WFB.
    eapply syllogism_4_meta.
    5: { apply modus_ponens; wf_auto2. }
    5: { apply bot_elim; wf_auto2. }
    all: wf_auto2.
  Defined.

  Lemma disj_right_intro_meta {Σ : Signature} (Γ : Theory) (A B : Pattern) (i : ProofInfo) :
    well_formed A ->
    well_formed B ->
    Γ ⊢i B using i ->
    Γ ⊢i (A or B) using i.
  Proof.
    intros HwfA HwfB HB.
    eapply MP.
    { exact HB. }
    {
      apply useBasicReasoning.
      apply disj_right_intro; wf_auto2.
    }
  Defined.

  Lemma disj_left_intro_meta {Σ : Signature} (Γ : Theory) (A B : Pattern) (i : ProofInfo) :
    well_formed A ->
    well_formed B ->
    Γ ⊢i A using i ->
    Γ ⊢i (A or B) using i.
  Proof.
    intros HwfA HwfB HA.
    eapply MP.
    { exact HA. }
    apply useBasicReasoning.
    apply disj_left_intro; assumption.
  Defined.

  Lemma not_not_elim {Σ : Signature} (Γ : Theory) (A : Pattern) :
    well_formed A ->
    Γ ⊢i (!(!A) ---> A)
    using BasicReasoning.
  Proof.
    intros WFA.
    apply P3. exact WFA.
  Defined.

  Lemma not_not_elim_meta {Σ : Signature} Γ A (i : ProofInfo) :
    well_formed A ->
    Γ ⊢i (! ! A) using i ->
    Γ ⊢i A using i.
  Proof.
    intros wfA nnA.
    eapply MP.
    { apply nnA. }
    { apply useBasicReasoning. apply not_not_elim. exact wfA. }
  Defined.

  Lemma double_neg_elim {Σ : Signature} (Γ : Theory) (A B : Pattern) :
    well_formed A ->
    well_formed B ->
    Γ ⊢i (((!(!A)) ---> (!(!B))) ---> (A ---> B))
    using BasicReasoning.
  Proof.
    intros WFA WFB.
    eapply syllogism_meta.
    5: apply P4.
    4: apply P4.
    all: wf_auto2.
  Defined.

  Lemma double_neg_elim_meta {Σ : Signature} (Γ : Theory) (A B : Pattern) (i : ProofInfo) :
    well_formed A ->
    well_formed B -> 
    Γ ⊢i ((!(!A)) ---> (!(!B))) using i ->
    Γ ⊢i (A ---> B) using i.
  Proof.
    intros WFA WFB H.
    eapply MP.
    - exact H.
    - apply useBasicReasoning.
      apply double_neg_elim; wf_auto2.
  Defined.

  Lemma not_not_impl_intro {Σ : Signature} (Γ : Theory) (A B : Pattern) :
    well_formed A ->
    well_formed B ->
    Γ ⊢i ((A ---> B) ---> ((! ! A) ---> (! ! B)))
    using BasicReasoning.
  Proof.
    intros WFA WFB.
    
    epose (S1 := @syllogism _ Γ (! ! A) A B _ _ _).
    
    epose (MP1 := MP (@not_not_elim _ _ A _) S1).
    
    epose(NNB := @not_not_intro _ Γ B _).

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

  Lemma contraposition {Σ : Signature} (Γ : Theory) (A B : Pattern) : 
    well_formed A ->
    well_formed B -> 
    Γ ⊢i ((A ---> B) ---> ((! B) ---> (! A)))
    using BasicReasoning.
  Proof.
    intros WFA WFB.
    epose proof (@P4 _ Γ (! A) (! B) _ _) as m.
    apply syllogism_meta with (B := (! (! A) ---> ! (! B))).
    - shelve.
    - shelve.
    - shelve.
    - apply @not_not_impl_intro; wf_auto2.
    - exact m. (* apply (P4 _ _ _). shelve. shelve. *)
      Unshelve.
      all: wf_auto2.
  Defined.

  Lemma or_comm_meta {Σ : Signature} (Γ : Theory) (A B : Pattern) (i : ProofInfo):
    well_formed A ->
    well_formed B ->
    Γ ⊢i (A or B) using i ->
    Γ ⊢i (B or A) using i.
  Proof.
    intros WFA WFB H. unfold patt_or in *.    
    epose proof (P4 := (@P4 _ Γ A (!B) _ _)).
    epose proof (NNI := @not_not_intro  _ Γ B _).
    apply (useBasicReasoning i) in P4.
    apply (useBasicReasoning i) in NNI.
    epose proof (SI := @syllogism_meta _ Γ _ _ _ _ _ _ _ H NNI).
    eapply MP.
    - exact SI.
    - exact P4.
      Unshelve.
      all: wf_auto2.
  Defined.

  Lemma A_implies_not_not_A_alt {Σ : Signature} (Γ : Theory) (A : Pattern) (i : ProofInfo) :
    well_formed A ->
    Γ ⊢i A using i ->
    Γ ⊢i (!( !A )) using i.
  Proof.
    intros WFA H. unfold patt_not.
    eapply MP.
    { apply H. }
    {
      apply useBasicReasoning.
      apply not_not_intro.
      exact WFA.
    }
  Defined.

  Lemma P5i {Σ : Signature} (Γ : Theory) (A B : Pattern) :
    well_formed A ->
    well_formed B ->
    Γ ⊢i (! A ---> (A ---> B))
    using BasicReasoning.
  Proof.
    intros WFA WFB.
    eapply syllogism_meta.
    5: apply P4.
    4: apply P1.
    all: wf_auto2.
  Defined.

  Lemma false_implies_everything {Σ : Signature} (Γ : Theory) (phi : Pattern) :
    well_formed phi ->
    Γ ⊢i (Bot ---> phi) using BasicReasoning.
  Proof.
    apply bot_elim.
  Defined.

  Lemma A_implies_not_not_A_alt_Γ {Σ : Signature} (Γ : Theory) (A : Pattern) (i : ProofInfo) :
    well_formed A ->
    Γ ⊢i A using i ->
    Γ ⊢i (!( !A )) using i.
  Proof.
    intros WFA H. unfold patt_not.
    eapply MP.
    { apply H. }
    { apply useBasicReasoning. apply not_not_intro. exact WFA. }
  Defined.


  Lemma exclusion {Σ : Signature} (G : Theory) (A : Pattern) (i : ProofInfo) :
    well_formed A ->
    G ⊢i A using i ->
    G ⊢i (A ---> Bot) using i ->
    G ⊢i Bot using i.
  Proof.
    intros WFA H H0.
    eapply MP.
    apply H.
    apply H0.
  Defined.

  Lemma modus_tollens {Σ : Signature} Γ A B (i : ProofInfo) :
    Γ ⊢i (A ---> B) using i ->
    Γ ⊢i (!B ---> !A) using i.
  Proof.
    intros H.
    pose proof (wf := proved_impl_wf _ _ (proj1_sig H)).
    assert (wfA : well_formed A) by wf_auto2.
    assert (wfB : well_formed B) by wf_auto2.

    eapply MP.
    2: { apply useBasicReasoning. apply contraposition; wf_auto2. }
    apply H.
  Defined.
  
  Lemma A_impl_not_not_B {Σ : Signature} Γ A B :
    well_formed A ->
    well_formed B ->
    Γ ⊢i ((A ---> ! !B) ---> (A ---> B))
    using BasicReasoning.
  Proof.
    intros WFA WFB.

    assert (H0 : Γ ⊢i (! !B ---> B) using BasicReasoning).
    {
      apply not_not_elim. wf_auto2.
    }

    assert (H1 : Γ ⊢i ((A ---> ! !B) ---> (! !B ---> B) ---> (A ---> B)) using BasicReasoning).
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

  Lemma prf_weaken_conclusion {Σ : Signature} Γ A B B' :
    well_formed A ->
    well_formed B ->
    well_formed B' ->
    Γ ⊢i ((B ---> B') ---> ((A ---> B) ---> (A ---> B')))
    using BasicReasoning.
  Proof.
    intros wfA wfB wfB'.
    apply reorder_meta;[wf_auto2|wf_auto2|wf_auto2|].
    apply syllogism; wf_auto2.
  Defined.

  Lemma prf_weaken_conclusion_meta {Σ : Signature} Γ A B B' (i : ProofInfo) :
    well_formed A ->
    well_formed B ->
    well_formed B' ->
    Γ ⊢i (B ---> B') using i ->
    Γ ⊢i ((A ---> B) ---> (A ---> B')) using i.
  Proof.
    intros wfA wfB wfB' BimpB'.
    assert (H1: Γ ⊢i ((A ---> B) ---> (B ---> B') ---> (A ---> B')) using i).
    {
      apply useBasicReasoning. apply syllogism; wf_auto2.
    }
    apply reorder_meta in H1;[|wf_auto2|wf_auto2|wf_auto2].
    eapply MP. 2: apply H1. apply BimpB'.
  Defined.

  Lemma prf_weaken_conclusion_iter {Σ : Signature} Γ l g g'
          (wfl : Pattern.wf l) (wfg : well_formed g) (wfg' : well_formed g') :
    Γ ⊢i ((g ---> g') ---> (fold_right patt_imp g l ---> fold_right patt_imp g' l))
    using BasicReasoning.
  Proof.
    induction l.
    - apply A_impl_A. wf_auto2.
    - pose proof (wfl' := wfl).
      apply andb_prop in wfl.
      fold (map well_formed) in wfl.
      destruct wfl as [wfa wfl].
      (* I do not know how to fold it, so I just assert & clear. *)
      assert (wfl'' : Pattern.wf l) by apply wfl.
      clear wfl.
      specialize (IHl wfl'').
      simpl in *.
      eapply syllogism_meta.
      5: eapply prf_weaken_conclusion.
      4: apply IHl.
      all: wf_auto2.
  Defined.

  Lemma prf_weaken_conclusion_iter_meta {Σ : Signature} Γ l g g' (i : ProofInfo):
    Pattern.wf l ->
    well_formed g ->
    well_formed g' ->
    Γ ⊢i (g ---> g') using i ->
    Γ ⊢i ((fold_right patt_imp g l) ---> (fold_right patt_imp g' l)) using i.
  Proof.
    intros wfl wfg wfg' gimpg'.
    eapply MP.
    2: { apply useBasicReasoning. apply prf_weaken_conclusion_iter; wf_auto2. }
    1: { apply gimpg'. }
  Defined.

  Lemma prf_weaken_conclusion_iter_meta_meta {Σ : Signature} Γ l g g' (i : ProofInfo):
    Pattern.wf l ->
    well_formed g ->
    well_formed g' ->
    Γ ⊢i (g ---> g') using i ->
    Γ ⊢i (fold_right patt_imp g l) using i ->
    Γ ⊢i (fold_right patt_imp g' l) using i.
  Proof.
    intros wfl wfg wfg' gimpg' H.
    eapply MP.
    { apply gimpg'. }
    eapply MP.
    { apply H. }
    apply reorder_meta;[wf_auto2|wf_auto2|wf_auto2|].
    apply useBasicReasoning.
    apply prf_weaken_conclusion_iter.
    all: wf_auto2.
  Defined.

  Lemma prf_weaken_conclusion_meta_meta {Σ : Signature} Γ A B B' (i : ProofInfo) :
    well_formed A ->
    well_formed B ->
    well_formed B' ->
    Γ ⊢i (B ---> B') using i ->
    Γ ⊢i (A ---> B) using i ->
    Γ ⊢i (A ---> B') using i.
  Proof.
    intros WFA WFB WFB' H H0.
    eapply MP. 2: apply prf_weaken_conclusion_meta. 1: apply H0.
    4: apply H. all: wf_auto2.
  Defined.

  Lemma prf_strenghten_premise {Σ : Signature} Γ A A' B :
    well_formed A ->
    well_formed A' ->
    well_formed B ->
    Γ ⊢i ((A' ---> A) ---> ((A ---> B) ---> (A' ---> B))) using BasicReasoning.
  Proof.
    intros wfA wfA' wfB.
    apply syllogism; wf_auto2.
  Defined.

  Lemma prf_strenghten_premise_iter {Σ : Signature}  Γ l₁ l₂ h h' g :
    Pattern.wf l₁ -> Pattern.wf l₂ ->
    well_formed h ->
    well_formed h' ->
    well_formed g ->
    Γ ⊢i (h' ---> h) --->
        foldr patt_imp g (l₁ ++ h::l₂) --->
        foldr patt_imp g (l₁ ++ h'::l₂)
    using BasicReasoning.
  Proof.
    intros wfl₁ wfl₂ wfh wfh' wfg.
    induction l₁.
    - simpl. apply prf_strenghten_premise. all: wf_auto2.
    - pose proof (wfal₁ := wfl₁).
      remember (foldr patt_imp g (h::l₂)) as g1.
      remember (foldr patt_imp g (h'::l₂)) as g2.
      unfold Pattern.wf in wfl₁. simpl in wfl₁. apply andb_prop in wfl₁.
      destruct wfl₁ as [wfa wfl₁].
      specialize (IHl₁ wfl₁).
      remember (foldr patt_imp g (l₁ ++ h::l₂)) as b.
      remember (foldr patt_imp g (l₁ ++ h'::l₂)) as b'.

      assert (prf: Γ ⊢i ((b ---> b') ---> ((a ---> b) ---> (a ---> b'))) using BasicReasoning).
      { apply prf_weaken_conclusion; subst; wf_auto2. }

      subst.
      eapply syllogism_meta.
      5: { apply prf. }
      4: { apply IHl₁. }
      all: wf_auto2.
  Defined.

  Lemma prf_strenghten_premise_meta {Σ : Signature} Γ A A' B (i : ProofInfo) :
    well_formed A ->
    well_formed A' ->
    well_formed B ->
    Γ ⊢i (A' ---> A) using i ->
    Γ ⊢i ((A ---> B) ---> (A' ---> B)) using i.
  Proof.
    intros wfA wfA' wfB A'impA.
    assert (H1: Γ ⊢i ((A' ---> A) ---> (A ---> B) ---> (A' ---> B)) using i).
    {
      apply useBasicReasoning. apply syllogism; wf_auto2.
    }
    eapply MP. 2: apply H1. apply A'impA.
  Defined.

  Lemma prf_strenghten_premise_meta_meta {Σ : Signature} Γ A A' B (i : ProofInfo) :
    well_formed A ->
    well_formed A' ->
    well_formed B ->
    Γ ⊢i (A' ---> A) using i ->
    Γ ⊢i (A ---> B) using i ->
    Γ ⊢i (A' ---> B) using i.
  Proof.
    intros wfA wfA' wfB A'impA AimpB.
    eapply MP. 2: apply prf_strenghten_premise_meta. 1: apply AimpB.
    4: apply A'impA. all: wf_auto2.
  Defined.

  Lemma prf_strenghten_premise_iter_meta {Σ : Signature} Γ l₁ l₂ h h' g (i : ProofInfo) :
    Pattern.wf l₁ -> Pattern.wf l₂ ->
    well_formed h ->
    well_formed h' ->
    well_formed g ->
    Γ ⊢i (h' ---> h) using i ->
    Γ ⊢i foldr patt_imp g (l₁ ++ h::l₂) --->
         foldr patt_imp g (l₁ ++ h'::l₂)
    using i.  
  Proof.
    intros WFl₁ WFl₂ WFh WFh' WFg H.
    eapply MP.
    2: { apply useBasicReasoning. apply prf_strenghten_premise_iter; wf_auto2. }
    exact H.
  Defined.

  Lemma prf_strenghten_premise_iter_meta_meta {Σ : Signature} Γ l₁ l₂ h h' g (i : ProofInfo) :
    Pattern.wf l₁ -> Pattern.wf l₂ ->
    well_formed h ->
    well_formed h' ->
    well_formed g ->
    Γ ⊢i (h' ---> h) using i ->
    Γ ⊢i foldr patt_imp g (l₁ ++ h::l₂) using i ->
    Γ ⊢i foldr patt_imp g (l₁ ++ h'::l₂) using i.  
  Proof.
    intros WFl₁ WFl₂ WFh WFh' WFg H H0.
    eapply MP.
    2: eapply prf_strenghten_premise_iter_meta.
    7: eassumption. 1: assumption. all: wf_auto2.
  Defined.


  Local Example example_nested_const {Σ : Signature} Γ a b c:
    well_formed a ->
    well_formed b ->
    well_formed c ->
    (* like P2 but nested a bit *)
    Γ ⊢i (a ---> (b ---> (c ---> a)))
    using BasicReasoning.
  Proof.
    intros wfa wfb wfc.
    assert (H1: Γ ⊢i ((c ---> a) ---> (b ---> (c ---> a))) using BasicReasoning).
    {
      apply P1; wf_auto2.
    }
    assert (H2: Γ ⊢i (a ---> (c ---> a)) using BasicReasoning).
    { apply P1; wf_auto2. }

    eapply (@syllogism_meta _ _ _ _ _ _ _ _ _ H2 H1).
    Unshelve. all: wf_auto2.
  Defined.

  (* This will form a base for the tactic 'exact 0' *)
  Lemma nested_const {Σ : Signature} Γ a l:
    well_formed a ->
    Pattern.wf l ->
    Γ ⊢i (a ---> (fold_right patt_imp a l))
    using BasicReasoning.
  Proof.
    intros wfa wfl.
    induction l; simpl.
    - apply A_impl_A. exact wfa.
    - pose proof (wfa0l := wfl).
      unfold Pattern.wf in wfl. simpl in wfl. apply andb_prop in wfl. destruct wfl as [wfa0 wfl].
      specialize (IHl wfl).
      assert (H1 : Γ ⊢i ((foldr patt_imp a l) ---> (a0 ---> (foldr patt_imp a l))) using BasicReasoning).
      {
        apply P1; wf_auto2.
      }
      eapply syllogism_meta.
      5: apply H1. 4: assumption. all: wf_auto2.
  Defined.

  Lemma nested_const_middle {Σ : Signature} Γ a l₁ l₂:
    well_formed a ->
    Pattern.wf l₁ ->
    Pattern.wf l₂ ->
    Γ ⊢i (fold_right patt_imp a (l₁ ++ a :: l₂))
    using BasicReasoning.
  Proof.
    intros wfa wfl₁ wfl₂.
    induction l₁; simpl.
    - apply nested_const; wf_auto2.
    - pose proof (wfa0l₁ := wfl₁).
      unfold Pattern.wf in wfl₁. simpl in wfl₁. apply andb_prop in wfl₁. destruct wfl₁ as [wfa0 wfl₁].
      specialize (IHl₁ wfl₁). simpl in IHl₁.
      eapply MP. 2: apply P1. 1: apply IHl₁. all: wf_auto2.
  Defined.

  Lemma prf_reorder_iter {Σ : Signature} Γ a b g l₁ l₂:
    well_formed a ->
    well_formed b ->
    well_formed g ->
    Pattern.wf l₁ ->
    Pattern.wf l₂ ->
    Γ ⊢i ((fold_right patt_imp g (l₁ ++ [a;b] ++ l₂)) --->
         (fold_right patt_imp g (l₁ ++ [b;a] ++ l₂)))
    using BasicReasoning.
  Proof.
    intros wfa wfb wfg wfl₁ wfl₂.
    induction l₁; simpl in *.
    - apply reorder; wf_auto2.
    - pose proof (wfa0l₁ := wfl₁).
      unfold Pattern.wf in wfl₁. apply andb_prop in wfl₁. destruct wfl₁ as [wfa0 wfl₁].
      specialize (IHl₁ wfl₁).
      eapply prf_weaken_conclusion_meta.
      4: apply IHl₁.
      all: wf_auto2.
  Defined.

  Lemma prf_reorder_iter_meta {Σ : Signature} Γ a b g l₁ l₂ (i : ProofInfo):
    well_formed a ->
    well_formed b ->
    well_formed g ->
    Pattern.wf l₁ ->
    Pattern.wf l₂ ->
    Γ ⊢i (fold_right patt_imp g (l₁ ++ [a;b] ++ l₂)) using i ->
    Γ ⊢i (fold_right patt_imp g (l₁ ++ [b;a] ++ l₂)) using i.
  Proof.
    (* TODO we should have a function/lemma for creating these "meta" variants. *)
    intros WFa WFb WFg Wfl1 Wfl2 H.
    eapply MP.
    2: { apply useBasicReasoning. apply prf_reorder_iter; wf_auto2. }
    exact H.
  Defined.
  
  Lemma A_impl_not_not_B_meta {Σ : Signature} Γ A B (i : ProofInfo) :
    well_formed A ->
    well_formed B ->
    Γ ⊢i A ---> ! !B using i ->
    Γ ⊢i A ---> B using i.
  Proof.
    intros WFA WFB H.
    eapply MP.
    2: { apply useBasicReasoning. apply A_impl_not_not_B; wf_auto2. }
    exact H.
  Defined.

  Lemma pf_conj_elim_l {Σ : Signature} Γ A B :
    well_formed A ->
    well_formed B ->
    Γ ⊢i A and B ---> A using BasicReasoning.
  Proof.
    intros WFA WFB. unfold patt_and. unfold patt_not at 1.

    assert (Γ ⊢i (! A ---> (! A or ! B)) using BasicReasoning).
    { apply disj_left_intro; wf_auto2. }

    assert (Γ ⊢i ((! A or ! B) ---> (! A or ! B ---> ⊥) ---> ⊥) using BasicReasoning).
    {
      apply modus_ponens; wf_auto2.
    }
    assert (Γ ⊢i (! A ---> ((! A or ! B ---> ⊥) ---> ⊥)) using BasicReasoning).
    { eapply syllogism_meta. 5: apply H0. 4: apply H. all: wf_auto2. }
    epose proof (reorder_meta _ _ _ H1).
    apply A_impl_not_not_B_meta;[wf_auto2|wf_auto2|].
    apply H2.
    Unshelve.
    all: wf_auto2.
  Defined.

  Lemma pf_conj_elim_r {Σ : Signature} Γ A B :
    well_formed A ->
    well_formed B ->
    Γ ⊢i A and B ---> B using BasicReasoning.
  Proof.
    intros WFA WFB. unfold patt_and. unfold patt_not at 1.

    assert (Γ ⊢i (! B ---> (! A or ! B)) using BasicReasoning).
    { apply disj_right_intro; wf_auto2. }

    assert (Γ ⊢i ((! A or ! B) ---> (! A or ! B ---> ⊥) ---> ⊥) using BasicReasoning).
    { apply modus_ponens; wf_auto2. }

    assert (Γ ⊢i (! B ---> ((! A or ! B ---> ⊥) ---> ⊥)) using BasicReasoning).
    { eapply syllogism_meta. 5: apply H0. 4: apply H. all: wf_auto2. }
    epose proof (reorder_meta  _ _ _ H1).
    apply A_impl_not_not_B_meta;[wf_auto2|wf_auto2|].
    apply H2.
    Unshelve.
    all: wf_auto2.
  Defined.

  Lemma pf_conj_elim_l_meta {Σ : Signature} Γ A B (i : ProofInfo) :
    well_formed A ->
    well_formed B ->
    Γ ⊢i A and B using i ->
    Γ ⊢i A using i.
  Proof.
    intros WFA WFB H.
    eapply MP.
    2: { apply useBasicReasoning. apply pf_conj_elim_l. wf_auto2. shelve. }
    1: apply H.
    Unshelve. all: wf_auto2.
  Defined.
  
  Lemma pf_conj_elim_r_meta {Σ : Signature} Γ A B (i : ProofInfo) :
    well_formed A ->
    well_formed B ->
    Γ ⊢i A and B using i ->
    Γ ⊢i B using i.
  Proof.
    intros WFA WFB H.
    eapply MP.
    2: apply useBasicReasoning; apply pf_conj_elim_r.
    1: apply H.
    all: wf_auto2.
  Defined.

  Lemma A_or_notA {Σ : Signature} Γ A :
    well_formed A ->
    Γ ⊢i A or ! A using BasicReasoning.
  Proof.
    intros wfA.
    unfold patt_or.
    apply A_impl_A. wf_auto2.
  Defined.

  Lemma P4m_meta {Σ : Signature} (Γ : Theory) (A B : Pattern) (i : ProofInfo) :
    well_formed A ->
    well_formed B ->
    Γ ⊢i A ---> B using i ->
    Γ ⊢i A ---> !B using i ->
    Γ ⊢i !A using i.
  Proof.
    intros wfA wfB AimpB AimpnB.
    pose proof (H1 := @P4m _ Γ A B wfA wfB).
    assert (H2 : Γ ⊢i (A ---> ! B) ---> ! A using i).
    { eapply MP. 2: { apply useBasicReasoning; apply H1. } exact AimpB. }
    eapply MP. 2: { apply H2. } exact AimpnB.
  Defined.


Lemma MLGoal_exactn {Σ : Signature} (Γ : Theory) (l₁ l₂ : list Pattern) (g : Pattern):
  @mkMLGoal Σ Γ (l₁ ++ g :: l₂) g BasicReasoning.
Proof.
  mlExtractWF wfl₁gl₂ wfg.
  fromMLGoal.
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
      unfold Pattern.wf in wfgl₂;
      simpl in wfgl₂;
      apply andb_prop in wfgl₂;
      destruct wfgl₂ as [_ wfl₂];
      exact wfl₂
    ).
  }
Defined.

Tactic Notation "mlExactn" constr(n) :=
  useBasicReasoning;
  unshelve (eapply (@cast_proof_ml_hyps _ _ _ _ _ _ _));
  [shelve|(rewrite <- (firstn_skipn n); rewrite /firstn; rewrite /skipn; reflexivity)|idtac];
  apply MLGoal_exactn.


Local Example ex_mlExactn {Σ : Signature} Γ a b c:
  well_formed a = true ->
  well_formed b = true ->
  well_formed c = true ->
  Γ ⊢i a ---> b ---> c ---> b using BasicReasoning.
Proof.
  intros wfa wfb wfc.
  toMLGoal.
  { wf_auto2. }
  mlIntro. mlIntro. mlIntro.
  mlExactn 1.
Defined.



Lemma MLGoal_weakenConclusion' {Σ : Signature} Γ l g g' (i : ProofInfo):
Γ ⊢i g ---> g' using i ->
@mkMLGoal Σ Γ l g i ->
@mkMLGoal Σ Γ l g' i.
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

eapply (@cast_proof' _ _ _ _ _ Hiter).

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
pose proof (H1 := @prf_weaken_conclusion_iter Σ Γ l g g' wfl wfg wfg').
remember ((g ---> g')) as a.
remember (foldr patt_imp g l) as b.
remember (foldr patt_imp g' l) as c.
assert (well_formed a) by (subst; wf_auto2).
assert (well_formed b) by (subst; wf_auto2).
assert (well_formed c) by (subst; wf_auto2).
pose proof (H2' := @prf_weaken_conclusion_under_implication _ Γ a b c ltac:(assumption) ltac:(assumption) ltac:(assumption)).
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

Lemma MLGoal_weakenConclusion_under_first_implication {Σ : Signature} Γ l g g' i:
@mkMLGoal Σ Γ ((g ---> g') :: l) g i ->
@mkMLGoal Σ Γ ((g ---> g') :: l) g' i .
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

Lemma MLGoal_weakenConclusion {Σ : Signature} Γ l₁ l₂ g g' i:
@mkMLGoal Σ Γ (l₁ ++ (g ---> g') :: l₂) g i ->
@mkMLGoal Σ Γ (l₁ ++ (g ---> g') :: l₂) g' i.
Proof.
unfold of_MLGoal in *. simpl in *.
intros H wfg' wfl₁gg'l₂.

apply prf_weaken_conclusion_iter_under_implication_iter_meta.
{ abstract (pose proof (wfl₁ := wf_take (length l₁) wfl₁gg'l₂); rewrite take_app in wfl₁; exact wfl₁). }
{ abstract (
    pose proof (wfgg'l₂ := wf_drop (length l₁) wfl₁gg'l₂);
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
    pose proof (wfgg'l₂ := wf_drop (length l₁) wfl₁gg'l₂);
    rewrite drop_app in wfgg'l₂;
    pose proof (Htmp := wfgg'l₂);
    unfold Pattern.wf in Htmp;
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
    unfold Pattern.wf in Htmp;
    simpl in Htmp;
    apply andb_prop in Htmp;
    destruct Htmp as [wfgg' wfl₂];
    pose proof (wfg := well_formed_imp_proj1 wfgg');
    exact wfg
  ).
}
exact wfl₁gg'l₂.
Defined.


Tactic Notation "mlApply" constr(n) :=
  unshelve (eapply (@cast_proof_ml_hyps _ _ _ _ _ _ _));
  [shelve|(rewrite <- (firstn_skipn n); rewrite /firstn; rewrite /skipn; reflexivity)|idtac];
  apply MLGoal_weakenConclusion;
  let hyps := fresh "hyps" in rewrite [hyps in @mkMLGoal _ _ hyps _]/app.

Local Example ex_mlApply {Σ : Signature} Γ a b:
  well_formed a ->
  well_formed b ->
  Γ ⊢i a ---> (a ---> b) ---> b using BasicReasoning.
Proof.
  intros wfa wfb.
  toMLGoal.
  { wf_auto2. }
  mlIntro. mlIntro.
  mlApply 1.
  fromMLGoal. apply P1; wf_auto2.
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

mlIntro. mlIntro. mlIntro. mlIntro.
mlApply 1.
mlApply 2.
mlIntro.
mlApply 3.
mlApply 0.
mlExactn 4.
Defined.

Lemma prf_add_assumption {Σ : Signature} Γ a b i :
well_formed a ->
well_formed b ->
Γ ⊢i b using i ->
Γ ⊢i (a ---> b) using i.
Proof.
intros wfa wfb H.
eapply MP.
{ apply H. }
{ useBasicReasoning. apply P1; wf_auto2. }
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
  { apply prf_add_assumption; wf_auto2. }

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

Lemma myGoal_assert {Σ : Signature} Γ l g h i:
well_formed h ->
@mkMLGoal Σ Γ l h i ->
@mkMLGoal Σ Γ (l ++ [h]) g i ->
@mkMLGoal Σ Γ l g i.
Proof.
intros wfh H1 H2.
unfold of_MLGoal in *. simpl in *.
intros wfg wfl.
eapply prf_add_lemma_under_implication_meta_meta.
4: apply H1. 6: apply H2. all: try assumption.
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
  { apply prf_add_assumption; wf_auto2. }
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

Lemma myGoal_assert_generalized {Σ : Signature} Γ l1 l2 g h i:
well_formed h ->
@mkMLGoal Σ Γ l1 h i ->
@mkMLGoal Σ Γ (l1 ++ [h] ++ l2) g i ->
@mkMLGoal Σ Γ (l1 ++ l2) g i.
Proof.
intros wfh H1 H2.
unfold of_MLGoal in *. simpl in *.
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
    unfold Pattern.wf; rewrite map_app; rewrite foldr_app;
    simpl; rewrite wfh; unfold Pattern.wf in wfl2; rewrite wfl2;
    simpl; exact wfl1
  ).
}
Defined.



Tactic Notation "mlAssert" "(" constr(t) ")" :=
  match goal with
  | |- @of_MLGoal ?Sgm (@mkMLGoal ?Sgm ?Ctx ?l ?g ?i) =>
    let Hwf := fresh "Hwf" in
    assert (Hwf : well_formed t);
    [idtac|
      let H := fresh "H" in
      assert (H : @mkMLGoal Sgm Ctx l t i);
      [ | (eapply (@myGoal_assert Sgm Ctx l g t i Hwf H); rewrite [_ ++ _]/=; clear H)]
    ]
  end.

Local Example ex_mlAssert {Σ : Signature} Γ a:
  well_formed a ->
  Γ ⊢i (a ---> a ---> a) using BasicReasoning.
Proof.
  intros wfa.
  toMLGoal.
  { wf_auto2. }
  mlIntro. mlIntro.
  mlAssert (a).
  { wf_auto2. }
  { mlExactn 1. }
  { mlExactn 2. }
Qed.

Tactic Notation "mlAssert" "(" constr(t) ")" "using" "first" constr(n) :=
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
      | apply (cast_proof_ml_hyps Heql1) in H;
        eapply (@myGoal_assert_generalized Sgm Ctx (take n l) (drop n l) g t i Hwf H);
        rewrite [_ ++ _]/=; clear l1 l2 Heql1 Heql2 H] 
    ]
  end.

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
  do 3 mlIntro.
  mlAssert (p) using first 2.
  { wf_auto2. }
  { admit. }
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
pose proof (H1 := @Constructive_dilemma Σ Γ p r q r wfp wfr wfq wfr).
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
  pose proof (@modus_ponens Σ Γ _ _ wfa wfg).
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
  pose proof (H0 := @prf_strenghten_premise_iter_meta_meta Σ Γ [] []).
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

Lemma MLGoal_add {Σ : Signature} Γ l g h i:
Γ ⊢i h using i ->
@mkMLGoal Σ Γ (h::l) g i ->
@mkMLGoal Σ Γ l g i.
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

Tactic Notation "mlAdd" constr(n) :=
  match goal with
  | |- @of_MLGoal ?Sgm (@mkMLGoal ?Sgm ?Ctx ?l ?g ?i) =>
    apply (@MLGoal_add Sgm Ctx l g _ i n)
  end.
