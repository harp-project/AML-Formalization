From Coq Require Import ssreflect ssrfun ssrbool.

From Ltac2 Require Import Ltac2 Control.

From Coq Require Import Bool String.
From Coq.Logic Require Import FunctionalExtensionality Eqdep_dec.
From Equations Require Import Equations.

Require Import Coq.Program.Tactics.

From MatchingLogic Require Import
    Utils.extralibrary
    Logic
    DerivedOperators_Syntax
    ProofSystem
    (*ProofMode_base*)
    ProofInfo
.

From stdpp Require Import list tactics fin_sets coGset gmap sets.

From MatchingLogic.Utils Require Import stdpp_ext.

Import extralibrary.

Import
  MatchingLogic.Logic.Notations
  MatchingLogic.DerivedOperators_Syntax.Notations
  MatchingLogic.ProofInfo.Notations
.

Set Default Proof Mode "Classic".

Open Scope string_scope.
Open Scope list_scope.
Open Scope ml_scope.

Lemma MP {Σ : Signature} {Γ : Theory} {ϕ₁ ϕ₂ : Pattern} {i : ProofInfo} :
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
    
      simpl;
      destruct H1 as [pf1 Hpf1];
      destruct H2 as [pf2 Hpf2];
      destruct Hpf1,Hpf2;
      constructor; simpl;
      [set_solver
      |set_solver
      |(destruct (uses_kt pf1),(uses_kt pf2); simpl in *; congruence)
      |idtac]
    .
    unfold is_true in pwi_pf_kt.
    rewrite implb_true_iff in pwi_pf_kt.
    unfold is_true in pwi_pf_kta.
    rewrite implb_true_iff in pwi_pf_kta.
    unfold is_true in pwi_pf_kt0.
    rewrite implb_true_iff in pwi_pf_kt0.
    unfold is_true in pwi_pf_kta0.
    rewrite implb_true_iff in pwi_pf_kta0.
    unfold is_true.
    rewrite implb_true_iff.
    intro H.
    rewrite orb_true_iff in H.
    destruct H as [H|H].
    {
      specialize (pwi_pf_kta H).
      rewrite andb_true_iff in pwi_pf_kta.
      destruct pwi_pf_kta as [H1 H2].
      rewrite H1 H2. reflexivity.
    }
    {
      specialize (pwi_pf_kta0 H).
      rewrite andb_true_iff in pwi_pf_kta0.
      destruct pwi_pf_kta0 as [H1 H2].
      rewrite H1 H2.
      rewrite orb_true_r.
      reflexivity.
    }
  }
Defined.

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

Lemma A_impl_A {Σ : Signature} (Γ : Theory) (A : Pattern)  :
  (well_formed A) ->
  Γ ⊢i (A ---> A)
  using BasicReasoning.
Proof. 
  intros WFA.
  pose proof (_1 := P2 Γ A (A ---> A) A ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2)).
  pose proof (_2 := P1 Γ A (A ---> A) ltac:(wf_auto2) ltac:(wf_auto2)).
  pose proof (_3 := MP _2 _1).
  pose proof (_4 := P1 Γ A A ltac:(wf_auto2) ltac:(wf_auto2)).
  pose proof (_5 := MP _4 _3).
  exact _5.
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
  { apply useBasicReasoning. apply P1; wf_auto2. }
Defined.

Lemma hypothesis {Σ : Signature} (Γ : Theory) (axiom : Pattern) :
  well_formed axiom ->
  (axiom ∈ Γ) ->
  Γ ⊢i axiom
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
      [( set_solver )
      |( set_solver )
      |( reflexivity)
      |( reflexivity)
      ]
    ).
  }
Defined.

Arguments P1 {Σ} _ (_%ml) (_%ml) _ _ .
Arguments P2 {Σ} _ (_%ml) (_%ml) (_%ml) _ _ _.
Arguments P3 {Σ} _ (_%ml) _.

Lemma P4m  {Σ : Signature}(Γ : Theory) (A B : Pattern) :
  well_formed A ->
  well_formed B ->
  Γ ⊢i ((A ---> B) ---> ((A ---> !B) ---> !A))
  using BasicReasoning.
Proof.
  intros WFA WFB.
  pose (H1 := P2 Γ A B Bot ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2)).
  assert (well_formed_closed_ex_aux A 0 = true).
  {
    wf_auto2.
  }
  (*
  unshelve (epose proof (H2 := (P2 Γ (A ---> B ---> Bot) (A ---> B) (A ---> Bot) _ _ _ ))).
  {
(*    compositeSimplifyAllWfHyps.
    wf_auto2_composite_step. *)
    wf_auto2.
  }
  *)
  pose proof (H2 := (P2 Γ (A ---> B ---> Bot) (A ---> B) (A ---> Bot) ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2))).
  pose proof (H3 := MP H1 H2).
  pose proof (H4 := (P1 Γ (((A ---> B ---> Bot) ---> A ---> B) ---> (A ---> B ---> Bot) ---> A ---> Bot)
    (A ---> B) ltac:(wf_auto2) ltac:(wf_auto2))).
  pose proof (H5 := MP H3 H4).
  
  (*
  (* This one is just for performance debugging purposes *)
  unshelve (epose proof (H6 := (P2 Γ (A ---> B) ((A ---> B ---> Bot) ---> A ---> B) ((A ---> B ---> Bot) ---> A ---> Bot) _ _ _))).
  {
    wf_auto2_step.
    wf_auto2_step.
    wf_auto2_step.
    wf_auto2_step.
    wf_auto2_step.
    wf_auto2_step.
    wf_auto2.
  }
  *)

  
  pose proof (H6 := (P2 Γ (A ---> B) ((A ---> B ---> Bot) ---> A ---> B) ((A ---> B ---> Bot) ---> A ---> Bot)
    ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2))).
  pose proof (H7 := MP H5 H6).
  pose proof (H8 := (P1 Γ (A ---> B) (A ---> B ---> Bot) ltac:(wf_auto2) ltac:(wf_auto2))).
  pose proof (H9 := MP H8 H7).
  exact H9.
Defined.

Lemma P4i {Σ : Signature} (Γ : Theory) (A : Pattern) :
  well_formed A ->
  Γ ⊢i ((A ---> !A) ---> !A)
  using BasicReasoning.
Proof.
  intros WFA.
  eapply MP.
  { apply (A_impl_A _ A WFA). }
  { apply (P4m _ A A WFA WFA). }
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
           ++ apply (A_impl_A _ ABC ltac:(wf_auto2)).
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

Lemma reorder_meta {Σ : Signature} {Γ : Theory} {A B C : Pattern} {i : ProofInfo} :
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

Lemma syllogism_meta {Σ : Signature} {Γ : Theory} {A B C : Pattern} {i : ProofInfo} :
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
      * apply (A_impl_A _ (A ---> B) ltac:(wf_auto2)).
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
  pose proof (m8 := reorder Γ (A ---> Bot) (B) Bot ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2)).
  apply (MP m8 m7).
Defined.

Lemma conj_intro {Σ : Signature} (Γ : Theory) (A B : Pattern) :
  well_formed A ->
  well_formed B ->
  Γ ⊢i (A ---> B ---> (A and B))
  using BasicReasoning.
Proof.
  intros WFA WFB.
  pose proof (tB := (A_impl_A Γ B ltac:(wf_auto2))).
  unshelve (epose proof (t1 := MP (P2 Γ (!(!A) ---> !B) A Bot ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2)) (P1 _ _ B _ _))); try_wfauto2.
  unshelve (epose proof (t2 := MP (reorder_meta _ _ _ (P4 Γ (!A) B ltac:(wf_auto2) ltac:(wf_auto2))) (P1 _ _ B _ _))); try_wfauto2.
  unshelve (epose proof (t3'' := MP (P1 Γ A (!(!A) ---> !B) _ _) (P1 _ _ B _ _))); try_wfauto2.
  unshelve (epose proof (t4 := MP tB (MP t2 (P2 Γ B B _ _ _ _)))); try_wfauto2.
  unshelve (epose proof (t5'' := 
          MP t4
                       (MP t1
                                     (P2 Γ B ((!(!A) ---> !B) ---> !A)
                                         (((!(!A) ---> !B) ---> A) ---> !(!(!A) ---> !B)) _ _ _)))); try_wfauto2.
  
  unshelve (epose proof (tA := (P1 Γ A B) _ _)); try_wfauto2.
  unshelve (epose proof (tB' := MP tB
                            (P1 _ (B ---> B) A _ _))); try_wfauto2.
  unshelve (epose proof (t3' := MP t3''
                            (P2 _ B A ((!(!A) ---> !B) ---> A) _ _ _))); try_wfauto2.
  unshelve (epose proof (t3 := MP t3'
                           (P1 _ ((B ---> A) ---> B ---> (! (! A) ---> ! B) ---> A) A _ _))); try_wfauto2.
  unshelve (epose proof (t5' := MP t5''
                            (P2 _ B ((!(!A) ---> !B) ---> A) (!(!(!A) ---> !B)) _ _ _))); try_wfauto2.
  unshelve (epose proof (t5 := MP t5' 
                           (P1 _ ((B ---> (! (! A) ---> ! B) ---> A) ---> B ---> ! (! (! A) ---> ! B))
                               A _ _))); try_wfauto2.
  unshelve (epose proof (t6 := MP tA
                           (MP t3
                                         (P2 _ A (B ---> A) (B ---> (!(!A) ---> !B) ---> A) _ _ _)))); try_wfauto2.
  unshelve (epose proof (t7 := MP t6 
                           (MP t5 
                                         (P2 _ A (B ---> (!(!A) ---> !B) ---> A) (B ---> !(!(!A) ---> !B)) _ _ _)))); try_wfauto2.
  apply t7.
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
      * eapply (P4 _ Bot Bot _ _).
    + eapply (P1 _ (Bot ---> Bot) (A ---> Bot) _ _).
  - eapply (P4 _ A Bot _ _).
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

  epose (S1 := syllogism Γ (! ! A) A B _ _ _).

  epose (MP1 := MP (not_not_elim _ A _) S1).

  epose(NNB := not_not_intro Γ B _).

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
  epose proof (P4 Γ (! A) (! B) _ _) as m.
  apply @syllogism_meta with (B := (! (! A) ---> ! (! B))).
  - shelve.
  - shelve.
  - shelve.
  - apply not_not_impl_intro; wf_auto2.
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
  epose proof (P4 := (P4 Γ A (!B) _ _)).
  epose proof (NNI := not_not_intro  Γ B _).
  apply (useBasicReasoning i) in P4.
  apply (useBasicReasoning i) in NNI.
  epose proof (SI := syllogism_meta _ _ _ H NNI).
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
    (* fold does not work in wfl, so I just assert & clear. *)
    assert (wfl'' : Pattern.wf l) by apply wfl.
    clear wfl.
    specialize (IHl wfl'').
    simpl in *.
    eapply syllogism_meta.
    5: eapply prf_weaken_conclusion.
    4: apply IHl.
    
    all: try solve [wf_auto2].
Qed.


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

  eapply (syllogism_meta _ _ _ H2 H1).
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

(* NOTE: this should hold, but because of the proof system being in Set, 
it is not straightforward to prove. *)
Lemma reorder_iter_perm {Σ : Signature} Γ ϕ l₁ l₂:
  well_formed ϕ -> Pattern.wf l₁ -> Pattern.wf l₂ ->
  l₁ ⊆ l₂ ->
  Γ ⊢i foldr patt_imp ϕ l₁ ---> foldr patt_imp ϕ l₂ using BasicReasoning.
Proof.
  move: l₂.
  remember (length l₁) as l.
  assert (H: length l₁ <= l) by lia. clear Heql. move: l₁ ϕ H.
  induction l; intros l₁ ϕ Hl l₂ Hwf1 Hwf2 Hwf3 Hs.
  * destruct l₁. 2: simpl in Hl; lia.
    apply nested_const; wf_auto2.
  * destruct l₁ as [| a l₁].
    1: apply nested_const; wf_auto2.
    remember (list_difference l₂ [a]) as l₂'.
    remember (list_difference l₁ [a]) as l₁'.
Abort.

Lemma reorder_head_to_middle {Σ : Signature} (Γ : Theory) :
  ∀ (l1 l2 : list Pattern) (g x : Pattern) ,
    Pattern.wf l1 -> Pattern.wf l2 → well_formed g → well_formed x →
    Γ ⊢i foldr patt_imp g (l1 ++ x :: l2) --->  foldr patt_imp g (x :: l1 ++ l2)
      using BasicReasoning.
Proof.
  induction l1; intros l2 g x Hwf1 Hwf2 Hwfg Hwfx; simpl.
  * apply A_impl_A. wf_auto2.
  * specialize (IHl1 l2 g x ltac:(wf_auto2) Hwf2 Hwfg Hwfx).
    eapply prf_weaken_conclusion_meta_meta.
    4: apply reorder. 1-6: wf_auto2.
    simpl in IHl1.
    eapply prf_weaken_conclusion_meta. 1-3: wf_auto2.
    assumption.
Defined.

Lemma reorder_head_to_middle_meta {Σ : Signature} (Γ : Theory) i :
  ∀ (l1 l2 : list Pattern) (g x : Pattern) ,
    Pattern.wf l1 -> Pattern.wf l2 → well_formed g → well_formed x →
    Γ ⊢i foldr patt_imp g (l1 ++ x :: l2) using i ->
    Γ ⊢i foldr patt_imp g (x :: l1 ++ l2) using i.
Proof.
  intros l1 l2 g x Wf1 Wf2 Wf3 Wf4 H.
  eapply MP. 2: gapply reorder_head_to_middle.
  assumption.
  try_solve_pile.
  all: wf_auto2.
Defined.

Lemma reorder_middle_to_head {Σ : Signature} (Γ : Theory) :
  ∀ (l1 l2 : list Pattern) (g x : Pattern) ,
    Pattern.wf l1 -> Pattern.wf l2 → well_formed g → well_formed x →
    Γ ⊢i foldr patt_imp g (x :: l1 ++ l2) ---> foldr patt_imp g (l1 ++ x::l2)
      using BasicReasoning.
Proof.
  induction l1; intros l2 g x Hwf1 Hwf2 Hwfg Hwfx; simpl.
  * apply A_impl_A. wf_auto2.
  * specialize (IHl1 l2 g x ltac:(wf_auto2) Hwf2 Hwfg Hwfx).
    eapply prf_strenghten_premise_meta_meta.
    4: apply reorder. 1-6: wf_auto2.
    simpl in IHl1.
    eapply prf_weaken_conclusion_meta. 1-3: wf_auto2.
    assumption.
Defined.

Corollary reorder_middle_to_head_meta {Σ : Signature} (Γ : Theory) i :
  ∀ (l1 l2 : list Pattern) (g x : Pattern) ,
    Pattern.wf l1 -> Pattern.wf l2 → well_formed g → well_formed x →
    Γ ⊢i foldr patt_imp g (x :: l1 ++ l2) using i ->
    Γ ⊢i foldr patt_imp g (l1 ++ x::l2) using i.
Proof.
  intros l1 l2 g x Wf1 Wf2 Wf3 Wf4 H.
  eapply MP. 2: gapply reorder_middle_to_head.
  assumption.
  try_solve_pile.
  all: wf_auto2.
Defined.

Corollary reorder_last_to_middle {Σ : Signature} (Γ : Theory) :
  ∀ (l1 l2 : list Pattern) (g x : Pattern) ,
    Pattern.wf l1 -> Pattern.wf l2 → well_formed g → well_formed x →
    Γ ⊢i foldr patt_imp g (l1 ++ x::l2) ---> foldr patt_imp g (l1 ++ l2 ++ [x])
      using BasicReasoning.
Proof.
  intros l1 l2 g x Hwf1 Hwf2 Hwfg Hwfx.
  eapply prf_weaken_conclusion_meta_meta.
  5: apply reorder_head_to_middle. 1-3, 5-8: wf_auto2.
  pose proof (H := reorder_middle_to_head Γ (l1 ++ l2) [] g x); simpl in H.
  rewrite app_nil_r -app_assoc in H.
  simpl. apply H. all: wf_auto2.
Defined.

Corollary reorder_last_to_middle_meta {Σ : Signature} (Γ : Theory) i :
  ∀ (l1 l2 : list Pattern) (g x : Pattern) ,
    Pattern.wf l1 -> Pattern.wf l2 → well_formed g → well_formed x →
    Γ ⊢i foldr patt_imp g (l1 ++ x::l2) using i ->
    Γ ⊢i foldr patt_imp g (l1 ++ l2 ++ [x]) using i.
Proof.
  intros l1 l2 g x Wf1 Wf2 Wf3 Wf4 H.
  eapply MP. 2: gapply reorder_last_to_middle.
  assumption.
  try_solve_pile.
  all: wf_auto2.
Defined.

Corollary reorder_middle_to_last {Σ : Signature} (Γ : Theory) :
  ∀ (l1 l2 : list Pattern) (g x : Pattern) ,
    Pattern.wf l1 -> Pattern.wf l2 → well_formed g → well_formed x →
    Γ ⊢i foldr patt_imp g (l1 ++ l2 ++ [x]) ---> foldr patt_imp g (l1 ++ x::l2)
      using BasicReasoning.
Proof.
  intros l1 l2 g x Hwf1 Hwf2 Hwfg Hwfx.
  eapply prf_strenghten_premise_meta_meta.
  5: apply reorder_middle_to_head. 1-3, 5-8: wf_auto2.
  pose proof (H := reorder_head_to_middle Γ (l1 ++ l2) [] g x); simpl in H.
  rewrite app_nil_r -app_assoc in H.
  simpl. apply H. all: wf_auto2.
Defined.

Corollary reorder_middle_to_last_meta {Σ : Signature} (Γ : Theory) i :
  ∀ (l1 l2 : list Pattern) (g x : Pattern) ,
    Pattern.wf l1 -> Pattern.wf l2 → well_formed g → well_formed x →
    Γ ⊢i foldr patt_imp g (l1 ++ l2 ++ [x]) using i ->
    Γ ⊢i foldr patt_imp g (l1 ++ x::l2) using i.
Proof.
  intros l1 l2 g x Wf1 Wf2 Wf3 Wf4 H.
  eapply MP. 2: gapply reorder_middle_to_last.
  assumption.
  try_solve_pile.
  all: wf_auto2.
Defined.

Corollary reorder_head_to_last {Σ : Signature} (Γ : Theory) :
  ∀ (l : list Pattern) (g x : Pattern) ,
    Pattern.wf l → well_formed g → well_formed x →
    Γ ⊢i foldr patt_imp g (l ++ [x]) --->  foldr patt_imp g (x :: l)
      using BasicReasoning.
Proof.
  intros l g x Hwf Hwf2 Hwf3.
  apply (reorder_middle_to_last Γ [] l g x).
  all: wf_auto2.
Defined.

Corollary reorder_head_to_last_meta {Σ : Signature} (Γ : Theory) :
  forall (l : list Pattern) (g x : Pattern) i,
  Pattern.wf l → well_formed g → well_formed x
  → Γ ⊢i foldr patt_imp g (l ++ [x]) using i
  → Γ ⊢i foldr patt_imp g (x :: l) using i.
Proof.
  intros l g x i Wfl Wfg Wfx H. eapply MP.
  2: {
    pose proof (reorder_head_to_last Γ l g x) as H0.
    ospecialize* H0. 1-3: wf_auto2.
    use i in H0. exact H0. 
  }
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
  pose proof (H1 := P4m Γ A B wfA wfB).
  assert (H2 : Γ ⊢i (A ---> ! B) ---> ! A using i).
  { eapply MP. 2: { apply useBasicReasoning; apply H1. } exact AimpB. }
  eapply MP. 2: { apply H2. } exact AimpnB.
Defined.



  (*
    Γ ⊢ φ₁ → φ₂
    -------------------- (x ∉ FV(φ₂))
    Γ ⊢ (∃x. φ₁) → φ₂
  *)
  Lemma Ex_gen {Σ : Signature} (Γ : Theory) (ϕ₁ ϕ₂ : Pattern) (x : evar) (i : ProofInfo)
      {pile : ProofInfoLe (ExGen := {[x]}, SVSubst := ∅, KT := false, AKT := false) i} :
    x ∉ free_evars ϕ₂ ->
    Γ ⊢i ϕ₁ ---> ϕ₂ using i ->
    Γ ⊢i (exists_quantify x ϕ₁ ---> ϕ₂) using i.
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
      constructor; simpl.
      {
        rewrite elem_of_subseteq. intros x0 Hx0.
        rewrite elem_of_gset_to_coGset in Hx0.
        rewrite elem_of_union in Hx0.
        destruct Hx0.
        {
          rewrite elem_of_singleton in H. subst.
          eapply pile_impl_allows_gen_x.
          apply pile.
        }
        {
          inversion Hpf.
          apply pwi_pf_ge.
          rewrite elem_of_gset_to_coGset.
          assumption.
        }
      }
      {
        inversion Hpf.
        apply pwi_pf_svs.
      }
      {
        inversion Hpf.
        apply pwi_pf_kt.
      }
      {
        inversion Hpf.
        apply pwi_pf_kta.
      }
    }
  Defined.

  (*
     Γ ⊢ φ[y/x] → ∃x. φ
   *)
  Lemma Ex_quan {Σ : Signature} (Γ : Theory) (ϕ : Pattern) (y : evar) :
    well_formed (patt_exists ϕ) ->
    Γ ⊢i (instantiate (patt_exists ϕ) (patt_free_evar y) ---> (patt_exists ϕ))
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
        [( set_solver )
        |( set_solver )
        |( reflexivity )
        |( reflexivity )
        ]
      ).
    }
  Defined.

  (*
    Γ ⊢ φ
    --------------
    Γ ⊢ ∀x. φ
  *)
  Lemma universal_generalization {Σ : Signature} Γ ϕ x (i : ProofInfo) :
    ProofInfoLe (ExGen := {[x]}, SVSubst := ∅, KT := false, AKT := false) i ->
    well_formed ϕ ->
    Γ ⊢i ϕ using i ->
    Γ ⊢i patt_forall (ϕ^{{evar: x ↦ 0}}) using i.
  Proof.
    intros pile wfϕ Hϕ.
    unfold patt_forall.
    unfold patt_not at 1.
    replace (! ϕ^{{evar: x ↦ 0}})
      with ((! ϕ)^{{evar: x ↦ 0}})
      by reflexivity.
    apply Ex_gen.
    { exact pile. }
    { simpl. set_solver. }
    unfold patt_not.
    apply A_implies_not_not_A_alt.
    { wf_auto2. }
    { exact Hϕ. }
  Defined.

  (*
    Γ ⊢ φ₁ → φ₂
    -----------------------
    Γ ⊢ (∃x. φ₁) → (∃x. φ₂)
  *)
  Lemma ex_quan_monotone {Σ : Signature} Γ x ϕ₁ ϕ₂ (i : ProofInfo)
    (pile : ProofInfoLe (ExGen := {[x]}, SVSubst := ∅, KT := false, AKT := false) i) :
    Γ ⊢i ϕ₁ ---> ϕ₂ using i ->
    Γ ⊢i (exists_quantify x ϕ₁) ---> (exists_quantify x ϕ₂) using i.
  Proof.
    intros H.
    pose proof (Hwf := proved_impl_wf Γ _ (proj1_sig H)).
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

    replace ϕ₂ with (instantiate (ex, ϕ₂^{{evar: x ↦ 0}}) (patt_free_evar x)) at 1.
    2: { unfold instantiate.
        rewrite bevar_subst_evar_quantify_free_evar.
        now do 2 apply andb_true_iff in wfϕ₂ as [_ wfϕ₂].
        reflexivity.
    }
    (* i =  gpi *)
    eapply useBasicReasoning.
    apply Ex_quan.
    abstract (wf_auto2).
  Defined.

  Definition forall_quantify {Σ : Signature} x p : Pattern
  := all, p^{{evar:x↦0}}.

  (*
    Γ ⊢ φ₁ → φ₂
    -----------------------
    Γ ⊢ (∀x. φ₁) → (∀x. φ₂)
  *)
  Lemma all_quan_monotone {Σ : Signature} Γ x ϕ₁ ϕ₂ (i : ProofInfo)
    (pile : ProofInfoLe (ExGen := {[x]}, SVSubst := ∅, KT := false, AKT := false) i) :
    Γ ⊢i ϕ₁ ---> ϕ₂ using i ->
    Γ ⊢i (forall_quantify x ϕ₁) ---> (forall_quantify x ϕ₂) using i.
  Proof.
    intros H.
    unfold forall_quantify.
    unfold patt_forall.
    apply modus_tollens.
    pose proof (Htmp := ex_quan_monotone Γ x (! ϕ₂) (! ϕ₁) i pile).
    unfold exists_quantify in Htmp. mlSimpl in Htmp.
    apply Htmp. clear Htmp.
    apply modus_tollens.
    exact H.
  Defined.

  (*
    Γ ⊢ φ₁ → φ₂
    -----------------------
    Γ ⊢ (∀x. φ₁) → (∀x. φ₂)
  *)
  Lemma forall_monotone {Σ : Signature} Γ x ϕ₁ ϕ₂ (i : ProofInfo)
    (pile : ProofInfoLe (ExGen := {[x]}, SVSubst := ∅, KT := false, AKT := false) i) :
    x ∉ free_evars ϕ₁ ->
    x ∉ free_evars ϕ₂ ->
    Γ ⊢i (evar_open x 0 ϕ₁) ---> (evar_open x 0 ϕ₂) using i ->
    Γ ⊢i (patt_forall ϕ₁) ---> (patt_forall ϕ₂) using i.
  Proof.
    intros Hxn1 Hxn2 H.
    rewrite -[ϕ₁](evar_quantify_evar_open x 0).
    { assumption. }
    { wf_auto2. }
    rewrite -[ϕ₂](evar_quantify_evar_open x 0).
    { assumption. }
    { wf_auto2. }
    apply all_quan_monotone.
    { exact pile. }
    exact H.
  Qed.


  (*
     This is basically [universal_generalization]
    but under an implication.
    Γ ⊢ φ → ψ
    -------------
    Γ ⊢ φ → ∀x. ψ

    I wonder if we could get an iterative version [forall_gen_iter]?
    Like,
    Γ ⊢ φ₁ → ... → φₖ → ψ
    ----------------------------
    Γ ⊢ φ₁ → ... → φₖ → ∀x. ψ
  *)
  Lemma forall_gen {Σ : Signature} Γ ϕ₁ ϕ₂ x (i : ProofInfo):
    evar_is_fresh_in x ϕ₁ ->
    ProofInfoLe (ExGen := {[x]}, SVSubst := ∅, KT := false, AKT := false) i ->
    Γ ⊢i ϕ₁ ---> ϕ₂ using i ->
    Γ ⊢i ϕ₁ ---> forall_quantify x ϕ₂ using i.
  Proof.
    intros Hfr pile Himp.
    pose proof (Hwf := proved_impl_wf _ _ (proj1_sig Himp)).
    pose proof (wfϕ₁ := well_formed_imp_proj1 _ _ Hwf).
    pose proof (wfϕ₂ := well_formed_imp_proj2 _ _ Hwf).

    eapply prf_strenghten_premise_meta_meta.
    4: { apply useBasicReasoning. apply not_not_intro. wf_auto2. }
    1-3: wf_auto2.
    unfold patt_forall.
    apply modus_tollens.

    replace (! ϕ₂^{{evar: x ↦ 0}})
            with ((! ϕ₂)^{{evar: x ↦ 0}})
                  by reflexivity.
    apply Ex_gen.
    { exact pile. }
    { simpl. unfold evar_is_fresh_in in Hfr. clear -Hfr. set_solver. }
    apply modus_tollens; assumption.
  Defined.

Close Scope string_scope.
Close Scope list_scope.
Close Scope ml_scope.
