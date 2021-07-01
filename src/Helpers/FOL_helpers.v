From Coq Require Import ssreflect ssrfun ssrbool.

From Coq Require Import Ensembles Bool.
From MatchingLogic Require Import Syntax Semantics DerivedOperators ProofSystem.

From stdpp Require Import list.

From MatchingLogic.Utils Require Import stdpp_ext.
Import MatchingLogic.Syntax.Notations MatchingLogic.DerivedOperators.Notations.

Open Scope ml_scope.
Section FOL_helpers.

  Context {Σ : Signature}.
  
  Notation "theory ⊢ pattern" := (@ML_proof_system Σ theory pattern) (at level 95, no associativity).

  Lemma A_impl_A (Γ : Theory) (A : Pattern)  :
    (well_formed A) -> Γ ⊢ (A ---> A).
  Proof. 
    intros.
    epose proof (_1 := P2 Γ A (A ---> A) A _ _ _).
    epose proof (_2 := P1 Γ A (A ---> A) _ _).

    epose proof (_3 := Modus_ponens _ _ _ _ _ _2 _1). (*M_p th phi1 phi2 wf_phi1 wf_phi2 phi1_proved phi1->phi2_proved*)
    
    epose proof (_4 := P1 Γ A A _ _).
    
    epose proof (_5 := Modus_ponens Γ _ _ _ _ _4 _3).
    exact _5.
    Unshelve.

    all: auto.
  Qed.

  #[local] Hint Resolve A_impl_A : core.
  
  Lemma P4m (Γ : Theory) (A B : Pattern) :
    (well_formed A) -> (well_formed B) -> Γ ⊢ ((A ---> B) ---> ((A ---> ¬B) ---> ¬A)).
  Proof.
    intros. eapply (Modus_ponens Γ _ _ _ _).
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
  Qed.



  Lemma P4i (Γ : Theory) (A : Pattern) :
    well_formed A -> Γ ⊢ ((A ---> ¬A) ---> ¬A).
  Proof.
    intros. eapply (Modus_ponens _ _ _ _ _).
    - eapply (A_impl_A _ A _). (*In the outdated: A_impl_A = P1*)
    - eapply (P4m _ A A _ _).
      Unshelve.
      all: auto 10.
  Qed.

  Lemma reorder (Γ : Theory) (A B C : Pattern) :
    well_formed A -> well_formed B -> well_formed C -> Γ ⊢ ((A ---> B ---> C) ---> ( B ---> A ---> C)).
  Proof.
    intros.
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
             ++ eapply (A_impl_A _ ABC _).
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
  Qed.

  Lemma reorder_meta (Γ : Theory) {A B C : Pattern} :
    well_formed A -> well_formed B -> well_formed C ->  
    Γ ⊢ (A ---> B ---> C) -> Γ ⊢ (B ---> A ---> C).
  Proof.
    intros.
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
             all:auto.
  Qed.

  Lemma syllogism (Γ : Theory) (A B C : Pattern) :
    well_formed A -> well_formed B -> well_formed C -> Γ ⊢ ((A ---> B) ---> (B ---> C) ---> (A ---> C)).
  Proof.
    intros.
    eapply (reorder_meta _ _ _ _).
    eapply (Modus_ponens _ _ _ _ _).
    - eapply(P1 _ (B ---> C) A _ _).
    - eapply (Modus_ponens _ _ _ _ _).
      + eapply (Modus_ponens _ _ _ _ _).
        * eapply (P2 _ A B C _ _ _).
        * eapply (P1 _ ((A ---> B ---> C) ---> (A ---> B) ---> A ---> C) (B ---> C) _ _).
      + eapply (P2 _ (B ---> C) (A ---> B ---> C) ((A ---> B) ---> A ---> C) _ _ _).
        Unshelve.
        all: auto 10.
  Qed.

  #[local] Hint Resolve syllogism : core.
  
  Lemma syllogism_intro (Γ : Theory) (A B C : Pattern) :
    well_formed A -> well_formed B -> well_formed C -> Γ ⊢ (A ---> B) -> Γ ⊢ (B ---> C) -> Γ ⊢ (A ---> C).
  Proof.
    intros.
    eapply (Modus_ponens _ _ _ _ _).
    - exact H2.
    - eapply (Modus_ponens _ _ _ _ _).
      + exact H3.
      + eapply (reorder_meta _ _ _ _). exact (syllogism _ A B C H H0 H1).
        Unshelve.
        all: auto.
  Qed.

  #[local] Hint Resolve syllogism_intro : core.
  
  Lemma modus_ponens (Γ : Theory) ( A B : Pattern) :
    well_formed A -> well_formed B -> Γ ⊢ (A ---> (A ---> B) ---> B).
  Proof.
    intros.
    eapply (Modus_ponens _ _ _ _ _).
    - eapply (P1 _ A (A ---> B) _ _).
    - eapply (Modus_ponens _ _ _ _ _).
      + eapply (Modus_ponens _ _ _ _ _).
        * eapply (A_impl_A _ (A ---> B) _).
        * eapply (P2 _ (A ---> B) A B _ _ _).
      + eapply (reorder_meta _ _ _ _).
        * eapply (syllogism _ A ((A ---> B) ---> A) ((A ---> B) ---> B) _ _ _).
          Unshelve.
          all: auto 10.
  Qed.

  #[local] Hint Resolve modus_ponens : core.
  
  Lemma not_not_intro (Γ : Theory) (A : Pattern) :
    well_formed A -> Γ ⊢ (A ---> ¬(¬A)).
  Proof.
    intros.
    assert(@well_formed Σ Bot).
    shelve.
    exact (modus_ponens _ A Bot H H0).
    Unshelve.
    all: auto.
  Qed.

  #[local] Hint Resolve not_not_intro : core.

  Lemma deduction (Γ : Theory) (A B : Pattern) :
    well_formed A -> well_formed B -> Γ ⊢ A -> Γ ⊢ B -> Γ ⊢ (A ---> B).
  Proof.
    intros.
    eapply (Modus_ponens _ _ _ _ _).
    - exact H2.
    - eapply (P1 _ B A _ _).
      Unshelve.
      all: auto.
  Qed.

  Lemma P4_intro (Γ : Theory) (A B : Pattern)  :
    well_formed A -> well_formed B -> 
    Γ ⊢ ((¬ B) ---> (¬ A)) -> Γ ⊢ (A ---> B).
  Proof.
    intros.
    epose (Modus_ponens Γ _ _ _ _ H1 (P4m Γ (¬ B) (¬ A) _ _)).
    epose (P1 Γ (¬ ¬A) (¬ B) _ _).
    epose (syllogism_intro Γ (¬ (¬ A)) (¬ B ---> ¬ (¬ A)) (¬ (¬ B)) _ _ _ m0 m).
    epose (not_not_intro Γ A _).
    epose (not_not_intro Γ B _).
    epose (syllogism_intro Γ A (¬ (¬ A)) (¬ (¬ B)) _ _ _ m2 m1).
    unfold patt_not in m4.
    epose (P3 Γ B _).
    epose (syllogism_intro Γ A ((B ---> Bot) ---> Bot) B _ _ _ m4 m5).
    exact m6.

    Unshelve.
    all: auto.
    auto 10.
  Qed.


  Lemma P4 (Γ : Theory) (A B : Pattern)  :
    well_formed A -> well_formed B -> 
    Γ ⊢ (((¬ A) ---> (¬ B)) ---> (B ---> A)).
  Proof.
    intros.
    epose (P3 Γ A _).
    epose (P1 Γ (((A ---> Bot) ---> Bot) ---> A) B _ _).
    epose (P2 Γ (B) ((A ---> Bot) ---> Bot) (A) _ _ _).
    epose (Modus_ponens Γ _ _ _ _ m m0).
    epose (Modus_ponens Γ _ _ _ _ m2 m1).
    epose (P1 Γ ((B ---> (A ---> Bot) ---> Bot) ---> B ---> A) ((A ---> Bot) ---> (B ---> Bot)) _ _ ).
    epose (Modus_ponens Γ _ _ _ _ m3 m4).
    epose (P2 Γ ((A ---> Bot) ---> (B ---> Bot)) (B ---> (A ---> Bot) ---> Bot) (B ---> A) _ _ _).
    epose (Modus_ponens Γ _ _ _ _ m5 m6).
    epose (reorder Γ (A ---> Bot) (B) (Bot) _ _ _).
    eapply (Modus_ponens Γ _ _ _ _ m8 m7).
    Unshelve.
    all: auto 10.
  Qed.

  Lemma conj_intro (Γ : Theory) (A B : Pattern) :
    well_formed A -> well_formed B -> Γ ⊢ (A ---> B ---> (A and B)).
  Proof.
    intros.
    epose(tB := (A_impl_A Γ B _)).
    epose(t1 := Modus_ponens Γ _ _ _ _ (P2 _ (¬(¬A) ---> ¬B) A Bot _ _ _)
                             (P1 _ _ B _ _)).
    epose(t2 := Modus_ponens Γ _ _ _ _  (reorder_meta _ _ _ _ (P4 _ (¬A) B _ _))
                             (P1 _ _ B _ _)).
    epose(t3'' := Modus_ponens Γ _ _ _ _ (P1 _ A (¬(¬A) ---> ¬B) _ _)
                               (P1 _ _ B _ _)).
    epose(t4 := Modus_ponens Γ _ _ _ _ tB
                             (Modus_ponens Γ _ _ _ _ t2
                                           (P2 _ B B _ _ _ _))).
    epose(t5'' := 
            Modus_ponens Γ _ _ _ _ t4
                         (Modus_ponens Γ _ _ _ _ t1
                                       (P2 _ B ((¬(¬A) ---> ¬B) ---> ¬A)
                                           (((¬(¬A) ---> ¬B) ---> A) ---> ¬(¬(¬A) ---> ¬B)) _ _ _))).
    
    epose(tA := (P1 Γ A B) _ _).
    epose(tB' := Modus_ponens Γ _ _ _ _ tB
                              (P1 _ (B ---> B) A _ _)).
    epose(t3' := Modus_ponens Γ _ _ _ _ t3''
                              (P2 _ B A ((¬(¬A) ---> ¬B) ---> A) _ _ _)).
    epose(t3 := Modus_ponens Γ _ _ _ _ t3'
                             (P1 _ ((B ---> A) ---> B ---> (¬ (¬ A) ---> ¬ B) ---> A) A _ _)).
    epose(t5' := Modus_ponens Γ _ _ _ _ t5''
                              (P2 _ B ((¬(¬A) ---> ¬B) ---> A) (¬(¬(¬A) ---> ¬B)) _ _ _)).
    epose(t5 := Modus_ponens Γ _ _ _ _ t5' 
                             (P1 _ ((B ---> (¬ (¬ A) ---> ¬ B) ---> A) ---> B ---> ¬ (¬ (¬ A) ---> ¬ B))
                                 A _ _)).
    epose(t6 := Modus_ponens Γ _ _ _ _ tA
                             (Modus_ponens Γ _ _ _ _ t3
                                           (P2 _ A (B ---> A) (B ---> (¬(¬A) ---> ¬B) ---> A) _ _ _))).
    epose(t7 := Modus_ponens Γ _ _ _ _ t6 
                             (Modus_ponens Γ _ _ _ _ t5 
                                           (P2 _ A (B ---> (¬(¬A) ---> ¬B) ---> A) (B ---> ¬(¬(¬A) ---> ¬B)) _ _ _))).
    unfold patt_and.  unfold patt_or.
    exact t7.
    Unshelve.
    all: auto 10.
  Qed.


  Lemma conj_intro_meta (Γ : Theory) (A B : Pattern) :
    well_formed A -> well_formed B -> Γ ⊢ A -> Γ ⊢ B -> Γ ⊢ (A and B).
  Proof.
    intros.
    eapply (Modus_ponens _ _ _ _ _).
    - exact H2.
    - eapply (Modus_ponens _ _ _ _ _).
      + exact H1.
      + exact (conj_intro _ A B H H0).
        Unshelve.
        all: auto.
  Qed.
  
  (* Lemma conj_intro_meta_e (Γ : Theory) (A B : Pattern) : *) 
  Definition conj_intro_meta_e := conj_intro_meta.    (*The same as conj_intro_meta*)

  Lemma disj (Γ : Theory) (A B : Pattern) :
    well_formed A -> well_formed B -> Γ ⊢ (A ---> B ---> (A or B)).
  Proof.
    intros. unfold patt_or.
    
    epose proof (t1 := (P1 Γ B (¬A) _ _)).
    
    epose proof (t2 := (P1 Γ (B ---> (¬A ---> B)) A _ _)).
    
    epose proof (t3 := Modus_ponens Γ _ _ _ _ t1 t2).
    
    exact t3.
    Unshelve.
    all: auto 10.
  Qed.

  Lemma disj_intro (Γ : Theory) (A B : Pattern) :
    well_formed A -> well_formed B -> Γ ⊢ A -> Γ ⊢ B -> Γ ⊢ (A or B).
  Proof.
    intros.
    eapply (Modus_ponens _ _ _ _ _).
    - exact H2.
    - eapply (Modus_ponens _ _ _ _ _).
      + exact H1.
      + exact (disj _ A B H H0).
        Unshelve.
        all: auto.
  Qed.

  Lemma syllogism_4_meta (Γ : Theory) (A B C D : Pattern) :
    well_formed A -> well_formed B -> well_formed C -> well_formed D ->
    Γ ⊢ (A ---> B ---> C) -> Γ ⊢ (C ---> D) -> Γ ⊢ (A ---> B ---> D).
  Proof.
    intros.
    eapply (Modus_ponens _ _ _ _ _).
    - exact H3.
    - eapply (Modus_ponens _ _ _ _ _).
      + eapply (Modus_ponens _ _ _ _ _).
        * eapply (Modus_ponens _ _ _ _ _).
          -- eapply (Modus_ponens _ _ _ _ _).
             ++ exact H4.
             ++ eapply (P1 _ (C ---> D) B _ _).
          -- eapply (P2 _ B C D _ _ _).
        * eapply (P1 _ ((B ---> C) ---> B ---> D) A _ _).
      + eapply (P2 _ A (B ---> C) (B ---> D) _ _ _).
        Unshelve.
        all: auto.
  Qed.

  Lemma bot_elim (Γ : Theory) (A : Pattern) :
    well_formed A -> Γ ⊢ (Bot ---> A).
  Proof.
    intros.
    eapply (Modus_ponens _ _ _ _ _).
    - eapply (Modus_ponens _ _ _ _ _).
      + eapply (Modus_ponens _ _ _ _ _).
        * eapply (Modus_ponens _ _ _ _ _).
          -- eapply (P1 _ Bot Bot _ _).
          -- eapply (P2 _ Bot Bot Bot _ _ _).
        * eapply (P4 _ Bot Bot _ _).
      + eapply (P1 _ (Bot ---> Bot) (A ---> Bot) _ _).
    - eapply (P4 _ A Bot _ _).
      Unshelve.
      all: auto.
  Qed.

  Lemma modus_ponens' (Γ : Theory) (A B : Pattern) :
    well_formed A -> well_formed B -> Γ ⊢ (A ---> (¬B ---> ¬A) ---> B).
  Proof.
    intros.
    assert(well_formed (¬ B ---> ¬ A)).
    shelve.
    exact (reorder_meta Γ H1 H H0 (P4 _ B A H0 H)).
    Unshelve.
    all: auto.
  Qed.

  Lemma disj_right_intro (Γ : Theory) (A B : Pattern) :
    well_formed A -> well_formed B -> Γ ⊢ (B ---> (A or B)).
  Proof.
    intros.
    assert(well_formed (¬A)).
    shelve.
    exact (P1 _ B (¬A) H0 H1).
    Unshelve.
    all: auto.
  Qed.

  #[local] Hint Resolve disj_right_intro : core.
  
  Lemma disj_left_intro (Γ : Theory) (A B : Pattern) :
    well_formed A -> well_formed B -> Γ ⊢ (A ---> (A or B)).
  Proof.
    intros.
    eapply (syllogism_4_meta _ _ _ _ _ _ _ _ _ (modus_ponens _ A Bot _ _) (bot_elim _ B _)).
    Unshelve.
    all: auto.
  Qed.

  #[local] Hint Resolve disj_left_intro : core.

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
  Qed.

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
  Qed.

  Lemma not_not_elim (Γ : Theory) (A : Pattern) :
    well_formed A -> Γ ⊢ (¬(¬A) ---> A).
  Proof.
    intros.
    unfold patt_not.
    exact (P3 Γ A H).
  Qed.

  #[local] Hint Resolve not_not_elim : core.

  Lemma not_not_elim_meta Γ A :
    well_formed A ->
    Γ ⊢ (¬ ¬ A) ->
    Γ ⊢ A.
  Proof.
    intros wfA nnA.
    pose proof (H := not_not_elim Γ A wfA).
    eapply Modus_ponens. 4: apply H.
    all: auto.
  Qed.

  #[local] Hint Resolve not_not_elim_meta : core.

  Lemma double_neg_elim (Γ : Theory) (A B : Pattern) :
    well_formed A -> well_formed B -> Γ ⊢ (((¬(¬A)) ---> (¬(¬B))) ---> (A ---> B)).
  Proof.
    intros.
    eapply (syllogism_intro _ _ _ _ _ _ _).
    - eapply (P4 _ (¬A) (¬B) _ _).
    - eapply (P4 _ B A _ _).
      Unshelve.
      all: auto.
  Qed.

  Lemma double_neg_elim_meta (Γ : Theory) (A B : Pattern) :
    well_formed A -> well_formed B -> 
    Γ ⊢ ((¬(¬A)) ---> (¬(¬B))) -> Γ ⊢ (A ---> B).
  Proof.
    intros.
    eapply (Modus_ponens _ _ _ _ _).
    - exact H1.
    - exact (double_neg_elim _ A B H H0).
      Unshelve.
      all: auto.
  Qed.

  Lemma P4_rev_meta (Γ : Theory) (A B : Pattern) :
    well_formed A -> well_formed B -> Γ ⊢ (A ---> B) -> Γ ⊢ ((A ---> B) ---> (¬B ---> ¬A)).
  Proof.
    intros.
    eapply (deduction _ _ _ _ _).
    - exact H1.
    - eapply (Modus_ponens _ _ _ _ _).
      + eapply (syllogism_intro _ _ _ _ _ _ _).
        * eapply (syllogism_intro _ _ _ _ _ _ _).
          -- eapply (not_not_elim _ A _).
          -- exact H1.
        * eapply (not_not_intro _ B _).
      + eapply (P4 _ (¬A) (¬B) _ _).
        Unshelve.
        all: auto.
  Qed.

  Lemma P4_rev_meta' (Γ : Theory) (A B : Pattern) :
    well_formed A ->
    well_formed B ->
    Γ ⊢ (A ---> B) ->
    Γ ⊢ (¬B ---> ¬A).
  Proof.
    intros wfA wfB AimpB.
    pose proof (H := P4_rev_meta Γ A B wfA wfB AimpB).
    eapply Modus_ponens.
    4: apply H.
    all: auto.
  Qed.

  #[local] Hint Resolve P4_rev_meta' : core.
  
  Lemma P4m_neg (Γ : Theory) (A B : Pattern) :
    well_formed A -> well_formed B -> Γ ⊢ ((¬B ---> ¬A) ---> (A ---> ¬B) --->  ¬A).
  Proof.
    intros.
    epose proof (PT := (P4 Γ B A _ _)).
    eapply (syllogism_intro _ _ _ _ _ _ _).
    - exact PT.
    - eapply (P4m _ _ _ _ _).
      Unshelve.
      all: auto.
  Qed.

  Lemma not_not_impl_intro_meta (Γ : Theory) (A B : Pattern) :
    well_formed A -> well_formed B -> Γ ⊢ (A ---> B) -> Γ ⊢ ((¬¬A) ---> (¬¬B)).
  Proof.
    intros.
    epose proof (NN1 := not_not_elim Γ A _).
    epose proof (NN2 := not_not_intro Γ B _).
    
    epose proof (S1 := syllogism_intro _ _ _ _ _ _ _ H1 NN2).
    
    epose proof (S2 := syllogism_intro _ _ _ _ _ _ _ NN1 S1).
    exact S2.
    Unshelve.
    all: auto.
  Qed.

  Lemma not_not_impl_intro (Γ : Theory) (A B : Pattern) :
    well_formed A -> well_formed B -> Γ ⊢ ((A ---> B) ---> ((¬¬A) ---> (¬¬B))).
  Proof.
    intros.
    
    epose (S1 := syllogism Γ (¬¬A) A B _ _ _).
    
    epose (MP1 := Modus_ponens _ (¬ (¬ A) ---> A) ((A ---> B) ---> ¬ (¬ A) ---> B) _ _ (not_not_elim _ A _) S1).
    
    epose(NNB := not_not_intro Γ B _).

    epose(P1 := (P1 Γ (B ---> ¬ (¬ B)) (¬¬A) _ _)).
    
    epose(MP2 := Modus_ponens _ _ _ _ _ NNB P1).
    
    epose(P2 := (P2 Γ (¬¬A) B (¬¬B) _ _ _)).
    
    epose(MP3 := Modus_ponens _ _ _ _ _ MP2 P2).
    
    eapply syllogism_intro with (B := (¬ (¬ A) ---> B)).
    - shelve.
    - shelve.
    - shelve.
    - assumption.
    - assumption.
      Unshelve.
      all: auto 10.
  Qed.


  Lemma contraposition (Γ : Theory) (A B : Pattern) : 
    well_formed A -> well_formed B -> 
    Γ ⊢ ((A ---> B) ---> ((¬ B) ---> (¬ A))).
  Proof.
    intros.
    epose proof (P4 Γ (¬ A) (¬ B) _ _) as m.
    apply syllogism_intro with (B := (¬ (¬ A) ---> ¬ (¬ B))).
    - shelve.
    - shelve.
    - shelve.
    - eapply (not_not_impl_intro _ _ _ _ _).
    - exact m. (* apply (P4 _ _ _). shelve. shelve. *)
      Unshelve.
      all: auto.
  Qed.

  Lemma or_comm_meta (Γ : Theory) (A B : Pattern) :
    well_formed A -> well_formed B ->
    Γ ⊢ (A or B) -> Γ ⊢ (B or A).
  Proof.
    intros. unfold patt_or in *.
    
    epose proof (P4 := (P4 Γ A (¬B) _ _)).
    
    epose proof (NNI := not_not_intro Γ B _).
    
    epose proof (SI := syllogism_intro Γ _ _ _ _ _ _ H1 NNI).
    
    eapply (Modus_ponens _ _ _ _ _).
    - exact SI.
    - exact P4.
      Unshelve.
      all: auto.
  Qed.

  Lemma A_implies_not_not_A_alt (Γ : Theory) (A : Pattern) :
    well_formed A -> Γ ⊢ A -> Γ ⊢ (¬( ¬A )).
  Proof.
    intros. unfold patt_not.
    epose proof (NN := not_not_intro Γ A _).
    
    epose proof (MP := Modus_ponens _ _ _ _ _ H0 NN).
    assumption.
    Unshelve.
    all: auto.
  Qed.

  Lemma P5i (Γ : Theory) (A B : Pattern) :
    well_formed A -> well_formed B -> Γ ⊢ (¬ A ---> (A ---> B)).
  Proof.
    intros.
    
    epose proof (Ax1 := (P1 Γ (¬A) (¬B) _ _)).
    
    epose proof (Ax2 := (P4 Γ B A _ _)).
    
    epose proof (TRANS := syllogism_intro _ _ _ _ _ _ _ Ax1 Ax2).
    assumption.
    Unshelve.
    all: auto.
  Qed.

  Lemma false_implies_everything (Γ : Theory) (phi : Pattern) :
    well_formed phi -> Γ ⊢ (Bot ---> phi).
  Proof.
    intro.
    
    epose proof (B_B := (A_impl_A Γ Bot _)).
    epose proof (P4 := P5i Γ Bot phi _ _).
    
    eapply (Modus_ponens _ _ _ _ _) in P4.
    - assumption.
    - assumption.
      Unshelve.
      all: auto.
  Qed.


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
Qed. *)

  (* Notation "Γ ⊢ pattern" := (@ML_proof_system Σ Γ pattern) (at level 95, no associativity). *)
  Check ⊥.

  (*Was an axiom in AML_definition.v*)
  Lemma Prop_bot (Γ : Theory) (C : Application_context) :
    Γ ⊢ ((subst_ctx C patt_bott) ---> patt_bott).
  Proof.
    induction C.
    - simpl. eapply false_implies_everything. shelve.
    - simpl. epose proof (m0 := Framing_left Γ (subst_ctx C Bot) (Bot) p IHC).
      epose proof (m1 := syllogism_intro Γ _ _ _ _ _ _ (m0) (Prop_bott_left Γ p Prf)). exact m1.
    - simpl. epose proof (m2 := Framing_right Γ (subst_ctx C Bot) (Bot) p IHC).

      epose proof (m3 := syllogism_intro Γ _ _ _ _ _ _ (m2) (Prop_bott_right Γ p Prf)). exact m3.
      
      Unshelve.
      all: auto.
  Qed.

  (*Was an axiom in AML_definition.v*)
  Lemma Framing (Γ : Theory) (C : Application_context) (A B : Pattern):
    well_formed A -> well_formed B -> Γ ⊢ (A ---> B) -> Γ ⊢ ((subst_ctx C A) ---> (subst_ctx C B)).
  Proof.
    induction C; intros.
    - simpl. exact H1.
    - simpl. epose (Framing_left Γ (subst_ctx C A) (subst_ctx C B) p (IHC _ _ H1)). exact m.
    - simpl. epose (Framing_right Γ (subst_ctx C A) (subst_ctx C B) p (IHC _ _ H1)). exact m.
      Unshelve.
      all: auto.
  Qed.

  Lemma A_implies_not_not_A_ctx (Γ : Theory) (A : Pattern) (C : Application_context) :
    well_formed A -> Γ ⊢ A -> Γ ⊢ (¬ (subst_ctx C ( ¬A ))).
  Proof.
    intros.
    epose proof (ANNA := A_implies_not_not_A_alt Γ _ _ H0).
    replace (¬ (¬ A)) with ((¬ A) ---> Bot) in ANNA. 2: auto.
    epose proof (EF := Framing _ C (¬ A) Bot _ _ ANNA).
    epose proof (PB := Prop_bot Γ C).
    
    epose (TRANS := syllogism_intro _ _ _ _ _ _ _ EF PB).
    
    unfold patt_not.
    assumption.
    Unshelve.
    2,4:assert (@well_formed Σ (¬ A)).
    6,7:assert (@well_formed Σ (Bot)).
    all: auto.
  Qed.


  Lemma A_implies_not_not_A_alt_Γ (G : Theory) (A : Pattern) :
    well_formed A -> G ⊢ A -> G ⊢ (¬( ¬A )).
  Proof.
    intros. unfold patt_not.
    epose proof (NN := not_not_intro G A _).
    
    epose proof (MP := Modus_ponens G _ _ _ _ H0 NN).
    
    assumption.
    Unshelve.
    all: auto.
  Qed.

  (* Lemma equiv_implies_eq (Γ : Theory) (A B : Pattern) :
  well_formed A -> well_formed B -> Γ ⊢ (A <---> B) -> Γ ⊢ ()
   *) (*Need equal*)
  
  (* Lemma equiv_implies_eq_Γ *)

  (*...Missing some lemmas because of the lack of defidness definition...*)

  Lemma ctx_bot_prop (Γ : Theory) (C : Application_context) (A : Pattern) :
    well_formed A -> Γ ⊢ (A ---> Bot) -> Γ ⊢ (subst_ctx C A ---> Bot).
  Proof.
    intros.
    epose proof (FR := Framing Γ C A Bot _ _ H0).
    epose proof (BPR := Prop_bot Γ C).
    
    epose proof (TRANS := syllogism_intro _ _ _ _ _ _ _ FR BPR).
    
    assumption.
    Unshelve.
    4: assert (@well_formed Σ (Bot)).
    all: auto.
  Qed.

  Lemma not_not_A_ctx_implies_A (Γ : Theory) (C : Application_context) (A : Pattern):
    well_formed A -> Γ ⊢ (¬ (subst_ctx C ( ¬A ))) -> Γ ⊢ A.
  Proof.
    intros.
    unfold patt_not in H0 at 1.
    
    epose (BIE := false_implies_everything Γ (subst_ctx C Bot) _).
    
    epose (TRANS := syllogism_intro _ _ _ _ _ _ _ H0 BIE).
    
    induction C.
    - simpl in TRANS.
      epose (NN := not_not_elim Γ A _).
      epose (MP := Modus_ponens _ _ _ _ _ TRANS NN). assumption.
    - eapply IHC.
      Unshelve.
      all: auto.
  Abort.

  Definition empty_Γ := Empty_set (@Pattern Σ).
  Lemma exclusion (G : Theory) (A : Pattern) :
    well_formed A -> G ⊢ A -> G ⊢ (A ---> Bot) -> G ⊢ Bot.
  Proof.
    intros.
    epose(Modus_ponens G A Bot _ _ H0 H1).
    assumption.
    Unshelve.
    all: auto.
  Qed.

  Lemma modus_tollens Γ A B :
    well_formed A ->
    well_formed B ->
    Γ ⊢ (A ---> B) ->
    Γ ⊢ (¬B ---> ¬A).
  Proof.
    intros. unfold patt_not.
  Abort.

  Lemma A_impl_not_not_B Γ A B :
    well_formed A ->
    well_formed B ->
    Γ ⊢ ((A ---> ¬¬B) ---> (A ---> B)).
  Proof.
    intros.
    assert (Γ ⊢ (¬¬B ---> B)) by auto.
    assert (Γ ⊢ ((A ---> ¬¬B) ---> (¬¬B ---> B) ---> (A ---> B))) by auto.
    apply reorder_meta in H2; auto.
    eapply Modus_ponens. 4: apply H2. all: auto 10.
  Qed.

  #[local] Hint Resolve A_impl_not_not_B : core.

  Definition wf (l : list Pattern) := fold_right andb true (map well_formed l).

  Lemma well_formed_foldr g xs :
    well_formed g ->
    wf xs ->
    well_formed (foldr patt_imp g xs).
  Proof.
    intros wfg wfxs.
    induction xs.
    - simpl. exact wfg.
    - simpl. unfold wf in wfxs. simpl in wfxs.
      apply andb_prop in wfxs. destruct wfxs. auto.
  Qed.

  #[local] Hint Resolve well_formed_foldr : core.

  Lemma wf_take n xs :
    wf xs ->
    wf (take n xs).
  Proof.
    unfold wf. intros H.
    rewrite map_take.
    Search
    Search foldr andb.
  
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
  Qed.


  Fixpoint prf_weaken_conclusion_meta_iter Γ l g g'
           (wfl : wf l) (wfg : well_formed g) (wfg' : well_formed g') (gimpg' : Γ ⊢ (g ---> g')) :
    Γ ⊢ ((fold_right patt_imp g l) ---> (fold_right patt_imp g' l))
    :=
      (match l as a return
             (Γ ⊢ (g ---> g')) ->
             wf a ->
             Γ ⊢ ((fold_right patt_imp g a) ---> (fold_right patt_imp g' a))
       with
      | [] => fun gimpg' wfl => gimpg'
      | cons x xs =>
        fun gimpg' wfl =>
          let wfx := (proj1 (andb_prop _ _ wfl)) in
          let wfxs := (proj2 (andb_prop _ _ wfl)) in
          (prf_weaken_conclusion_meta
             Γ x (foldr patt_imp g xs) (foldr patt_imp g' xs)
             wfx
             (well_formed_foldr _ _ wfg wfxs)
             (well_formed_foldr _ _ wfg' wfxs)
             (prf_weaken_conclusion_meta_iter Γ xs g g' wfxs wfg wfg' gimpg')
          )
            
       end) gimpg' wfl.

  Lemma prf_weaken_conclusion_meta_iter_meta Γ l g g':
    wf l ->
    well_formed g ->
    well_formed g' ->
    Γ ⊢ (g ---> g') ->
    Γ ⊢ (fold_right patt_imp g l) ->
    Γ ⊢ (fold_right patt_imp g' l).
  Proof.
    intros wfl wfg wfg' gimpg' H.
    eapply Modus_ponens. 4: apply prf_weaken_conclusion_meta_iter. 3: apply H.
    all: auto using well_formed_foldr.
  Qed.
    
  Lemma prf_weaken_conclusion_meta_meta Γ A B B' :
    well_formed A ->
    well_formed B ->
    well_formed B' ->
    Γ ⊢ (B ---> B') ->
    Γ ⊢ (A ---> B) ->
    Γ ⊢ (A ---> B').
  Proof.
    intros.
    eapply Modus_ponens. 4: apply prf_weaken_conclusion_meta. 3: apply H3. all: auto.
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
  Qed.

  Check nth_error.
  Search list_lookup.
  Search list nat.

  Search nth_error Some.
  Lemma prf_strenghten_premise_meta_iter Γ l n h h' g :
    wf l ->
    well_formed h ->
    well_formed h' ->
    well_formed g ->
    l !! n = Some h ->
    Γ ⊢ (h' ---> h) ->
    Γ ⊢ ((fold_right patt_imp g l) ---> (fold_right patt_imp g (<[n := h']> l))).
  Proof.
    intros wfl wfh wfh' wfg ln H.
    Search list_lookup Some.
    pose proof (Hn := lookup_lt_Some _ _ _ ln).
    Check take_drop.

    rewrite <- (take_drop n l).
    rewrite <- (take_drop n l) in ln. Search app "!!".
    rewrite lookup_app_r in ln.
    { apply firstn_le_length.  }
    assert (Hlentake: length (take n l) + 0 = n).
    { rewrite firstn_length. lia. }
    rewrite <- Hlentake at 3.
    (*erewrite <- (take_drop (S n) l).*)
    Search list_insert app.
    simpl.
    rewrite insert_app_r.
    repeat rewrite foldr_app.
    remember (foldr patt_imp g (drop n l)) as g1.
    remember (foldr patt_imp g (<[0:=h']> (drop n l))) as g2.
    apply prf_weaken_conclusion_meta_iter.
    {  admit. }
    { admit. }
    { admit. }
    remember (drop n l) as l'.
    destruct l'.
    { simpl in *. subst. auto. }
    simpl in Heqg1. simpl in Heqg2.
    assert (p = h).
    {
      assert (Hn0: n - length (take n l) = 0).
      { pose proof (firstn_le_length n l). lia. }
      rewrite Hn0 in ln.
      simpl in ln.
      inversion ln.
      reflexivity.
    }
    subst p.
    subst g1 g2.
    apply prf_strenghten_premise_meta; auto.
  Admitted.
  

    
  Lemma A_impl_not_not_B_meta Γ A B :
    well_formed A ->
    well_formed B ->
    Γ ⊢ (A ---> ¬¬B) ->
    Γ ⊢ (A ---> B).
  Proof.
    intros.
    eapply Modus_ponens.
    4: { apply A_impl_not_not_B; auto. }
    all: auto.
  Qed.

  Lemma pf_conj_elim_l Γ A B :
    well_formed A ->
    well_formed B ->
    Γ ⊢ (A and B ---> A).
  Proof.
    intros. unfold patt_and. unfold patt_not at 1.

    assert (Γ ⊢ (¬ A ---> (¬ A or ¬ B))) by auto.
    assert (Γ ⊢ ((¬ A or ¬ B) ---> (¬ A or ¬ B ---> ⊥) ---> ⊥)) by auto.
    assert (Γ ⊢ (¬ A ---> ((¬ A or ¬ B ---> ⊥) ---> ⊥))).
    { eapply syllogism_intro. 5: apply H2. 4: apply H1. all: auto. }
    epose proof (reorder_meta _ _ _ _ H3).
    apply A_impl_not_not_B_meta; auto.
    Unshelve.
    all: auto.
  Qed.

  Lemma pf_conj_elim_r Γ A B :
    well_formed A ->
    well_formed B ->
    Γ ⊢ (A and B ---> B).
  Proof.
    intros. unfold patt_and. unfold patt_not at 1.

    assert (Γ ⊢ (¬ B ---> (¬ A or ¬ B))) by auto.
    assert (Γ ⊢ ((¬ A or ¬ B) ---> (¬ A or ¬ B ---> ⊥) ---> ⊥)) by auto.
    assert (Γ ⊢ (¬ B ---> ((¬ A or ¬ B ---> ⊥) ---> ⊥))).
    { eapply syllogism_intro. 5: apply H2. 4: apply H1. all: auto. }
    epose proof (reorder_meta _ _ _ _ H3).
    apply A_impl_not_not_B_meta; auto.
    Unshelve.
    all: auto.
  Qed.

  Lemma pf_conj_elim_l_meta Γ A B :
    well_formed A ->
    well_formed B ->
    Γ ⊢ (A and B) ->
    Γ ⊢ A.
  Proof.
    intros.
    eapply Modus_ponens.
    4: apply pf_conj_elim_l.
    3: apply H1.
    all: auto.
  Qed.
  
  Lemma pf_conj_elim_r_meta Γ A B :
    well_formed A ->
    well_formed B ->
    Γ ⊢ (A and B) ->
    Γ ⊢ B.
  Proof.
    intros.
    eapply Modus_ponens.
    4: apply pf_conj_elim_r.
    3: apply H1.
    all: auto.
  Qed.

  Lemma A_or_notA Γ A :
    well_formed A ->
    Γ ⊢ (A or ¬ A).
  Proof.
    intros wfA.
    unfold patt_or.
    auto.
  Qed.

  Lemma P4m_meta (Γ : Theory) (A B : Pattern) :
    well_formed A ->
    well_formed B ->
    Γ ⊢ (A ---> B) ->
    Γ ⊢ (A ---> ¬B) ->
    Γ ⊢ ¬A.
  Proof.
    intros wfA wfB AimpB AimpnB.
    Check P4m.
    pose proof (H1 := P4m Γ A B wfA wfB).
    assert (H2 : Γ ⊢ (A ---> ¬ B) ---> ¬ A).
    { eapply Modus_ponens. 4: apply H1. all: auto. }
    eapply Modus_ponens. 4: apply H2. all: auto.
  Qed.


  Lemma test_lemma Γ A B A' B':
    well_formed A ->
    well_formed B ->
    well_formed A' ->
    well_formed B' ->
    Γ ⊢ (A' ---> B') ->
    Γ ⊢ (A ---> A') ->
    Γ ⊢ (B' ---> B) ->
    Γ ⊢ (A ---> B).
  Proof.
    intros wfA wfB wfA' wfB' A'impB' AimpA' B'impB.
    (* A term with a hole, representing the goal. It will be hidden inside the 'our' context. *)
    (* Another existential hypotheses that our goal will have will be the well_formed-ness assumptions. *)
    epose (G1 := ?[g1] : (Γ ⊢ (A ---> B))).

    (* Now we try to simulate the following apply: *)
    (* eapply (prf_weaken_conclusion_meta_meta Γ _ _ _ _ _ _ B'impB). *)

    (* First, lets create a new goal *)
    epose (G2 := ?[g2] : (Γ ⊢ (A ---> B'))).
    (* Now, lets try to unify G1 with this. *)
    Check (prf_weaken_conclusion_meta_meta Γ A B' B wfA wfB' wfB B'impB G2).
    (*instantiate (g1 := (prf_weaken_conclusion_meta_meta Γ A B' B wfA wfB' wfB B'impB G2)).*)
    unify ?g1 (prf_weaken_conclusion_meta_meta Γ A B' B wfA wfB' wfB B'impB G2).
    Fail unify ?Goal0 I.
    (* Ok, it works, but: unify renamed our question mark variables.
       I can see two possible workarounds: (1) match on the 'current goal' hypothesis and derive the
       variable from the match; (2) remember in the context the terms to unify but do not unify them
       until the very end.
     *)

    (* Also, we probably want the context to be part of the goal, and not part of the Coq's context. *)
    move: G2.
    (* But then, how do we remember the name of the unification variable? *)
    (* Also:
       '''Error: ?Goal is a generated name. Only user-given names for existential variables can be referenced.
          To give a user name to an existential variable, introduce it with the ?[name] syntax.'''
       So it looks we need to defer the unification to later. And that is ugly, because we do not get
       checking when doing the interactive proof.
     *)
  Abort.

  Record MyGoal : Type := mkMyGoal { mgTheory : Theory; mgHypotheses: list Pattern; mgConclusion : Pattern }.

  Definition MyGoal_from_goal (Γ : Theory) (goal : Pattern) : MyGoal := mkMyGoal Γ nil goal.

  Notation "[ G ⊢ l ==> g ]" := (mkMyGoal G l g).

  Compute (MyGoal_from_goal (Empty_set _) patt_bott).

  Check fold_right.
  Coercion of_MyGoal (MG : MyGoal) : Prop := (mgTheory MG) ⊢ (fold_right patt_imp (mgConclusion MG) (mgHypotheses MG)).

  Compute of_MyGoal (mkMyGoal (Empty_set _) [(patt_bound_evar 1); (patt_bound_evar 2)] (patt_bound_evar 3)).

  Lemma of_MyGoal_from_goal Γ (goal : Pattern) : of_MyGoal (MyGoal_from_goal Γ goal) <-> (Γ ⊢ goal).
  Proof. reflexivity. Qed.

  Lemma MyGoal_intro (Γ : Theory) (l : list Pattern) (x g : Pattern):
    mkMyGoal Γ (l ++ [x]) g ->
    mkMyGoal Γ l (x ---> g).
  Proof.
    intros H.
    unfold of_MyGoal in H. simpl in H. rewrite foldr_app in H. simpl in H. exact H.
  Qed.
  
  
  Ltac toMyGoal := rewrite -of_MyGoal_from_goal; unfold MyGoal_from_goal.
  Ltac fromMyGoal := unfold of_MyGoal; simpl.
  Ltac mgIntro := apply MyGoal_intro; simpl.

  Goal (Empty_set _) ⊢ (patt_bound_evar 1 ---> patt_bound_evar 2).
  Proof.
    toMyGoal. mgIntro. fromMyGoal.
  Abort.

  Goal
    (Empty_set _) ⊢ (patt_bound_evar 1 ---> patt_bound_evar 2) ->
    (Empty_set _) ⊢ (patt_bound_evar 2 ---> patt_bound_evar 3)
  .
  Proof.
    intros H.
    toMyGoal. mgIntro. fromMyGoal.
  Abort.

  Search list nat.

  Lemma MyGoal_weakenConclusion Γ l g g':
    wf l ->
    well_formed g ->
    well_formed g' ->
    Γ ⊢ (g ---> g') ->
    mkMyGoal Γ l g ->
    mkMyGoal Γ l g'.
  Proof.
    intros wfg wfg' gimpg' H.
    unfold of_MyGoal in *. simpl in *.
    eauto using prf_weaken_conclusion_meta_iter_meta.
  Qed.
  
  Lemma conclusion_anyway Γ A B:
    well_formed A ->
    well_formed B ->
    Γ ⊢ ((A ---> B) ---> (¬ A ---> B) ---> B).
  Proof.
    intros wfA wfB.
    assert (H1: Γ ⊢ (B ---> ¬ ¬ B)) by auto.

    epose proof (H10 := P4m_neg Γ (¬B) A _ _). Unshelve. all: auto.
    
    assert (H2: Γ ⊢ ((A ---> B) ---> (¬ A ---> B) ---> ¬¬B)) by admit.
    assert (H3: Γ ⊢ (((¬ A ---> B) ---> ¬ ¬ B) ---> ((¬ A ---> B) ---> B))) by auto.
    assert (H4: Γ ⊢ (((A ---> B) ---> ((¬ A ---> B) ---> ¬ ¬ B)) ---> ((A ---> B) ---> ((¬ A ---> B) ---> B)))).
    { apply prf_weaken_conclusion_meta; auto. }
    eapply Modus_ponens. 4: apply H4. all: auto 10.
    (* Give up *)
  Abort.
  
  Lemma conclusion_anyway_meta Γ A B:
    well_formed A ->
    well_formed B ->
    Γ ⊢ (A ---> B) ->
    Γ ⊢ (¬ A ---> B) ->
    Γ ⊢ B.
  Proof.
    intros wfA wfB AimpB nAimpB.
    assert (H1: Γ ⊢ (B ---> ¬ ¬ B)) by auto.
    assert (H2: Γ ⊢ (¬ A ---> ¬ ¬ B)).
    { eapply syllogism_intro. 5: apply H1. all: auto. }
    clear H1.
    assert (H3: Γ ⊢ (¬ B ---> ¬ A)) by auto.
    epose proof (H4 := P4m_neg Γ (¬B) A _ _).
    assert (H5: Γ ⊢ ((¬ B ---> ¬ A) ---> ¬ ¬ B)).
    { eapply Modus_ponens. 4: apply H4. all: auto. }
    assert (H6: Γ ⊢ (¬ ¬ B)).
    { eapply Modus_ponens. 4: apply H5. all: auto. }
    auto.
    Unshelve. all: auto.
  Qed.
    
  Lemma pf_or_elim Γ A B C :
    well_formed A ->
    well_formed B ->
    well_formed C ->
    Γ ⊢ (A ---> C) ->
    Γ ⊢ (B ---> C) ->
    Γ ⊢ (A or B) ->
    Γ ⊢ C.
  Proof.
    intros wfA wfB wfC AimpC BimpC AorB.
    unfold patt_or.
    assert (H1: Γ ⊢ ((¬ A ---> B) ---> (B ---> C) ---> (¬ A ---> C))).
    { eapply syllogism; auto. }
    apply reorder_meta in H1; auto.
    assert (H2: Γ ⊢ ((¬ A ---> B) ---> (¬ A ---> C))).
    { eapply Modus_ponens. 4: apply H1. all: auto. }
    unfold patt_or in AorB.
    assert (H3: Γ ⊢ (¬ A ---> C)).
    { eapply Modus_ponens. 4: apply H2. all: auto. }
    eapply conclusion_anyway. 4: apply H3. all: auto.
  Qed.
  
  Lemma pf_iff_split Γ A B:
    well_formed A ->
    well_formed B ->
    Γ ⊢ (A ---> B) ->
    Γ ⊢ (B ---> A) ->
    Γ ⊢ (A <---> B).
  Proof.
    intros wfA wfB AimplB BimplA.
    unfold patt_iff.
    apply conj_intro_meta; auto.
  Qed.

  Lemma pf_iff_proj1 Γ A B:
    well_formed A ->
    well_formed B ->
    Γ ⊢ (A <---> B) ->
    Γ ⊢ (A ---> B).
  Proof.
    intros. unfold patt_iff in H1.
    apply pf_conj_elim_l_meta in H1; auto.
  Qed.

  Lemma pf_iff_proj2 Γ A B:
    well_formed A ->
    well_formed B ->
    Γ ⊢ (A <---> B) ->
    Γ ⊢ (B ---> A).
  Proof.
    intros. unfold patt_iff in H1.
    apply pf_conj_elim_r_meta in H1; auto.
  Qed.

  Lemma pf_iff_iff Γ A B:
    well_formed A ->
    well_formed B ->
    (Γ ⊢ (A <---> B)) <-> ((Γ ⊢ (A ---> B)) /\ (Γ ⊢ (B ---> A))).
  Proof.
    intros. firstorder using pf_iff_proj1,pf_iff_proj2,pf_iff_split.
  Qed.
  

  Lemma pf_iff_equiv_refl Γ A :
    well_formed A ->
    Γ ⊢ (A <---> A).
  Proof.
    intros.
    apply pf_iff_split; auto.
  Qed.

  Lemma pf_iff_equiv_sym Γ A B :
    well_formed A ->
    well_formed B ->
    Γ ⊢ (A <---> B) ->
    Γ ⊢ (B <---> A).
  Proof.
    intros wfA wfB H.
    apply pf_iff_iff in H; auto. apply pf_iff_iff; auto.
    exact (conj (proj2 H) (proj1 H)).
  Qed.

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
  Qed.  
    
  Lemma pf_prop_bott_iff Γ AC:
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
        eapply syllogism_intro. 5: apply H0. 4: apply H. 1,2,3: auto.
      + apply bot_elim; auto.
    - apply pf_iff_iff in IHAC; auto.
      destruct IHAC as [IH1 IH2].
      apply pf_iff_split; auto.
      + pose proof (H := IH1).
        eapply Framing_right in H.
        eassert (Γ ⊢ ( ?[psi] $ ⊥ ---> ⊥)).
        { apply Prop_bott_right. shelve. }
        eapply syllogism_intro. 5: apply H0. 4: apply H. 1,2,3: auto.
      + apply bot_elim; auto.
        Unshelve. all: auto.
  Qed.
  
  Lemma pf_prop_or_iff Γ AC p q:
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
      + admit.
      + 
        Set Printing All.
        Check pf_or_elim.
        eapply pf_or_elim.
        Search patt_or ML_proof_system.
  Abort.
  

  
(* Axiom extension : forall G A B,
  G ⊢ A -> (Add Sigma_pattern G B) ⊢ A. *)

(* Lemma empty_Γ_implies_any A : forall G,
  empty_Γ ⊢ A -> G ⊢ A. *)

(* Lemma equiv_cong G phi1 phi2 C x :
  (G ⊢ (phi1 <~> phi2)) -> G ⊢ ((e_subst_var C phi1 x) <~> (e_subst_var C phi2 x)). *)

(* Lemma eq_refl
  (phi : Sigma_pattern) (Γ : Ensemble Sigma_pattern) :
    Γ ⊢ (phi ~=~ phi). *)

(* Lemma eq_trans
  (phi1 phi2 phi3 : Sigma_pattern) (Γ : Ensemble Sigma_pattern) :
    Γ ⊢ (phi1 ~=~ phi2) -> Γ ⊢ (phi2 ~=~ phi3) ->
    Γ ⊢ (phi1 ~=~ phi3). *)

(* Lemma eq_symm
  (phi1 phi2 : Sigma_pattern)  (Γ : Ensemble Sigma_pattern) :
    Γ ⊢ (phi1 ~=~ phi2) -> Γ ⊢ (phi2 ~=~ phi1). *)

(* Lemma eq_evar_subst
  (x : EVar) (phi1 phi2 psi : Sigma_pattern) (Γ : Ensemble Sigma_pattern) :
    Γ ⊢ (phi1 ~=~ phi2) ->
    Γ ⊢ ((e_subst_var psi phi1 x) ~=~ (e_subst_var psi phi2 x)). *)

(* Lemma A_implies_A_totality A:
  A proved -> |_ A _| proved. *)

(* Lemma A_totality_implies_A A:
  |_ A _| proved -> A proved. *)

(* Lemma universal_instantiation (Γ : Theory) (A : Pattern) (x y : evar):
  Γ ⊢ ((all' x, A) ---> (e_subst_var A y x)). *)
End FOL_helpers.

(* Hints *)
#[export]
 Hint Resolve A_impl_A : core.
