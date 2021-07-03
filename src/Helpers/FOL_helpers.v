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

  (* TODO: maybe generalize to any connective? *)
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
    rewrite foldr_andb_true_take; auto.
  Qed.

  #[local] Hint Resolve wf_take : core.

  Lemma wf_drop n xs:
    wf xs ->
    wf (drop n xs).
  Proof.
    unfold wf. intros H.
    rewrite map_drop.
    rewrite foldr_andb_true_drop; auto.
  Qed.
  
  #[local] Hint Resolve wf_drop : core.

  Lemma wf_insert n p xs:
    wf xs ->
    well_formed p ->
    wf (<[n := p]> xs).
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

  Lemma wf_tail' p xs:
    wf (p :: xs) ->
    wf xs.
  Proof.
    unfold wf. intros H. simpl in H. apply andb_prop in H. rewrite (proj2 H). reflexivity.
  Qed.

  #[local] Hint Resolve wf_tail' : core.

  Lemma wf_cons x xs:
    well_formed x ->
    wf xs ->
    wf (x :: xs).
  Proof.
    intros wfx wfxs.
    unfold wf. simpl. rewrite wfx.
    unfold wf in wfxs. rewrite wfxs.
    reflexivity.
  Qed.

  #[local] Hint Resolve wf_cons : core.
  
  Lemma wf_app xs ys:
    wf xs ->
    wf ys ->
    wf (xs ++ ys).
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

  Lemma prf_weaken_conclusion Γ A B B' :
    well_formed A ->
    well_formed B ->
    well_formed B' ->
    Γ ⊢ ((B ---> B') ---> ((A ---> B) ---> (A ---> B'))).
  Proof.
    intros wfA wfB wfB'.
    apply reorder_meta; auto.
  Qed.
  
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
  Qed.

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

  Lemma prf_strenghten_premise Γ A A' B :
    well_formed A ->
    well_formed A' ->
    well_formed B ->
    Γ ⊢ ((A' ---> A) ---> ((A ---> B) ---> (A' ---> B))).
  Proof.
    intros wfA wfA' wfB. auto.
  Qed.

  Lemma prf_strenghten_premise_iter Γ l n h h' g :
    wf l ->
    well_formed h ->
    well_formed h' ->
    well_formed g ->
    l !! n = Some h ->
    Γ ⊢ ((h' ---> h) ---> ((fold_right patt_imp g l) ---> (fold_right patt_imp g (<[n := h']> l)))).
  Proof.
    intros wfl wfh wfh' wfg ln.
    pose proof (Hn := lookup_lt_Some _ _ _ ln).

    rewrite <- (take_drop n l).
    rewrite <- (take_drop n l) in ln.
    rewrite lookup_app_r in ln.
    { apply firstn_le_length.  }
    assert (Hlentake: length (take n l) + 0 = n).
    { rewrite firstn_length. lia. }
    rewrite <- Hlentake at 3.
    clear Hlentake.

    simpl.
    rewrite insert_app_r.
    repeat rewrite foldr_app.

    move: n Hn ln.
    induction l; intros n Hn ln.
    - rewrite take_nil. simpl.
      rewrite drop_nil. simpl. apply reorder_meta. 4: apply P1. all: auto.
    - pose proof (wfal := wfl).
      remember (foldr patt_imp g (drop n l)) as g1.
      remember (foldr patt_imp g (<[0:=h']> (drop n l))) as g2.
      unfold wf in wfl. simpl in wfl. apply andb_prop in wfl.
      destruct wfl as [wfa wfl].
      specialize (IHl wfl).
      simpl in Hn.
      destruct n.
      { subst. inversion ln. subst a. simpl. apply prf_strenghten_premise; auto. }
      assert (Hn': n < length l) by lia.
      simpl.
      specialize (IHl n ltac:(lia)).
      simpl in ln. specialize (IHl ln).
      remember (foldr patt_imp (foldr patt_imp g (drop n l)) (take n l)) as b.
      remember (foldr patt_imp (foldr patt_imp g (<[0:=h']> (drop n l))) (take n l)) as b'.

      assert (prf: Γ ⊢ ((b ---> b') ---> ((a ---> b) ---> (a ---> b')))).
      { apply prf_weaken_conclusion; subst; auto. }

      eapply syllogism_intro. 5: apply prf. all: subst; auto 10.
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
  Qed.
  
  Lemma prf_strenghten_premise_iter_meta Γ l n h h' g :
    wf l ->
    well_formed h ->
    well_formed h' ->
    well_formed g ->
    l !! n = Some h ->
    Γ ⊢ (h' ---> h) ->
    Γ ⊢ ((fold_right patt_imp g l) ---> (fold_right patt_imp g (<[n := h']> l))).
  Proof.
    intros.
    eapply Modus_ponens.
    4: apply prf_strenghten_premise_iter.
    3: apply H4.
    all: auto.
  Qed.

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
    { eapply Modus_ponens. 4: apply H2. all: auto. }
    eapply Modus_ponens. 4: apply H3. all: auto.
  Qed.

  Example example_nested_const Γ a b c:
    well_formed a ->
    well_formed b ->
    well_formed c ->
    (* like P2 but nested a bit *)
    Γ ⊢ (a ---> (b ---> (c ---> a))).
  Proof.
    intros wfa wfb wfc.
    assert (H1: Γ ⊢ ((c ---> a) ---> (b ---> (c ---> a)))) by auto using P1.
    assert (H2: Γ ⊢ (a ---> (c ---> a))) by auto using P1.
    (*Check prf_strenghten_premise_meta.*)
    eapply (syllogism_intro _ _ _ _ _ _ _ H2 H1).
    Unshelve. all: auto.
  Qed.

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
      remember (l₁ ++ a :: l₂) as xs.
      assert (wf xs).
      { subst. auto. }
      destruct xs as [|x xs].
      { assert (@length Pattern nil = length (l₁ ++ a :: l₂)). rewrite Heqxs. reflexivity.
        simpl in H0. rewrite app_length in H0. simpl in H0. lia.
      }
      simpl. simpl in IHl₁.
      unfold wf in H. apply andb_prop in H. destruct H as [wfx wfxs].
      apply reorder_meta; auto.
      eapply prf_strenghten_premise_meta_meta. 4: apply IHl₁. all: auto using P1.
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
      eapply prf_weaken_conclusion_meta; auto.
  Qed.

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

  Lemma MyGoal_exact Γ l g n:
    wf l ->
    well_formed g ->
    l !! n = Some g ->
    mkMyGoal Γ l g.
  Proof.
    intros wfl wfg ln.
    pose proof (Hn := lookup_lt_Some l n g ln).
    Check take_drop_middle.
    pose proof (Heq := take_drop_middle l n g ln).
    rewrite -Heq.
    unfold of_MyGoal. simpl.
    apply nested_const_middle; auto.
  Qed.  
  
  Ltac toMyGoal := rewrite -of_MyGoal_from_goal; unfold MyGoal_from_goal.
  Ltac fromMyGoal := unfold of_MyGoal; simpl.
  Ltac mgIntro := apply MyGoal_intro; simpl.
  Ltac mgExactn n := apply (MyGoal_exact _ _ _ n); auto.

  (* This almost works, but bound variables are not well-formed. TODO: change to free and move to example file. *)
  Print Signature. Print MLVariables. Check (@variables Σ).
  Goal (Empty_set _) ⊢ (patt_bound_evar 1 ---> patt_bound_evar 2 ---> patt_bound_evar 3 ---> patt_bound_evar 2).
  Proof.
    toMyGoal. mgIntro. mgIntro. mgIntro. mgExactn 1.
  Abort.

  Goal
    (Empty_set _) ⊢ (patt_bound_evar 1 ---> patt_bound_evar 2) ->
    (Empty_set _) ⊢ (patt_bound_evar 2 ---> patt_bound_evar 3)
  .
  Proof.
    intros H.
    toMyGoal. mgIntro. fromMyGoal.
  Abort.

  Lemma MyGoal_weakenConclusion' Γ l g g':
    wf l ->
    well_formed g ->
    well_formed g' ->
    Γ ⊢ (g ---> g') ->
    mkMyGoal Γ l g ->
    mkMyGoal Γ l g'.
  Proof.
    intros wfg wfg' gimpg' H.
    unfold of_MyGoal in *. simpl in *.
    eauto using prf_weaken_conclusion_iter_meta_meta.
  Qed.
  
  Lemma prf_contraction Γ a b:
    well_formed a ->
    well_formed b ->
    Γ ⊢ ((a ---> (a ---> b)) ---> (a ---> b)).
  Proof.
    intros wfa wfb.
    assert (H1 : Γ ⊢ (a ---> ((a ---> b) ---> b))) by auto.
    assert (H2 : Γ ⊢ ((a ---> ((a ---> b) ---> b)) ---> ((a ---> (a ---> b)) ---> (a ---> b)))) by auto using P2.
    eapply Modus_ponens. 4: apply H2. all: auto.
  Qed.

  #[local] Hint Resolve prf_contraction : core.
  

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
    4: apply H4. all: auto.
  Qed.

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
    all: auto.
  Qed.

  Lemma prf_weaken_conclusion_under_implication_meta_meta Γ a b c:
    well_formed a ->
    well_formed b ->
    well_formed c ->
    Γ ⊢ (a ---> b) ->
    Γ ⊢ (a ---> (b ---> c)) ->
    Γ ⊢ (a ---> c).
  Proof.
    intros wfa wfb wfc H1 H2.
    eapply Modus_ponens.
    4: apply prf_weaken_conclusion_under_implication_meta. 3: apply H2.
    all: auto.
  Qed.

  Lemma prf_weaken_conclusion_iter_under_implication Γ l g g':
    wf l ->
    well_formed g ->
    well_formed g' ->
    Γ ⊢ (((g ---> g') ---> (foldr patt_imp g l)) ---> ((g ---> g') ---> (foldr patt_imp g' l))).
  Proof.
    intros wfl wfg wfg'.
    pose proof (H1 := prf_weaken_conclusion_iter Γ l g g' wfl wfg wfg').
    remember ((g ---> g')) as a.
    remember (foldr patt_imp g l) as b.
    remember (foldr patt_imp g' l) as c.
    pose proof (H2 := prf_weaken_conclusion_under_implication Γ a b c ltac:(subst;auto) ltac:(subst;auto) ltac:(subst; auto)).
    apply reorder_meta in H2. 2,3,4: subst;auto.
    eapply Modus_ponens. 4: apply H2. all: subst;auto.
  Qed.

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
  Qed.
  
  Lemma MyGoal_weakenConclusion_under_first_implication Γ l g g':
    wf l ->
    well_formed g ->
    well_formed g' ->
    mkMyGoal Γ ((g ---> g') :: l) g ->
    mkMyGoal Γ ((g ---> g') :: l) g'.
  Proof.
    apply prf_weaken_conclusion_iter_under_implication_meta.
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
      eapply prf_weaken_conclusion_meta. all: auto.
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
  Qed.


  Lemma MyGoal_weakenConclusion Γ l₁ l₂ g g':
    wf l₁ ->
    wf l₂ ->
    well_formed g ->
    well_formed g' ->
    mkMyGoal Γ (l₁ ++ (g ---> g') :: l₂) g ->
    mkMyGoal Γ (l₁ ++ (g ---> g') :: l₂) g'.
  Proof.
    apply prf_weaken_conclusion_iter_under_implication_iter_meta.
  Qed.

  Lemma MyGoal_weakenConclusion_under_nth Γ l n g g':
    wf l ->
    well_formed g ->
    well_formed g' ->
    l !! n = Some (g ---> g') ->
    mkMyGoal Γ l g ->
    mkMyGoal Γ l g'.
  Proof.
    intros wfl wfg wfg' ln H.
    pose proof (Hmid := take_drop_middle l n (g ---> g') ln).
    rewrite -Hmid in H. rewrite -Hmid. apply MyGoal_weakenConclusion; auto.
  Qed.

  Tactic Notation "mgApply'" constr(n) int_or_var(depth) :=
    match goal with
    | |- of_MyGoal (mkMyGoal ?Ctx ?l ?g) =>
      eapply (MyGoal_weakenConclusion_under_nth Ctx l n _ g);[idtac|idtac|idtac|reflexivity|idtac];auto depth
    end.
  Ltac mgApply n := mgApply' n 5.
  
  Lemma Constructive_dilemma Γ p q r s:
    well_formed p ->
    well_formed q ->
    well_formed r ->
    well_formed s ->
    Γ ⊢ ((p ---> q) ---> (r ---> s) ---> (p or r) ---> (q or s)).
  Proof.
    intros wfp wfq wfr wfs.
    unfold patt_or.

    toMyGoal. mgIntro. mgIntro. mgIntro. mgIntro.
    mgApply' 1 7.
    mgApply' 2 7.
    mgIntro.
    mgApply' 3 7.
    mgApply' 0 7.
    mgExactn 4.
    auto 8.
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
    eapply conclusion_anyway_meta. 4: apply H3. all: auto.
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
      + eapply pf_or_elim.
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
