From Coq Require Import ssreflect ssrfun ssrbool.

From Coq Require Import Ensembles Bool.
From MatchingLogic Require Import Syntax Semantics DerivedOperators ProofSystem.

From stdpp Require Import list.

From MatchingLogic.Utils Require Import stdpp_ext.

Import extralibrary.

Import
  MatchingLogic.Syntax.Notations
  MatchingLogic.DerivedOperators.Notations
  MatchingLogic.ProofSystem.Notations
.

Open Scope ml_scope.
Section FOL_helpers.

  Context {Σ : Signature}.

  (*Notation "theory ⊢ pattern" := (@ML_proof_system Σ theory pattern) (at level 95, no associativity).*)

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

    all: auto.
  Defined.

  #[local] Hint Resolve A_impl_A : core.
  
  Lemma P4m (Γ : Theory) (A B : Pattern) :
    (well_formed A) -> (well_formed B) -> Γ ⊢ ((A ---> B) ---> ((A ---> ¬B) ---> ¬A)).
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



  Lemma P4i (Γ : Theory) (A : Pattern) :
    well_formed A -> Γ ⊢ ((A ---> ¬A) ---> ¬A).
  Proof.
    intros WFA. eapply (Modus_ponens _ _ _ _ _).
    - eapply (A_impl_A _ A _). (*In the outdated: A_impl_A = P1*)
    - eapply (P4m _ A A _ _).
      Unshelve.
      all: auto 10.
  Defined.

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
  Defined.

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
             all:auto.
  Defined.

  Lemma syllogism (Γ : Theory) (A B C : Pattern) :
    well_formed A -> well_formed B -> well_formed C -> Γ ⊢ ((A ---> B) ---> (B ---> C) ---> (A ---> C)).
  Proof.
    intros WFA WFB WFC.
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
  Defined.

  #[local] Hint Resolve syllogism : core.
  
  Lemma syllogism_intro (Γ : Theory) (A B C : Pattern) :
    well_formed A -> well_formed B -> well_formed C -> Γ ⊢ (A ---> B) -> Γ ⊢ (B ---> C) -> Γ ⊢ (A ---> C).
  Proof.
    intros H H0 H1 H2 H3.
    eapply (Modus_ponens _ _ _ _ _).
    - exact H2.
    - eapply (Modus_ponens _ _ _ _ _).
      + exact H3.
      + eapply (reorder_meta _ _ _ _). exact (syllogism _ A B C H H0 H1).
        Unshelve.
        all: auto.
  Defined.

  #[local] Hint Resolve syllogism_intro : core.
  
  Lemma modus_ponens (Γ : Theory) ( A B : Pattern) :
    well_formed A -> well_formed B -> Γ ⊢ (A ---> (A ---> B) ---> B).
  Proof.
    intros WFA WFB.
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
  Defined.

  #[local] Hint Resolve modus_ponens : core.
  
  Lemma not_not_intro (Γ : Theory) (A : Pattern) :
    well_formed A -> Γ ⊢ (A ---> ¬(¬A)).
  Proof.
    intros WFA.
    assert(@well_formed Σ Bot).
    shelve.
    exact (modus_ponens _ A Bot WFA H).
    Unshelve.
    all: auto.
  Defined.

  #[local] Hint Resolve not_not_intro : core.

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
    Γ ⊢ ((¬ B) ---> (¬ A)) -> Γ ⊢ (A ---> B).
  Proof.
    intros H H0 H1.
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
  Defined.


  Lemma P4 (Γ : Theory) (A B : Pattern)  :
    well_formed A -> well_formed B -> 
    Γ ⊢ (((¬ A) ---> (¬ B)) ---> (B ---> A)).
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
    epose (reorder Γ (A ---> Bot) (B) (Bot) _ _ _).
    eapply (Modus_ponens Γ _ _ _ _ m8 m7).
    Unshelve.
    all: auto 10.
  Defined.

  Lemma conj_intro (Γ : Theory) (A B : Pattern) :
    well_formed A -> well_formed B -> Γ ⊢ (A ---> B ---> (A and B)).
  Proof.
    intros WFA WFB.
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
  Defined.


  Lemma conj_intro_meta (Γ : Theory) (A B : Pattern) :
    well_formed A -> well_formed B -> Γ ⊢ A -> Γ ⊢ B -> Γ ⊢ (A and B).
  Proof.
    intros WFA WFB H H0.
    eapply (Modus_ponens _ _ _ _ _).
    - exact H0.
    - eapply (Modus_ponens _ _ _ _ _).
      + exact H.
      + exact (conj_intro _ A B WFA WFB).
        Unshelve.
        all: auto.
  Defined.
  
  (* Lemma conj_intro_meta_e (Γ : Theory) (A B : Pattern) : *) 
  Definition conj_intro_meta_e := conj_intro_meta.    (*The same as conj_intro_meta*)

  Lemma disj (Γ : Theory) (A B : Pattern) :
    well_formed A -> well_formed B -> Γ ⊢ (A ---> B ---> (A or B)).
  Proof.
    intros WFA WFV. unfold patt_or.
    
    epose proof (t1 := (P1 Γ B (¬A) _ _)).
    
    epose proof (t2 := (P1 Γ (B ---> (¬A ---> B)) A _ _)).
    
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
      + exact (disj _ A B WFA WFB).
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
        all: auto.
  Defined.

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
        * eapply (P4 _ Bot Bot _ _).
      + eapply (P1 _ (Bot ---> Bot) (A ---> Bot) _ _).
    - eapply (P4 _ A Bot _ _).
      Unshelve.
      all: auto.
  Defined.

  Lemma modus_ponens' (Γ : Theory) (A B : Pattern) :
    well_formed A -> well_formed B -> Γ ⊢ (A ---> (¬B ---> ¬A) ---> B).
  Proof.
    intros WFA WFB.
    assert(well_formed (¬ B ---> ¬ A)).
    shelve.
    exact (reorder_meta Γ H WFA WFB (P4 _ B A WFB WFA)).
    Unshelve.
    all: auto.
  Defined.

  Lemma disj_right_intro (Γ : Theory) (A B : Pattern) :
    well_formed A -> well_formed B -> Γ ⊢ (B ---> (A or B)).
  Proof.
    intros WFA WFB.
    assert(well_formed (¬A)).
    shelve.
    exact (P1 _ B (¬A) WFB H).
    Unshelve.
    all: auto.
  Defined.

  #[local] Hint Resolve disj_right_intro : core.
  
  Lemma disj_left_intro (Γ : Theory) (A B : Pattern) :
    well_formed A -> well_formed B -> Γ ⊢ (A ---> (A or B)).
  Proof.
    intros WFA WFB.
    eapply (syllogism_4_meta _ _ _ _ _ _ _ _ _ (modus_ponens _ A Bot _ _) (bot_elim _ B _)).
    Unshelve.
    all: auto.
  Defined.

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
  Defined.

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

  Lemma not_not_elim (Γ : Theory) (A : Pattern) :
    well_formed A -> Γ ⊢ (¬(¬A) ---> A).
  Proof.
    intros WFA.
    unfold patt_not.
    exact (P3 Γ A WFA).
  Defined.

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
  Defined.

  #[local] Hint Resolve not_not_elim_meta : core.

  Lemma double_neg_elim (Γ : Theory) (A B : Pattern) :
    well_formed A -> well_formed B -> Γ ⊢ (((¬(¬A)) ---> (¬(¬B))) ---> (A ---> B)).
  Proof.
    intros WFA WFB.
    eapply (syllogism_intro _ _ _ _ _ _ _).
    - eapply (P4 _ (¬A) (¬B) _ _).
    - eapply (P4 _ B A _ _).
      Unshelve.
      all: auto.
  Defined.

  Lemma double_neg_elim_meta (Γ : Theory) (A B : Pattern) :
    well_formed A -> well_formed B -> 
    Γ ⊢ ((¬(¬A)) ---> (¬(¬B))) -> Γ ⊢ (A ---> B).
  Proof.
    intros WFA WFB H.
    eapply (Modus_ponens _ _ _ _ _).
    - exact H.
    - exact (double_neg_elim _ A B WFA WFB).
      Unshelve.
      all: auto.
  Defined.

  Lemma P4_rev_meta (Γ : Theory) (A B : Pattern) :
    well_formed A -> well_formed B -> Γ ⊢ (A ---> B) -> Γ ⊢ ((A ---> B) ---> (¬B ---> ¬A)).
  Proof.
    intros WFA WFB H.
    eapply (deduction _ _ _ _ _).
    - exact H.
    - eapply (Modus_ponens _ _ _ _ _).
      + eapply (syllogism_intro _ _ _ _ _ _ _).
        * eapply (syllogism_intro _ _ _ _ _ _ _).
          -- eapply (not_not_elim _ A _).
          -- exact H.
        * eapply (not_not_intro _ B _).
      + eapply (P4 _ (¬A) (¬B) _ _).
        Unshelve.
        all: auto.
  Defined.

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
  Defined.

  #[local] Hint Resolve P4_rev_meta' : core.
  
  Lemma P4m_neg (Γ : Theory) (A B : Pattern) :
    well_formed A -> well_formed B -> Γ ⊢ ((¬B ---> ¬A) ---> (A ---> ¬B) --->  ¬A).
  Proof.
    intros WFA WFB.
    epose proof (PT := (P4 Γ B A _ _)).
    eapply (syllogism_intro _ _ _ _ _ _ _).
    - exact PT.
    - eapply (P4m _ _ _ _ _).
      Unshelve.
      all: auto.
  Defined.

  Lemma not_not_impl_intro_meta (Γ : Theory) (A B : Pattern) :
    well_formed A -> well_formed B -> Γ ⊢ (A ---> B) -> Γ ⊢ ((¬¬A) ---> (¬¬B)).
  Proof.
    intros WFA WFB H.
    epose proof (NN1 := not_not_elim Γ A _).
    epose proof (NN2 := not_not_intro Γ B _).
    
    epose proof (S1 := syllogism_intro _ _ _ _ _ _ _ H NN2).
    
    epose proof (S2 := syllogism_intro _ _ _ _ _ _ _ NN1 S1).
    exact S2.
    Unshelve.
    all: auto.
  Defined.

  Lemma not_not_impl_intro (Γ : Theory) (A B : Pattern) :
    well_formed A -> well_formed B -> Γ ⊢ ((A ---> B) ---> ((¬¬A) ---> (¬¬B))).
  Proof.
    intros WFA WFB.
    
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
  Defined.


  Lemma contraposition (Γ : Theory) (A B : Pattern) : 
    well_formed A -> well_formed B -> 
    Γ ⊢ ((A ---> B) ---> ((¬ B) ---> (¬ A))).
  Proof.
    intros WFA WFB.
    epose proof (P4 Γ (¬ A) (¬ B) _ _) as m.
    apply syllogism_intro with (B := (¬ (¬ A) ---> ¬ (¬ B))).
    - shelve.
    - shelve.
    - shelve.
    - eapply (not_not_impl_intro _ _ _ _ _).
    - exact m. (* apply (P4 _ _ _). shelve. shelve. *)
      Unshelve.
      all: auto.
  Defined.

  Lemma or_comm_meta (Γ : Theory) (A B : Pattern) :
    well_formed A -> well_formed B ->
    Γ ⊢ (A or B) -> Γ ⊢ (B or A).
  Proof.
    intros WFA WFB H. unfold patt_or in *.
    
    epose proof (P4 := (P4 Γ A (¬B) _ _)).
    
    epose proof (NNI := not_not_intro Γ B _).
    
    epose proof (SI := syllogism_intro Γ _ _ _ _ _ _ H NNI).
    
    eapply (Modus_ponens _ _ _ _ _).
    - exact SI.
    - exact P4.
      Unshelve.
      all: auto.
  Defined.

  Lemma A_implies_not_not_A_alt (Γ : Theory) (A : Pattern) :
    well_formed A -> Γ ⊢ A -> Γ ⊢ (¬( ¬A )).
  Proof.
    intros WFA H. unfold patt_not.
    epose proof (NN := not_not_intro Γ A _).
    
    epose proof (MP := Modus_ponens _ _ _ _ _ H NN).
    assumption.
    Unshelve.
    all: auto.
  Defined.

  Lemma P5i (Γ : Theory) (A B : Pattern) :
    well_formed A -> well_formed B -> Γ ⊢ (¬ A ---> (A ---> B)).
  Proof.
    intros WFA WFB.
    
    epose proof (Ax1 := (P1 Γ (¬A) (¬B) _ _)).
    
    epose proof (Ax2 := (P4 Γ B A _ _)).
    
    epose proof (TRANS := syllogism_intro _ _ _ _ _ _ _ Ax1 Ax2).
    assumption.
    Unshelve.
    all: auto.
  Defined.

  Lemma false_implies_everything (Γ : Theory) (phi : Pattern) :
    well_formed phi -> Γ ⊢ (Bot ---> phi).
  Proof.
    intros WFA.
    
    epose proof (B_B := (A_impl_A Γ Bot _)).
    epose proof (P4 := P5i Γ Bot phi _ _).
    
    eapply (Modus_ponens _ _ _ _ _) in P4.
    - assumption.
    - assumption.
      Unshelve.
      all: auto.
  Defined.


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
    - simpl. epose proof (m0 := Framing_left Γ (subst_ctx C Bot) (Bot) p IHC).
      epose proof (m1 := syllogism_intro Γ _ _ _ _ _ _ (m0) (Prop_bott_left Γ p Prf)). exact m1.
    - simpl. epose proof (m2 := Framing_right Γ (subst_ctx C Bot) (Bot) p IHC).

      epose proof (m3 := syllogism_intro Γ _ _ _ _ _ _ (m2) (Prop_bott_right Γ p Prf)). exact m3.
      
      Unshelve.
      all: auto.
  Defined.

  (*Was an axiom in AML_definition.v*)
  Lemma Framing (Γ : Theory) (C : Application_context) (A B : Pattern):
    well_formed A -> well_formed B -> Γ ⊢ (A ---> B) -> Γ ⊢ ((subst_ctx C A) ---> (subst_ctx C B)).
  Proof.
    induction C; intros WFA WFB H.
    - simpl. exact H.
    - simpl. epose (Framing_left Γ (subst_ctx C A) (subst_ctx C B) p (IHC _ _ H)). exact m.
    - simpl. epose (Framing_right Γ (subst_ctx C A) (subst_ctx C B) p (IHC _ _ H)). exact m.
      Unshelve.
      all: auto.
  Defined.

  Lemma A_implies_not_not_A_ctx (Γ : Theory) (A : Pattern) (C : Application_context) :
    well_formed A -> Γ ⊢ A -> Γ ⊢ (¬ (subst_ctx C ( ¬A ))).
  Proof.
    intros WFA H.
    epose proof (ANNA := A_implies_not_not_A_alt Γ _ _ H).
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
  Defined.


  Lemma A_implies_not_not_A_alt_Γ (G : Theory) (A : Pattern) :
    well_formed A -> G ⊢ A -> G ⊢ (¬( ¬A )).
  Proof.
    intros WFA H. unfold patt_not.
    epose proof (NN := not_not_intro G A _).
    
    epose proof (MP := Modus_ponens G _ _ _ _ H NN).
    
    assumption.
    Unshelve.
    all: auto.
  Defined.

  (* Lemma equiv_implies_eq (Γ : Theory) (A B : Pattern) :
  well_formed A -> well_formed B -> Γ ⊢ (A <---> B) -> Γ ⊢ ()
   *) (*Need equal*)
  
  (* Lemma equiv_implies_eq_Γ *)

  (*...Missing some lemmas because of the lack of defidness definition...*)

  Lemma ctx_bot_prop (Γ : Theory) (C : Application_context) (A : Pattern) :
    well_formed A -> Γ ⊢ (A ---> Bot) -> Γ ⊢ (subst_ctx C A ---> Bot).
  Proof.
    intros WFA H.
    epose proof (FR := Framing Γ C A Bot _ _ H).
    epose proof (BPR := Prop_bot Γ C).
    
    epose proof (TRANS := syllogism_intro _ _ _ _ _ _ _ FR BPR).
    
    assumption.
    Unshelve.
    4: assert (@well_formed Σ (Bot)).
    all: auto.
  Defined.

  Lemma not_not_A_ctx_implies_A (Γ : Theory) (C : Application_context) (A : Pattern):
    well_formed A -> Γ ⊢ (¬ (subst_ctx C ( ¬A ))) -> Γ ⊢ A.
  Proof.
    intros WFA H.
    unfold patt_not in H at 1.
    
    epose (BIE := false_implies_everything Γ (subst_ctx C Bot) _).
    
    epose (TRANS := syllogism_intro _ _ _ _ _ _ _ H BIE).
    
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
    intros WFA H H0.
    epose(Modus_ponens G A Bot _ _ H H0).
    assumption.
    Unshelve.
    all: auto.
  Defined.

  Lemma modus_tollens Γ A B :
    well_formed A ->
    well_formed B ->
    Γ ⊢ (A ---> B) ->
    Γ ⊢ (¬B ---> ¬A).
  Proof.
    intros WFA WFB H.
    eapply Modus_ponens.
    4: apply contraposition.
    all: auto.
  Defined.
  
  Lemma A_impl_not_not_B Γ A B :
    well_formed A ->
    well_formed B ->
    Γ ⊢ ((A ---> ¬¬B) ---> (A ---> B)).
  Proof.
    intros WFA WFB.
    assert (Γ ⊢ (¬¬B ---> B)) by auto.
    assert (Γ ⊢ ((A ---> ¬¬B) ---> (¬¬B ---> B) ---> (A ---> B))) by auto.
    apply reorder_meta in H0; auto.
    eapply Modus_ponens. 4: apply H0. all: auto 10.
  Defined.

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
  Defined.
  
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

  Lemma prf_strenghten_premise Γ A A' B :
    well_formed A ->
    well_formed A' ->
    well_formed B ->
    Γ ⊢ ((A' ---> A) ---> ((A ---> B) ---> (A' ---> B))).
  Proof.
    intros wfA wfA' wfB. auto.
  Defined.

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
  Defined.


  
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
  
  Lemma prf_strenghten_premise_iter_meta Γ l n h h' g :
    wf l ->
    well_formed h ->
    well_formed h' ->
    well_formed g ->
    l !! n = Some h ->
    Γ ⊢ (h' ---> h) ->
    Γ ⊢ ((fold_right patt_imp g l) ---> (fold_right patt_imp g (<[n := h']> l))).
  Proof.
    intros WFl WFh WFh' WFg H H0.
    eapply Modus_ponens.
    4: apply prf_strenghten_premise_iter.
    3: apply H0.
    all: auto.
  Defined.

  Lemma prf_strenghten_premise_iter_meta_meta Γ l n h h' g :
    wf l ->
    well_formed h ->
    well_formed h' ->
    well_formed g ->
    l !! n = Some h ->
    Γ ⊢ (h' ---> h) ->
    Γ ⊢ (fold_right patt_imp g l) ->
    Γ ⊢ (fold_right patt_imp g (<[n := h']> l)).
  Proof.
    intros WFl WFh WFh' WFg H H0 H1.
    eapply Modus_ponens.
    4: eapply prf_strenghten_premise_iter_meta.
    8: apply H. all: auto.
  Defined.

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
  Defined.

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
    eapply (syllogism_intro _ _ _ _ _ _ _ H2 H1).
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
  Defined.
  
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
  Defined.

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
    intros WFA WFB H.
    eapply Modus_ponens.
    4: { apply A_impl_not_not_B; auto. }
    all: auto.
  Defined.

  Lemma pf_conj_elim_l Γ A B :
    well_formed A ->
    well_formed B ->
    Γ ⊢ (A and B ---> A).
  Proof.
    intros WFA WFB. unfold patt_and. unfold patt_not at 1.

    assert (Γ ⊢ (¬ A ---> (¬ A or ¬ B))) by auto.
    assert (Γ ⊢ ((¬ A or ¬ B) ---> (¬ A or ¬ B ---> ⊥) ---> ⊥)) by auto.
    assert (Γ ⊢ (¬ A ---> ((¬ A or ¬ B ---> ⊥) ---> ⊥))).
    { eapply syllogism_intro. 5: apply H0. 4: apply H. all: auto. }
    epose proof (reorder_meta _ _ _ _ H1).
    apply A_impl_not_not_B_meta; auto.
    Unshelve.
    all: auto.
  Defined.

  Lemma pf_conj_elim_r Γ A B :
    well_formed A ->
    well_formed B ->
    Γ ⊢ (A and B ---> B).
  Proof.
    intros WFA WFB. unfold patt_and. unfold patt_not at 1.

    assert (Γ ⊢ (¬ B ---> (¬ A or ¬ B))) by auto.
    assert (Γ ⊢ ((¬ A or ¬ B) ---> (¬ A or ¬ B ---> ⊥) ---> ⊥)) by auto.
    assert (Γ ⊢ (¬ B ---> ((¬ A or ¬ B ---> ⊥) ---> ⊥))).
    { eapply syllogism_intro. 5: apply H0. 4: apply H. all: auto. }
    epose proof (reorder_meta _ _ _ _ H1).
    apply A_impl_not_not_B_meta; auto.
    Unshelve.
    all: auto.
  Defined.

  Lemma pf_conj_elim_l_meta Γ A B :
    well_formed A ->
    well_formed B ->
    Γ ⊢ (A and B) ->
    Γ ⊢ A.
  Proof.
    intros WFA WFB H.
    eapply Modus_ponens.
    4: apply pf_conj_elim_l.
    3: apply H.
    all: auto.
  Defined.
  
  Lemma pf_conj_elim_r_meta Γ A B :
    well_formed A ->
    well_formed B ->
    Γ ⊢ (A and B) ->
    Γ ⊢ B.
  Proof.
    intros WFA WFB H.
    eapply Modus_ponens.
    4: apply pf_conj_elim_r.
    3: apply H.
    all: auto.
  Defined.

  Lemma A_or_notA Γ A :
    well_formed A ->
    Γ ⊢ (A or ¬ A).
  Proof.
    intros wfA.
    unfold patt_or.
    auto.
  Defined.

  Lemma P4m_meta (Γ : Theory) (A B : Pattern) :
    well_formed A ->
    well_formed B ->
    Γ ⊢ (A ---> B) ->
    Γ ⊢ (A ---> ¬B) ->
    Γ ⊢ ¬A.
  Proof.
    intros wfA wfB AimpB AimpnB.
    pose proof (H1 := P4m Γ A B wfA wfB).
    assert (H2 : Γ ⊢ (A ---> ¬ B) ---> ¬ A).
    { eapply Modus_ponens. 4: apply H1. all: auto. }
    eapply Modus_ponens. 4: apply H2. all: auto.
  Defined.

  Record MyGoal : Type := mkMyGoal { mgTheory : Theory; mgHypotheses: list Pattern; mgConclusion : Pattern }.

  Definition MyGoal_from_goal (Γ : Theory) (goal : Pattern) : MyGoal := mkMyGoal Γ nil goal.

  Notation "[ G ⊢ l ==> g ]" := (mkMyGoal G l g).


  Coercion of_MyGoal (MG : MyGoal) : Type := (mgTheory MG) ⊢ (fold_right patt_imp (mgConclusion MG) (mgHypotheses MG)).


  Lemma of_MyGoal_from_goal Γ (goal : Pattern) : of_MyGoal (MyGoal_from_goal Γ goal) = (Γ ⊢ goal).
  Proof. reflexivity. Defined.

  Lemma MyGoal_intro (Γ : Theory) (l : list Pattern) (x g : Pattern):
    mkMyGoal Γ (l ++ [x]) g ->
    mkMyGoal Γ l (x ---> g).
  Proof.
    intros H.
    unfold of_MyGoal in H. simpl in H. rewrite foldr_app in H. simpl in H. exact H.
  Defined.

  Lemma MyGoal_exact Γ l g n:
    wf l ->
    well_formed g ->
    l !! n = Some g ->
    mkMyGoal Γ l g.
  Proof.
    intros wfl wfg ln.
    pose proof (Hn := lookup_lt_Some l n g ln).
    pose proof (Heq := take_drop_middle l n g ln).
    rewrite -Heq.
    unfold of_MyGoal. simpl.
    apply nested_const_middle; auto.
  Defined.  

End FOL_helpers.

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

#[global]
Ltac toMyGoal := rewrite <- of_MyGoal_from_goal; unfold MyGoal_from_goal.
#[global]
Ltac fromMyGoal := unfold of_MyGoal; simpl.
#[global]
Ltac mgIntro := apply MyGoal_intro; simpl.
#[global]
Ltac mgExactn n := apply (MyGoal_exact _ _ _ n); auto.


Section FOL_helpers.

  Context {Σ : Signature}.

  (* This almost works, but bound variables are not well-formed. TODO: change to free and move to example file. *)

  Goal ∅ ⊢ (patt_bound_evar 1 ---> patt_bound_evar 2 ---> patt_bound_evar 3 ---> patt_bound_evar 2).
  Proof.
    toMyGoal. mgIntro. mgIntro. mgIntro. mgExactn 1.
  Abort.

  Goal
    ∅ ⊢ (patt_bound_evar 1 ---> patt_bound_evar 2) ->
    ∅ ⊢ (patt_bound_evar 2 ---> patt_bound_evar 3)
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
  Defined.
  
  Lemma prf_contraction Γ a b:
    well_formed a ->
    well_formed b ->
    Γ ⊢ ((a ---> (a ---> b)) ---> (a ---> b)).
  Proof.
    intros wfa wfb.
    assert (H1 : Γ ⊢ (a ---> ((a ---> b) ---> b))) by auto.
    assert (H2 : Γ ⊢ ((a ---> ((a ---> b) ---> b)) ---> ((a ---> (a ---> b)) ---> (a ---> b)))) by auto using P2.
    eapply Modus_ponens. 4: apply H2. all: auto.
  Defined.

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
  Defined.

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
  Defined.

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
  Defined.

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
  Defined.

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
  
  Lemma MyGoal_weakenConclusion_under_first_implication Γ l g g':
    wf l ->
    well_formed g ->
    well_formed g' ->
    mkMyGoal Γ ((g ---> g') :: l) g ->
    mkMyGoal Γ ((g ---> g') :: l) g'.
  Proof.
    apply prf_weaken_conclusion_iter_under_implication_meta.
  Defined.

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
  Defined.

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


  Lemma MyGoal_weakenConclusion Γ l₁ l₂ g g':
    wf l₁ ->
    wf l₂ ->
    well_formed g ->
    well_formed g' ->
    mkMyGoal Γ (l₁ ++ (g ---> g') :: l₂) g ->
    mkMyGoal Γ (l₁ ++ (g ---> g') :: l₂) g'.
  Proof.
    apply prf_weaken_conclusion_iter_under_implication_iter_meta.
  Defined.

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
  Defined.

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
  Defined.

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
      { apply prf_impl_distr_meta; auto. }
      assert (H3 : Γ ⊢ ((a ---> foldr patt_imp g (l ++ [h]) ---> foldr patt_imp g l)
                          ---> ((a ---> foldr patt_imp g (l ++ [h])) ---> (a ---> foldr patt_imp g l)))).
      { auto using P2. }

      eapply prf_weaken_conclusion_meta_meta.
      4: apply H3. all: auto 10.
  Defined.

  Lemma prf_add_lemma_under_implication_meta Γ l g h:
    wf l ->
    well_formed g ->
    well_formed h ->
    Γ ⊢ (foldr patt_imp h l) ->
    Γ ⊢ ((foldr patt_imp g (l ++ [h])) ---> (foldr patt_imp g l)).
  Proof.
    intros WFl WFg WGh H. eapply Modus_ponens. 4: apply prf_add_lemma_under_implication. all: auto 7.
  Defined.

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

  Lemma myGoal_assert Γ l g h:
    wf l ->
    well_formed g ->
    well_formed h ->
    mkMyGoal Γ l h ->
    mkMyGoal Γ (l ++ [h]) g ->
    mkMyGoal Γ l g.
  Proof.
    intros wfl wfg wfh H1 H2.
    eapply prf_add_lemma_under_implication_meta_meta. 4: apply H1. all: auto.
  Defined.
  
  Tactic Notation "mgAssert" "(" ident(n) ":" constr(t) ")" :=
    match goal with
    | |- of_MyGoal (mkMyGoal ?Ctx ?l ?g) =>
      (*assert (n : Ctx ⊢ (foldr patt_imp t l));*)
      assert (n : mkMyGoal Ctx l t);
      [ | (eapply (myGoal_assert Ctx l g t _ _ _ n); rewrite [_ ++ _]/=)]
    end.

  Lemma P4i' (Γ : Theory) (A : Pattern) :
    well_formed A →
    Γ ⊢ ((¬A ---> A) ---> A).
  Proof.
    intros wfA.
    assert (H1: Γ ⊢ ((¬ A ---> ¬ ¬ A) ---> ¬ ¬ A)).
    { apply P4i. auto. }
    assert (H2: Γ ⊢ ((¬ A ---> A) ---> (¬ A ---> ¬ ¬ A))).
    { eapply prf_weaken_conclusion_meta; auto. }
    
    eapply prf_strenghten_premise_meta_meta. 4: apply H2. all: auto.
    eapply prf_weaken_conclusion_meta_meta. 4: apply not_not_elim. all: auto.
  Defined.

  #[local] Hint Resolve P4i' : core.

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
    pose proof (H1 := Constructive_dilemma Γ p r q r wfp wfr wfq wfr).
    assert (Γ ⊢ ((r or r) ---> r)).
    { unfold patt_or. apply P4i'; auto. }
    rewrite -> tofold in H1. rewrite 3!consume in H1.
    eapply prf_weaken_conclusion_iter_meta_meta in H1. 5: apply H. all: auto 10.
  Defined.


  Lemma prf_disj_elim_meta Γ p q r:
    well_formed p ->
    well_formed q ->
    well_formed r ->
    Γ ⊢ (p ---> r) ->
    Γ ⊢ ((q ---> r) ---> (p or q) ---> r).
  Proof.
    intros WFp WHq WFr H. eapply Modus_ponens. 4: apply prf_disj_elim.
    all: auto.
  Defined.
  
  
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
      pose proof (modus_ponens Γ _ _ wfa wfg).
      eapply Modus_ponens. 4: apply H. all: auto.
    - pose proof (wfa0l := wfl).
      unfold wf in wfl. simpl in wfl. apply andb_prop in wfl. destruct wfl as [wfa0 wfl].
      specialize (IHl wfl).
      simpl in IHl. simpl.
      (* < change a0 and a in the LHS > *)
      assert (H : Γ ⊢ (a ---> a0 ---> foldr patt_imp g l) ---> (a0 ---> a ---> foldr patt_imp g l)).
      { apply reorder; auto. }
      rewrite -> tofold. rewrite consume.
      pose proof (H0 := prf_strenghten_premise_iter_meta_meta Γ ([] ++ [a0 ---> a ---> foldr patt_imp g l]) 0).
      simpl in H0.
      specialize (H0 (a0 ---> a ---> foldr patt_imp g l) (a ---> a0 ---> foldr patt_imp g l)).
      specialize (H0 (a0 ---> foldr patt_imp g l)).
      simpl. apply H0. all: auto. clear H0 H.
      (* </change a0 and a > *)
      assert (Γ ⊢ ((a ---> a0 ---> foldr patt_imp g l) ---> (a0 ---> foldr patt_imp g l))).
      { eapply Modus_ponens. 4: apply modus_ponens. all: auto 10. }
      
      eapply prf_strenghten_premise_meta_meta. 5: apply H. all: auto.
      apply reorder; auto.
  Defined.

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
  
  Lemma MyGoal_add Γ l g h:
    Γ ⊢ h ->
    wf l ->
    well_formed g ->
    well_formed h ->
    mkMyGoal Γ (h::l) g ->
    mkMyGoal Γ l g.
  Proof.
    intros H WFl WFg WFh H0.
    apply prf_add_proved_to_assumptions_meta with (a := h).
    all: auto.
  Defined.

  Tactic Notation "mgAdd" constr(n) :=
    match goal with
    | |- of_MyGoal (mkMyGoal ?Ctx ?l ?g) =>
      apply (MyGoal_add Ctx l g _ n)
    end.

  Lemma test_mgAdd Γ l g h:
    wf l ->
    well_formed g ->
    well_formed h ->
    Γ ⊢ (h ---> g) ->
    Γ ⊢ h ->
    Γ ⊢ g.
  Proof.
    intros WFl WFg WFh H H0. toMyGoal.
    mgAdd H0; [auto|auto|auto|].
    mgAdd H; [auto|auto|auto|].
    mgApply' 0 5. mgExactn 1.
  Defined.
    
  Lemma not_concl Γ p q:
    well_formed p ->
    well_formed q ->
    Γ ⊢ (p ---> (q ---> ((p ---> ¬ q) ---> ⊥))).
  Proof.
    intros wfp wfq.
    rewrite -> tofold. repeat rewrite consume.
    replace ((([] ++ [p]) ++ [q]) ++ [p ---> ¬ q]) with ([p;q;p--->¬q]) by reflexivity.
    replace ([p;q;p--->¬q]) with ([p] ++ [q; p ---> ¬q] ++ []) by reflexivity.
    apply prf_reorder_iter_meta; auto.
    simpl.
    fold (¬ q).
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
      apply prf_reorder_iter_meta; auto.
      simpl. auto.
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
    Γ ⊢ (((p and q) ---> r) ---> (p ---> (q ---> r))).
  Proof.
    intros wfp wfq wfr.
    toMyGoal. repeat mgIntro.
    unfold patt_and. mgApply' 0 10.
    mgIntro. unfold patt_or at 2.
    mgAssert (nnp: (¬ ¬ p)).
    {
      mgAdd (not_not_intro Γ p wfp); auto 10.
      mgApply' 0 10.
      mgExactn 2; auto 10.
    }
    clear nnp.
    mgAssert (nq: (¬ q)).
    {
      mgApply' 3 10. mgExactn 4; auto 10.
    }
    clear nq.
    mgApply' 5 10. mgExactn 2; auto 10.
    Unshelve. all: auto 10.
  Defined.

  
  Lemma and_impl' Γ p q r:
    well_formed p ->
    well_formed q ->
    well_formed r ->
    Γ ⊢ ((p ---> (q ---> r)) ---> ((p and q) ---> r)).
  Proof.
    intros wfp wfq wfr.
    toMyGoal. repeat mgIntro.
    mgAssert (Hp: p).
    {
      mgAdd (pf_conj_elim_l Γ p q wfp wfq); auto 10.
      mgApply' 0 10.
      mgExactn 2; auto 10.
    }
    mgAssert (Hq: q).
    {
      mgAdd (pf_conj_elim_r Γ p q wfp wfq); auto 10.
      mgApply' 0 10.
      mgExactn 2; auto 10.
    }
    clear Hp Hq.
    (* This pattern is basically an "apply ... in" *)
    mgAssert (Hqir: (q ---> r)).
    { mgApply' 0 10. mgExactn 2; auto 10. }
    clear Hqir.
    mgApply' 4 10. mgExactn 3; auto 10.
    Unshelve.
    all: auto 10.
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
      toMyGoal. repeat mgIntro.
      mgAdd IHl; auto 10.
      mgAssert (Hfp: (foldr patt_imp r (l ++ [p]))).
      { mgApply' 1 10. mgExactn 3; auto 10. }
      clear Hfp.
      mgAssert (Hfq: (foldr patt_imp r (l ++ [q]))).
      { mgApply' 2 10. mgExactn 3; auto 10. }
      clear Hfq.
      mgAssert (Hfqifpoq: (foldr patt_imp r (l ++ [q]) ---> foldr patt_imp r (l ++ [p or q]))).
      { mgApply' 0 10. mgExactn 4; auto 10. }
      clear Hfqifpoq.
      mgApply' 6 14.
      mgExactn 5; auto 15.
      Unshelve. all: auto 15.
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
          (<[1 := foldr patt_imp r (l₁ ++ q :: a :: l₂)]>
           ([foldr patt_imp r (l₁ ++ p :: a :: l₂); foldr patt_imp r (l₁ ++ a :: q :: l₂)]))
          by reflexivity.
      
      eapply prf_strenghten_premise_iter_meta_meta with (n := 1).
      5: { reflexivity. }
      5: {  apply prf_reorder_iter; auto. }
      all: auto 10.

      replace
        ([foldr patt_imp r (l₁ ++ p :: a :: l₂); foldr patt_imp r (l₁ ++ a :: q :: l₂)])
        with
          (<[0 := foldr patt_imp r (l₁ ++ p :: a :: l₂)  ]>(
             [foldr patt_imp r (l₁ ++ a :: p :: l₂); foldr patt_imp r (l₁ ++ a :: q :: l₂)]
          ))
        by reflexivity.
      eapply prf_strenghten_premise_iter_meta_meta with (n := 0).
      5: { reflexivity. }
      5: {  apply prf_reorder_iter; auto. }
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
    wf l₁ ->
    wf l₂ ->
    well_formed p ->
    well_formed q ->
    well_formed r ->
    mkMyGoal Γ (l₁ ++ [p] ++ l₂) r ->
    mkMyGoal Γ (l₁ ++ [q] ++ l₂) r ->
    mkMyGoal Γ (l₁ ++ [p or q] ++ l₂) r.
  Proof.
    intros WFl1 WFl2 WFp WFq WFr H H0.
    apply prf_disj_elim_iter_2_meta_meta; auto.
  Defined.

  Tactic Notation "mgDestruct" constr(n) :=
    match goal with
    | |- of_MyGoal (mkMyGoal ?Ctx ?l ?g) =>
      let Htd := fresh "Htd" in
      epose proof (Htd :=take_drop);
      specialize (Htd n l);
      rewrite [take _ _]/= in Htd;
      rewrite [drop _ _]/= in Htd;
      rewrite -Htd; clear Htd;
      epose proof (Htd :=take_drop);
      specialize (Htd 1 (drop n l));
      rewrite [take _ _]/= in Htd;
      rewrite ![drop _ _]/= in Htd;
      rewrite -Htd; clear Htd;
      apply MyGoal_disj_elim; simpl
    end.

  Example exd Γ a b p q c:
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
    toMyGoal. repeat mgIntro.

    mgDestruct 1; auto 10.
  Abort.
  
    
  
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
  Defined.
    
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
  Defined.
  
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
  Defined.

  Lemma pf_iff_proj1 Γ A B:
    well_formed A ->
    well_formed B ->
    Γ ⊢ (A <---> B) ->
    Γ ⊢ (A ---> B).
  Proof.
    intros WFA WFB H. unfold patt_iff in H.
    apply pf_conj_elim_l_meta in H; auto.
  Defined.

  Lemma pf_iff_proj2 Γ A B:
    well_formed A ->
    well_formed B ->
    Γ ⊢ (A <---> B) ->
    Γ ⊢ (B ---> A).
  Proof.
    intros WFA WFB H. unfold patt_iff in H.
    apply pf_conj_elim_r_meta in H; auto.
  Defined.

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

  Lemma prf_conclusion Γ a b:
    well_formed a ->
    well_formed b ->
    Γ ⊢ b ->
    Γ ⊢ (a ---> b).
  Proof.
    intros WFa WFb H. eapply Modus_ponens. 4: apply P1. all: auto.
  Defined.
  

  Lemma prf_equiv_congruence_implicative_ctx Γ p q C:
    well_formed p ->
    well_formed q ->
    is_implicative_context C ->
    Γ ⊢ (p <---> q) ->
    Γ ⊢ (((emplace C p) <---> (emplace C q))).
  Proof.
    intros wfp wfq impC Hiff.
    destruct C.
    induction pcPattern; simpl; unfold is_implicative_context in impC; simpl in impC; inversion impC;
      unfold emplace; simpl.
    - destruct (evar_eqdec pcEvar x); simpl. exact Hiff. apply pf_iff_equiv_refl. auto.
      (*
      + apply A_impl_A. unfold patt_iff. auto.
      + apply prf_conclusion; auto. unfold patt_iff. auto. apply pf_iff_equiv_refl. auto.*)
    - apply pf_iff_equiv_refl. auto.  (*apply prf_conclusion; auto unfold patt_iff. auto. apply pf_iff_equiv_refl. auto.*)
    - unfold emplace in *. simpl in *.
      pose proof (pwf := pcPattern_wf).
      unfold well_formed,well_formed_closed in pwf. simpl in pwf.
      apply andb_prop in pwf. destruct pwf as [pwf1 pwf2].
      apply andb_prop in pwf1. destruct pwf1 as [pwfp1 pwfp2].
      apply andb_prop in pwf2. destruct pwf2 as [pwfc1 pwfc2].
      assert (Hwf1 : well_formed pcPattern1).
      { unfold well_formed,well_formed_closed. rewrite pwfp1 pwfc1. reflexivity. }
      assert (Hwf2 : well_formed pcPattern2).
      { unfold well_formed,well_formed_closed. rewrite pwfp2 pwfc2. reflexivity. }
      
      destruct (decide (count_evar_occurrences pcEvar pcPattern1 ≠ 0)),
      (decide (count_evar_occurrences pcEvar pcPattern2 ≠ 0)); simpl in H0; try lia.
      + remember (free_evar_subst pcPattern1 p pcEvar) as p1.
        remember (free_evar_subst pcPattern2 p pcEvar) as p2.
        remember (free_evar_subst pcPattern1 q pcEvar) as q1.
        remember (free_evar_subst pcPattern2 q pcEvar) as q2.
        assert (pcOneOcc1 : count_evar_occurrences pcEvar pcPattern1 = 1).
        { lia. }
        specialize (IHpcPattern1 ltac:(auto) ltac:(lia)).
        unfold is_implicative_context in IHpcPattern1.
        simpl in IHpcPattern1.
        simpl in impC. rewrite andbT in impC.
        specialize (IHpcPattern1 impC).
        clear IHpcPattern2. (* Can't specialize. *)
        (* There is no occurrence of pcEvar in pcPattern2 (by [n0]).
           Therefore, p2 = q2. We need a lemma for that. *)
        pose proof (Hnoocp := @free_evar_subst_no_occurrence _ pcEvar pcPattern2 p ltac:(lia)).
        pose proof (Hnoocq := @free_evar_subst_no_occurrence _ pcEvar pcPattern2 q ltac:(lia)).
        subst p2 q2. rewrite Hnoocp Hnoocq.
        unfold patt_iff.

        epose proof (H1 := pf_conj_elim_l_meta _ _ _ _ _ IHpcPattern1).
        epose proof (H2 := pf_conj_elim_r_meta _ _ _ _ _ IHpcPattern1).
        Unshelve. 2,3,4,5: subst; auto.
        
        apply conj_intro_meta. 1,2: subst; auto.
        unfold patt_iff in IHpcPattern1.

        * toMyGoal. mgIntro. mgIntro. mgAdd H2. 1,2,3: subst; auto.
          mgApply' 1 5. 1,2: subst; auto.
          mgApply' 0 5. 1,2,3: subst; auto.
          mgExactn 2; subst; auto.

        * toMyGoal. mgIntro. mgIntro. mgAdd H1. 1,2,3: subst; auto.
          mgApply' 1 5. 1,2: subst; auto.
          mgApply' 0 5. 1,2,3: subst; auto.
          mgExactn 2; subst; auto.
      + remember (free_evar_subst pcPattern1 p pcEvar) as p1.
        remember (free_evar_subst pcPattern2 p pcEvar) as p2.
        remember (free_evar_subst pcPattern1 q pcEvar) as q1.
        remember (free_evar_subst pcPattern2 q pcEvar) as q2.
        assert (pcOneOcc1 : count_evar_occurrences pcEvar pcPattern2 = 1).
        { lia. }
        specialize (IHpcPattern2 ltac:(auto) ltac:(lia)).
        unfold is_implicative_context in IHpcPattern1.
        simpl in IHpcPattern1.
        simpl in impC. (*rewrite andbT in impC.*)
        specialize (IHpcPattern2 impC).
        clear IHpcPattern1. (* Can't specialize. *)
        pose proof (Hnoocp := @free_evar_subst_no_occurrence _ pcEvar pcPattern1 p ltac:(lia)).
        pose proof (Hnoocq := @free_evar_subst_no_occurrence _ pcEvar pcPattern1 q ltac:(lia)).
        subst p1 q1. rewrite Hnoocp Hnoocq.
        unfold patt_iff.

        epose proof (H1 := pf_conj_elim_l_meta _ _ _ _ _ IHpcPattern2).
        epose proof (H2 := pf_conj_elim_r_meta _ _ _ _ _ IHpcPattern2).
        Unshelve. 2,3,4,5: subst; auto.
        
        apply conj_intro_meta. 1,2: subst; auto.
        unfold patt_iff in IHpcPattern2.
        
        * toMyGoal. mgIntro. mgIntro. mgAdd H1. 1,2,3: subst; auto.
          mgApply' 0 5. 1,2,3: subst; auto.
          mgApply' 1 5. 1,2: subst; auto.
          mgExactn 2; subst; auto.

        * toMyGoal. mgIntro. mgIntro. mgAdd H2. 1,2,3: subst; auto.
          mgApply' 0 5. 1,2,3: subst; auto.
          mgApply' 1 5. 1,2: subst; auto.
          mgExactn 2; subst; auto.      
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
        * apply Framing_left.
          eapply prf_weaken_conclusion_meta_meta. 4: apply IH2. all: auto.
        * apply Framing_left.
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
        * apply Framing_right.
          eapply prf_weaken_conclusion_meta_meta. 4: apply IH2. all: auto.
        * apply Framing_right.
          eapply prf_weaken_conclusion_meta_meta. 4: apply IH2. all: auto.
  Defined.

  Lemma prf_prop_ex_iff Γ AC p:
    well_formed (patt_exists p) ->
    Γ ⊢ ((subst_ctx AC (patt_exists p)) <---> (patt_exists (subst_ctx AC p))).
  Proof.
    intros Hwf.

    induction AC; simpl.
    - apply pf_iff_equiv_refl; auto.
    -
      assert (Hwfex: well_formed (ex , subst_ctx AC p)).
      { unfold well_formed. simpl.
        pose proof (Hwf' := Hwf).
        unfold well_formed in Hwf. simpl in Hwf.
        apply andb_prop in Hwf. destruct Hwf as [Hwfp Hwfc].
        apply (@wp_sctx _ AC p) in Hwfp. rewrite Hwfp. simpl. clear Hwfp.
        unfold well_formed_closed. unfold well_formed_closed in Hwfc. simpl in Hwfc. simpl.
        apply (@wc_sctx _ AC p 1 0). rewrite Hwfc. reflexivity.
      }
      
      apply pf_iff_iff in IHAC; auto.
      destruct IHAC as [IH1 IH2].
      apply pf_iff_split; auto.
      + pose proof (H := IH1).
        eapply Framing_left in IH1.
        eapply syllogism_intro. 4: apply IH1.
        all:auto.
        remember (subst_ctx AC p) as p'.
        apply Prop_ex_left. all: subst; auto.
      + admit.
    -
      assert (Hwfex: well_formed (ex , subst_ctx AC p)).
      { unfold well_formed. simpl.
        pose proof (Hwf' := Hwf).
        unfold well_formed in Hwf. simpl in Hwf.
        apply andb_prop in Hwf. destruct Hwf as [Hwfp Hwfc].
        apply (@wp_sctx _ AC p) in Hwfp. rewrite Hwfp. simpl. clear Hwfp.
        unfold well_formed_closed. unfold well_formed_closed in Hwfc. simpl in Hwfc. simpl.
        apply (@wc_sctx _ AC p 1 0). rewrite Hwfc. reflexivity.
      }
      
      apply pf_iff_iff in IHAC; auto.
      destruct IHAC as [IH1 IH2].
      apply pf_iff_split; auto.
      + pose proof (H := IH1).
        eapply Framing_right in IH1.
        eapply syllogism_intro. 4: apply IH1.
        all:auto.
        remember (subst_ctx AC p) as p'.
        apply Prop_ex_right. all: subst; auto.
      + admit.
  Abort.


  Lemma and_of_negated_iff_not_impl Γ p1 p2:
    well_formed p1 ->
    well_formed p2 ->
    Γ ⊢ (¬ (¬ p1 ---> p2) <---> ¬ p1 and ¬ p2).
  Proof.
    intros wfp1 wfp2.
    apply conj_intro_meta; auto.
    - toMyGoal.
      mgIntro. mgIntro.
      mgApply' 0 7.
      mgIntro.
      unfold patt_or.
      mgAdd (not_not_elim Γ p2 ltac:(auto)); auto 10.
      mgApply' 0 10.
      mgApply' 2 10.
      mgAdd (not_not_intro Γ (¬ p1) ltac:(auto)); auto 10.
      mgApply' 0 10.
      mgExactn 4. auto 10.
    - toMyGoal.
      mgIntro. mgIntro.
      unfold patt_and.
      mgApply' 0 10.
      unfold patt_or.
      mgIntro.
      mgAdd (not_not_intro Γ p2 ltac:(auto)); auto 10.
      mgApply' 0 10.
      mgApply' 2 10.
      mgAdd (not_not_elim Γ (¬ p1) ltac:(auto)); auto 10.
      mgApply' 0 10.
      mgExactn 4. auto 10.
  Defined.

  Lemma and_impl_2 Γ p1 p2:
    well_formed p1 ->
    well_formed p2 ->
    Γ ⊢ (¬ (p1 ---> p2) <---> p1 and ¬ p2).
  Proof.
    intros wfp1 wfp2.
    apply conj_intro_meta; auto.
    - toMyGoal.
      mgIntro. mgIntro.
      mgApply' 0 10.
      mgIntro.
      unfold patt_or.
      mgAdd (not_not_elim Γ p2 ltac:(auto)); auto 10.
      mgApply' 0 10.
      mgApply' 2 10.
      mgAdd (not_not_intro Γ p1 ltac:(auto)); auto 10.
      mgApply' 0 10.
      mgExactn 4. auto 10.
    - toMyGoal.
      mgIntro. mgIntro.
      mgApply' 0 10.
      unfold patt_or.
      mgIntro.
      mgAdd (not_not_intro Γ p2 ltac:(auto)); auto 10.
      mgApply' 0 10.
      mgApply' 2 10.
      mgAdd (not_not_elim Γ p1 ltac:(auto)); auto 10.
      mgApply' 0 10.
      mgExactn 4.
      auto 10.
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

  Lemma patt_and_comm (A B : Pattern) Γ:
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
    wf l ->
    well_formed r ->
    well_formed r' ->
    mkMyGoal Γ l r' ->
    mkMyGoal Γ l r.
  Proof.
    intros Himp l wfl wfr wfr' H.
    eapply prf_weaken_conclusion_iter_meta_meta.
    4: { apply Himp; auto. }
    all: auto.
  Defined.

  Tactic Notation "mgApplyMeta" uconstr(t) :=
    unshelve (eapply (MyGoal_applyMeta _ _ _ t)).

  Ltac mgLeft := mgApplyMeta (disj_left_intro _ _ _ _ _).
  Ltac mgRight := mgApplyMeta (disj_right_intro _ _ _ _ _).
  
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
      mgIntro. unfold patt_and.
      mgIntro. mgApply' 0 10.
      mgDestruct 1; auto.
      + apply modus_tollens in pip'; auto.
        mgAdd pip'; auto.
        mgLeft; auto 10.
        mgApply' 0 10.
        mgExactn 2; auto 10.
      + apply modus_tollens in qiq'; auto.
        mgAdd qiq'; auto.
        mgRight; auto 10.
        mgApply' 0 10.
        mgExactn 2; auto 10.
    - toMyGoal.
      mgIntro. unfold patt_and.
      mgIntro. mgApply' 0 10.
      mgDestruct 1; auto.
      + mgLeft; auto 10.
        apply modus_tollens in p'ip; auto.
        mgAdd p'ip; auto.
        mgApply' 0 10.
        mgExactn 2; auto 10.
      + mgRight; auto 10.
        apply modus_tollens in q'iq; auto.
        mgAdd q'iq; auto.
        mgApply' 0 10.
        mgExactn 2; auto 10.
        Unshelve. all: auto.
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
      mgIntro.
      mgDestruct 0; auto.
      + mgLeft; auto.
      + mgRight; auto.
    - toMyGoal.
      mgIntro.
      mgDestruct 0; auto.
      + mgLeft; auto.
      + mgRight; auto.
        Unshelve. all: auto.
  Defined.

  Ltac mgSplit := apply conj_intro_meta; auto.
  
  Lemma impl_iff_notp_or_q Γ p q:
    well_formed p ->
    well_formed q ->
    Γ ⊢ ((p ---> q) <---> (¬ p or q)).
  Proof.
    intros wfp wfq.
    mgSplit.
    - toMyGoal. mgIntro.
      mgAdd (A_or_notA Γ p wfp); auto.
      mgDestruct 0; auto.
      + mgRight; auto.
        mgApply' 1 10.
        mgExactn 0; auto.
      + mgLeft; auto.
        mgExactn 0; auto.
    - toMyGoal. mgIntro. mgIntro. unfold patt_or.
      mgApply' 0 10.
      mgApplyMeta (not_not_intro _ _ _); auto.
      mgExactn 1; auto.
      Unshelve. all: auto.
  Defined.

  Lemma p_and_notp_is_bot Γ p:
    well_formed p ->
    Γ ⊢ (⊥ <---> p and ¬ p).
  Proof.
    intros wfp.
    mgSplit.
    - apply bot_elim; auto.
    - unfold patt_and. toMyGoal.
      mgIntro.
      mgApply' 0 10.
      mgAdd (A_or_notA Γ (¬ p) ltac:(auto)); auto 10.
      mgExactn 0; auto 10.
  Defined.

  Lemma weird_lemma Γ A B L R:
    well_formed A ->
    well_formed B ->
    well_formed L ->
    well_formed R ->
    Γ ⊢ (((L and A) ---> (B or R)) ---> (L ---> ((A ---> B) or R))).
  Proof.
    intros wfA wfB wfL wfR.
    toMyGoal. mgIntro. mgIntro.
    mgAdd (A_or_notA Γ A wfA); auto 10.
    mgDestruct 0; auto 10.
    - mgAssert (Htmp: (B or R)); auto 10.
      { mgApply' 1 10. unfold patt_and at 2. mgIntro.
        mgDestruct 3; auto 10.
        + mgApply' 3 10. mgExactn 2; auto 10.
        + mgApply' 3 10. mgExactn 0; auto 10.
      }
      clear Htmp.
      mgDestruct 3; auto 10.
      + mgLeft; auto. mgIntro. mgExactn 3; auto 10.
      + mgRight; auto. mgExactn 3; auto.
    - mgLeft; auto. mgIntro.
      mgApplyMeta (bot_elim _ _ _); auto 10.
      mgApply' 0 10. mgExactn 3; auto.
      Unshelve. all: auto 10.
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
    all: auto.
  Defined.

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

(*   Lemma ex_elim :
    forall φ x Γ,
    Γ ⊢ ((ex , φ) ---> bevar_subst φ (patt_free_evar x) 0).
  Proof.
    .
    pose proof (Ex_quan Γ φ x). unfold instantiate in H.
    eapply Modus_ponens. 4: apply P1.
  Qed. *)

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
      - epose proof (syllogism Γ B A r _ _ _).
        epose proof (Modus_ponens Γ (B ---> A) ((A ---> r) ---> B ---> r)
                    ltac:(auto) ltac:(auto) _ _). auto.
      - epose proof (syllogism Γ A B r _ _ _).
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
      - epose proof (prf_weaken_conclusion Γ l A B _ _ _).
        epose proof (Modus_ponens Γ (A ---> B) ((l ---> A) ---> l ---> B)
                    ltac:(auto) ltac:(auto) _ _). auto.
      - epose proof (prf_weaken_conclusion Γ l B A _ _ _).
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
      rewrite <- evar_open_bevar_subst_same in H0, H1.
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
     17, 18: exact 0.
     all: try apply evar_quantify_well_formed; auto.
     all: try apply subst_patctx_wf; auto.
     1-2: simpl; apply evar_quantify_not_free.
     + eapply subst_patctx_wf in WFC. 2: exact WF2.
       apply andb_true_iff in WFC as [E1 E2]. apply E2.
     + eapply subst_patctx_wf in WFC. 2: exact WF1.
       apply andb_true_iff in WFC as [E1 E2]. apply E2.
  Defined.

  Lemma imp_trans_mixed_meta Γ A B C D :
    well_formed A -> well_formed B -> well_formed C -> well_formed D ->
    Γ ⊢ (C ---> A) -> Γ ⊢ (B ---> D)
  ->
    Γ ⊢ ((A ---> B) ---> C ---> D).
  Proof.
    intros WFA WFB WFC WFD H H0.
    epose proof (prf_weaken_conclusion Γ A B D WFA WFB WFD).
    eapply Modus_ponens in H1; auto.
    epose proof (prf_strenghten_premise Γ A C D WFA WFC WFD).
    eapply Modus_ponens in H2; auto.
    epose proof (syllogism_intro Γ _ _ _ _ _ _ H1 H2). auto.
    Unshelve. all: auto.
  Defined.

  Theorem congruence_iff_helper :
    forall sz ψ, le (Syntax.size ψ) sz ->
     forall φ1 φ2 x Γ (MF : mu_free ψ), well_formed φ1 -> well_formed φ2 ->
     Γ ⊢ (φ1 <---> φ2)
    ->
     well_formed ψ ->
     Γ ⊢ (free_evar_subst ψ φ1 x <---> free_evar_subst ψ φ2 x).
  Proof.
    induction sz; destruct ψ; intros Hsz φ1 φ2 x' Γ MF WF1 WF2 H WFψ.
    6, 8, 9, 10: simpl in Hsz; lia.
    all: try apply pf_iff_equiv_refl; auto.
    1-2: cbn; break_match_goal; auto; apply pf_iff_equiv_refl; auto.
    * simpl in MF, Hsz.
      apply well_formed_app_1 in WFψ as WF1'.
      apply well_formed_app_2 in WFψ as WF2'.
      apply andb_true_iff in MF as [MF1 MF2].
      specialize (IHsz ψ1 ltac:(lia) φ1 φ2 x' Γ MF1 WF1 WF2 H WF1') as IHψ1.
      specialize (IHsz ψ2 ltac:(lia) φ1 φ2 x' Γ MF2 WF1 WF2 H WF2') as IHψ2.
      apply pf_iff_iff in IHψ1. apply pf_iff_iff in IHψ2.
      destruct IHψ1 as [H0 H1], IHψ2 as [H2 H3].
      pose proof (Framing_left Γ (free_evar_subst ψ1 φ1 x') (free_evar_subst ψ1 φ2 x') (free_evar_subst ψ2 φ1 x') H0) as Trans1.
      pose proof (Framing_right Γ (free_evar_subst ψ2 φ1 x') (free_evar_subst ψ2 φ2 x') (free_evar_subst ψ1 φ2 x') H2) as Trans2.
      epose proof (syllogism_intro Γ _ _ _ _ _ _ Trans1 Trans2).
      clear Trans1 Trans2. 2-5: shelve.

      pose proof (Framing_right Γ (free_evar_subst ψ2 φ2 x') (free_evar_subst ψ2 φ1 x') (free_evar_subst ψ1 φ2 x') H3) as Trans1.
      pose proof (Framing_left Γ _ _ (free_evar_subst ψ2 φ1 x') H1) as Trans2.
      epose proof (syllogism_intro Γ _ _ _ _ _ _ Trans1 Trans2).
      apply pf_iff_iff; auto.
      Unshelve.
      1-3, 8-10: apply well_formed_app.
      all: now apply well_formed_free_evar_subst.
    * simpl in MF, Hsz.
      apply well_formed_app_1 in WFψ as WF1'.
      apply well_formed_app_2 in WFψ as WF2'.
      apply andb_true_iff in MF as [MF1 MF2].
      specialize (IHsz ψ1 ltac:(lia) φ1 φ2 x' Γ MF1 WF1 WF2 H WF1') as IHψ1.
      specialize (IHsz ψ2 ltac:(lia) φ1 φ2 x' Γ MF2 WF1 WF2 H WF2') as IHψ2.
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
      epose proof (IHsz (evar_open 0 fx ψ) _ φ1 φ2 x' Γ _ WF1 WF2 H H0).
      cbn.
      pose proof (Ex_quan Γ (free_evar_subst ψ φ1 x') fx).
      pose proof (Ex_quan Γ (free_evar_subst ψ φ2 x') fx).
      unfold instantiate in *.
      rewrite <- evar_open_bevar_subst_same in H2, H3.
      do 2 rewrite <- evar_open_free_evar_subst_swap in H1; auto.
      apply pf_iff_iff in H1; auto. 2-3: shelve. destruct H1 as [IH1 IH2].
      eapply syllogism_intro in H2. 5: exact IH2. 2-4: shelve.
      eapply syllogism_intro in H3. 5: exact IH1. 2-4: shelve.
      apply (Ex_gen _ _ _ fx) in H2. apply (Ex_gen _ _ _ fx) in H3.
      2-7: shelve.
      unfold exists_quantify in H3, H2. simpl in H2, H3.
      erewrite -> evar_quantify_evar_open in H2, H3; auto.
      2-5: shelve.
      apply pf_iff_iff; auto.
      Unshelve.
      20,21: exact 0. all: auto.
      all: try replace (ex , free_evar_subst ψ φ1 x') with (free_evar_subst (ex, ψ) φ1 x') by reflexivity.
      all: try replace (ex , free_evar_subst ψ φ2 x') with (free_evar_subst (ex, ψ) φ2 x') by reflexivity.
      all: try apply well_formed_free_evar_subst; auto.
      rewrite <- evar_open_size. simpl in H. lia.
      now apply mu_free_evar_open.
      1, 4, 5, 7: apply well_formed_free_evar_subst with (x := x') (q := φ1) in WFψ as HE1; auto; simpl in HE1; apply wf_ex_to_wf_body in HE1; apply (HE1 fx).
      5-7, 9: apply well_formed_free_evar_subst with (x := x') (q := φ2) in WFψ as HE1; auto; simpl in HE1; apply wf_ex_to_wf_body in HE1; apply (HE1 fx).
      12: {
         apply well_formed_free_evar_subst with (x:= x') (q := φ1) in WFψ.
         unfold well_formed, well_formed_closed in WFψ.
         apply andb_true_iff in WFψ. destruct WFψ. now simpl in H4. auto. 
      }
      13: {
         apply well_formed_free_evar_subst with (x := x') (q := φ2) in WFψ.
         unfold well_formed, well_formed_closed in WFψ.
         apply andb_true_iff in WFψ. destruct WFψ. now simpl in H4. auto. 
      }
      all: simpl; eapply not_elem_of_larger_impl_not_elem_of.
      all: try apply free_evars_free_evar_subst.
   all: apply sets.not_elem_of_union; auto.
   * inversion MF.
  Defined.

  Lemma and_weaken A B C Γ:
    well_formed A -> well_formed B -> well_formed C ->
    Γ ⊢ (B ---> C)
   ->
    Γ ⊢ ((A and B) ---> (A and C)).
  Proof.
    intros WFA WFB WFC H.
    epose proof (and_impl' Γ A B (A and C) _ _ _). eapply Modus_ponens. 4: exact H0.
    1-2: shelve.
    apply reorder_meta; auto.
    epose proof (prf_strenghten_premise Γ C B (A ---> A and C) _ _ _).
    eapply Modus_ponens. 4: eapply Modus_ponens. 7: exact H1. all: auto.
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
    pose proof (conj_intro Γ B D WFB WFD).
    epose proof (prf_strenghten_premise Γ B A (D ---> B and D) WFB WFA _).
    eapply Modus_ponens in H2; auto. 2: shelve.
    eapply Modus_ponens in H2; auto.
    apply reorder_meta in H2; auto.
    epose proof (prf_strenghten_premise Γ D C (A ---> B and D) WFD WFC _).
    eapply Modus_ponens in H3; auto. 2: shelve.
    eapply Modus_ponens in H3; auto.
    apply reorder_meta in H3; auto.
    epose proof (and_impl' _ _ _ _ _ _ _).
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
    pose proof (pf_conj_elim_l Γ A B WFA WFB).
    epose proof (@impl_and Γ (A and B) A (A and B) C _ _ _ _ H0 H).
    epose proof (and_impl _ _ _ _ _ _ _).
    eapply Modus_ponens in H2. 4: exact H1. 2-3: shelve.
    epose proof (prf_contraction _ _ _ _ _).
    eapply Modus_ponens in H3. 4: exact H2. auto.
    Unshelve. all: unfold patt_and, patt_or, patt_not; auto 20.
  Defined.

End FOL_helpers.

(* Hints *)
#[export]
 Hint Resolve A_impl_A : core.
