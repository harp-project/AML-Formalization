Require Export locally_nameless.

Section FOL_helpers.

Lemma wf_sctx (C : Application_context) (A : Pattern) :
  well_formed A -> well_formed (subst_ctx C A).
Proof.
  intros.
  induction C; unfold well_formed in *. destruct H; split; unfold well_formed_closed in *; simpl.
  - exact H.
  - exact H0.
  - split.
    + destruct H. destruct IHC. simpl. split.
      * exact H1.
      * destruct Prf. exact H3.
    + simpl. unfold well_formed_closed in *. simpl.  split.
      * destruct IHC. exact H1.
      * destruct Prf. exact H1.
  - split.
    + simpl. split.
      * destruct Prf. exact H0.
      * destruct IHC. exact H0.
    + simpl. unfold well_formed_closed in *. simpl. split.
      * destruct Prf. exact H1.
      * destruct IHC. exact H1.
Qed.

Lemma wp_sctx (C : Application_context) (A : Pattern) :
  well_formed_positive A -> well_formed_positive (subst_ctx C A).
Proof.
  intros.
  induction C.
  - auto.
  - simpl. split.
    + exact IHC.
    + unfold well_formed in Prf. destruct Prf. exact H0.
  - simpl. split.
    + unfold well_formed in Prf. destruct Prf. exact H0.
    + exact IHC.
Qed.

Lemma wc_sctx (C : Application_context) (A : Pattern) :
  well_formed_closed_aux A 0 -> well_formed_closed_aux (subst_ctx C A) 0.
Proof.
  intros.
  induction C.
  - auto.
  - simpl. split.
    + exact IHC.
    + unfold well_formed in Prf. destruct Prf. unfold well_formed_closed in H1. exact H1.
  - simpl. split.
    + unfold well_formed in Prf. destruct Prf. unfold well_formed_closed in H1. exact H1.
    + exact IHC.
Qed.

(*Use this tactic for most of the well-formedness related goals*)
Ltac wf_proof := 
  unfold well_formed; unfold well_formed_closed; simpl;
  
  repeat (match goal with
  | H : well_formed _         |- _ => destruct H
  | H0 : well_formed_closed _ |- _ => (unfold well_formed_closed in H0; simpl)
  end);
  
  repeat (match goal with
  | |- _ /\ _ => split
  end);
  
  match goal with
  | H  : well_formed_closed _     |- well_formed_closed _       => exact H
  | H  : well_formed_positive _   |- well_formed_positive (subst_ctx _ _) => eapply (wp_sctx _ _ H)
  | H  : well_formed_closed_aux _ _   |- well_formed_closed_aux (subst_ctx _ _) _ => eapply (wc_sctx _ _ H)
  | H0 : well_formed_positive _   |- well_formed_positive _               => exact H0
  | H1 : well_formed_closed_aux _ _ 
                                  |- well_formed_closed_aux _ _           => exact H1
  |                               |- True                                 => trivial
  | _                                                                     => idtac
  end .

Ltac wf_check := 
match goal with
| |- well_formed _ => admit
| _                => fail
end. 

Lemma A_impl_A (theory : Theory) (A : Pattern)  :
(well_formed A) -> theory ⊢ (A --> A).
Proof. 
  intros.
  epose(_1 := P2 theory A (A --> A) A _ _ _).
  epose(_2 := P1 theory A (A --> A) _ _).

  epose(_3 := Modus_ponens _ _ _ _ _ _2 _1). (*M_p th phi1 phi2 wf_phi1 wf_phi2 phi1_proved phi1->phi2_proved*)
  
  epose(_4 := P1 theory A A _ _).
  
  epose(_5 := Modus_ponens theory _ _ _ _ _4 _3).
  exact _5.
  Unshelve.
  all:wf_proof.
Qed.
  
Lemma P4m (theory : Theory) (A B : Pattern) :
 (well_formed A) -> (well_formed B) -> theory ⊢ ((A --> B) --> ((A --> ¬B) --> ¬A)).
Proof.
  intros. eapply (Modus_ponens theory _ _ _ _).
  - eapply(P1 _ (A --> B) (A --> B --> Bot) _ _).
  - eapply (Modus_ponens _ _ _ _ _).
    + eapply (Modus_ponens _ _ _ _ _).
      * eapply (Modus_ponens _ _ _ _ _).
        -- eapply(P2 _ A B Bot _ _ _).
        -- eapply(P2 _ (A --> B --> Bot) (A --> B) (A --> Bot) _ _ _).
      * eapply (P1 _ (((A --> B --> Bot) --> A --> B) --> (A --> B --> Bot) --> A --> Bot)
                   (A --> B) _ _).
    + eapply (P2 _ (A --> B)
                 ((A --> B --> Bot) --> A --> B)
                 ((A --> B --> Bot) --> A --> Bot) _ _ _).
  Unshelve.
  all: wf_proof.
Qed.



Lemma P4i (theory : Theory) (A : Pattern) :
well_formed A -> theory ⊢ ((A --> ¬A) --> ¬A).
Proof.
  intros. eapply (Modus_ponens _ _ _ _ _).
  - eapply (A_impl_A _ A _). (*In the outdated: A_impl_A = P1*)
  - eapply (P4m _ A A _ _).
  Unshelve.
  all:wf_proof.
Qed.

Lemma reorder (theory : Theory) (A B C : Pattern) :
well_formed A -> well_formed B -> well_formed C -> theory ⊢ ((A --> B --> C) --> ( B --> A --> C)).
Proof.
  intros.
  epose(t1 := (Modus_ponens theory _ _ _ _
              (P1 theory ((A --> B) --> A --> C) B _ _)
              (P1 theory (((A --> B) --> A --> C) --> B --> (A --> B) --> A --> C) (A --> B --> C) _ _))).
  
  pose(ABC := (A --> B --> C)).
  
  eapply (Modus_ponens _ _ _ _ _).
  - eapply (Modus_ponens _ _ _ _ _).
    + eapply(P1 _ B A _ _).
    + eapply(P1 _ (B --> A --> B) (A --> B --> C) _ _).
  - eapply (Modus_ponens _ _ _ _ _).
    + eapply (Modus_ponens _ _ _ _ _).
      * eapply (Modus_ponens _ _ _ _ _).
        -- eapply (Modus_ponens _ _ _ _ _).
          ++ eapply (A_impl_A _ ABC _).
          ++ eapply (Modus_ponens _ _ _ _ _).
            ** eapply (Modus_ponens _ _ _ _ _).
              --- eapply(P2 _ A B C _ _ _).
              --- eapply(P1 _ _ (A --> B --> C) _ _).
            ** eapply(P2 _ ABC ABC ((A --> B) --> (A --> C)) _ _ _).
        -- eapply (Modus_ponens _ _ _ _ _).
          ++ eapply t1.
          ++ eapply(P2 _ ABC ((A --> B) --> (A --> C)) (B --> (A --> B) --> (A --> C)) _ _ _).
      * eapply (Modus_ponens _ _ _ _ _).
        -- eapply (Modus_ponens _ _ _ _ _).
          ++ eapply(P2 _ B (A --> B) (A --> C) _ _ _).
          ++ eapply(P1 _ _ ABC _ _).
        -- eapply(P2 _ ABC (B --> (A --> B) --> A --> C) ((B --> A --> B) --> B --> A --> C) _ _ _).
    + eapply(P2 _ ABC (B --> A --> B) (B --> A --> C) _ _ _).
  Unshelve.
  all:wf_proof.
Qed.

Lemma reorder_meta (theory : Theory) {A B C : Pattern} :
  well_formed A -> well_formed B -> well_formed C ->  
  theory ⊢ (A --> B --> C) -> theory ⊢ (B --> A --> C).
Proof.
  intros.
  eapply (Modus_ponens _ _ _ _ _).
  - exact (P1 _ B A H0 H).
  - eapply (Modus_ponens _ _ _ _ _).
    + eapply (Modus_ponens _ _ _ _ _).
      * eapply (Modus_ponens _ _ _ _ _).
        -- exact H2.
        -- eapply(P2 _ A B C _ _ _).
      * assert (well_formed ((A --> B) --> A --> C)).
        -- shelve. 
        -- exact (P1 _ ((A --> B) --> A --> C) B H3 H0).
    + assert(well_formed (A --> B)).
      * shelve.
      * assert(well_formed (A --> C)).
        -- shelve.
        -- exact (P2 _ B (A --> B) (A --> C) H0 H3 H4).
  Unshelve.
  all:wf_proof.
Qed.

Lemma syllogism (theory : Theory) (A B C : Pattern) :
  well_formed A -> well_formed B -> well_formed C -> theory ⊢ ((A --> B) --> (B --> C) --> (A --> C)).
Proof.
  intros.
  eapply (reorder_meta _ _ _ _).
  eapply (Modus_ponens _ _ _ _ _).
  - eapply(P1 _ (B --> C) A _ _).
  - eapply (Modus_ponens _ _ _ _ _).
    + eapply (Modus_ponens _ _ _ _ _).
      * eapply (P2 _ A B C _ _ _).
      * eapply (P1 _ ((A --> B --> C) --> (A --> B) --> A --> C) (B --> C) _ _).
    + eapply (P2 _ (B --> C) (A --> B --> C) ((A --> B) --> A --> C) _ _ _).
  Unshelve.
  all:wf_proof.
Qed.

Lemma syllogism_intro (theory : Theory) (A B C : Pattern) :
  well_formed A -> well_formed B -> well_formed C -> theory ⊢ (A --> B) -> theory ⊢ (B --> C) -> theory ⊢ (A --> C).
Proof.
  intros.
  eapply (Modus_ponens _ _ _ _ _).
  - exact H2.
  - eapply (Modus_ponens _ _ _ _ _).
    + exact H3.
    + eapply (reorder_meta _ _ _ _). exact (syllogism _ A B C H H0 H1).
  Unshelve.
  all:wf_proof.
Qed.

Lemma modus_ponens (theory : Theory) ( A B : Pattern) :
  well_formed A -> well_formed B -> theory ⊢ (A --> (A --> B) --> B).
Proof.
  intros.
  eapply (Modus_ponens _ _ _ _ _).
    - eapply (P1 _ A (A --> B) _ _).
    - eapply (Modus_ponens _ _ _ _ _).
      + eapply (Modus_ponens _ _ _ _ _).
        * eapply (A_impl_A _ (A --> B) _).
        * eapply (P2 _ (A --> B) A B _ _ _).
      + eapply (reorder_meta _ _ _ _).
        * eapply (syllogism _ A ((A --> B) --> A) ((A --> B) --> B) _ _ _).
  Unshelve.
  all:wf_proof.
Qed.

Lemma not_not_intro (theory : Theory) (A : Pattern) :
  well_formed A -> theory ⊢ (A --> ¬(¬A)).
Proof.
  intros.
  assert(well_formed Bot).
  shelve.
  exact (modus_ponens _ A Bot H H0).
  Unshelve.
  all:wf_proof.
Qed.

Lemma deduction (theory : Theory) (A B : Pattern) :
  well_formed A -> well_formed B -> theory ⊢ A -> theory ⊢ B -> theory ⊢ (A --> B).
Proof.
  intros.
  eapply (Modus_ponens _ _ _ _ _).
  - exact H2.
  - eapply (P1 _ B A _ _).
  Unshelve.
  all:wf_proof.
Qed.

Lemma P4_intro (theory : Theory) (A B : Pattern)  :
well_formed A -> well_formed B -> 
theory ⊢ ((¬ B) --> (¬ A)) -> theory ⊢ (A --> B).
Proof.
  intros.
  epose (Modus_ponens theory _ _ _ _ H1 (P4m theory (¬ B) (¬ A) _ _)).
  epose (P1 theory (¬ ¬A) (¬ B) _ _).
  epose (syllogism_intro theory (¬ (¬ A)) (¬ B --> ¬ (¬ A)) (¬ (¬ B)) _ _ _ m0 m).
  epose (not_not_intro theory A _).
  epose (not_not_intro theory B _).
  epose (syllogism_intro theory A (¬ (¬ A)) (¬ (¬ B)) _ _ _ m2 m1).
  unfold patt_not in m4.
  epose (P3 theory B _).
  epose (syllogism_intro theory A ((B --> Bot) --> Bot) B _ _ _ m4 m5).
  exact m6.
  
  Unshelve.
  (*TODO: Investigate why this wf_proof doesn't finish...*)
  (* all:wf_proof. *)
  all:wf_check.
Admitted.

Lemma P4 (theory : Theory) (A B : Pattern)  :
well_formed A -> well_formed B -> 
theory ⊢ (((¬ A) --> (¬ B)) --> (B --> A)).
Proof.
  intros.
  epose (P3 theory A _).
  epose (P1 theory (((A --> Bot) --> Bot) --> A) B _ _).
  epose (P2 theory (B) ((A --> Bot) --> Bot) (A) _ _ _).
  epose (Modus_ponens theory _ _ _ _ m m0).
  epose (Modus_ponens theory _ _ _ _ m2 m1).
  epose (P1 theory ((B --> (A --> Bot) --> Bot) --> B --> A) ((A --> Bot) --> (B --> Bot)) _ _ ).
  epose (Modus_ponens theory _ _ _ _ m3 m4).
  epose (P2 theory ((A --> Bot) --> (B --> Bot)) (B --> (A --> Bot) --> Bot) (B --> A) _ _ _).
  epose (Modus_ponens theory _ _ _ _ m5 m6).
  epose (reorder theory (A --> Bot) (B) (Bot) _ _ _).
  eapply (Modus_ponens theory _ _ _ _ m8 m7).
  Unshelve.
  (*TODO: This wf_proof doesn't finish too*)
  (* 1-3: wf_proof. assert (theory ⊢ ((((A --> Bot) --> Bot) --> A) -->
        B --> ((A --> Bot) --> Bot) --> A)). auto. clear m0. *)
  (* all:try (timeout 2 wf_proof). *)
  (* Too slow because of unfolding hypothesises in posed lemmas too *)
  (* all:wf_proof. *)
  all:wf_check.
Admitted.

Lemma conj_intro (theory : Theory) (A B : Pattern) :
well_formed A -> well_formed B -> theory ⊢ (A --> B --> (A and B)).
Proof.
  intros.
  epose(tB := (A_impl_A theory B _)).
  epose(t1 := Modus_ponens theory _ _ _ _ (P2 _ (¬(¬A) --> ¬B) A Bot _ _ _)
                                           (P1 _ _ B _ _)).
  epose(t2 := Modus_ponens theory _ _ _ _  (reorder_meta _ _ _ _ (P4 _ (¬A) B _ _))
                                          (P1 _ _ B _ _)).
  epose(t3'' := Modus_ponens theory _ _ _ _ (P1 _ A (¬(¬A) --> ¬B) _ _)
                                           (P1 _ _ B _ _)).
  epose(t4 := Modus_ponens theory _ _ _ _ tB
                                          (Modus_ponens theory _ _ _ _ t2
                                                                       (P2 _ B B _ _ _ _))).
  epose(t5'' := 
        Modus_ponens theory _ _ _ _ t4
                                    (Modus_ponens theory _ _ _ _ t1
                                                                 (P2 _ B ((¬(¬A) --> ¬B) --> ¬A)
                                                                 (((¬(¬A) --> ¬B) --> A) --> ¬(¬(¬A) --> ¬B)) _ _ _))).
  
  epose(tA := (P1 theory A B) _ _).
  epose(tB' := Modus_ponens theory _ _ _ _ tB
                                          (P1 _ (B --> B) A _ _)).
  epose(t3' := Modus_ponens theory _ _ _ _ t3''
                                          (P2 _ B A ((¬(¬A) --> ¬B) --> A) _ _ _)).
  epose(t3 := Modus_ponens theory _ _ _ _ t3'
                                         (P1 _ ((B --> A) --> B --> (¬ (¬ A) --> ¬ B) --> A) A _ _)).
  epose(t5' := Modus_ponens theory _ _ _ _ t5''
                                          (P2 _ B ((¬(¬A) --> ¬B) --> A) (¬(¬(¬A) --> ¬B)) _ _ _)).
  epose(t5 := Modus_ponens theory _ _ _ _ t5' 
                                         (P1 _ ((B --> (¬ (¬ A) --> ¬ B) --> A) --> B --> ¬ (¬ (¬ A) --> ¬ B))
                    A _ _)).
  epose(t6 := Modus_ponens theory _ _ _ _ tA
                                         (Modus_ponens theory _ _ _ _ t3
                                                                      (P2 _ A (B --> A) (B --> (¬(¬A) --> ¬B) --> A) _ _ _))).
  epose(t7 := Modus_ponens theory _ _ _ _ t6 
                                         (Modus_ponens theory _ _ _ _ t5 
                                                                      (P2 _ A (B --> (¬(¬A) --> ¬B) --> A) (B --> ¬(¬(¬A) --> ¬B)) _ _ _))).
  unfold patt_and.  unfold patt_or.
  exact t7.
  Unshelve.
  (*TODO: This doesn't finish too*)
  (* all:wf_proof. *)
  all:wf_check.
Admitted.

Lemma conj_intro_meta (theory : Theory) (A B : Pattern) :
  well_formed A -> well_formed B -> theory ⊢ A -> theory ⊢ B -> theory ⊢ (A and B).
Proof.
  intros.
  eapply (Modus_ponens _ _ _ _ _).
  - exact H2.
  - eapply (Modus_ponens _ _ _ _ _).
    + exact H1.
    + exact (conj_intro _ A B H H0).
  Unshelve.
  all:unfold patt_and.
  all:wf_proof.
Qed.

(* Lemma conj_intro_meta_e (theory : Theory) (A B : Pattern) : *) 
Definition conj_intro_meta_e := conj_intro_meta.    (*The same as conj_intro_meta*)

Lemma disj (theory : Theory) (A B : Pattern) :
  well_formed A -> well_formed B -> theory ⊢ (A --> B --> (A or B)).
Proof.
  intros. unfold patt_or.
  
  epose(t1 := (P1 theory B (¬A) _ _)).
  
  epose(t2 := (P1 theory (B --> (¬A --> B)) A _ _)).
  
  epose(t3 := Modus_ponens theory _ _ _ _ t1 t2).
  
  exact t3.
  Unshelve.
  all:wf_proof.
Qed.

Lemma disj_intro (theory : Theory) (A B : Pattern) :
  well_formed A -> well_formed B -> theory ⊢ A -> theory ⊢ B -> theory ⊢ (A or B).
Proof.
  intros.
  eapply (Modus_ponens _ _ _ _ _).
  - exact H2.
  - eapply (Modus_ponens _ _ _ _ _).
    + exact H1.
    + exact (disj _ A B H H0).
  Unshelve.
  all:wf_proof.
Qed.

Lemma syllogism_4_meta (theory : Theory) (A B C D : Pattern) :
  well_formed A -> well_formed B -> well_formed C -> well_formed D ->
  theory ⊢ (A --> B --> C) -> theory ⊢ (C --> D) -> theory ⊢ (A --> B --> D).
Proof.
  intros.
  eapply (Modus_ponens _ _ _ _ _).
  - exact H3.
  - eapply (Modus_ponens _ _ _ _ _).
    + eapply (Modus_ponens _ _ _ _ _).
      * eapply (Modus_ponens _ _ _ _ _).
        -- eapply (Modus_ponens _ _ _ _ _).
          ++ exact H4.
          ++ eapply (P1 _ (C --> D) B _ _).
        -- eapply (P2 _ B C D _ _ _).
      * eapply (P1 _ ((B --> C) --> B --> D) A _ _).
    + eapply (P2 _ A (B --> C) (B --> D) _ _ _).
  Unshelve.
  all:wf_proof.
Qed.

Lemma bot_elim (theory : Theory) (A : Pattern) :
  well_formed A -> theory ⊢ (Bot --> A).
Proof.
  intros.
  eapply (Modus_ponens _ _ _ _ _).
  - eapply (Modus_ponens _ _ _ _ _).
    + eapply (Modus_ponens _ _ _ _ _).
      * eapply (Modus_ponens _ _ _ _ _).
        -- eapply (P1 _ Bot Bot _ _).
        -- eapply (P2 _ Bot Bot Bot _ _ _).
      * eapply (P4 _ Bot Bot _ _).
    + eapply (P1 _ (Bot --> Bot) (A --> Bot) _ _).
  - eapply (P4 _ A Bot _ _).
  Unshelve.
  all:wf_proof.
Qed.

Lemma modus_ponens' (theory : Theory) (A B : Pattern) :
  well_formed A -> well_formed B -> theory ⊢ (A --> (¬B --> ¬A) --> B).
Proof.
  intros.
  assert(well_formed (¬ B --> ¬ A)).
  shelve.
  exact (reorder_meta theory H1 H H0 (P4 _ B A H0 H)).
  Unshelve.
  all:wf_proof.
Qed.

Lemma disj_right_intro (theory : Theory) (A B : Pattern) :
  well_formed A -> well_formed B -> theory ⊢ (B --> (A or B)).
Proof.
  intros.
  assert(well_formed (¬A)).
  shelve.
  exact (P1 _ B (¬A) H0 H1).
  Unshelve.
  all:wf_proof.
Qed.

Lemma disj_left_intro (theory : Theory) (A B : Pattern) :
  well_formed A -> well_formed B -> theory ⊢ (A --> (A or B)).
Proof.
  intros.
  eapply (syllogism_4_meta _ _ _ _ _ _ _ _ _ (modus_ponens _ A Bot _ _) (bot_elim _ B _)).
  Unshelve.
  all:wf_proof. 
Qed.

(*TODO: Is this redundant?*)
Lemma not_not_elim (theory : Theory) (A : Pattern) :
  well_formed A -> theory ⊢ (¬(¬A) --> A).
Proof.
  intros.
  unfold patt_not.
  exact (P3 theory A H).
Qed.

Lemma double_neg_elim (theory : Theory) (A B : Pattern) :
  well_formed A -> well_formed B -> theory ⊢ (((¬(¬A)) --> (¬(¬B))) --> (A --> B)).
Proof.
  intros.
  eapply (syllogism_intro _ _ _ _ _ _ _).
  - eapply (P4 _ (¬A) (¬B) _ _).
  - eapply (P4 _ B A _ _).
  Unshelve.
  all:wf_proof.
Qed.

Lemma double_neg_elim_meta (theory : Theory) (A B : Pattern) :
  well_formed A -> well_formed B -> 
  theory ⊢ ((¬(¬A)) --> (¬(¬B))) -> theory ⊢ (A --> B).
Proof.
  intros.
  eapply (Modus_ponens _ _ _ _ _).
  - exact H1.
  - exact (double_neg_elim _ A B H H0).
  Unshelve.
  all:wf_proof.
Qed.

Lemma P4_rev_meta (theory : Theory) (A B : Pattern) :
  well_formed A -> well_formed B -> theory ⊢ (A --> B) -> theory ⊢ ((A --> B) --> (¬B --> ¬A)).
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
  all:wf_proof.
Qed.

Lemma P4m_neg (theory : Theory) (A B : Pattern) :
  well_formed A -> well_formed B -> theory ⊢ ((¬B --> ¬A) --> (A --> ¬B) -->  ¬A).
Proof.
  intros.
  epose (PT := (P4 theory B A _ _)).
  eapply (syllogism_intro _ _ _ _ _ _ _).
  - exact PT.
  - eapply (P4m _ _ _ _ _).
  Unshelve.
  all:wf_proof.
Qed.

Lemma not_not_impl_intro_meta (theory : Theory) (A B : Pattern) :
  well_formed A -> well_formed B -> theory ⊢ (A --> B) -> theory ⊢ ((¬¬A) --> (¬¬B)).
Proof.
  intros.
  epose (NN1 := not_not_elim theory A _).
  epose (NN2 := not_not_intro theory B _).
  
  epose (S1 := syllogism_intro _ _ _ _ _ _ _ H1 NN2).
  
  epose (S2 := syllogism_intro _ _ _ _ _ _ _ NN1 S1).
  exact S2.
  Unshelve.
  all:wf_proof.
Qed.

Lemma not_not_impl_intro (theory : Theory) (A B : Pattern) :
  well_formed A -> well_formed B -> theory ⊢ ((A --> B) --> ((¬¬A) --> (¬¬B))).
Proof.
  intros.
  
  epose (S1 := syllogism theory (¬¬A) A B _ _ _).
  
  epose (MP1 := Modus_ponens _ (¬ (¬ A) --> A) ((A --> B) --> ¬ (¬ A) --> B) _ _ (not_not_elim _ A _) S1).
  
  epose(NNB := not_not_intro theory B _).

  epose(P1 := (P1 theory (B --> ¬ (¬ B)) (¬¬A) _ _)).
  
  epose(MP2 := Modus_ponens _ _ _ _ _ NNB P1).
  
  epose(P2 := (P2 theory (¬¬A) B (¬¬B) _ _ _)).
  
  epose(MP3 := Modus_ponens _ _ _ _ _ MP2 P2).
  
  eapply syllogism_intro with (B := (¬ (¬ A) --> B)).
    - shelve.
    - shelve.
    - shelve.
    - assumption.
    - assumption.
  Unshelve.
  (* TODO: Doesn't finish
  all:wf_proof. *)
  all:wf_check.
Admitted.

Lemma contraposition (theory : Theory) (A B : Pattern) : 
  well_formed A -> well_formed B -> 
  theory ⊢ ((A --> B) --> ((¬ B) --> (¬ A))).
Proof.
  intros.
  epose(P4 theory (¬ A) (¬ B) _ _).
  apply syllogism_intro with (B := (¬ (¬ A) --> ¬ (¬ B))).
  - shelve.
  - shelve.
  - shelve.
  - eapply (not_not_impl_intro _ _ _ _ _).
  - exact m. (* apply (P4 _ _ _). shelve. shelve. *)
  Unshelve.
  all:wf_proof.
Qed.

Lemma or_comm_meta (theory : Theory) (A B : Pattern) :
  well_formed A -> well_formed B ->
  theory ⊢ (A or B) -> theory ⊢ (B or A).
Proof.
  intros. unfold patt_or in *.
  
  epose (P4 := (P4 theory A (¬B) _ _)).
  
  epose (NNI := not_not_intro theory B _).
  
  epose (SI := syllogism_intro theory _ _ _ _ _ _ H1 NNI).
  
  eapply (Modus_ponens _ _ _ _ _).
  - exact SI.
  - exact P4.
  Unshelve.
  all:wf_proof.
Qed.

Lemma A_implies_not_not_A_alt (theory : Theory) (A : Pattern) :
  well_formed A -> theory ⊢ A -> theory ⊢ (¬( ¬A )).
Proof.
  intros. unfold patt_not.
  epose (NN := not_not_intro theory A _).
  
  epose (MP := Modus_ponens _ _ _ _ _ H0 NN).
  assumption.
  Unshelve.
  all:wf_proof.
Qed.

Lemma P5i (theory : Theory) (A B : Pattern) :
  well_formed A -> well_formed B -> theory ⊢ (¬ A --> (A --> B)).
Proof.
  intros.
  
  epose (Ax1 := (P1 theory (¬A) (¬B) _ _)).
  
  epose (Ax2 := (P4 theory B A _ _)).
  
  epose (TRANS := syllogism_intro _ _ _ _ _ _ _ Ax1 Ax2).
  assumption.
  Unshelve.
  all:wf_proof.
Qed.

Lemma false_implies_everything (theory : Theory) (phi : Pattern) :
  well_formed phi -> theory ⊢ (Bot --> phi).
Proof.
  intro.
  
  epose (B_B := (A_impl_A theory Bot _)).
  epose (P4 := P5i theory Bot phi _ _).
  
  eapply (Modus_ponens _ _ _ _ _) in P4.
  - assumption.
  - assumption.
  Unshelve.
  all:wf_proof.
Qed.


(* Goal  forall (A B : Pattern) (theory : Theory) , well_formed A -> well_formed B ->
  theory ⊢ (A $ Bot $ B --> Bot).
Proof.
  intros.
  epose (Prop_bott_right theory A H).
  epose (Framing_left theory (A $ Bot) (Bot) B (m)).
  epose (Prop_bott_left theory B H0).
  epose (syllogism_intro theory _ _ _ _ _ _ (m0) (m1)).
  exact m2.
  Unshelve.
  all:wf_proof.
Qed. *)

(*Was an axiom in AML_definition.v*)
Lemma Prop_bot (theory : Theory) (C : Application_context) :
  theory ⊢ ((subst_ctx C patt_bott) --> patt_bott).
Proof.
  induction C.
  - simpl. eapply false_implies_everything. shelve.
  - simpl. epose (Framing_left theory (subst_ctx C Bot) (Bot) p IHC).
           epose (syllogism_intro theory _ _ _ _ _ _ (m) (Prop_bott_left theory p Prf)). exact m0.
  - simpl. epose (Framing_right theory (subst_ctx C Bot) (Bot) p IHC).
           epose (syllogism_intro theory _ _ _ _ _ _ (m) (Prop_bott_right theory p Prf)). exact m0.
  Unshelve.
  all:wf_proof.
  all: assert(well_formed Bot).
  all:wf_proof.
Qed.

(*Was an axiom in AML_definition.v*)
Lemma Framing (theory : Theory) (C : Application_context) (A B : Pattern):
  well_formed A -> well_formed B -> theory ⊢ (A --> B) -> theory ⊢ ((subst_ctx C A) --> (subst_ctx C B)).
Proof.
  induction C; intros.
  - simpl. exact H1.
  - simpl. epose (Framing_left theory (subst_ctx C A) (subst_ctx C B) p (IHC _ _ H1)). exact m.
   - simpl. epose (Framing_right theory (subst_ctx C A) (subst_ctx C B) p (IHC _ _ H1)). exact m.
  Unshelve.
  all:wf_proof.
Qed.

Lemma A_implies_not_not_A_ctx (theory : Theory) (A : Pattern) (C : Application_context) :
  well_formed A -> theory ⊢ A -> theory ⊢ (¬ (subst_ctx C ( ¬A ))).
Proof.
  intros.
  epose (ANNA := A_implies_not_not_A_alt theory _ _ H0).
  replace (¬ (¬ A)) with ((¬ A) --> Bot) in ANNA. 2: auto.
  epose (EF := Framing _ C (¬ A) Bot _ _ ANNA).
  epose (PB := Prop_bot theory C).
  
  epose (TRANS := syllogism_intro _ _ _ _ _ _ _ EF PB).
  
  unfold patt_not.
  assumption.
  Unshelve.
  2,4:assert (well_formed (¬ A)).
  6,7:assert (well_formed (Bot)).
  all:wf_proof.
Qed.

Lemma A_implies_not_not_A_alt_theory (G : Theory) (A : Pattern) :
  well_formed A -> G ⊢ A -> G ⊢ (¬( ¬A )).
Proof.
  intros. unfold patt_not.
  epose (NN := not_not_intro G A _).
  
  epose (MP := Modus_ponens G _ _ _ _ H0 NN).
  
  assumption.
  Unshelve.
  all:wf_proof.
Qed.

(* Lemma equiv_implies_eq (theory : Theory) (A B : Pattern) :
  well_formed A -> well_formed B -> theory ⊢ (A <--> B) -> theory ⊢ ()
 *) (*Need equal*)
 
(* Lemma equiv_implies_eq_theory *)

(*...Missing some lemmas because of the lack of defidness definition...*)

Lemma ctx_bot_prop (theory : Theory) (C : Application_context) (A : Pattern) :
  well_formed A -> theory ⊢ (A --> Bot) -> theory ⊢ (subst_ctx C A --> Bot).
Proof.
  intros.
  epose (FR := Framing theory C A Bot _ _ H0).
  epose (BPR := Prop_bot theory C).
  
  epose (TRANS := syllogism_intro _ _ _ _ _ _ _ FR BPR).
  
  assumption.
  Unshelve.
  4: assert (well_formed (Bot)).
  all:wf_proof.
Qed.

Lemma not_not_A_ctx_implies_A (theory : Theory) (C : Application_context) (A : Pattern):
  well_formed A -> theory ⊢ (¬ (subst_ctx C ( ¬A ))) -> theory ⊢ A.
Proof.
  intros.
  unfold patt_not in H0 at 1.
  
  epose (BIE := false_implies_everything theory (subst_ctx C Bot) _).
  
  epose (TRANS := syllogism_intro _ _ _ _ _ _ _ H0 BIE).
  
  induction C.
  - simpl in TRANS.
    epose (NN := not_not_elim theory A _).
    epose (MP := Modus_ponens _ _ _ _ _ TRANS NN). assumption.
  - eapply IHC.
  Unshelve.
  Abort.
  
Definition empty_theory := {|patterns := Empty_set Pattern|}.
Lemma exclusion (G : Theory) (A : Pattern) :
  well_formed A -> G ⊢ A -> G ⊢ (A --> Bot) -> G ⊢ Bot.
Proof.
  intros.
  epose(Modus_ponens G A Bot _ _ H0 H1).
  assumption.
  Unshelve.
  all:wf_proof.
Qed.

Axiom exclusion_axiom : forall G A,
  G ⊢ A -> G ⊢ (¬ A) -> False.

Axiom or_or : forall G A,
G ⊢ A \/ G ⊢ (¬ A).

(* Axiom extension : forall G A B,
  G ⊢ A -> (Add Sigma_pattern G B) ⊢ A. *)

(* Lemma empty_theory_implies_any A : forall G,
  empty_theory ⊢ A -> G ⊢ A. *)

(* Lemma equiv_cong G phi1 phi2 C x :
  (G ⊢ (phi1 <~> phi2)) -> G ⊢ ((e_subst_var C phi1 x) <~> (e_subst_var C phi2 x)). *)

(* Lemma eq_refl
  (phi : Sigma_pattern) (theory : Ensemble Sigma_pattern) :
    theory ⊢ (phi ~=~ phi). *)

(* Lemma eq_trans
  (phi1 phi2 phi3 : Sigma_pattern) (theory : Ensemble Sigma_pattern) :
    theory ⊢ (phi1 ~=~ phi2) -> theory ⊢ (phi2 ~=~ phi3) ->
    theory ⊢ (phi1 ~=~ phi3). *)

(* Lemma eq_symm
  (phi1 phi2 : Sigma_pattern)  (theory : Ensemble Sigma_pattern) :
    theory ⊢ (phi1 ~=~ phi2) -> theory ⊢ (phi2 ~=~ phi1). *)

(* Lemma eq_evar_subst
  (x : EVar) (phi1 phi2 psi : Sigma_pattern) (theory : Ensemble Sigma_pattern) :
    theory ⊢ (phi1 ~=~ phi2) ->
    theory ⊢ ((e_subst_var psi phi1 x) ~=~ (e_subst_var psi phi2 x)). *)

(* Lemma A_implies_A_totality A:
  A proved -> |_ A _| proved. *)

(* Lemma A_totality_implies_A A:
  |_ A _| proved -> A proved. *)

(* Lemma universal_instantiation (theory : Theory) (A : Pattern) (x y : evar):
  theory ⊢ ((all' x, A) --> (e_subst_var A y x)). *)
