Require Export locally_nameless.
Require Import Coq.Program.Equality.

Section FOL_helpers.

Ltac wf_check := 
match goal with
| |- well_formed _ => admit
| _                => fail
end.

(*TODO: Uncomment this and replace wf_checks with wf_proof and admitted with qed after getting rid of conflict*)
(* Ltac wf_proof := 
  unfold well_formed; unfold well_formed_closed; simpl;
  
  (*All hypothesises wf_closed_aux or wf_positive form*)
  repeat (match goal with
  | H : well_formed _         |- _ => destruct H
  | H0 : well_formed_closed _ |- _ => (unfold well_formed_closed in H0; simpl)
  end);
  
  (*Split all goals*)
  repeat (match goal with
  | |- _ /\ _ => split
  end);
  
  (*Solve them*)
  match goal with
  | H  : well_formed_closed _     |- well_formed_closed _       => exact H
  | H0 : well_formed_positive _   |- well_formed_positive _     => exact H0
  | H1 : well_formed_closed_aux _ _ 
                                  |- well_formed_closed_aux _ _ => exact H1
  |                               |- True                       => trivial
  | _                                                           => idtac
  end . *)

Lemma A_impl_A (theory : Theory) (A : Pattern)  :
(well_formed A) -> theory |- (A --> A).
Proof. 
  intros.
  assert(well_formed (A --> A)).
  shelve.  
  pose(_1 := P2 theory A (A --> A) A H H0 H).
  pose(_2 := P1 theory A (A --> A) H H0).

  assert(well_formed (A --> (A --> A) --> A)).
  shelve.
  assert(well_formed ((A --> (A --> A) --> A) --> (A --> A --> A) --> A --> A)).
  shelve.
  pose(_3 := Modus_ponens _ _ _ H1 H2 _2 _1). (*M_p th phi1 phi2 wf_phi1 wf_phi2 phi1_proved phi1->phi2_proved*)
  
  pose(_4 := P1 theory A A H H).
  
  assert(well_formed ((A --> A --> A))).
  shelve.
  assert(well_formed ((A --> A --> A) --> A --> A)).
  shelve.
  
  pose(_5 := Modus_ponens theory _ _ H3 H4 _4 _3).
  exact _5.
  Unshelve.
  all:wf_check.
Admitted.
  
Lemma P4m (A B : Pattern) (theory : Theory) :
 (well_formed A) -> (well_formed B) -> theory |- ((A --> B) --> ((A --> ¬B) --> ¬A)).
Proof.
  intros. eapply (Modus_ponens theory _ _ ).
  - shelve.
  - shelve.
  - eapply(P1 _ (A --> B) (A --> B --> Bot)).
    -- shelve.
    -- shelve.
  - eapply Modus_ponens.
    + shelve.
    + shelve.
    + eapply Modus_ponens.
      * shelve.
      * shelve.
      * eapply Modus_ponens.
        -- shelve.
        -- shelve.
        -- eapply(P2 _ A B Bot).
          ** shelve.
          ** shelve.
          ** shelve.
        -- eapply(P2 _ (A --> B --> Bot) (A --> B) (A --> Bot)).
          ** shelve.
          ** shelve.
          ** shelve.
      * eapply (P1 _ (((A --> B --> Bot) --> A --> B) --> (A --> B --> Bot) --> A --> Bot)
                   (A --> B)).
        -- shelve.
        -- shelve.
    + eapply (P2 _ (A --> B)
                 ((A --> B --> Bot) --> A --> B)
                 ((A --> B --> Bot) --> A --> Bot)).
      * shelve.
      * shelve.
      * shelve.
  Unshelve.
  all:wf_check.
Admitted.



Lemma P4i (theory : Theory) (A : Pattern) :
well_formed A -> theory |- ((A --> ¬A) --> ¬A).
Proof.
  intros. eapply Modus_ponens.
  (* assert (well_formed (A --> A)). Needed for proving 1' and to apply 2'*)
  - shelve. (*  exact H0. *)
  - shelve. (* wf_proof H. *)
  - eapply (A_impl_A _ A). (*2'*) (*In the outdated: A_impl_A ?= P1*)
    + exact H.
  - eapply (P4m A A _).
    + exact H.
    + exact H.
  Unshelve.
  all:wf_check.
Admitted.

Lemma reorder (theory : Theory) (A B C : Pattern) :
well_formed A -> well_formed B -> well_formed C -> theory |- ((A --> B --> C) --> ( B --> A --> C)).
Proof.
  intros.
  (*Helping hypothesises inside t1*)
  assert(well_formed ((A --> B) --> A --> C)).
  shelve.
  assert(well_formed (((A --> B) --> A --> C) --> B --> (A --> B) --> A --> C)).
  shelve.
  assert(well_formed (A --> B --> C)).
  shelve.
  
  (*Helping hypothesises for t1*)
  assert(well_formed
   (((A --> B) --> A --> C) -->
    B --> (A --> B) --> A --> C)).
  shelve.
  assert(well_formed
   ((((A --> B) --> A --> C) --> B --> (A --> B) --> A --> C) -->
    (A --> B --> C) --> ((A --> B) --> A --> C) --> B --> (A --> B) --> A --> C)).
  shelve.
  pose(t1 := (Modus_ponens theory _ _ H5 H6
              (P1 theory ((A --> B) --> A --> C) B H2 H0)
              (P1 theory (((A --> B) --> A --> C) --> B --> (A --> B) --> A --> C) (A --> B --> C) H3 H4))).
  
  pose(ABC := (A --> B --> C)).
  
  eapply Modus_ponens.
  - shelve.
  - shelve.
  - eapply Modus_ponens.
    + shelve.
    + shelve.
    + eapply(P1 _ B A).
      * shelve.
      * shelve.
    + eapply(P1 _ (B --> A --> B) (A --> B --> C)).
      * shelve.
      * shelve.
  - eapply Modus_ponens.
    + shelve.
    + shelve.
    + eapply Modus_ponens.
      * shelve.
      * shelve.
      * eapply Modus_ponens.
        -- shelve.
        -- shelve.
        -- eapply Modus_ponens.
          ++ shelve.
          ++ shelve.
          ++ eapply (A_impl_A _ ABC).
            ** shelve.
          ++ eapply Modus_ponens.
            ** shelve.
            ** shelve.
            ** eapply Modus_ponens.
              --- shelve.
              --- shelve.
              --- eapply(P2 _ A B C).
                +++ shelve.
                +++ shelve.
                +++ shelve.
              --- eapply(P1 _ _ (A --> B --> C)).
                +++ shelve.
                +++ shelve.
            ** eapply(P2 _ ABC ABC ((A --> B) --> (A --> C))).
              --- shelve.
              --- shelve.
              --- shelve.
        -- eapply Modus_ponens.
          ++ shelve.
          ++ shelve.
          ++ eapply t1.
          ++ eapply(P2 _ ABC ((A --> B) --> (A --> C)) (B --> (A --> B) --> (A --> C))).
            ** shelve.
            ** shelve.
            ** shelve.
      * eapply Modus_ponens.
        -- shelve.
        -- shelve.
        -- eapply Modus_ponens.
          ++ shelve.
          ++ shelve.
          ++ eapply(P2 _ B (A --> B) (A --> C)).
            ** shelve.
            ** shelve.
            ** shelve.
          ++ eapply(P1 _ _ ABC).
            ** shelve.
            ** shelve.
        -- eapply(P2 _ ABC (B --> (A --> B) --> A --> C) ((B --> A --> B) --> B --> A --> C)).
          ++ shelve.
          ++ shelve.
          ++ shelve.
    + eapply(P2 _ ABC (B --> A --> B) (B --> A --> C)).
      * shelve.
      * shelve.
      * shelve.
  Unshelve.
  all:wf_check.
Admitted.

Lemma reorder_meta (theory : Theory) {A B C : Pattern} :
  well_formed A -> well_formed B -> well_formed C ->  
  theory |- (A --> B --> C) -> theory |- (B --> A --> C).
Proof.
  intros.
  eapply Modus_ponens.
  - shelve.
  - shelve.
  - exact (P1 _ B A H0 H).
  - eapply Modus_ponens.
    + shelve.
    + shelve.
    + eapply Modus_ponens.
      * shelve.
      * shelve.
      * eapply Modus_ponens.
        -- shelve.
        -- shelve.
        -- exact H2.
        -- eapply(P2 _ A B C).
          ++ shelve.
          ++ shelve.
          ++ shelve.
      * assert (well_formed ((A --> B) --> A --> C)).
        -- shelve. 
        -- exact (P1 _ ((A --> B) --> A --> C) B H3 H0).
    + assert(well_formed (A --> B)).
      * shelve.
      * assert(well_formed (A --> C)).
        -- shelve.
        -- exact (P2 _ B (A --> B) (A --> C) H0 H3 H4).
  Unshelve.
  all:wf_check.
Admitted.

(*TODO: Prove this axiom*)
Lemma P4 (theory : Theory) (phi psi : Pattern)  :
well_formed phi -> well_formed psi -> 
theory |- (((¬ phi) --> (¬ psi)) --> (psi --> phi)).
Admitted.

Lemma conj_intro (theory : Theory) (A B : Pattern) :
well_formed A -> well_formed B -> theory |- (A --> B --> (A and B)).
Proof.
  intros.
  pose(tB := (A_impl_A theory B H0)).
  
  (*Helping hypothesises for posing t1*)
  assert(well_formed (¬ (¬ A) --> ¬ B)).
  shelve.
  assert(well_formed Bot).
  shelve.
  assert(well_formed (((¬ (¬ A) --> ¬ B) --> A --> Bot) -->
               ((¬ (¬ A) --> ¬ B) --> A) -->
               (¬ (¬ A) --> ¬ B) --> Bot)).
  shelve.
  assert(well_formed
   ((((¬ (¬ A) --> ¬ B) --> A --> Bot) -->
     ((¬ (¬ A) --> ¬ B) --> A) --> (¬ (¬ A) --> ¬ B) --> Bot) -->
    B -->
    ((¬ (¬ A) --> ¬ B) --> A --> Bot) -->
    ((¬ (¬ A) --> ¬ B) --> A) --> (¬ (¬ A) --> ¬ B) --> Bot)).
  shelve.
  assert(well_formed
   (((¬ (¬ A) --> ¬ B) --> A --> Bot) -->
    ((¬ (¬ A) --> ¬ B) --> A) --> (¬ (¬ A) --> ¬ B) --> Bot)).
  shelve.
  
  pose(t1 := Modus_ponens theory _ _ H5 H4 (P2 _ (¬(¬A) --> ¬B) A Bot H1 H H2)
                                           (P1 _ _ B H3 H0)).
  
  (*Helping hypothesises for posing t2*)
  assert(well_formed (¬A)).
  shelve.
  assert(well_formed (B --> (¬ (¬ A) --> ¬ B) --> ¬ A)).
  shelve.
  assert(well_formed (¬ (¬ A) --> ¬ B)).
  shelve.
  assert(well_formed
   ((B --> (¬ (¬ A) --> ¬ B) --> ¬ A) -->
    B --> B --> (¬ (¬ A) --> ¬ B) --> ¬ A)).
  shelve.
  assert(well_formed (B --> (¬ (¬ A) --> ¬ B) --> ¬ A)).
  shelve.
  
  pose(t2 := Modus_ponens theory _ _ H10 H9  (reorder_meta _ H8 H0 H6 (P4 _ (¬A) B H6 H0))
                                          (P1 _ _ B H7 H0)).
  (*Helping hypothesises for posing t3''*)
  assert(well_formed (A --> (¬ (¬ A) --> ¬ B) --> A)).
  shelve.
  assert(well_formed
   ((A --> (¬ (¬ A) --> ¬ B) --> A) -->
    B --> A --> (¬ (¬ A) --> ¬ B) --> A)).
  shelve.
  
  pose(t3'' := Modus_ponens theory _ _ H11 H12 (P1 _ A (¬(¬A) --> ¬B) H H8)
                                           (P1 _ _ B H11 H0)).
  
  (*Helping hypothesises for posing t4*)
  assert(well_formed ((¬ (¬ A) --> ¬ B) --> ¬ A)).
  shelve.
  assert(well_formed
   ((B --> B --> (¬ (¬ A) --> ¬ B) --> ¬ A) -->
    (B --> B) --> B --> (¬ (¬ A) --> ¬ B) --> ¬ A)).
  shelve.
  assert(well_formed (B --> B --> (¬ (¬ A) --> ¬ B) --> ¬ A)).
  shelve.
  assert(well_formed
   ((B --> B) --> B --> (¬ (¬ A) --> ¬ B) --> ¬ A)).
  shelve.
  assert(well_formed (B --> B)).
  shelve.
  
  pose(t4 := Modus_ponens theory _ _ H17 H16 tB
                                          (Modus_ponens theory _ _ H15 H14 t2
                                                                       (P2 _ B B _ H0 H0 H13))).
  (*Helping hypothesises for posing t5''*)
  assert(well_formed
    (((¬ (¬ A) --> ¬ B) --> A) --> ¬ (¬ (¬ A) --> ¬ B))).
  shelve.
  assert(well_formed
   ((B -->
     ((¬ (¬ A) --> ¬ B) --> A --> Bot) -->
     ((¬ (¬ A) --> ¬ B) --> A) -->
     (¬ (¬ A) --> ¬ B) --> Bot) -->
    (B --> (¬ (¬ A) --> ¬ B) --> ¬ A) -->
    B -->
    ((¬ (¬ A) --> ¬ B) --> A) -->
    ¬ (¬ (¬ A) --> ¬ B))).
  shelve.
  assert(well_formed
   (B -->
    ((¬ (¬ A) --> ¬ B) --> A --> Bot) -->
    ((¬ (¬ A) --> ¬ B) --> A) -->
    (¬ (¬ A) --> ¬ B) --> Bot)).
  shelve.
  assert(well_formed
   ((B --> (¬ (¬ A) --> ¬ B) --> ¬ A) -->
    B -->
    ((¬ (¬ A) --> ¬ B) --> A) -->
    ¬ (¬ (¬ A) --> ¬ B))).
  shelve.
  assert(well_formed (B --> (¬ (¬ A) --> ¬ B) --> ¬ A)).
  shelve.
  
  pose(t5'' := 
        Modus_ponens theory _ _ H22 H21 t4
                                    (Modus_ponens theory _ _ H20 H19 t1
                                                                 (P2 _ B ((¬(¬A) --> ¬B) --> ¬A)
                                                                 (((¬(¬A) --> ¬B) --> A) --> ¬(¬(¬A) --> ¬B)) H0 H13 H18))).
  
  pose(tA := (P1 theory A B) H H0).
  (*Helpers for posing tB'*)
  assert(well_formed (B --> B)).
  shelve.
  assert(well_formed ((B --> B) --> A --> B --> B)).
  shelve.
  pose(tB' := Modus_ponens theory _ _ H23 H24 tB
                                          (P1 _ (B --> B) A H23 H)).
  (*Helpers for posing t3'*)
  assert(well_formed ((¬ (¬ A) --> ¬ B) --> A)).
  shelve.
  assert(well_formed
   ((B --> A --> (¬ (¬ A) --> ¬ B) --> A) -->
    (B --> A) --> B --> (¬ (¬ A) --> ¬ B) --> A)).
  shelve.
  assert(well_formed (B --> A --> (¬ (¬ A) --> ¬ B) --> A)).
  shelve.
  pose(t3' := Modus_ponens theory _ _ H27 H26 t3''
                                          (P2 _ B A ((¬(¬A) --> ¬B) --> A) H0 H H25)).
  (*Helpers for posing t3*)
  assert(well_formed ((B --> A) --> B --> (¬ (¬ A) --> ¬ B) --> A)).
  shelve.
  assert(well_formed
   (((B --> A) --> B --> (¬ (¬ A) --> ¬ B) --> A) -->
    A --> (B --> A) --> B --> (¬ (¬ A) --> ¬ B) --> A)).
    shelve.
  pose(t3 := Modus_ponens theory _ _ H28 H29 t3'
                                         (P1 _ ((B --> A) --> B --> (¬ (¬ A) --> ¬ B) --> A) A H28 H)).
  (*Helpers for posing t5'*)
  assert(well_formed (¬ (¬ (¬ A) --> ¬ B))).
  shelve.
  assert(well_formed
   ((B --> ((¬ (¬ A) --> ¬ B) --> A) --> ¬ (¬ (¬ A) --> ¬ B)) -->
    (B --> (¬ (¬ A) --> ¬ B) --> A) --> B --> ¬ (¬ (¬ A) --> ¬ B))).
  shelve.
  assert(well_formed (B --> ((¬ (¬ A) --> ¬ B) --> A) --> ¬ (¬ (¬ A) --> ¬ B))).
  shelve.
  
  pose(t5' := Modus_ponens theory _ _ H32 H31 t5''
                                          (P2 _ B ((¬(¬A) --> ¬B) --> A) (¬(¬(¬A) --> ¬B)) H0 H25 H30)).
  (*Helpers for posing t5*)
  assert(well_formed
   ((B --> (¬ (¬ A) --> ¬ B) --> A) -->
    B --> ¬ (¬ (¬ A) --> ¬ B))).
  shelve.
  assert(well_formed
   (((B --> (¬ (¬ A) --> ¬ B) --> A) -->
     B --> ¬ (¬ (¬ A) --> ¬ B)) -->
    A -->
    (B --> (¬ (¬ A) --> ¬ B) --> A) -->
    B --> ¬ (¬ (¬ A) --> ¬ B))).
  shelve.
  
  pose(t5 := Modus_ponens theory _ _ H33 H34 t5' 
                                         (P1 _ ((B --> (¬ (¬ A) --> ¬ B) --> A) --> B --> ¬ (¬ (¬ A) --> ¬ B))
                    A H33 H)).
  (*Helpers for posing t6*)
  assert(well_formed (B --> A)).
  shelve.
  assert(well_formed (B --> (¬ (¬ A) --> ¬ B) --> A)).
  shelve.
  assert(well_formed
   ((A -->
     (B --> A) --> B --> (¬ (¬ A) --> ¬ B) --> A) -->
    (A --> B --> A) -->
    A --> B --> (¬ (¬ A) --> ¬ B) --> A)).
  shelve.
  assert(well_formed
   (A -->
    (B --> A) --> B --> (¬ (¬ A) --> ¬ B) --> A)).
  shelve.
  assert(well_formed
   ((A --> B --> A) -->
    A --> B --> (¬ (¬ A) --> ¬ B) --> A)).
  shelve.
  assert(well_formed (A --> B --> A)).
  shelve.
  pose(t6 := Modus_ponens theory _ _ H40 H39 tA
                                         (Modus_ponens theory _ _ H38 H37 t3
                                                                      (P2 _ A (B --> A) (B --> (¬(¬A) --> ¬B) --> A) H H35 H36))).
  (*Helpers for posing t7*)
  assert(well_formed (B --> ¬ (¬ (¬ A) --> ¬ B))).
  shelve.
  assert(well_formed
   ((A -->
     (B --> (¬ (¬ A) --> ¬ B) --> A) -->
     B --> ¬ (¬ (¬ A) --> ¬ B)) -->
    (A --> B --> (¬ (¬ A) --> ¬ B) --> A) -->
    A --> B --> ¬ (¬ (¬ A) --> ¬ B))).
  shelve.
  assert(well_formed
   (A -->
    (B --> (¬ (¬ A) --> ¬ B) --> A) -->
    B --> ¬ (¬ (¬ A) --> ¬ B))).
  shelve.
  assert(well_formed
   ((A --> B --> (¬ (¬ A) --> ¬ B) --> A) -->
    A --> B --> ¬ (¬ (¬ A) --> ¬ B))).
  shelve.
  assert(well_formed (A --> B --> (¬ (¬ A) --> ¬ B) --> A)).
  shelve.
  
  pose(t7 := Modus_ponens theory _ _ H45 H44 t6 
                                         (Modus_ponens theory _ _ H43 H42 t5 
                                                                      (P2 _ A (B --> (¬(¬A) --> ¬B) --> A) (B --> ¬(¬(¬A) --> ¬B)) H H36 H41))).
  unfold patt_and.  unfold patt_or.
  exact t7.
  Unshelve.
  (*Warr: If replaced with wf_proof will take a while to run*)
  all:wf_check.
Admitted.

Lemma conj_intro_meta (theory : Theory) (A B : Pattern) :
  well_formed A -> well_formed B -> theory |- A -> theory |- B -> theory |- (A and B).
Proof.
  intros.
  eapply Modus_ponens.
  - shelve.
  - shelve.
  - exact H2.
  - eapply Modus_ponens.
    + shelve.
    + shelve.
    + exact H1.
    + exact (conj_intro _ A B H H0).
  Unshelve.
  all:wf_check.
Admitted.

(* Lemma conj_intro_meta_e (theory : Theory) (A B : Pattern) : *) 
Definition conj_intro_meta_e := conj_intro_meta.    (*The same as conj_intro_meta*)

Lemma disj (theory : Theory) (A B : Pattern) :
  well_formed A -> well_formed B -> theory |- (A --> B --> (A or B)).
Proof.
  intros. unfold patt_or.
  
  assert(well_formed (¬ A)).
  shelve.
  pose(t1 := (P1 theory B (¬A) H0 H1)).
  
  assert(well_formed (B --> ¬ A --> B)).
  shelve.
  pose(t2 := (P1 theory (B --> (¬A --> B)) A H2 H)).
  
  assert(well_formed
   ((B --> ¬ A --> B) --> A --> B --> ¬ A --> B)).
   shelve.
  pose(t3 := Modus_ponens theory _ _ H2 H3 t1 t2).
  
  exact t3.
  Unshelve.
  all:wf_check.
Admitted.

Lemma disj_intro (theory : Theory) (A B : Pattern) :
  well_formed A -> well_formed B -> theory |- A -> theory |- B -> theory |- (A or B).
Proof.
  intros.
  eapply Modus_ponens.
  - shelve.
  - shelve.
  - exact H2.
  - eapply Modus_ponens.
    + shelve.
    + shelve.
    + exact H1.
    + exact (disj _ A B H H0).
  Unshelve.
  all:wf_check.
Admitted.

Lemma syllogism (theory : Theory) (A B C : Pattern) :
  well_formed A -> well_formed B -> well_formed C -> theory |- ((A --> B) --> (B --> C) --> (A --> C)).
Proof.
  intros.
  eapply reorder_meta.
  shelve.
  shelve.
  shelve.
  eapply Modus_ponens.
  - shelve.
  - shelve.
  - eapply(P1 _ (B --> C) A).
    + shelve.
    + shelve.
  - eapply Modus_ponens.
    + shelve.
    + shelve.
    + eapply Modus_ponens.
      * shelve.
      * shelve.
      * eapply (P2 _ A B C).
        -- shelve.
        -- shelve.
        -- shelve.
      * eapply (P1 _ ((A --> B --> C) --> (A --> B) --> A --> C) (B --> C)).
        -- shelve.
        -- shelve.
    + eapply (P2 _ (B --> C) (A --> B --> C) ((A --> B) --> A --> C)).
      * shelve.
      * shelve.
      * shelve.
  Unshelve.
  all:wf_check.
Admitted.

Lemma syllogism_intro (theory : Theory) (A B C : Pattern) :
  well_formed A -> well_formed B -> well_formed C -> theory |- (A --> B) -> theory |- (B --> C) -> theory |- (A --> C).
Proof.
  intros.
  eapply Modus_ponens.
  - shelve.
  - shelve.
  - exact H2.
  - eapply Modus_ponens.
    + shelve.
    + shelve.
    + exact H3.
    + eapply reorder_meta. shelve. shelve. shelve. exact (syllogism _ A B C H H0 H1).
  Unshelve.
  all:wf_check.
Admitted.

Lemma syllogism_4_meta (theory : Theory) (A B C D : Pattern) :
  well_formed A -> well_formed B -> well_formed C -> well_formed D ->
  theory |- (A --> B --> C) -> theory |- (C --> D) -> theory |- (A --> B --> D).
Proof.
  intros.
  eapply Modus_ponens.
  - shelve.
  - shelve.
  - exact H3.
  - eapply Modus_ponens.
    + shelve.
    + shelve.
    + eapply Modus_ponens.
      * shelve.
      * shelve.
      * eapply Modus_ponens.
        -- shelve.
        -- shelve.
        -- eapply Modus_ponens.
          ++ shelve.
          ++ shelve.
          ++ exact H4.
          ++ eapply (P1 _ (C --> D) B).
            ** shelve.
            ** shelve.
        -- eapply (P2 _ B C D).
          ++ shelve.
          ++ shelve.
          ++ shelve.
      * eapply (P1 _ ((B --> C) --> B --> D) A).
        -- shelve.
        -- shelve.
    + eapply (P2 _ A (B --> C) (B --> D)).
      * shelve.
      * shelve.
      * shelve.
  Unshelve.
  all:wf_check.
Admitted.

Lemma bot_elim (theory : Theory) (A : Pattern) :
  well_formed A -> theory |- (Bot --> A).
Proof.
  intros.
  eapply Modus_ponens.
  - shelve.
  - shelve.
  - eapply Modus_ponens.
    + shelve.
    + shelve.
    + eapply Modus_ponens.
      * shelve.
      * shelve.
      * eapply Modus_ponens.
        -- shelve.
        -- shelve.
        -- eapply (P1 _ Bot Bot).
          ++ shelve.
          ++ shelve.
        -- eapply (P2 _ Bot Bot Bot).
          ++ shelve.
          ++ shelve.
          ++ shelve.
      * eapply (P4 _ Bot Bot).
        -- shelve.
        -- shelve.
    + eapply (P1 _ (Bot --> Bot) (A --> Bot)).
      * shelve.
      * shelve.
  - eapply (P4 _ A Bot).
    + shelve.
    + shelve.
  Unshelve.
  all:wf_check.
Admitted.

Lemma modus_ponens (theory : Theory) ( A B : Pattern) :
  well_formed A -> well_formed B -> theory |- (A --> (A --> B) --> B).
Proof.
  intros.
  eapply Modus_ponens.
    - shelve.
    - shelve.
    - eapply (P1 _ A (A --> B)).
      + shelve.
      + shelve.
    - eapply Modus_ponens.
      + shelve.
      + shelve.
      + eapply Modus_ponens.
        * shelve.
        * shelve.
        * eapply (A_impl_A _ (A --> B)).
          -- shelve.
        * eapply (P2 _ (A --> B) A B).
          -- shelve.
          -- shelve.
          -- shelve.
      + eapply reorder_meta.
        * shelve.
        * shelve.
        * shelve.
        * eapply (syllogism _ A ((A --> B) --> A) ((A --> B) --> B)).
          -- shelve.
          -- shelve.
          -- shelve.
  Unshelve.
  all:wf_check.
Admitted.

Lemma modus_ponens' (theory : Theory) (A B : Pattern) :
  well_formed A -> well_formed B -> theory |- (A --> (¬B --> ¬A) --> B).
Proof.
  intros.
  assert(well_formed (¬ B --> ¬ A)).
  shelve.
  exact (reorder_meta theory H1 H H0 (P4 _ B A H0 H)).
  Unshelve.
  all:wf_check.
Admitted.

Lemma disj_right_intro (theory : Theory) (A B : Pattern) :
  well_formed A -> well_formed B -> theory |- (B --> (A or B)).
Proof.
  intros.
  assert(well_formed (¬A)).
  shelve.
  exact (P1 _ B (¬A) H0 H1).
  Unshelve.
  all:wf_check.
Admitted.

Lemma disj_left_intro (theory : Theory) (A B : Pattern) :
  well_formed A -> well_formed B -> theory |- (A --> (A or B)).
Proof.
  intros.
  assert(well_formed Bot).
  shelve.
  eapply (syllogism_4_meta _ _ _ _ _ _ _ _ _ (modus_ponens _ A Bot H H1) (bot_elim _ B H0)).
  Unshelve.
  all:wf_check. 
Admitted.

Lemma not_not_intro (theory : Theory) (A : Pattern) :
  well_formed A -> theory |- (A --> ¬(¬A)).
Proof.
  intros.
  assert(well_formed Bot).
  shelve.
  unfold patt_or. exact (modus_ponens _ A Bot H H0).
  Unshelve.
  all:wf_check.
Admitted.

Lemma not_not_elim (theory : Theory) (A : Pattern) :
  well_formed A -> theory |- (¬(¬A) --> A).
Proof.
  intros.
  eapply Modus_ponens.
  - shelve.
  - shelve.
  - eapply (modus_ponens _ (¬A) Bot).
    + shelve.
    + shelve.
  - eapply (P4 _ A (¬(¬A))).
    + shelve.
    + shelve.
  Unshelve.
  all:wf_check.
Admitted.

Lemma double_neg_elim (theory : Theory) (A B : Pattern) :
  well_formed A -> well_formed B -> theory |- (((¬(¬A)) --> (¬(¬B))) --> (A --> B)).
Proof.
  intros.
  eapply syllogism_intro.
  - shelve.
  - shelve.
  - shelve.
  - eapply (P4 _ (¬A) (¬B)).
    + shelve.
    + shelve.
  - eapply (P4 _ B A).
    + shelve.
    + shelve.
  Unshelve.
  all:wf_check.
Admitted.

Lemma double_neg_elim_meta (theory : Theory) (A B : Pattern) :
  well_formed A -> well_formed B -> 
  theory |- ((¬(¬A)) --> (¬(¬B))) -> theory |- (A --> B).
Proof.
  intros.
  eapply Modus_ponens.
  - shelve.
  - shelve.
  - exact H1.
  - exact (double_neg_elim _ A B H H0).
  Unshelve.
  all:wf_check.
Admitted.

Lemma deduction (theory : Theory) (A B : Pattern) :
  well_formed A -> well_formed B -> theory |- A -> theory |- B -> theory |- (A --> B).
Proof.
  intros.
  eapply Modus_ponens.
  - shelve.
  - shelve.
  - exact H2.
  - eapply (P1 _ B A).
    + shelve.
    + shelve.
  Unshelve.
  all:wf_check.
Admitted.

Lemma P4_rev_meta (theory : Theory) (A B : Pattern) :
  well_formed A -> well_formed B -> theory |- (A --> B) -> theory |- ((A --> B) --> (¬B --> ¬A)).
Proof.
  intros.
  eapply deduction.
  - shelve.
  - shelve.
  - exact H1.
  - eapply Modus_ponens.
    + shelve.
    + shelve.
    + eapply syllogism_intro.
      * shelve.
      * shelve.
      * shelve.
      * eapply syllogism_intro.
        -- shelve.
        -- shelve.
        -- shelve.
        -- eapply (not_not_elim _ A).
          ++ shelve.
        -- exact H1.
      * eapply (not_not_intro _ B).
        -- shelve.
    + eapply (P4 _ (¬A) (¬B)).
      * shelve.
      * shelve.
  Unshelve.
  all:wf_check.
Admitted.

Lemma P4m_neg (theory : Theory) (A B : Pattern) :
  well_formed A -> well_formed B -> theory |- ((¬B --> ¬A) --> (A --> ¬B) -->  ¬A).
Proof.
  intros.
  pose (PT := (P4 theory B A H0 H)).
  eapply syllogism_intro.
  - shelve.
  - shelve.
  - shelve.
  - exact PT.
  - apply P4m.
    + shelve.
    + shelve.
  Unshelve.
  all:wf_check.
Admitted.

Lemma not_not_impl_intro_meta (theory : Theory) (A B : Pattern) :
  well_formed A -> well_formed B -> theory |- (A --> B) -> theory |- ((¬¬A) --> (¬¬B)).
Proof.
  intros.
  pose (NN1 := not_not_elim theory A H).
  pose (NN2 := not_not_intro theory B H0).
  
  assert(well_formed (¬ (¬ B))).
  shelve.
  pose (S1 := syllogism_intro _ _ _ _ H H0 H2 H1 NN2).
  
  assert(well_formed (¬ (¬ A))).
  shelve.
  pose (S2 := syllogism_intro _ _ _ _ H3 H H2 NN1 S1).
  exact S2.
  Unshelve.
  all:wf_check.
Admitted.

Lemma not_not_impl_intro (theory : Theory) (A B : Pattern) :
  well_formed A -> well_formed B -> theory |- ((A --> B) --> ((¬¬A) --> (¬¬B))).
Proof.
  intros.
  
  assert(well_formed (¬ (¬ A))).
  shelve.
  pose (S1 := syllogism theory (¬¬A) A B H1 H H0).
  
  assert(well_formed ((¬ (¬ A) --> A) --> (A --> B) --> ¬ (¬ A) --> B)).
  shelve.
  assert(well_formed (¬ (¬ A) --> A)).
  shelve.
  pose (MP1 := Modus_ponens _ (¬ (¬ A) --> A) ((A --> B) --> ¬ (¬ A) --> B) H3 H2 (not_not_elim _ A H) S1).
  
  pose(NNB := not_not_intro theory B H0).
  
  assert(well_formed (B --> ¬ (¬ B))).
  shelve.
  pose(P1 := (P1 theory (B --> ¬ (¬ B)) (¬¬A) H4 H1)).
  
  assert(well_formed ((B --> ¬ (¬ B)) --> ¬ (¬ A) --> B --> ¬ (¬ B))).
  shelve.
  pose(MP2 := Modus_ponens _ _ _ H4 H5 NNB P1).
  
  assert(well_formed (¬(¬ B))).
  shelve.
  pose(P2 := (P2 theory (¬¬A) B (¬¬B) H1 H0 H6)).
  
  assert(well_formed
   ((¬ (¬ A) --> B --> ¬ (¬ B)) --> (¬ (¬ A) --> B) --> ¬ (¬ A) --> ¬ (¬ B))).
  shelve.
  assert(well_formed (¬ (¬ A) --> B --> ¬ (¬ B))).
  shelve.
  pose(MP3 := Modus_ponens _ _ _ H8 H7 MP2 P2).
  
  apply syllogism_intro with (B := (¬ (¬ A) --> B)).
    - shelve.
    - shelve.
    - shelve.
    - assumption.
    - assumption.
  Unshelve.
  all:wf_check.
Admitted.

Lemma contraposition (theory : Theory) (A B : Pattern) : 
  well_formed A -> well_formed B -> 
  theory |- ((A --> B) --> ((¬ B) --> (¬ A))).
Proof.
  intros.
  assert(well_formed (¬ A)).
  shelve.
  assert(well_formed (¬ B)).
  shelve.
  pose(P4 theory (¬ A) (¬ B) H1 H2).
  apply syllogism_intro with (B := (¬ (¬ A) --> ¬ (¬ B))).
  - shelve.
  - shelve.
  - shelve.
  - apply not_not_impl_intro. shelve. shelve.
  - apply (P4 _ _ _). shelve. shelve.
  Unshelve.
  all:wf_check.
Admitted.

Lemma or_comm_meta (theory : Theory) (A B : Pattern) :
  well_formed A -> well_formed B ->
  theory |- (A or B) -> theory |- (B or A).
Proof.
  intros. unfold patt_or in *.
  
  assert(well_formed (¬B)).
  shelve.
  pose (P4 := (P4 theory A (¬B) H H2)).
  
  pose (NNI := not_not_intro theory B H0).
  
  assert(well_formed (¬ (¬ B))).
  shelve.
  assert(well_formed (¬ A)).
  shelve.
  pose (SI := syllogism_intro theory _ _ _ H4 H0 H3 H1 NNI).
  
  eapply Modus_ponens.
  - shelve.
  - shelve.
  - exact SI.
  - exact P4.
  Unshelve.
  all:wf_check.
Admitted.

Lemma A_implies_not_not_A_alt (theory : Theory) (A : Pattern) :
  well_formed A -> theory |- A -> theory |- (¬( ¬A )).
Proof.
  intros. unfold patt_not.
  pose (NN := not_not_intro theory A H).
  
  assert(well_formed (A --> ¬ (¬ A))).
  shelve.
  pose (MP := Modus_ponens _ _ _ H H1 H0 NN).
  assumption.
  Unshelve.
  all:wf_check.
Admitted.

(*TODO: Prove this axiom*)
Lemma Prop_bot (theory : Theory) (C : Application_context) :
  theory |- ((subst_ctx C patt_bott) --> patt_bott).
Admitted.

Lemma A_implies_not_not_A_ctx (theory : Theory) (A : Pattern) (C : Application_context) :
  well_formed A -> theory |- A -> theory |- (¬ (subst_ctx C ( ¬A ))).
Proof.
  intros.
  pose (ANNA := A_implies_not_not_A_alt theory _ H H0).
  replace (¬ (¬ A)) with ((¬ A) --> Bot) in ANNA. 2: auto.
  pose (EF := Framing _ C (¬ A) Bot ANNA).
  pose (PB := Prop_bot theory C).
  
  assert(well_formed Bot).
  shelve.
  assert(well_formed (subst_ctx C Bot)).
  shelve.
  assert(well_formed (subst_ctx C (¬ A))).
  shelve.
  pose (TRANS := syllogism_intro _ _ _ _ H3 H2 H1 EF PB).
  
  unfold patt_not.
  assumption.
  Unshelve.
  all:wf_check.
Admitted.

Lemma A_implies_not_not_A_alt_theory (G : Theory) (A : Pattern) :
  well_formed A -> G |- A -> G |- (¬( ¬A )).
Proof.
  intros. unfold patt_not.
  pose (NN := not_not_intro G A H).
  
  assert(well_formed (A --> ¬ (¬ A))).
  shelve.
  pose (MP := Modus_ponens G _ _ H H1 H0 NN).
  
  assumption.
  Unshelve.
  all:wf_check.
Admitted.

(* Lemma equiv_implies_eq (theory : Theory) (A B : Pattern) :
  well_formed A -> well_formed B -> theory |- (A <--> B) -> theory |- ()
 *)
 
(* Lemma equiv_implies_eq_theory *)

(*...TODO: Missed some because totality not defined...*)

Lemma ctx_bot_prop (theory : Theory) (C : Application_context) (A : Pattern) :
  well_formed A -> theory |- (A --> Bot) -> theory |- (subst_ctx C A --> Bot).
Proof.
  intros.
  pose (FR := Framing theory C A Bot H0).
  pose (BPR := Prop_bot theory C).
  
  assert(well_formed Bot).
  shelve.
  assert(well_formed (subst_ctx C Bot)).
  shelve.
  assert(well_formed (subst_ctx C A)).
  shelve.
  pose (TRANS := syllogism_intro _ _ _ _ H3 H2 H1 FR BPR).
  
  assumption.
  Unshelve.
  all:wf_check.
Admitted.

Lemma P5i (theory : Theory) (A B : Pattern) :
  well_formed A -> well_formed B -> theory |- (¬ A --> (A --> B)).
Proof.
  intros.
  
  assert(well_formed (¬A)).
  shelve.
  assert(well_formed (¬B)).
  shelve.
  pose (Ax1 := (P1 theory (¬A) (¬B) H1 H2)).
  
  pose (Ax2 := (P4 theory B A H0 H)).
  
  assert(well_formed (A --> B)).
  shelve.
  assert(well_formed (¬ B --> ¬ A)).
  shelve.
  pose (TRANS := syllogism_intro _ _ _ _ H1 H4 H3 Ax1 Ax2).
  assumption.
  Unshelve.
  all:wf_check.
Admitted.

Lemma false_implies_everything (theory : Theory) (phi : Pattern) :
  well_formed phi -> theory |- (Bot --> phi).
Proof.
  intro.
  
  assert(well_formed Bot).
  shelve.
  pose (B_B := (A_impl_A theory Bot H0)).
  pose (P4 := P5i theory Bot phi H0 H).
  
  apply Modus_ponens in P4.
  - assumption.
  - shelve.
  - shelve.
  - assumption.
  Unshelve.
  all:wf_check.
Admitted.

(*Totality és ezek helyett mit? (--> ezzel lenne equal is)*)

Lemma not_not_A_ctx_implies_A (theory : Theory) (C : Application_context) (A : Pattern):
  well_formed A -> theory |- (¬ (subst_ctx C ( ¬A ))) -> theory |- A.
Proof.
  intros.
  unfold patt_not in H0 at 1.
  
  assert(well_formed (subst_ctx C Bot)).
  shelve.
  pose (BIE := false_implies_everything theory (subst_ctx C Bot) H1).
  
  assert(well_formed Bot).
  shelve.
  assert(well_formed (subst_ctx C (¬ A))).
  shelve.
  pose (TRANS := syllogism_intro _ _ _ _ H3 H2 H1 H0 BIE).
  
  induction C.
  - simpl in TRANS.
    pose (NN := not_not_elim theory A H).
    assert(well_formed ((¬ A --> Bot) --> A)).
    shelve.
    assert(well_formed (¬ A --> Bot)).
    shelve.
    pose (MP := Modus_ponens _ _ _ H5 H4 TRANS NN). assumption.
  - eapply IHC.
  Unshelve.
  Abort.

Definition empty_theory := {|patterns := Empty_set Pattern|}.

Lemma provable_to_proved (theory : Theory) (A : Pattern) :
  well_formed A -> empty_theory |- A -> theory |- A.
Proof.
  intros. dependent induction H0.
  - unfold empty_theory in H1. contradict H1.
  - exact (P1 theory phi psi H0 H1).
  - exact (P2 theory phi psi xi H0 H1 H2).
  - exact (P3 theory phi H0).
  - exact (Modus_ponens theory phi1 phi2 H0 H1 (IHML_proof_system1 H0) (IHML_proof_system2 H1)).
  - exact (Ex_quan _ phi y H0).
  - assert (well_formed (phi1 --> phi2)). shelve.
    + exact (Ex_gen _ phi1 phi2 x H0 H1 (IHML_proof_system H4) H3).
  - exact (Prop_bott_left _ phi H0).
  - exact (Prop_bott_right _ phi H0).
  - exact (Prop_disj_left _ phi1 phi2 psi H0 H1 H2).
  - exact (Prop_disj_right _ phi1 phi2 psi H0 H1 H2).
  - exact (Prop_ex_left _ phi psi H0 H1).
  - exact (Prop_ex_right _ phi psi H0 H1).
  - assert (well_formed (phi1 --> phi2)). shelve.
    + exact (Framing _ C phi1 phi2 (IHML_proof_system H1)).
  - assert (well_formed phi). shelve.
    + exact (Svar_subst _ phi psi X (IHML_proof_system H1)).
  - exact (Pre_fixp _ phi).
  - assert (well_formed (instantiate (mu , phi) psi --> psi)). shelve.
    + exact (Knaster_tarski _ phi psi (IHML_proof_system H1)).
  - exact (Existence _).
  - exact (Singleton_ctx _ C1 C2 phi x).
  Unshelve.
  all:wf_check.
Admitted.

(* Lemma proved_impl_to_provable (theory : Theory) (A B : Pattern) :
  well_formed A -> well_formed B -> (theory |- A -> theory |- B) ->
  (empty_theory |- A -> empty_theory |- B).
Proof.
  intros. *)

Lemma exclusion (G : Theory) (A : Pattern) :
  well_formed A -> G |- A -> G |- (A --> Bot) -> G |- Bot.
Proof.
  intros.
  assert(well_formed (A --> Bot)).
  shelve.
  pose(Modus_ponens G A Bot H H2 H0 H1).
  assumption.
  Unshelve.
  all:wf_check.
Admitted.

Axiom exclusion_axiom : forall G A,
  G |- A -> G |- (¬ A) -> False.

Axiom or_or : forall G A,
G |- A \/ G |- (¬ A).

(*TODO: Prove if totality etc. defined*)
(* Axiom extension : forall G A B,
  G |- A -> (Add Sigma_pattern G B) |- A. *)

(* Lemma empty_theory_implies_any A : forall G,
  empty_theory |- A -> G |- A. *)

(* Lemma equiv_cong G phi1 phi2 C x :
  (G |- (phi1 <~> phi2)) -> G |- ((e_subst_var C phi1 x) <~> (e_subst_var C phi2 x)). *)

(* Lemma eq_refl
  (phi : Sigma_pattern) (theory : Ensemble Sigma_pattern) :
    theory |- (phi ~=~ phi). *)

(* Lemma eq_trans
  (phi1 phi2 phi3 : Sigma_pattern) (theory : Ensemble Sigma_pattern) :
    theory |- (phi1 ~=~ phi2) -> theory |- (phi2 ~=~ phi3) ->
    theory |- (phi1 ~=~ phi3). *)

(* Lemma eq_symm
  (phi1 phi2 : Sigma_pattern)  (theory : Ensemble Sigma_pattern) :
    theory |- (phi1 ~=~ phi2) -> theory |- (phi2 ~=~ phi1). *)

(* Lemma eq_evar_subst
  (x : EVar) (phi1 phi2 psi : Sigma_pattern) (theory : Ensemble Sigma_pattern) :
    theory |- (phi1 ~=~ phi2) ->
    theory |- ((e_subst_var psi phi1 x) ~=~ (e_subst_var psi phi2 x)). *)

(* Lemma A_implies_A_totality A:
  A proved -> |_ A _| proved. *)

(* Lemma A_totality_implies_A A:
  |_ A _| proved -> A proved. *)

(* Lemma universal_instantiation (theory : Theory) (A : Pattern) (x y : evar):
  theory |- ((all' x, A) --> (e_subst_var A y x)). *)

























