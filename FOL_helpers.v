Require Import AML_definition.
Import AML_notations.
Require Import Coq.Sets.Ensembles.


Section FOL_helpers.

(* Helper lemmas for first order reasoning *)
Lemma reorder (A B C : Sigma_pattern) :
  ((A ~> B ~> C) ~> (B ~> A ~> C)) proved.
Proof.
  pose(t1 := (Mod_pon
                (Prop_tau _ (P2 ((A ~> B) ~> A ~> C) B))
                (Prop_tau _ (P2 _ (A ~> B ~> C))) )).
  pose(ABC := (A ~> B ~> C)).

  eapply Mod_pon.
  - (* t7 *) eapply Mod_pon.
    + eapply Prop_tau. eapply (P2 B A).
    + eapply Prop_tau. eapply (P2 (B ~> A ~> B) (A ~> B ~> C)).
  - eapply Mod_pon.
    + (* t6 *) eapply Mod_pon.
      * (* t5 *) eapply Mod_pon.
        -- (* t4 *) eapply Mod_pon.
           ++ eapply Prop_tau. eapply (P1 ABC).
           ++ eapply Mod_pon.
              ** (* t2 *) eapply Mod_pon.
                 --- eapply Prop_tau. eapply (P3 A B C).
                 --- eapply Prop_tau. eapply (P2 _ (A ~> B ~> C)).
              ** eapply Prop_tau. eapply (P3 ABC ABC ((A ~> B) ~> (A ~> C))).
        -- eapply Mod_pon.
           ++ (* t1 *) eapply t1.
           ++ eapply Prop_tau.
              eapply (P3 ABC ((A ~> B) ~> (A ~> C)) (B ~> (A~>B) ~> (A~>C))).
      * eapply Mod_pon.
        -- (* t3 *) eapply Mod_pon.
           ++ eapply Prop_tau. eapply (P3 B (A ~> B) (A ~> C)).
           ++ eapply Prop_tau. eapply (P2 _ ABC).
        -- eapply Prop_tau. eapply (P3 ABC (B ~> (A ~> B) ~> A ~> C)
                                           ((B ~> A ~> B) ~> B ~> A ~> C)).
    + eapply Prop_tau. eapply (P3 ABC (B ~> A ~> B) (B ~> A ~> C)).
Qed.

Lemma reorder_meta {A B C : Sigma_pattern} :
  (A ~> B ~> C) proved -> (B ~> A ~> C) proved.
Proof.
  intros.
  eapply Mod_pon.
  - eapply Prop_tau. exact (P2 B A).
  - eapply Mod_pon.
    + eapply Mod_pon.
      * eapply Mod_pon.
        -- exact H.
        -- eapply Prop_tau. eapply (P3 A B C).
      * eapply Prop_tau. exact (P2 ((A ~> B) ~> A ~> C) B).
    + eapply Prop_tau. exact (P3 B (A ~> B) (A ~> C)).
Qed.


Lemma conj_intro (A B : Sigma_pattern) :
  (A ~> B ~> (A _&_ B)) proved.
Proof.
  pose(tB := Prop_tau (B ~> B) (P1 B)).
  pose(t1 := Mod_pon (Prop_tau _ (P3 (¬(¬A) ~> ¬B) A Bot))
                     (Prop_tau _ (P2 _ B))).
  pose(t2 := Mod_pon (reorder_meta (Prop_tau _ (P4 (¬A) B)))
                     (Prop_tau _ (P2 _ B))).
  pose(t3'' := Mod_pon (Prop_tau _ (P2 A (¬(¬A) ~> ¬B)))
                       (Prop_tau _ (P2 _ B))).
  pose(t4 := Mod_pon tB (Mod_pon t2 (Prop_tau _ (P3 B B _)))).
  pose(t5'' :=
    Mod_pon t4 (Mod_pon t1 (Prop_tau _
                              (P3 B
                                  ((¬(¬A) ~> ¬B) ~> ¬A)
                                  (((¬(¬A) ~> ¬B) ~> A) ~> ¬(¬(¬A) ~> ¬B)))))).
  pose(tA := Prop_tau _ (P2 A B)).
  pose(tB' := Mod_pon tB (Prop_tau _ (P2 (B ~> B) A))).
  pose(t3' := Mod_pon t3'' (Prop_tau _ (P3 B A ((¬(¬A) ~> ¬B) ~> A)))).
  pose(t3 := Mod_pon t3'
              (Prop_tau _ (P2 ((B ~> A) ~> B ~> (¬ (¬ A) ~> ¬ B) ~> A) A))).
  pose(t5' := Mod_pon t5''
                (Prop_tau _ (P3 B ((¬(¬A) ~> ¬B) ~> A) (¬(¬(¬A) ~> ¬B))))).
  pose(t5 := Mod_pon t5'
              (Prop_tau _
                (P2 ((B ~> (¬ (¬ A) ~> ¬ B) ~> A) ~> B ~> ¬ (¬ (¬ A) ~> ¬ B))
                    A))).
  pose(t6 := Mod_pon tA
              (Mod_pon t3
                (Prop_tau _ (P3 A (B ~> A) (B ~> (¬(¬A) ~> ¬B) ~> A))))).
  pose(t7 := Mod_pon t6
              (Mod_pon t5
                (Prop_tau _
                  (P3 A (B ~> (¬(¬A) ~> ¬B) ~> A) (B ~> ¬(¬(¬A) ~> ¬B)))))).

  unfold sp_and. unfold sp_or.
  exact t7.

(*
  (* t7 *)
  eapply Mod_pon.
  - (* t6*)
    eapply Mod_pon.
    + (* tAlpha *)
      eapply Prop_tau. exact (P2 A B).
    + eapply Mod_pon.
      * (* t3 *)
        eapply Mod_pon.
        -- (* t3' *)
           eapply Mod_pon.
           ++ (* t3'' *)
              eapply Mod_pon.
              ** eapply Prop_tau. exact (P2 A (¬(¬A) ~> ¬B)).
              ** eapply Prop_tau. eapply (P2 _ B).
           ++ eapply Prop_tau. eapply (P3 B A ((¬(¬A) ~> ¬B) ~> A)).
        -- eapply Prop_tau.
           eapply (P2 ((B ~> A) ~> B ~> (¬ (¬ A) ~> ¬ B) ~> A) A).
      * eapply Prop_tau. eapply (P3 A (B ~> A) (B ~> (¬(¬A) ~> ¬B) ~> A)).
  - eapply Mod_pon.
    + (* t5 *)
      eapply Mod_pon.
      * (* t5' *)
        eapply Mod_pon.
        -- (* t5'' *)
           eapply Mod_pon.
           ++ (* t4 *)
              eapply Mod_pon.
              --- (* tBeta *)
                  +++ eapply Prop_tau. exact (P1 B).
              --- eapply Mod_pon.
                  +++ (* t2 *)
                      eapply Mod_pon.
                      *** eapply reorder_meta. eapply Prop_tau.
                          eapply (P4 (¬A) B).
                      *** eapply Prop_tau. eapply (P2 _ B).
                  +++ eapply Prop_tau. eapply (P3 B B _).
           ++ eapply Mod_pon.
              ** (* t1 *)
                 eapply Mod_pon.
                 --- eapply Prop_tau. exact (P3 (¬(¬A) ~> ¬B) A Bot).
                 --- eapply Prop_tau. eapply (P2 _ B).
              ** eapply Prop_tau. eapply (P3 B ((¬(¬A) ~> ¬B) ~> ¬A) _).
        -- eapply Prop_tau. eapply (P3 B ((¬(¬A) ~> ¬B) ~> A) (¬(¬(¬A) ~> ¬B))).
      * eapply Prop_tau.
        eapply (P2 ((B ~> (¬ (¬ A) ~> ¬ B) ~> A) ~> B ~> ¬ (¬ (¬ A) ~> ¬ B)) A).
    + eapply Prop_tau.
      eapply (P3 A (B ~> (¬(¬A) ~> ¬B) ~> A) (B ~> ¬(¬(¬A) ~> ¬B))).
*)

Qed.

Lemma conj_intro_meta (A B : Sigma_pattern) :
  A proved -> B proved -> (A _&_ B) proved.
Proof.
  intros.
  eapply Mod_pon.
  - exact H0.
  - eapply Mod_pon.
    + exact H.
    + exact (conj_intro A B).
Qed.

Lemma conj_intro_meta_e (A B : Sigma_pattern) (theory : Ensemble Sigma_pattern) :
  (theory |- A) -> (theory |- B) -> (theory |- (A _&_ B)).
Proof.
  intros.
  eapply E_mod_pon.
  - eapply H0.
  - eapply E_mod_pon.
    + eapply H.
    + eapply ext. eapply conj_intro.
Qed.


Lemma disj (A B : Sigma_pattern) :
  (A ~> B ~> (A _|_ B)) proved.
Proof.
  intros. unfold sp_or.

  pose(t1 := Prop_tau _ (P2 B (¬A))).
  pose(t2 := Prop_tau _ (P2 (B ~> (¬A ~> B)) A)).
  pose(t3 := Mod_pon t1 t2).

  exact t3.
Qed.

Lemma disj_intro (A B : Sigma_pattern) :
  A proved -> B proved -> (A _|_ B) proved.
Proof.
  intros.
  eapply Mod_pon.
  - exact H0.
  - eapply Mod_pon.
    + exact H.
    + exact (disj A B).
Qed.


Lemma syllogism (A B C : Sigma_pattern) :
  ((A ~> B) ~> (B ~> C) ~> (A ~> C)) proved.
Proof.
  eapply reorder_meta.
  eapply Mod_pon.
  - (* t5 *) eapply Prop_tau. eapply (P2 (B ~> C) A).
  - (* t4 *)eapply Mod_pon.
    + (* t3 *) eapply Mod_pon.
      * eapply Prop_tau. eapply (P3 A B C).
      * (* t2 *) eapply Prop_tau.
        eapply (P2 ((A ~> B ~> C) ~> (A ~> B) ~> A ~> C) (B ~> C)).
    + (* t1 *) eapply Prop_tau.
      eapply (P3 (B ~> C) (A ~> B ~> C) ((A ~> B) ~> A ~> C)).
Qed.

Lemma syllogism_intro (A B C : Sigma_pattern) :
  (A ~> B) proved -> (B ~> C) proved -> (A ~> C) proved.
Proof.
  intros.
  eapply Mod_pon.
  - exact H.
  - eapply Mod_pon.
    + exact H0.
    + eapply reorder_meta. exact (syllogism A B C).
Qed.

Lemma syllogism_4_meta (A B C D : Sigma_pattern) :
  (A ~> B ~> C) proved -> (C ~> D) proved -> (A ~> B ~> D) proved.
Proof.
  intros.
  eapply Mod_pon.
  - exact H.
  - eapply Mod_pon.
    + eapply Mod_pon.
      * eapply Mod_pon.
        -- eapply Mod_pon.
           ++ exact H0.
           ++ eapply Prop_tau. eapply (P2 (C ~> D) B).
        -- eapply Prop_tau. eapply (P3 B C D).
      * eapply Prop_tau. eapply (P2 ((B ~> C) ~> B ~> D) A).
    + eapply Prop_tau. eapply (P3 A (B ~> C) (B ~> D)).
Qed.


Lemma bot_elim (A : Sigma_pattern) :
  (Bot ~> A) proved.
Proof.
  eapply Mod_pon.
  - eapply Mod_pon.
    + eapply Mod_pon.
      * eapply Mod_pon.
        -- eapply Prop_tau. eapply (P2 Bot Bot).
        -- eapply Prop_tau. eapply (P3 Bot Bot Bot).
      * eapply Prop_tau. eapply (P4 Bot Bot).
    + eapply Prop_tau. eapply (P2 (Bot ~> Bot) (A ~> Bot)).
  - eapply Prop_tau. eapply (P4 A Bot).
Qed.


Lemma modus_ponens (A B : Sigma_pattern) :
  (A ~> (A ~> B) ~> B) proved.
Proof.
  eapply Mod_pon.
  - (* t3 *) eapply Prop_tau. eapply (P2 A (A ~> B)).
  - (* t6 *) eapply Mod_pon.
    + (* t4 *)
      eapply Mod_pon.
      * (* t1 *) eapply Prop_tau. eapply (P1 (A ~> B)).
      * (* t2 *) eapply Prop_tau. eapply (P3 (A ~> B) A B).
    + (* t5 *)
      eapply reorder_meta.
      eapply (syllogism A ((A ~> B) ~> A) ((A ~> B) ~> B)).
Qed.

Lemma modus_ponens' (A B : Sigma_pattern) :
  (A ~> (¬B ~> ¬A) ~> B) proved.
Proof. exact (reorder_meta (Prop_tau _ (P4 B A))). Qed.

Lemma disj_right_intro (A B : Sigma_pattern) :
  (B ~> (A _|_ B)) proved.
Proof. exact (Prop_tau _ (P2 B (¬A))). Qed.

Lemma disj_left_intro (A B : Sigma_pattern) :
  (A ~> (A _|_ B)) proved.
Proof. eapply (syllogism_4_meta _ _ _ _ (modus_ponens A Bot) (bot_elim B)). Qed.


Lemma not_not_elim (A : Sigma_pattern) :
  (¬(¬A) ~> A) proved.
Proof.
  eapply Mod_pon.
  - (* t1 *) eapply (modus_ponens (¬A) Bot).
  - (* t2 *) eapply Prop_tau. eapply (P4 A (¬(¬A))).
Qed.


Lemma not_not_intro (A : Sigma_pattern) :
  (A ~> ¬(¬A)) proved.
Proof. unfold sp_not. exact (modus_ponens A Bot). Qed.

Lemma double_elim (A B : Sigma_pattern) :
  (((¬(¬A)) ~> (¬(¬B))) ~> (A ~> B)) proved.
Proof.
  eapply syllogism_intro.
  - eapply Prop_tau. eapply (P4 (¬A) (¬B)).
  - eapply Prop_tau. eapply (P4 B A).
Qed.

Lemma double_elim_meta (A B : Sigma_pattern) :
  ((¬(¬A)) ~> (¬(¬B))) proved -> (A ~> B) proved.
Proof.
  intros.
  eapply Mod_pon.
  - exact H.
  - exact (double_elim A B).
Qed.

Lemma not_not_impl_intro (A B : Sigma_pattern) :
  (A ~> B ~> (¬¬A ~> ¬¬B)) proved.
(*
Proof.
  pose( base := Mod_pon (not_not_intro (B)) (Prop_tau _ (P2 (B ~> ¬¬B) (A ~> ¬¬A)))).
  Check (reorder_meta base).
  pose (a := conj A B).
  unfold sp_and in a. unfold sp_or in a. *)
Admitted.

Lemma P5i (A C : Sigma_pattern) :
  (¬A ~> (A ~> C)) proved.
(*
Proof.
  eapply Mod_pon.
  - eapply reorder_meta. eapply Prop_tau. eapply (P4 C A).
  - eapply Prop_tau. eapply (P3 (¬A) (¬C) (A ~> C)). *)
Admitted.


Lemma a (A B : Sigma_pattern) :
  (¬( ¬¬A ~> ¬¬B )) proved -> (¬( A ~> B)) proved.
(*
Proof.
  intros.
  unfold sp_not.

   eapply Mod_pon.
  - eapply Prop_tau. eapply (P1 Bot).
  - eapply Mod_pon.
    + eapply Mod_pon.
      * eapply Prop_tau. eapply (P1 Bot).
      * eapply Prop_tau. eapply (P2 (Bot ~> Bot) (A ~> B)).
    + eapply Prop_tau. eapply (P3 (A ~> B) Bot Bot).

eapply Prop_tau. eapply (P2 (A ~> B) Bot). *)
Admitted.

Lemma double_elim_ex (A B :Sigma_pattern) :
  ((ex x, (¬¬A ~> ¬¬B)) ~> (ex x, (A ~> B))) proved.
Admitted.

Lemma double_elim_ex_meta (A B :Sigma_pattern) :
  (ex x, (¬¬A ~> ¬¬B)) proved -> (ex x, (A ~> B)) proved.
Admitted.

End FOL_helpers.
