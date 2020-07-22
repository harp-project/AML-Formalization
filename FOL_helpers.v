Require Export AML_definition.
Import AML_notations.
Require Import Coq.Program.Equality.


Section FOL_helpers.

Lemma A_impl_A (A : Sigma_pattern) : (A ~> A) proved.
Proof.
  pose(_1' := P3 A (A ~> A) A).
  pose(_2' := P2 A (A ~> A)).
  pose(_4' := P2 A A).

  pose(_1 := Prop_tau ((A ~> (A ~> A) ~> A) ~> (A ~> A ~> A) ~> A ~> A) _1').
  pose(_2 := Prop_tau (A ~> (A ~> A) ~> A) _2').
  pose(_3 := Mod_pon _2 _1).
  pose(_4 := Prop_tau (A ~> A ~> A) _4').
  pose(_5 := Mod_pon _4 _3).
  exact _5.
Qed.

Lemma P4m (A B : Sigma_pattern) :
  ((A ~> B) ~> ((A ~> ¬B) ~> ¬A)) proved.
Proof.
  eapply Mod_pon.
  - (* t8 *) eapply Prop_tau. eapply (P2 (A ~> B) (A ~> B ~> Bot)).
  - (* t7 *) eapply Mod_pon.
    + (* t6 *) eapply Mod_pon.
      * (* t5 *) eapply Mod_pon.
        -- (* t4 *) eapply Prop_tau. eapply (P3 A B Bot).
        -- (* t3 *) eapply Prop_tau.
           eapply (P3 (A ~> B ~> Bot) (A ~> B) (A ~> Bot)).
      * (* t2 *) eapply Prop_tau.
        eapply (P2 (((A ~> B ~> Bot) ~> A ~> B) ~> (A ~> B ~> Bot) ~> A ~> Bot)
                   (A ~> B)).
    + (* t1 *) eapply Prop_tau.
      eapply (P3 (A ~> B)
                 ((A ~> B ~> Bot) ~> A ~> B)
                 ((A ~> B ~> Bot) ~> A ~> Bot)).
Qed.

Lemma P4i (A : Sigma_pattern) :
  ((A ~> ¬A) ~> ¬A) proved.
Proof.
  eapply Mod_pon.
  - eapply Prop_tau. eapply (P1 A).
  - eapply (P4m A A).
Qed.

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
    + eapply proof_sys_intro. eapply conj_intro.
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


Lemma not_not_intro (A : Sigma_pattern) :
  (A ~> ¬(¬A)) proved.
(* Donko Istvan *)
Proof. unfold sp_not. exact (modus_ponens A Bot). Qed.


Lemma not_not_elim (A : Sigma_pattern) :
  (¬(¬A) ~> A) proved.
(* Istvan Donko *)
Proof.
  eapply Mod_pon.
  - (* t1 *) eapply (modus_ponens (¬A) Bot).
  - (* t2 *) eapply Prop_tau. eapply (P4 A (¬(¬A))).
Qed.

Lemma double_neg_elim (A B : Sigma_pattern) :
  (((¬(¬A)) ~> (¬(¬B))) ~> (A ~> B)) proved.
Proof.
  eapply syllogism_intro.
  - eapply Prop_tau. eapply (P4 (¬A) (¬B)).
  - eapply Prop_tau. eapply (P4 B A).
Qed.

Lemma double_neg_elim_meta (A B : Sigma_pattern) :
  ((¬(¬A)) ~> (¬(¬B))) proved -> (A ~> B) proved.
Proof.
  intros.
  eapply Mod_pon.
  - exact H.
  - exact (double_neg_elim A B).
Qed.

Lemma deduction (A B : Sigma_pattern) :
  A proved -> B proved -> (A ~> B) proved.
Proof.
  intros.
  eapply Mod_pon.
  - exact H0. 
  - eapply (Prop_tau _ (P2 B A)).
Qed.

Lemma P4_rev_meta (A B : Sigma_pattern) :
  (A ~> B) proved -> ((A ~> B) ~> (¬B ~> ¬A)) proved.
Proof.
  intros.
  eapply deduction.
  - exact H.
  - eapply Mod_pon.
    * eapply syllogism_intro.
      + eapply syllogism_intro.
        -- eapply (not_not_elim A).
        -- exact H.
      + eapply (not_not_intro B).
    * eapply (Prop_tau _ (P4 (¬A) (¬B))).
Qed.

Lemma P4m_neg (A B : Sigma_pattern) :
  ((¬B ~> ¬A) ~> (A ~> ¬B) ~>  ¬A) proved.
Proof.
  pose (PT := Prop_tau _ (P4 B A)).
  eapply syllogism_intro.
  * exact PT.
  * apply P4m.
Qed.

Lemma not_not_impl_intro_meta (A B : Sigma_pattern) :
  (A ~> B) proved -> ((¬¬A) ~> (¬¬B)) proved.
Proof.
  intros.
  pose (NN1 := not_not_elim A).
  pose (NN2 := not_not_intro B).
  pose (S1 := syllogism_intro _ _ _ H NN2).
  pose (S2 := syllogism_intro _ _ _ NN1 S1).
  exact S2.
Qed.

Lemma not_not_impl_intro (A B : Sigma_pattern) :
  ((A ~> B) ~> ((¬¬A) ~> (¬¬B))) proved.
Proof.
  intros.
  pose (S1 := syllogism (¬¬A) A B).
  pose (MP1 := @Mod_pon (¬ (¬ A) ~> A) ((A ~> B) ~> ¬ (¬ A) ~> B) (not_not_elim A) S1).
  pose (NNB := not_not_intro B).
  pose (P2 := Prop_tau _ (P2 (B ~> ¬ (¬ B)) (¬¬A))).
  pose (MP2 := Mod_pon NNB P2).
  pose (P3 := Prop_tau _ (P3 (¬¬A) B (¬¬B))).
  pose (MP3 := Mod_pon MP2 P3).
  apply syllogism_intro with (B := (¬ (¬ A) ~> B)); assumption.
Qed.

Lemma contraposition (A B : Sigma_pattern) :
  ((A ~> B) ~> ((¬ B) ~> (¬ A))) proved.
Proof.
  pose (Prop_tau _ (P4 (¬ A) (¬ B))).
  apply syllogism_intro with (B := (¬ (¬ A) ~> ¬ (¬ B))).
  * apply not_not_impl_intro.
  * apply (Prop_tau _ (P4 _ _)).
Qed.

(*
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

(* Q5 *)
(*
\neg \exists x . \neg phi -> phi[y/x]  // by notation
\neg phi[y/x] -> \exists x . \neg phi // by propositional reasoning
(\neg phi)[y/x] -> \exists x . \neg phi // meta-property of substitution
 *)

Lemma neg_ex_quan : forall A : Sigma_pattern, forall x y : EVar,
  ((¬ e_subst_var A 'y x) ~> (ex x, ¬A)) proved.
Proof.
  intros.
  unfold sp_not.


Qed.

  
Lemma Q5 : forall x y : EVar, forall A : Sigma_pattern,
  ((all x, A) ~> (e_subst_var A 'y x)) proved.
Proof.
  intros.
  unfold sp_forall.
  unfold sp_not.

Qed.

(* exists intro *)
(*
x \in \exists z . z /\ phi(z)
iff \exists z . x \in (z /\ phi(z))
iff \exists z . (x \in z) /\ phi(z)
iff \exists z . x=z /\ phi(z)
iff phi(x)
*)
Lemma exists_intro : forall x z : EVar, forall phi : EVar -> Sigma_pattern,
  (phi(x) ~> ('x -< ex z, 'z _&_ phi(z))) proved.
Proof.
  intros.

Qed.
*)

Lemma or_comm_meta A B:
  (A _|_ B) proved -> (B _|_ A) proved.
Proof.
  intros. unfold sp_or in *.
  pose (P4 := Prop_tau _ (P4 A (¬B))).
  pose (NNI := not_not_intro B).
  pose (SI := syllogism_intro _ _ _ H NNI).
  eapply Mod_pon.
  * exact SI.
  * exact P4.
Qed.
(* 
Lemma and_comm_meta A B:
  (A _&_ B) proved -> (B _&_ A) proved.
Proof.
  unfold sp_and.
  unfold sp_not at 1.
  unfold sp_not at 3.
  intros.
  pose (or_comm_meta (¬B) (¬A)).
  pose (syllogism_intro ).
Qed.

Lemma equiv_comm A B:
  (A <~> B) proved -> (B <~> A) proved.
Proof.
  intros. unfold sp_iff in *.
Qed. *)

Lemma A_implies_not_not_A_alt A:
  A proved -> (¬( ¬A )) proved
.
Proof.
  intros. unfold sp_not.
  pose (NN := not_not_intro A).
  pose (MP := Mod_pon H NN). assumption.
Qed.

(* Lemma 46 *)
Lemma A_implies_not_not_A_ctx A C:
  A proved -> (¬ (subst_ctx C ( ¬A ))) proved
.
Proof.
  intros.
  pose (ANNA := A_implies_not_not_A_alt _ H).
  replace (¬ (¬ A)) with ((¬ A) ~> Bot) in ANNA. 2: auto.
  pose (EF := Framing C (¬ A) Bot ANNA).

  pose (PB := Prop_bot C).
  pose (TRANS := syllogism_intro _ _ _ EF PB).
  unfold sp_not.
  assumption.
Qed.

Lemma A_implies_not_not_A_alt_theory G A:
  G |- A -> G |- (¬( ¬A ))
.
Proof.
  intros. unfold sp_not.
  pose (NN := not_not_intro A).
  pose (MP := E_mod_pon _ _ G H (proof_sys_intro _ _ NN)). assumption.
Qed.

(* Lemma 47 *)
Lemma equiv_implies_eq A B:
  (A <~> B) proved
->
  (A ~=~ B) proved.
Proof.
  intros.
  pose (CTX := A_implies_not_not_A_ctx (A <~> B) (ctx_app_r (^ definedness_symbol) box) H).
  simpl in CTX.
  unfold equal.
  assumption.
Qed.

Lemma equiv_implies_eq_theory G A B:
  G |- (A <~> B)
->
  G |- (A ~=~ B).
Proof.

Admitted.

Lemma e_eq_nne A:
  (A ~=~ (¬(¬A))) proved.
Proof.
  apply equiv_implies_eq.
  unfold "<~>".
  apply conj_intro_meta.
  * apply (not_not_intro A).
  * apply (not_not_elim A).
Qed.

(* Context Bot propagation *)
Lemma ctx_bot_prop A C :
  (A ~> Bot) proved
->
  (subst_ctx C A ~> Bot) proved.
Proof.
  intros.
  pose (FR := Framing C A Bot H).
  pose (BPR := Prop_bot C).
  pose (TRANS := syllogism_intro _ _ _ FR BPR).
  assumption.
Qed.

Lemma P5i A B:
  (¬ A ~> (A ~> B)) proved
.
Proof.
  pose (Ax1 := (Prop_tau _ (P2 (¬A) (¬B)))).
  pose (Ax2 := (Prop_tau _ (P4 B A))).
  pose (TRANS := syllogism_intro _ _ _ Ax1 Ax2).
  assumption.
Qed.

Lemma false_implies_everything phi:
  (Bot ~> phi) proved.
Proof.
  pose (B_B := (Prop_tau _ (P1 (Bot)))).
  pose (P4 := P5i Bot phi).
  apply Mod_pon in P4; assumption.
Qed.

(* Lemma 46 rev *)
Lemma not_not_A_ctx_implies_A A C:
  (¬ (subst_ctx C ( ¬A ))) proved -> A proved.
Proof.
  intro.
  unfold sp_not in H at 1.
  pose (BIE := false_implies_everything (subst_ctx C Bot)).
  (* assert (G |- (subst_ctx C (¬ A) ~> Bot)). { auto. } *)
  pose (TRANS := syllogism_intro _ _ _ H BIE).
  induction C.
  * simpl in TRANS.
    pose (NN := not_not_elim A).
    pose (MP := Mod_pon TRANS NN). assumption.
  * eapply IHC.
  Unshelve.
  pose (BPR := ctx_bot_prop).
Abort.


(* Lemma 47 rev *)
Lemma eq_implies_equiv G A B:
  G |- (A ~=~ B)
->
  G |- (A <~> B).
Proof.
  intros.
Abort.

Lemma provable_to_proved A : empty_theory |- A -> A proved.
Proof.
  intros. dependent induction H; assert (Empty_set Sigma_pattern = empty_theory); try(reflexivity).
  * inversion H.
  * assumption.
  * pose (IHProvable1 H1).
    pose (IHProvable2 H1).
    eapply Mod_pon.
    - exact a.
    - exact a0.
  * pose (IHProvable H1).
    eapply Ex_gen; assumption.
  * pose (IHProvable H0).
    eapply Framing; assumption.
  * pose (IHProvable H0).
    eapply Svar_subst; assumption.
  * pose (IHProvable H0).
    eapply Knaster_tarski; assumption.
Qed.

Lemma proved_impl_to_provable A B:
  (A proved -> B proved)
->
  (empty_theory |- A -> empty_theory |- B).
Proof.
  intros. apply provable_to_proved in H0.
  eapply proof_sys_intro. exact (H H0).
Qed.

Lemma exclusion G A:
  G |- A -> G |- (A ~> Bot) -> G |- Bot.
Proof.
  intros.
  unfold sp_not in H0.
  pose (E_mod_pon A Bot G H H0).
  assumption.
Qed.

Axiom exclusion_axiom : forall G A,
  G |- A -> G |- (¬ A) -> False.

Axiom or_or : forall G A,
G |- A \/ G |- (¬ A).

Axiom extension : forall G A B,
  G |- A -> (Add Sigma_pattern G B) |- A.

Lemma empty_theory_implies_any A : forall G,
  empty_theory |- A -> G |- A.
Proof.
  intros. dependent induction H; assert (Empty_set Sigma_pattern = empty_theory); try(reflexivity).
  * inversion H.
  * apply (proof_sys_intro _ _ H).
  * pose (IHProvable1 H1).
    pose (IHProvable2 H1).
    eapply E_mod_pon.
    - exact p.
    - exact p0.
  * pose (IHProvable H1).
    eapply E_ex_gen; assumption.
  * pose (IHProvable H0).
    eapply E_framing; assumption.
  * pose (IHProvable H0).
    eapply E_svar_subst; assumption.
  * pose (IHProvable H0).
    eapply E_knaster_tarski; assumption.
Qed.

Lemma empty_proves_A_impl_A (A : Sigma_pattern) : empty_theory |- (A ~> A).
Proof. eapply proof_sys_intro. exact (A_impl_A A). Qed.

(* mML : Proposition 44 *)
Lemma equiv_cong G phi1 phi2 C x :
  (G |- (phi1 <~> phi2)) -> G |- ((e_subst_var C phi1 x) <~> (e_subst_var C phi2 x)).
Admitted.

(* Proposition 7: definedness related properties *)
Lemma eq_refl
  (phi : Sigma_pattern) (theory : Ensemble Sigma_pattern) :
    theory |- (phi ~=~ phi).
Proof.
  pose (Prop_tau _ (P1 phi)).
  assert ((phi <~> phi) proved).
  { unfold "<~>". apply conj_intro_meta; assumption. }
  pose (A_implies_not_not_A_ctx (phi <~> phi) (ctx_app_r ^definedness_symbol box) H).
  simpl in a0. unfold "~=~". unfold total. unfold defined.
  apply proof_sys_intro. assumption.
Qed.

Lemma eq_trans
  (phi1 phi2 phi3 : Sigma_pattern) (theory : Ensemble Sigma_pattern) :
    theory |- (phi1 ~=~ phi2) -> theory |- (phi2 ~=~ phi3) ->
    theory |- (phi1 ~=~ phi3).
Proof.
  intros.
  
Admitted.

Lemma eq_symm
  (phi1 phi2 : Sigma_pattern)  (theory : Ensemble Sigma_pattern) :
    theory |- (phi1 ~=~ phi2) -> theory |- (phi2 ~=~ phi1).
Proof.
  intros.
  eapply E_mod_pon.
  * exact H.
  * apply (deduction_intro).
    pose (A_implies_not_not_A_ctx).
Admitted.

Lemma eq_evar_subst
  (x : EVar) (phi1 phi2 psi : Sigma_pattern) (theory : Ensemble Sigma_pattern) :
    theory |- (phi1 ~=~ phi2) ->
    theory |- ((e_subst_var psi phi1 x) ~=~ (e_subst_var psi phi2 x)).
Proof.
  intros.
  eapply E_mod_pon.
  * exact H.
  * apply (deduction_intro).
    unfold "~=~".
    pose (equiv_cong (Add Sigma_pattern theory (phi1 <~> phi2)) phi1 phi2 psi x).
    apply (equiv_implies_eq_theory (Add Sigma_pattern theory (phi1 <~> phi2)) (e_subst_var psi phi1 x) (e_subst_var psi phi2 x)).
    apply equiv_cong.
Admitted.


Lemma A_implies_A_totality A:
  A proved -> |_ A _| proved.
Proof.
  intros.
  pose (ANNA := A_implies_not_not_A_ctx A (ctx_app_r ^definedness_symbol box) H).
  exact ANNA.
Qed.

Lemma A_totality_implies_A A:
  |_ A _| proved -> A proved.
Proof.
  intros.
  unfold total in H. unfold defined in H.
Abort.


(**
  See: email from AML guys
*)
Lemma universal_instantiation A x y:
  ((all x, A) ~> (e_subst_var A ('y) x)) proved.
Proof.
  unfold sp_forall.
  pose (Prop_tau _ (P4 (e_subst_var A 'y x) (¬ ex x, (¬ A)))).
  eapply Mod_pon. 2: exact a.
  apply syllogism_intro with (B := ex x, (¬ A)).
  * assert ((¬ e_subst_var A 'y x) = e_subst_var (¬ A) 'y x).
    { unfold "¬". simpl. reflexivity. }
    rewrite H.
    apply (@Ex_quan (¬A) x y).
  * apply not_not_intro.
Qed.

Example universal_inst_test x y G :
  (Add _ G (Definedness_forall x)) |- |^ 'y ^|.
Proof.
  pose (hypothesis (Definedness_forall x) (Add Sigma_pattern G (Definedness_forall x))).
  pose (Ensembles_Ext.in_add_set Sigma_pattern G (Definedness_forall x)).
  pose (p i).
  unfold Definedness_forall in p0.
  pose (universal_instantiation (|^ ' x ^|) x y).
  pose (proof_sys_intro _ (Add Sigma_pattern G (Definedness_forall x)) a).
  pose (E_mod_pon _ _ _ p0 p1).
  simpl e_subst_var in p2.
  
  (* This assert and clear was needed to "refresh" the hypothesis
     without causing dependent type error
     potential Coq bug *)
  assert (Add Sigma_pattern G (all x, (|^ ' x ^|)))
   |- (^ {| id_si := "definedness" |} $ (if evar_eq_dec x x then ' y else ' x)).
   {  auto. }
  clear p2.
  case_eq (evar_eq_dec x x); intros.
  * rewrite H0 in H. assumption.
  * congruence.
Qed.

Ltac in_hyp := (
  unfold Add;
  repeat (
    try (eapply Union_intror; reflexivity);
    eapply Union_introl
  )).

Lemma not_not_A_proves_A : forall A : Sigma_pattern,
let G := (Add _ (Add _ empty_theory
                (¬(¬A)))
                ((¬A ~> ¬A) ~> (¬A ~> ¬(¬A)) ~> A))
  in
   G |- A.
Proof.
  intros.
  unfold G.
  eapply E_mod_pon.
  - eapply E_mod_pon.
    * eapply (hypothesis (¬(¬A)) G). in_hyp.
    * eapply (proof_sys_intro ((¬(¬A)) ~> (¬A ~> ¬(¬A))) G).
      + eapply Prop_tau. eapply (P2 (¬(¬A)) (¬A)).
  - eapply E_mod_pon.
    * eapply (proof_sys_intro _ G (Prop_tau _ (P1 (¬A)))).
    * eapply (hypothesis ((¬A ~> ¬A) ~> (¬A ~> ¬(¬A)) ~> A)). in_hyp.
Qed.

End FOL_helpers.
