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
  ((¬A ~> ¬B) ~> (A ~> ¬B) ~>  ¬A) proved.
Admitted.

Lemma double_elim (A B : Sigma_pattern) :
  (((¬(¬A)) ~> (¬(¬B))) ~> (A ~> B)) proved.
Proof.
  eapply syllogism_intro.
  - eapply Prop_tau. eapply (P4 (¬A) (¬B)).
  - eapply Prop_tau. eapply (P4 B A).
Qed.

(* double_elim_meta *)
Lemma double_neg_elim_meta (A B : Sigma_pattern) :
  ((¬(¬A)) ~> (¬(¬B))) proved -> (A ~> B) proved.
Proof.
  intros.
  eapply Mod_pon.
  - exact H.
  - exact (double_elim A B).
Qed.

Lemma not_not_impl_intro_meta (A B : Sigma_pattern) :
  (A ~> B) proved -> (¬¬A ~> ¬¬B) proved.
Admitted.

Lemma not_not_impl_intro (A B : Sigma_pattern) :
  (A ~> B ~> (¬¬A ~> ¬¬B)) proved.
Admitted.

(*
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

(* Lemma 47 *)
Lemma equiv_implies_eq A B:
  (A <~> B) proved
->
  (A ~=~ B) proved.
Proof.
  intros.
  pose (CTX := A_implies_not_not_A_ctx (A <~> B) (ctx_app_r definedness_symbol box) H).
  simpl in CTX.
  unfold equal.
  assumption.
Qed.

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

(* Proposition 7: definedness related properties *)
Lemma eq_refl
  (phi : Sigma_pattern) (theory : Ensemble Sigma_pattern) :
    theory |- (phi ~=~ phi).
Proof.
  pose (Prop_tau _ (P1 phi)).
  assert ((phi <~> phi) proved).
  { unfold "<~>". apply conj_intro_meta; assumption. }
  pose (A_implies_not_not_A_ctx (phi <~> phi) (ctx_app_r definedness_symbol box) H).
  simpl in a0. unfold "~=~". unfold total. unfold defined.
  apply proof_sys_intro. assumption.
Qed.

End FOL_helpers.
