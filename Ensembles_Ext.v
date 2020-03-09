Require Import Coq.Sets.Ensembles.

Inductive FA_Intersection {T C : Type} (f : C -> Ensemble T) : Ensemble T :=
  FA_Int_intro : forall x : T,
      (forall c : C, f c x) -> In T (FA_Intersection f) x.

Inductive FA_Union {T C : Type} (f : C -> Ensemble T) : Ensemble T :=
  FA_Uni_intro : forall x : T,
      (exists c : C, f c x) -> In T (FA_Union f) x.

Axiom FA_rel : forall T C : Type, forall f fcomp : C -> Ensemble T,
(forall c : C, Same_set T (Complement T (f c)) (fcomp c))
-> Same_set T (Complement T (FA_Union f)) (FA_Intersection fcomp).

Definition mu {T : Type} (f : Ensemble T -> Ensemble T) : Ensemble T :=
  FA_Intersection (fun S => let S' := f S in fun x => Included T S' S -> S x).

Definition nu {T : Type} (f : Ensemble T -> Ensemble T) : Ensemble T :=
  FA_Union (fun S => let S' := f S in fun x => Included T S S' -> S x).

Lemma Union_Empty_r {T : Type} : forall A : Ensemble T, Same_set T (Union T (Empty_set T) A) A.
Proof.
unfold Same_set. unfold Included. intros. apply conj;intros.
 * inversion H. inversion H0. exact H0.
 * unfold In in *. eapply Union_intror. exact H.
Qed.

Lemma Union_Empty_l {T : Type} : forall A : Ensemble T, Same_set T (Union T A (Empty_set T)) A.
Proof.
unfold Same_set. unfold Included. intros. apply conj;intros.
 * inversion H. exact H0. inversion H0.
 * unfold In in *. eapply Union_introl. exact H.
Qed.

Axiom Compl_Compl_Ensembles : forall T :Type, forall A :Ensemble T, Same_set T (Complement T (Complement T A)) A.

Axiom Compl_Union_Coml_Intes_Ensembles : forall T :Type, forall L R : Ensemble T, Same_set T (Complement T (Union T (Complement T L) (Complement T R))) (Intersection T L R).

Axiom Empty_is_Empty : forall T : Type, forall x : T, ~ In T (Empty_set T) x.

Lemma Complement_Empty_is_Full {T : Type} : Same_set T (Complement T (Empty_set T)) (Full_set T).
Proof.
unfold Same_set. unfold Complement. unfold Included. unfold In. eapply conj.
* intros. eapply Full_intro.
* intros. eapply Empty_is_Empty.
Qed.

Lemma Same_set_refl {T : Type} (A : Ensemble T) : Same_set T A A.
Proof. unfold Same_set;unfold Included;apply conj;intros;exact H. Qed.

Lemma Same_set_Compl {T : Type} (A B : Ensemble T) : Same_set T A B -> Same_set T (Complement T A) (Complement T B).
Proof.
unfold Same_set. unfold Included. unfold Complement. unfold not. unfold In.
intros. apply conj;intros;inversion H. exact (H0 (H3 _ H1)). exact (H0 (H2 _ H1)).
Qed.

Lemma Same_set_symmetric {T : Type} (A B : Ensemble T) : Same_set T A B -> Same_set T B A.
Proof. unfold Same_set. intros. inversion H. eapply conj;assumption. Qed.

Lemma Setmin_Val {T : Type} (A B : Ensemble T) : Same_set T (Complement T (Union T (Complement T A) B)) (Setminus T A B).
Proof.
unfold Same_set. unfold In.
rewrite <- (Extensionality_Ensembles _ _ _ (Compl_Compl_Ensembles _ B)).
rewrite (Extensionality_Ensembles _ _ _ (Compl_Union_Coml_Intes_Ensembles _ _ _)).
rewrite (Extensionality_Ensembles _ _ _ (Compl_Compl_Ensembles _ B)).
unfold Included. eapply conj;intros;inversion H;((unfold Setminus;apply conj)|| apply Intersection_intro);try exact H0; unfold Complement in *; unfold In in *; exact H1.
Qed.

Definition Symmetric_difference {T : Type} (A B : Ensemble T) : Ensemble T :=
  Union T (Setminus T A B) (Setminus T B A).

Lemma Symdiff_val {T : Type} (A B : Ensemble T) : Same_set T (Intersection T (Union T (Complement T A) B) (Union T (Complement T B) A))
  (Complement T (Symmetric_difference A B)).
Proof. unfold Symmetric_difference.
rewrite <- (Extensionality_Ensembles _ _ _ (Compl_Union_Coml_Intes_Ensembles T _ _)).
rewrite (Extensionality_Ensembles _ _ _ (Setmin_Val A B)).
rewrite (Extensionality_Ensembles _ _ _ (Setmin_Val B A)).
eapply Same_set_refl.
Qed.

