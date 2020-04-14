Require Import Coq.Sets.Ensembles.
Require Import Coq.Logic.Classical_Prop.

Inductive FA_Intersection {T C : Type} (f : C -> Ensemble T) : Ensemble T :=
FA_Int_intro :
  forall x : T, (forall c : C, f c x) -> In T (FA_Intersection f) x.

Inductive FA_Union {T C : Type} (f : C -> Ensemble T) : Ensemble T :=
FA_Uni_intro :
  forall x : T, (exists c : C, f c x) -> In T (FA_Union f) x.

Lemma FA_rel : forall T C : Type, forall f : C -> Ensemble T,
let fcom := fun c => Complement _ (f c) in
Same_set T (Complement T (FA_Union f)) (FA_Intersection fcom).
Proof.
unfold Same_set. unfold Complement. unfold not. unfold Included. unfold In.
split;intros.
* eapply FA_Int_intro. intros. exact (H (FA_Uni_intro f x (ex_intro _ c H0))).
* inversion H. inversion H0. subst. inversion H3. exact (H1 x0 H2).
Qed.

Definition FA_Inters_cond {T C : Type} (g : Ensemble C) (f : C -> Ensemble T) :
                          Ensemble T :=
FA_Intersection (fun c t => g c -> f c t).

Definition FA_Union_cond {T C : Type} (g : Ensemble C) (f : C -> Ensemble T) :
                         Ensemble T :=
FA_Union (fun c t => g c /\ f c t).

Lemma FA_Inters_same : forall T C : Type, forall f f' : C -> Ensemble T,
(forall c, Same_set _ (f c) (f' c)) ->
Same_set _ (FA_Intersection f) (FA_Intersection f').
Proof.
intros. unfold Same_set in *. unfold Included in *. unfold In in *.
eapply conj;intros;eapply FA_Int_intro;inversion H0;intros;destruct (H c);auto.
Qed.

Lemma FA_Union_same : forall T C : Type, forall f f' : C -> Ensemble T,
(forall c, Same_set _ (f c) (f' c)) ->
Same_set _ (FA_Union f) (FA_Union f').
Proof.
intros. unfold Same_set in *. unfold Included in *. unfold In in *.
eapply conj;intros;eapply FA_Uni_intro;inversion H0;destruct H1;destruct(H x1);
eapply ex_intro;auto.
Qed.

Definition mu {T : Type} (f : Ensemble T -> Ensemble T) : Ensemble T :=
  FA_Inters_cond (fun S => Included T (f S) S) (fun S => S).

Definition nu {T : Type} (f : Ensemble T -> Ensemble T) : Ensemble T :=
  FA_Union_cond  (fun S => Included T S (f S)) (fun S => S).

Lemma Union_Empty_r {T : Type} : forall A : Ensemble T,
Same_set T (Union T (Empty_set T) A) A.
Proof.
unfold Same_set. unfold Included. intros. apply conj;intros.
* inversion H. inversion H0. exact H0.
* unfold In in *. eapply Union_intror. exact H.
Qed.

Lemma Union_Empty_l {T : Type} : forall A : Ensemble T,
Same_set T (Union T A (Empty_set T)) A.
Proof.
unfold Same_set. unfold Included. intros. apply conj;intros.
* inversion H. exact H0. inversion H0.
* unfold In in *. eapply Union_introl. exact H.
Qed.

Lemma Compl_Compl_Ensembles : forall T :Type, forall A :Ensemble T,
  Same_set T (Complement T (Complement T A)) A.
Proof.
intros. unfold Same_set.
split;unfold Included;unfold Complement;unfold In;intros.
* now apply NNPP in H.
* unfold not. intro. apply (H0 H).
Qed.

Lemma Union_is_or : forall T : Type,
forall L R : Ensemble T, forall x : T, In T (Union T L R) x <-> L x \/ R x.
Proof.
unfold In. intros. split.
* intro. inversion H.
  - left. exact H0.
  - right. exact H0.
* intro. inversion H.
  - eapply Union_introl. exact H0.
  - eapply Union_intror. exact H0.
Qed.

Lemma Intersection_is_and : forall T : Type,
forall L R : Ensemble T, forall x : T,
  In T (Intersection T L R) x <-> L x /\ R x.
Proof.
unfold In. intros. split.
* intro. inversion H. split.
  - exact H0.
  - exact H1.
* intro. inversion H. eapply Intersection_intro.
  - exact H0.
  - exact H1.
Qed.

Lemma Same_set_Compl {T : Type} (A B : Ensemble T) :
Same_set T A B <-> Same_set T (Complement T A) (Complement T B).
Proof.
split.
* unfold Same_set. unfold Included. unfold Complement. unfold not. unfold In.
  intros. apply conj;intros;inversion H.
  - exact (H0 (H3 _ H1)).
  - exact (H0 (H2 _ H1)).
* unfold Same_set. unfold Included. unfold Complement. unfold In.
  intros. inversion H. apply conj.
  - intros. pose (imply_to_or _ _ (H1 x)). case o;intros.
    + now apply NNPP in H3.
    + contradiction (H3 H2).
  - intros. pose (imply_to_or _ _ (H0 x)). case o;intros.
    + now apply NNPP in H3.
    + contradiction (H3 H2).
Qed.

Lemma Compl_Union_Compl_Intes_Ensembles : forall T :Type,
forall L R : Ensemble T, Same_set T (Complement T (Union T (Complement T L)
                                                           (Complement T R)))
                                    (Intersection T L R).
Proof.
  intros.
  apply Same_set_Compl.
  rewrite (Extensionality_Ensembles _ _ _(Compl_Compl_Ensembles _ _)).
  unfold Same_set. unfold Included. unfold In. split;intros.
  - apply Union_is_or in H.
    unfold Complement. unfold not. unfold In. intro.
    inversion H0. case H;intros;unfold In in *.
    * exact (H4 H1).
    * exact (H4 H2).
  - apply Union_is_or.
    unfold Complement in *. unfold not in *. unfold In in *.
    apply not_and_or. intro. exact (H (proj2 (Intersection_is_and _ L R x) H0)).
Qed.

Lemma Empty_is_Empty : forall T : Type, forall x : T, ~ In T (Empty_set T) x.
Proof. unfold not. intros. inversion H. Qed.

Lemma Complement_Empty_is_Full {T : Type} :
Same_set T (Complement T (Empty_set T)) (Full_set T).
Proof.
unfold Same_set. unfold Complement. unfold Included. unfold In. eapply conj.
* intros. eapply Full_intro.
* intros. eapply Empty_is_Empty.
Qed.

Lemma Same_set_refl {T : Type} (A : Ensemble T) : Same_set T A A.
Proof. unfold Same_set;unfold Included;apply conj;intros;exact H. Qed.

Lemma Same_set_symmetric {T : Type} (A B : Ensemble T) :
Same_set T A B -> Same_set T B A.
Proof. unfold Same_set. intros. inversion H. eapply conj;assumption. Qed.

Lemma Setmin_Val {T : Type} (A B : Ensemble T) :
Same_set T (Complement T (Union T (Complement T A) B)) (Setminus T A B).
Proof.
unfold Same_set. unfold In.
rewrite <- (Extensionality_Ensembles _ _ _ (Compl_Compl_Ensembles _ B)).
rewrite
  (Extensionality_Ensembles _ _ _ (Compl_Union_Compl_Intes_Ensembles _ _ _)).
rewrite (Extensionality_Ensembles _ _ _ (Compl_Compl_Ensembles _ B)).
unfold Included.
eapply conj;intros;inversion H;
((unfold Setminus;apply conj)|| apply Intersection_intro);
try exact H0; unfold Complement in *; unfold In in *; exact H1.
Qed.

Definition Symmetric_difference {T : Type} (A B : Ensemble T) : Ensemble T :=
  Union T (Setminus T A B) (Setminus T B A).

Lemma Symdiff_val {T : Type} (A B : Ensemble T) :
Same_set T (Intersection T (Union T (Complement T A) B)
                           (Union T (Complement T B) A))
           (Complement T (Symmetric_difference A B)).
Proof. unfold Symmetric_difference.
rewrite <-
  (Extensionality_Ensembles _ _ _ (Compl_Union_Compl_Intes_Ensembles T _ _)).
rewrite (Extensionality_Ensembles _ _ _ (Setmin_Val A B)).
rewrite (Extensionality_Ensembles _ _ _ (Setmin_Val B A)).
eapply Same_set_refl.
Qed.
