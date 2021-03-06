Require Export Coq.Sets.Ensembles.
Require Export Coq.Logic.Classical_Prop.
Require Export Coq.Logic.Classical_Pred_Type.

(* README ForAll_Intersection/Union
Generic versions of the usual intersection and union operators.
These operators accumulate over the whole C carrier set. 
*)

Inductive FA_Intersection {T C : Type} (f : C -> Ensemble T) : Ensemble T :=
FA_Int_intro :
  forall x : T, (forall c : C, f c x) -> In T (FA_Intersection f) x.

Inductive FA_Union {T C : Type} (f : C -> Ensemble T) : Ensemble T :=
FA_Uni_intro :
  forall x : T, (exists c : C, f c x) -> In T (FA_Union f) x.

Definition FA_Inters_cond {T C : Type} (g : Ensemble C) (f : C -> Ensemble T) :
                          Ensemble T :=
FA_Intersection (fun c t => g c -> f c t).

Definition FA_Union_cond {T C : Type} (g : Ensemble C) (f : C -> Ensemble T) :
                         Ensemble T :=
FA_Union (fun c t => g c /\ f c t).

(* Knaster-Tarski Fixpoint operators *)

Definition mu {T : Type} (f : Ensemble T -> Ensemble T) : Ensemble T :=
  FA_Inters_cond (fun S => Included T (f S) S) (fun S => S).

Definition nu {T : Type} (f : Ensemble T -> Ensemble T) : Ensemble T :=
  FA_Union_cond  (fun S => Included T S (f S)) (fun S => S).

(* Properties of the generic operators *)

Lemma FA_rel : forall T C : Type, forall f : C -> Ensemble T,
let fcom := fun c => Complement _ (f c) in
Same_set T (Complement T (FA_Union f)) (FA_Intersection fcom).
Proof.
unfold Same_set. unfold Complement. unfold not. unfold Included. unfold In.
split;intros.
* eapply FA_Int_intro. intros. exact (H (FA_Uni_intro f x (ex_intro _ c H0))).
* inversion H. inversion H0. subst. inversion H3. exact (H1 x0 H2).
Qed.

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

(** Properties of the standard set operators

   see also:
   https://coq.github.io/doc/master/stdlib/Coq.Sets.Powerset_facts.html

 *)

Coercion Same_set_to_eq {T : Type} {A B : Ensemble T} :=
  fun (P : Same_set T A B) => Extensionality_Ensembles T A B P.

Lemma Union_same {T : Type} : forall A : Ensemble T,
  Same_set T (Union T A A) A.
Proof.
  unfold Same_set. unfold Included. split;intros.
  * inversion H; assumption.
  * unfold In. eapply Union_introl. assumption.
Qed.

Lemma Intersection_same {T : Type} : forall A : Ensemble T,
  Same_set T (Intersection T A A) A.
Proof.
  unfold Same_set. unfold Included. split;intros.
  * inversion H; assumption.
  * unfold In. eapply Intersection_intro; assumption.
Qed.

Lemma In_dec {T : Type} : forall A : Ensemble T, forall x : T,
  In T A x \/ ~ In T A x.
Proof.
  intros. unfold In.
  apply classic.
Qed.

Lemma Intersection_Setminus {T : Type} : forall S1 S2 : Ensemble T,
  Same_set T (Intersection T S1 (Complement T S2)) (Setminus T S1 S2).
Proof.
  unfold Same_set. unfold Included. split;intros.
  * inversion H; subst.
    unfold Setminus. unfold Complement in H1. unfold In in *. auto.
  * inversion H. unfold In in *. eapply Intersection_intro.
    - unfold In. assumption.
    - unfold Complement. unfold In. assumption.
Qed.

Lemma Minus_Empty_Inclusion {T : Type} : forall S1 S2 : Ensemble T,
  Same_set T (Setminus T S1 S2) (Empty_set T) <->
  Included T S1 S2.
Proof.
  unfold Same_set. intros. unfold Setminus. unfold Included. unfold In.
  split; intros.
  * destruct (In_dec S2 x).
    - auto.
    - assert (S1 x /\ ~ S2 x). { auto. }
      inversion H.
      pose (H3 x H2). contradiction.
  * split; intros.
    - inversion H0. pose (H x H1). contradiction.
    - contradiction.
Qed.

Lemma Union_Minus_Empty {T : Type} : forall S1 S2 : Ensemble T,
  Same_set T (Union T (Setminus T S1 S2) (Setminus T S2 S1)) (Empty_set T) <->
  Same_set T S1 S2.
Proof.
  unfold Same_set. intros. unfold Setminus. unfold Included. unfold In.
  split; intros; split; intros.
  * inversion H. destruct (In_dec S2 x).
    - auto.
    - assert (S1 x /\ ~ S2 x). { auto. }
      assert (Union T (fun x : T => S1 x /\ ~ S2 x) (fun x : T => S2 x /\ ~ S1 x) x).
      {
        eapply Union_introl.
        unfold In. assumption.
      }
      pose (H1 x H5). contradiction.
  * inversion H. destruct (In_dec S1 x).
    - auto.
    - assert (S2 x /\ ~ S1 x). { auto. }
      assert (Union T (fun x : T => S1 x /\ ~ S2 x) (fun x : T => S2 x /\ ~ S1 x) x).
      {
        eapply Union_intror.
        unfold In. assumption.
      }
      pose (H1 x H5). contradiction.
  * inversion H. inversion H0.
    - subst. inversion H3. pose (H1 x H4). contradiction.
    - subst. inversion H3. pose (H2 x H4). contradiction.
  * contradiction.
Qed.

Lemma Union_Symmetric {T : Type} : forall S1 S2 : Ensemble T,
  Same_set T (Union T S1 S2) (Union T S2 S1).
Proof.
  intros.
  constructor; unfold Included; unfold In; intros; inversion H;
    try (apply Union_intror; assumption); try (apply Union_introl; assumption).
Qed.

Lemma Intersection_Symmetric {T : Type} : forall S1 S2 : Ensemble T,
  Same_set T (Intersection T S1 S2) (Intersection T S2 S1).
Proof.
  intros; constructor; constructor; inversion H; assumption.
Qed.

Lemma Union_Transitive {T : Type} : forall S1 S2 S3 : Ensemble T,
  Same_set T (Union T (Union T S1 S2) S3) (Union T S1 (Union T S2 S3)).
Proof.
  intros. constructor; unfold Included; unfold In; intros; inversion H.
  inversion H0.
  apply Union_introl. exact H2.
  apply Union_intror. apply Union_introl. exact H2.
  apply Union_intror. apply Union_intror. exact H0.
  apply Union_introl. apply Union_introl. exact H0.
  inversion H0.
  apply Union_introl. apply Union_intror. exact H2.
  apply Union_intror. exact H2.
Qed.

Lemma Union_Compl_Fullset {T : Type} : forall S : Ensemble T,
  Same_set T (Union T (Complement T S) S) (Full_set T).
Proof.
  unfold Same_set. intros. unfold Setminus. unfold Included. unfold In.
  split; intros.
  * inversion H; subst.
    - eapply Full_intro.
    - eapply Full_intro.
  * inversion H. destruct (In_dec S x).
    - eapply Union_intror. assumption.
    - eapply Union_introl. assumption.
Qed.

Lemma Same_set_dec {T : Type} : forall S1 S2 : Ensemble T,
  Same_set T S1 S2 \/ ~Same_set T S1 S2.
Proof.
  intros. apply classic.
Qed.

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

Lemma Intersection_Full_r {T : Type} : forall A : Ensemble T,
Same_set T (Intersection T (Full_set T) A) A.
Proof.
unfold Same_set. unfold Included. intros. apply conj;intros.
* inversion H. exact H1. 
* unfold In in *. constructor. constructor. exact H.
Qed.

Lemma Intersection_Full_l {T : Type} : forall A : Ensemble T,
Same_set T (Intersection T A (Full_set T)) A.
Proof.
unfold Same_set. unfold Included. intros. apply conj;intros.
* inversion H. exact H0.
* unfold In in *. constructor. exact H. constructor.
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

(* Lemma Intersection_singleton_helper {T : Type} : forall S : Ensemble T, forall x : T,
  Same_set T (Intersection T (Singleton T x) S) (Empty_set T) \/
  Same_set T (Intersection T (Singleton T x) S) (Singleton T x).
Proof.
  intros. unfold Same_set. unfold Included. unfold Complement. unfold In.
  destruct (In_dec S x). *)

Lemma Intersection_singleton {T : Type} : forall S : Ensemble T, forall x : T,
  ~ Same_set T (Intersection T (Singleton T x) S) (Empty_set T)
<->
  In T S x.
Proof.
  unfold Same_set. unfold Included. unfold Complement. unfold In.
  intros.
  
  split;intros.
  * destruct (In_dec S x).
    - assumption.
    - assert (False). {
        apply H. split.
        * intros. inversion H1. subst. inversion H2. subst. contradiction. 
        * intros. contradiction.
      }
      contradiction.
  * unfold not. intros. inversion H0. destruct (In_dec (Intersection T (Singleton T x) S) x).
    - pose (H1 x H3). contradiction.
    - unfold not in H3. unfold In in H3.
      apply H3. apply Intersection_intro.
      + apply In_singleton.
      + assumption.
Qed.

Lemma Intersection_singleton_empty {T : Type} : forall S : Ensemble T, forall x : T,
  Same_set T (Intersection T (Singleton T x) S) (Empty_set T)
<->
  ~ In T S x.
Proof.
  unfold Same_set. unfold Included. unfold Complement. unfold In.
  intros.
  
  split;intros.
  * inversion H. destruct (In_dec S x).
    - assert (Intersection T (Singleton T x) S x). 
      { eapply Intersection_intro. apply In_singleton. assumption. }
      pose (H0 x H3).
      contradiction.
    - assumption.
  * split; intros.
   - inversion H0. subst. inversion H1. subst. contradiction.
   - contradiction.
Qed.

Lemma Compl_Union_Compl_Intes_Ensembles_alt : forall T :Type,
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

Lemma Compl_Union_Intes_Compl_Ensembles : forall T :Type,
forall L R : Ensemble T, Same_set T (Complement T (Union T L R))
                                    (Intersection T (Complement T L) (Complement T R)).
Proof.
  intros.
  pose (S := Compl_Union_Compl_Intes_Ensembles_alt T (Complement T L) (Complement T R)).
  pose (S1 := Compl_Compl_Ensembles T R).
  pose (S2 := Compl_Compl_Ensembles T L).
  apply Extensionality_Ensembles in S1.
  apply Extensionality_Ensembles in S2.
  rewrite S1, S2 in S. assumption.
Qed.

Lemma Compl_Intes_Union_Compl_Ensembles : forall T :Type,
forall L R : Ensemble T, Same_set T (Complement T (Intersection T L R))
                                    (Union T (Complement T L) (Complement T R)).
Proof.
  intros.
  apply Same_set_Compl.
  rewrite (Extensionality_Ensembles _ _ _(Compl_Compl_Ensembles _ _)).
  unfold Same_set. unfold Included. unfold In. split;intros.
  - inversion H.
    unfold Complement at 1. unfold not in *. unfold In in *.
    intros. subst. inversion H3.
    + unfold Complement in H2. unfold In in *. contradiction.
    + unfold Complement in H2. unfold In in *. contradiction.
  - rewrite (Same_set_to_eq (Compl_Union_Compl_Intes_Ensembles_alt T L R)) in H. assumption.
Qed.

(* (L inter R) U ~L = R U ~L *)
Lemma Intes_Union_Compl_Ensembles:
  forall (T : Type) (L R : Ensemble T),
  Same_set T (Union T (Intersection T L R) (Complement T L)) (Union T R (Complement T L)).
Proof.
  intros. constructor.
  * unfold Included. intros. inversion H; subst. apply Intersection_is_and in H0.
    apply Union_introl; apply H0.
    apply Union_intror; apply H0.
  * unfold Included. intros. inversion H; subst.
    assert (Union T (Complement T L) L = Full_set T).
    apply Same_set_to_eq; apply Union_Compl_Fullset.
    assert (In T (Full_set T) x) by constructor. rewrite <- H1 in H2.
    inversion H2; subst.
    apply Union_intror. exact H3.
    apply Union_introl. constructor; assumption.
    apply Union_intror. exact H0.
Qed.

(* FULL ⊆ /L U R <-> L ⊆ R *)
Lemma Full_subset_union_iff_subset:
  forall (T : Type) (L R : Ensemble T),
  Included T (Full_set T) (Union T (Complement T L) R) <-> Included T L R.
Proof.
  intros.
  split; intros.
  * unfold Included; intros.
    assert (Hin: In T (Union T (Complement T L) R) x). apply H. constructor.
    inversion Hin. contradiction. assumption.
  *  assert (Hfull: Union T (Complement T L) L = Full_set T).
     { apply Same_set_to_eq; apply Union_Compl_Fullset. }
     rewrite <- Hfull. unfold Included. intros.
     inversion H0.
     - left. assumption.
     - right. apply H. assumption.
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

Lemma Complement_Full_is_Empty {T : Type} :
Same_set T (Complement T (Full_set T)) (Empty_set T).
Proof.
unfold Same_set. unfold Complement. unfold Included. unfold In. eapply conj.
* intros. unfold not in H. 
  assert (Full_set T x). { apply Full_intro. }
  pose (H H0). contradiction.
* contradiction.
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
  (Extensionality_Ensembles _ _ _ (Compl_Union_Compl_Intes_Ensembles_alt _ _ _)).
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
  (Extensionality_Ensembles _ _ _ (Compl_Union_Compl_Intes_Ensembles_alt T _ _)).
rewrite (Extensionality_Ensembles _ _ _ (Setmin_Val A B)).
rewrite (Extensionality_Ensembles _ _ _ (Setmin_Val B A)).
eapply Same_set_refl.
Qed.

Lemma Included_Strict_Included {T : Type} : forall S1 S2 : Ensemble T,
  Included T S1 S2 <-> Same_set T S1 S2 \/ Strict_Included T S1 S2.
Proof.
  unfold Same_set. unfold Included, Strict_Included. unfold Complement. unfold In.
  split; intros.
  * destruct (Same_set_dec S1 S2).
    - left. assumption.
    - right. split.
      + unfold Included. intros. apply H. assumption.
      + unfold not in *. intros. apply H0. rewrite H1.
        apply Same_set_refl.
  * inversion H.
    - inversion H1. apply H2. assumption.
    - inversion H1. apply H2. assumption.
Qed.

Lemma Intersection_Comple_Strinct_Included {T : Type} : forall S1 S2 : Ensemble T,
  Same_set T (Intersection T S1 (Complement T S2)) (Empty_set T)
<->
  Same_set T S1 S2 \/ Strict_Included T S1 S2.
Proof.
  intros. rewrite <- Included_Strict_Included.
  unfold Same_set. unfold Included. unfold In.
  split; intros.
  * inversion H. destruct (In_dec S2 x).
    - assumption.
    - assert (Intersection T S1 (Complement T S2) x). 
      { eapply Intersection_intro.
        * assumption.
        * unfold In. unfold Complement. assumption.
      }
      pose (H1 x H4). contradiction.
  * split; intros.
    - inversion H0. subst. pose (H x H1). contradiction.
    - contradiction.
Qed.

Lemma Not_Intersection_Comple_Strinct_Included {T : Type} : forall S1 S2 : Ensemble T,
  ~ Same_set T (Intersection T S1 (Complement T S2)) (Empty_set T)
<->
  ~ (Same_set T S1 S2 \/ Strict_Included T S1 S2).
Proof.
  intros. rewrite <- Included_Strict_Included.
  unfold Same_set. unfold Included. unfold In.
  split; intros.
  * unfold not. intros. apply H.
    split; intros.
    - inversion H1. subst. pose (H0 x H2). contradiction.
    - contradiction.
  * unfold not. intros. apply H. inversion H0.
    intros. destruct (In_dec S2 x).
    - assumption.
    - assert (Intersection T S1 (Complement T S2) x).
      { eapply Intersection_intro; assumption. }
      pose (H1 x H5). contradiction.
Qed.

Lemma same_set_add_sub : forall T S E,
  Included T (Subtract T (Add T S E) E) S.
Proof.
  intros.
  unfold Subtract, Setminus, Add, Included, In.
  intros. inversion H.
  inversion H0.
  * assumption.
  * contradiction.
Qed.

Lemma in_add_set T S E:
In T (Add T S E) E.
Proof.
    unfold Add. apply Union_intror.
    apply In_singleton.
Qed.

(**
  If a set is not empty, then it contains elements
  Needed for semantics_of_definedness_2 in AML_definition
*)
Lemma Not_Empty_Contains_Elements : forall {T : Type}, forall S : Ensemble T,
  ~ Same_set T S (Empty_set T) ->
  exists x : T, S x.
Proof.
  unfold Same_set, Included, In.
  intros.
  apply not_and_or in H.
  inversion H.
  * pose (not_all_ex_not T (fun x => S x -> Empty_set T x) H0).
    inversion e.
    apply imply_to_and in H1. inversion H1.
    eexists. exact H2.
  * pose (not_all_ex_not T (fun x => Empty_set T x -> S x) H0).
    inversion e.
    apply imply_to_and in H1. inversion H1.
    contradiction.
Qed.

Lemma Contains_Elements_Not_Empty : forall {T : Type}, forall S : Ensemble T,
    (exists x : T, S x) -> ~ Same_set T S (Empty_set T).
Proof.
  unfold Same_set, Included, In.
  intros. inversion H. unfold not. intros.
  inversion H1.
  pose (H2 x H0). inversion e.
Qed.

Lemma Not_Empty_iff_Contains_Elements : forall {T : Type}, forall S : Ensemble T,
  ~ Same_set T S (Empty_set T) <->
  exists x : T, S x.
Proof.
  intros. split.
  - apply Not_Empty_Contains_Elements.
  - apply Contains_Elements_Not_Empty.
Qed.

Lemma Same_set_Full_set : forall {T : Type} (S : Ensemble T),
    Included T (Full_set T) S -> Same_set T (Full_set T) S.
Proof.
  intros. unfold Same_set.
  split. assumption.
  unfold Included. intros. constructor.
Qed.

Lemma Same_set_Empty_set : forall {T : Type} (S : Ensemble T),
    Included T S (Empty_set T) -> Same_set T S (Empty_set T).
Proof.
  intros H. unfold Same_set.
  split. assumption.
  unfold Included. intros. unfold In in H1. inversion H1.
Qed.

Lemma Included_transitive : forall {T : Type} (S1 S2 S3 : Ensemble T),
    Included T S1 S2 -> Included T S2 S3 -> Included T S1 S3.
Proof.
  intros. unfold Included in *. auto.
Qed.

Lemma Same_set_transitive : forall {T : Type} (S1 S2 S3 : Ensemble T),
    Same_set T S1 S2 -> Same_set T S2 S3 -> Same_set T S1 S3.
Proof.
  intros. unfold Same_set in *. firstorder using Included_transitive.
Qed.

Lemma Intersection_eq_Full :
  forall {T : Type} (S1 S2 : Ensemble T),
    Same_set T (Intersection T S1 S2) (Full_set T) -> (Same_set T S1 (Full_set T) /\ Same_set T S2 (Full_set T)).
Proof.
  intros.
  unfold Same_set in *.
  destruct H as [_ H]. unfold Included in *.
  split; split; intros; specialize (H x).
  + constructor.
  + apply H in H0. inversion H0. subst. assumption.
  + constructor.
  + apply H in H0. inversion H0. subst. assumption.
Qed.

Lemma eq_to_Same_set {T : Type} {A B : Ensemble T} :
  A = B -> Same_set T A B.
Proof.
  intros H. rewrite -> H. apply Same_set_refl.
Qed.

Lemma eq_iff_Same_set {T : Type} {A B : Ensemble T} :
  A = B <-> Same_set T A B.
Proof.
  split.
  - apply eq_to_Same_set.
  - apply Same_set_to_eq.
Qed.

Lemma Complement_Full_is_Empty_eq {T : Type} :
  (Complement T (Full_set T)) = (Empty_set T).
Proof.
  apply eq_iff_Same_set.
  apply Complement_Full_is_Empty.
Qed.

Lemma Complement_Empty_is_Full_eq {T : Type} :
  (Complement T (Empty_set T)) = (Full_set T).
Proof.
  apply eq_iff_Same_set.
  apply Complement_Empty_is_Full.
Qed.

Lemma Union_Empty_r_eq {T : Type} : forall A : Ensemble T,
(Union T (Empty_set T) A) = A.
Proof.
  intros A.
  apply eq_iff_Same_set.
  apply Union_Empty_r.
Qed.

Lemma Union_Empty_l_eq {T : Type} : forall A : Ensemble T,
(Union T A (Empty_set T)) = A.
Proof.
  intros A.
  apply eq_iff_Same_set.
  apply Union_Empty_l.
Qed.

Lemma Union_Full_l_eq {T : Type} : forall A : Ensemble T,
    Union T (Full_set T) A = Full_set T.
Proof.
  intros A.
  apply eq_iff_Same_set.
  apply Same_set_symmetric.
  apply Same_set_Full_set.
  unfold Included. unfold In.
  intros x H.
  left. unfold In. apply H.
Qed.

Lemma Union_Full_r_eq {T : Type} : forall A : Ensemble T,
    Union T A (Full_set T) = Full_set T.
Proof.
  intros A.
  apply eq_iff_Same_set.
  apply Same_set_symmetric.
  apply Same_set_Full_set.
  unfold Included. unfold In.
  intros x H.
  right. unfold In. apply H.
Qed.

Lemma Intersection_eq_Full_eq :
  forall {T : Type} (S1 S2 : Ensemble T),
    (Intersection T S1 S2) = (Full_set T) -> (S1 = (Full_set T) /\ S2 = (Full_set T)).
Proof.
  intros T S1 S2 H.
  apply eq_to_Same_set in H.
  apply Intersection_eq_Full in H.
  destruct H as [H1 H2].
  split; apply Same_set_to_eq; auto.
Qed.

Lemma Compl_Compl_Ensembles_eq : forall T :Type, forall A :Ensemble T,
  (Complement T (Complement T A)) = A.
Proof.
  intros T A.
  apply eq_iff_Same_set.
  apply Compl_Compl_Ensembles.
Qed.

Lemma Singleton_eq_iff_eq: forall T : Type, forall (x y : T),
      Singleton T x = Singleton T y <-> x = y.
Proof.
  intros T x y.
  split; intros H.
  - apply eq_iff_Same_set in H.
    unfold Same_set, Included, In in H.
    destruct H as [H1 H2].
    specialize (H1 x).
    specialize (H1 (In_singleton _ x)).
    inversion H1. reflexivity.
  - subst. reflexivity.
Qed.

Lemma Included_refl_eq : forall T : Type, forall (x y : Ensemble T),
      x = y -> Included T x y.
Proof.
  intros T x y H.
  unfold Included.
  intros x0.
  subst.
  auto.
Qed.

Definition Empty_Intersection T A B : Prop :=
  Intersection T A B = Empty_set T.
  
