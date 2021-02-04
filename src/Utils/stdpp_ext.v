(* Extensions to the stdpp library *)
From Coq Require Import ssreflect.
From stdpp Require Import pmap gmap mapset fin_sets sets.

Lemma not_elem_of_singleton_1 `{SemiSet A C} x y : ~ elem_of x ((singleton y) : C) -> ~ x = y.
Proof.
  unfold not. intros. rewrite <- elem_of_singleton in H5. auto.
Qed.

Lemma not_elem_of_singleton_2 `{SemiSet A C} x y : ~ x = y -> ~ elem_of x ((singleton y) : C).
Proof.
  unfold not. intros. rewrite -> elem_of_singleton in H5. auto.
Qed.

Lemma pmap_to_list_lookup {A} (M : Pmap A) (i : positive) (x : A)
  : (i,x) ∈ (map_to_list M) <-> lookup i M = Some x.
Proof.
  intros. unfold map_to_list. unfold Pto_list. unfold lookup. unfold Plookup.
  destruct M eqn:HM. simpl.
  split; intros.
  + apply Pelem_of_to_list in H. simpl in H.
    destruct H.
    * destruct H as [i' [Hi' Hsome]]. subst. apply Hsome.
    * inversion H.
  + apply Pelem_of_to_list.
    left. simpl. exists i. firstorder.
Qed.

Lemma gmap_to_list_lookup `{Countable K} {A} (M : gmap K A) (k : K) (a : A): ((k,a) ∈ (gmap_to_list M)) <-> (M !! k = Some a).
Proof.
  unfold elem_of.
  unfold lookup.
  destruct M as [PM PMwf] eqn: HM. simpl.
  unfold gmap_wf in PMwf.
  split; intros H'.
  + apply pmap_to_list_lookup.
    apply elem_of_list_omap in H'.
    destruct H' as [[k' a'] [HxinPM H']].
    apply fmap_Some_1 in H'.
    destruct H' as [k'' [H1 H2]]. inversion H2. subst. clear H2.
    assert (Hk': k' = encode k'').
    { apply bool_decide_unpack in PMwf.
      unfold map_Forall in PMwf.
      apply pmap_to_list_lookup in HxinPM.
      specialize (PMwf k' a' HxinPM).
      apply (inj Some). rewrite <- PMwf.
      apply fmap_Some_2. apply H1. }
    subst. apply HxinPM.
    
  + apply pmap_to_list_lookup in H'.
    apply elem_of_list_omap.
    exists (encode k, a). firstorder.
    rewrite -> decode_encode. simpl. reflexivity.
Qed.

Program Instance inj_unit_r : @Inj (K * ()) K (@eq (K * ())) (@eq K) (@fst K ()).
Next Obligation.
  intros. destruct x,y. simpl in H. subst. destruct u. destruct u0. reflexivity.
Defined.

Lemma gset_to_list_elem_of `{Countable K} (S : gset K) (k : K) : k ∈ (mapset_elements S) <-> k ∈ S.
Proof.
  unfold mapset_elements.
  destruct S as [M].
  unfold elem_of at 2.
  unfold gset_elem_of. unfold mapset_elem_of. simpl.
  rewrite <- gmap_to_list_lookup.
  unfold map_to_list.
  assert (Hk : k = fst (k, ())).
  { reflexivity. }
  rewrite -> Hk at 1.
  split; intros H'.
  + apply elem_of_list_fmap_2_inj in H'. apply H'.
    apply inj_unit_r.
  + apply elem_of_list_fmap_1. assumption.
Qed.

Lemma mapset_elements_to_set `{Countable K} (X : gset K) : list_to_set (mapset_elements X) = X.
Proof.
  apply (iffRL (@mapset_eq K (gmap K) _ _ _ _ _ _ _ _ gmap_finmap _ _)).
  intros x. 
  pose proof (H' := @elem_of_list_to_set K (gset K) _ _ _ _ _ x (mapset_elements X)).
  rewrite -> H'. apply gset_to_list_elem_of.
Qed.


Lemma rev_tail_rev_app A (l : list A) (a : A) :
  l <> [] -> rev (tail (l ++ [a])) = a :: rev (tail l).
Proof.
  remember (length l) as len.
  assert (length l <= len).
  { lia. }
  clear Heqlen.
  move: l H.
  induction len; intros l; destruct l.
  - simpl. intros _ H. contradiction.
  - simpl. intros H. lia.
  - intros _ H. contradiction.
  - simpl. intros _ _.
    destruct l.
    + reflexivity.
    + simpl. rewrite rev_app_distr.
      reflexivity.
Qed.


(* [1,2,3,4,5] -> [5,4,3,2,1] -> [4,3,2,1] -> [1,2,3,4] *)
Lemma rev_tail_rev_app_last A (l : list A) (xlast : A):
  last l = Some xlast ->
  rev (tail (rev l)) ++ [xlast] = l.
Proof.        
  move: xlast.
  induction l.
  - intros xlast. simpl. intros H. inversion H.
  - intros xlast. intros H. simpl.
    destruct l as [|b l'].
    + simpl. simpl in H. inversion H. reflexivity.
    + simpl. simpl in IHl. simpl in H.
      assert (Ha: [a] = rev [a]).
      { reflexivity. }
      assert (Hb: [b] = rev [b]).
      { reflexivity. }
      assert (Hxlast: [xlast] = rev [xlast]).
      { reflexivity. }
      specialize (IHl xlast H).
      rewrite -IHl.
      rewrite Hxlast.
      rewrite rev_tail_rev_app.
      { intros Contra.
        assert (Heqlen: length (rev l' ++ [b]) = @length A []).
        { rewrite Contra. reflexivity. }
        rewrite app_length in Heqlen. simpl in Heqlen. lia.
      }
      simpl. reflexivity.
Qed.


Lemma length_tail_zero A l: @length A (tail l) = 0 <-> (@length A l = 0 \/ @length A l = 1).
Proof.
  destruct l.
  - simpl. split. intros H. left. apply H.
    intros [H|H]. apply H. inversion H.
  - simpl. split.
    + intros H. rewrite H. right. reflexivity.
    + intros [H|H]. inversion H. lia.
Qed.

Lemma hd_error_app A (a b : A) (l : list A) :
  hd_error ((l ++ [a]) ++ [b]) = hd_error (l ++ [a]).
Proof.
  induction l.
  - reflexivity.
  - reflexivity.
Qed.


Lemma last_rev_head A (l : list A) (x : A) : last (x :: l) = hd_error (rev l ++ [x]).
Proof.
  remember (length l) as len.
  assert (Hlen: length l <= len).
  { lia. }
  clear Heqlen.
  move: l Hlen x.
  induction len; intros l Hlen x; destruct l eqn:Hl.
  - reflexivity.
  - simpl in Hlen. lia.
  - reflexivity.
  - simpl.
    rewrite hd_error_app.
    rewrite - (IHlen l0).
    { simpl in Hlen. lia. }
    simpl. reflexivity.
Qed.

Lemma hd_error_lookup A (l : list A) :
  l !! 0 = hd_error l.
Proof.
  destruct l; reflexivity.
Qed.

Lemma list_len_slice A (l1 l2 : list A) (a b : A) :
  a :: l1 = l2 ++ [b] -> length l1 = length l2.
Proof.
  intros H1.
  assert (H2: length (a :: l1) = length (l2 ++ [b])).
  { rewrite H1. reflexivity. }
  simpl in H2.
  rewrite app_length in H2. simpl in H2. lia.
Qed.
