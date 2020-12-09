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
