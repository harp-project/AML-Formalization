(* Extensions to the stdpp library *)
From Coq Require Import ssreflect ssrfun ssrbool.
From Coq.Logic Require Import Classical_Prop Classical_Pred_Type.
From stdpp Require Import pmap gmap mapset fin_sets sets list propset.

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

Program Instance inj_unit_r {K} : @Inj (K * ()) K (@eq (K * ())) (@eq K) (@fst K ()).
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

(* The same lemma for stdpp's `reverse *)
Lemma last_reverse_head A (l : list A) (x : A) : last (x :: l) = hd_error (reverse l ++ [x]).
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
    rewrite reverse_cons.
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

Fixpoint skip_eq {A} {eqdec: EqDecision A} (l : list (A * A)) :=
  match l with
  | nil => nil
  | (x,y) :: xs =>
    match (decide (x=y)) with
    | left _ => @skip_eq _ eqdec xs
    | right _ => l
    end
  end.

Lemma skip_eq_head_not_eq {A} {eqdec: EqDecision A} (l : list (A * A)) :
  ∀ x y, hd_error (skip_eq l) = Some (x,y) -> x <> y.
Proof.
  induction l; intros x y; simpl; intros H.
  - inversion H.
  - destruct a as [a₁ a₂].
    destruct (decide (a₁ = a₂)) eqn:Heq.
    + apply IHl. apply H.
    + simpl in H. inversion H. subst. apply n.
Qed.

Definition tail_skip_eq {A} {eqdec: EqDecision A} (l : list (A * A)) :=
  reverse (skip_eq (reverse l)).

Lemma tail_skip_eq_last_not_eq {A} {eqdec: EqDecision A} (l : list (A * A)) :
  ∀ x y, last (tail_skip_eq l) = Some (x, y) -> x <> y.
Proof.
  intros x y H.
  unfold tail_skip_eq in H.
  rewrite last_reverse in H.
  apply skip_eq_head_not_eq in H.
  apply H.
Qed.

Fixpoint common_length {A} {eqdec: EqDecision A} (l₁ l₂ : list A) :=
  match l₁,l₂ with
  | nil,nil => 0
  | nil,_ => 0
  | _,nil => 0
  | (x::xs),(y::ys) =>
    match (decide (x=y)) with
    | left _ => S (@common_length _ eqdec xs ys)
    | right _ => 0
    end
  end.

Lemma common_length_l_nil {A} {eqdec: EqDecision A} (l₁ : list A) :
  common_length l₁ nil = 0.
Proof.
  induction l₁; reflexivity.
Qed.

Lemma common_length_sym {A} {eqdec: EqDecision A} (l₁ l₂ : list A) :
  common_length l₁ l₂ = common_length l₂ l₁.
Proof.
  induction l₁; destruct l₂; simpl; try reflexivity.
  - rename IHl₁ into IH. simpl in IH.
    destruct (decide (a=a0)),(decide (a0=a)).
    + apply f_equal. destruct l₁.
      * simpl. rewrite common_length_l_nil. destruct l₂; reflexivity.
      * subst. destruct l₂.
        {rewrite common_length_l_nil. reflexivity. }
        simpl.
        destruct (decide (a1 = a)),(decide (a = a1)).
        4: reflexivity.
        3: { subst. contradiction. }
        2: { subst. contradiction.  }
        apply f_equal.
Abort.

Lemma common_length_rev {A} {eqdec: EqDecision A} (x y : A) (xs ys : list A) :
  common_length (reverse (x::xs)) (y::ys) =
  match (decide ((last (x::xs)) = Some y)) with
  | left _ => S (common_length (reverse (tail (reverse (x::xs)))) ys)
  | right _ => 0
  end.
Proof.
  induction xs; destruct ys.
  - simpl.
    destruct (decide (x=y)), (decide (Some x = Some y)); simpl; try reflexivity.
    subst. contradiction.
    inversion e. subst. contradiction.
Abort.

Lemma last_app_singleton {A} (m : A) (l : list A) :
  last (l ++ [m]) = Some m.
Proof.
  induction l.
  - reflexivity.
  - simpl.
    destruct (l ++ [m]).
    { simpl in IHl. inversion IHl. }
    apply IHl.
Qed.
                                
Lemma rev_reverse {A} (l : list A) :
  rev l = reverse l.
Proof.
  unfold reverse.
  rewrite -rev_alt.
  reflexivity.
Qed.

Lemma forall_zip_flip {A B : Type} (f : A -> B -> Prop) (xs : list A) (ys: list B) :
  Forall (curry f) (zip xs ys) <-> Forall (curry (flip f)) (zip ys xs).
Proof.
  split.
  - intros H.
    move: ys H.
    induction xs as [|x xs]; intros ys H.
    + rewrite zip_with_nil_r.
      apply Forall_nil.
      exact I.
    + destruct ys as [|y ys].
      { simpl. apply Forall_nil. exact I. }
      simpl in H. simpl.
      inversion H. subst. simpl in H2.
      apply Forall_cons. split.
      { simpl. apply H2. }
      apply IHxs. apply H3.
  - intros H.
    move: ys H.
    induction xs as [|x xs]; intros ys H.
    + simpl. apply Forall_nil. exact I.
    + destruct ys as [|y ys].
      { simpl. apply Forall_nil. exact I. }
      simpl in H. simpl.
      inversion H. subst. simpl in H2.
      apply Forall_cons. split.
      { simpl. apply H2. }
      apply IHxs. apply H3.
Qed.

Lemma tail_app_nonempty {A : Type} (x : A) (xs ys : list A) :
  tail ((x::xs) ++ ys) = (tail (x::xs)) ++ ys.
Proof.
  remember (length xs) as len.
  assert (Hlen: length xs <= len).
  { lia. }
  clear Heqlen.
  move: x xs Hlen.
  induction len; intros x xs Hlen.
  - destruct xs.
    2: { simpl in Hlen. inversion Hlen. }
    reflexivity.
  - reflexivity.
Qed.

Lemma tail_app_nonempty' {A : Type} (xs ys : list A) :
  length xs >= 1 ->
  tail (xs ++ ys) = (tail xs) ++ ys.
Proof.
  intros H.
  destruct xs as [|z zs].
  { simpl in H. lia. }
  rewrite tail_app_nonempty.
  reflexivity.
Qed.

Lemma length_tail {A : Type} (l : list A) :
  length (tail l) = length l - 1.
Proof.
  destruct l.
  - reflexivity.
  - simpl.
    rewrite PeanoNat.Nat.sub_0_r.
    reflexivity.
Qed.

Lemma reverse_zip_tail_r {A : Type} (m : A) (l : list A) :
  reverse (zip (m :: l) (tail (m :: l)))
  = zip (tail (reverse (m :: l))) (reverse (m :: l)).
Proof.
  remember (length l) as len.
  assert (Hlen: length l <= len).
  { lia. }
  clear Heqlen.
  move: m l Hlen.
  induction len; intros m l Hlen.
  - destruct l.
    2: { simpl in Hlen. inversion Hlen. }
    reflexivity.
  - destruct l as [|x l].
    { reflexivity. }
    simpl.
    (*rewrite !reverse_cons.*)
    destruct l as [|x' l'] eqn:Heq.
    { reflexivity. }
    simpl in IHlen.
    rewrite 3!reverse_cons.

    simpl in Hlen.
    (*assert (S (length l') <= len).
    { lia. }*)
    assert (length (x'::l') <= len).
    { simpl. lia. }

    (* extract `m` out of `tail` *)
    rewrite -> tail_app_nonempty'.
    2: { rewrite reverse_length. simpl. lia. }

    (* extract `x` out of `tail` *)
    rewrite 1!reverse_cons.
    rewrite -> tail_app_nonempty'.
    2: { rewrite reverse_length. simpl. lia. }

    rewrite -!app_assoc.
    rewrite [[x]++[m]]/=.
    rewrite zip_with_app_l.
    remember (length (tail (reverse (x' :: l')))) as len'.

    assert (len' = length l').
    { rewrite Heqlen'.
      rewrite length_tail.
      rewrite reverse_length.
      simpl.
      rewrite PeanoNat.Nat.sub_0_r.
      reflexivity.
    }
    assert (len' = length (reverse l')).
    { rewrite reverse_length. apply H0. }
    rewrite reverse_cons.
    rewrite -!app_assoc.
    rewrite H1.
    rewrite take_app.
    rewrite drop_app.

    rewrite [zip [x;m] _]/=.

    simpl.
    rewrite IHlen.
    { simpl in H. lia. }
    simpl.
    rewrite reverse_cons.

    assert (reverse l' = take (length (tail (reverse l' ++ [x']))) (reverse l' ++ [x'])).
    { rewrite length_tail. rewrite app_length. simpl.
      assert (length (reverse l') + 1 - 1 = length (reverse l')).
      { lia. }
      rewrite H2.
      rewrite take_app.
      reflexivity.
    }
    rewrite -> H2 at 4.

    rewrite zip_with_take_r.
    { rewrite length_tail. lia. }
    reflexivity.
Qed.

Lemma Forall_zip_flip_reverse {A : Type} (f : A -> A -> Prop) (m : A) (l : list A) :
  Forall (curry f) (zip (m::l) (tail (m::l)))
  <->
  Forall (curry (flip f)) (zip (reverse (m::l)) (tail (reverse (m::l)))).
Proof.
  rewrite -forall_zip_flip.
  rewrite -Forall_reverse.
  rewrite reverse_zip_tail_r.
  reflexivity.
Qed.

Lemma Forall_drop {A : Type} (P : A -> Prop) (n : nat) (l : list A) :
  Forall P l -> Forall P (drop n l).
Proof.
  remember (length l) as len.
  assert (Hlen: length l <= len).
  { lia. }
  clear Heqlen.
  move: n l Hlen.
  induction len; intros n l Hlen H.
  - destruct l as [|x l].
    { rewrite drop_nil. apply H. }
    simpl in Hlen. lia.
  - destruct l as [|x l], n.
    { simpl. apply Forall_nil. exact I. }
    { rewrite drop_nil. apply Forall_nil. exact I. }
    { simpl. apply H. }
    simpl. apply IHlen. simpl in Hlen. lia.
    inversion H. assumption.
Qed.

Lemma last_drop {A : Type} (l : list A) (n : nat) (x : A) :
  last l = Some x ->
  n < length l ->
  last (drop n l) = Some x.
Proof.
  remember (length l) as len.
  assert (Hlen: length l <= len).
  { lia. }

  move: l Hlen n x Heqlen.
  induction len; intros l Hlen n x Heqlen Hlast Hless.
  - inversion Hless.
  - destruct l as [|y l].
    { simpl in Hlast. inversion Hlast. }
    destruct n.
    { simpl. simpl in Hlast. apply Hlast. }
    rewrite skipn_cons.
    assert (n < len).
    { lia. }
    clear Hless.
    rename H into Hless.

    simpl in Hlen.
    assert (length l > 0).
    { simpl in Heqlen. lia. }

    destruct l.
    { simpl in H. lia. }

    simpl in Heqlen. inversion Heqlen. clear Heqlen.
    assert (length (a :: l) ≤ len).
    { simpl. lia. }
    apply IHlen.
    { simpl in Hlen. lia. }
    { simpl in Hlast. simpl. apply H1. }
    { simpl in Hlast. simpl. apply Hlast. }
    lia.
Qed.

Lemma tail_drop {A : Type} (l : list A) (n : nat) :
  tail (drop n l) = drop (S n) l.
Proof.
  move: n.
  induction l; intros n.
  - simpl. rewrite drop_nil. reflexivity.
  - simpl.
    destruct n.
    { by rewrite drop_0. }
      by rewrite -IHl.
Qed.

Lemma drop_tail {A : Type} (l : list A) (n : nat) :
  drop n (tail l) = drop (S n) l.
Proof.
  move: n.
  induction l; intros n.
  - simpl. rewrite drop_nil. reflexivity.
  - simpl.
    destruct n.
    { by rewrite drop_0. }
      by rewrite -IHl.
Qed.

Lemma tail_drop_comm {A : Type} (l : list A) (n : nat) :
  tail (drop n l) = drop n (tail l).
Proof.
    by rewrite tail_drop drop_tail.
Qed.

Lemma hd_drop_lookup {A : Type} (l : list A) (n : nat) (m : A) :
  l !! n = Some m ->
  hd_error (drop n l) = Some m.
Proof.
  move: l.
  induction n; intros l.
  - rewrite drop_0. by rewrite hd_error_lookup.
  - destruct l as [|x l].
    { simpl. intros H. exact H. }
    simpl.
    intros H.
    by rewrite IHn.
Qed.

Lemma list_ex_elem {A : Type} (l : list A) (n : nat) :
  n < length l -> exists x, l!!n = Some x.
Proof.
  remember (length l) as len.
  rewrite Heqlen.
  assert (Hlen: length l <= len).
  { lia. }
  clear Heqlen.

  move: l n Hlen.
  induction len; intros l n Hlen.
  - destruct l; intros H; lia.
  - destruct l; simpl.
    + simpl in IHlen.
      intros H. apply IHlen. lia. apply H.
    + intros H. destruct n.
      * simpl. exists a. reflexivity.
      * simpl.
        specialize (IHlen l).
        simpl in Hlen.
        assert (Hlen': length l <= len).
        { lia. }
        apply IHlen. lia. lia.
Qed.

Lemma list_last_length {A : Type} (l : list A):
  last l = l !! (length l - 1).
Proof.
  remember (length l) as len.
  rewrite Heqlen.
  assert (Hlen : length l <= len).
  { lia. }
  clear Heqlen.

  move: l Hlen.
  induction len; simpl; intros l Hlen.
  - assert (length l = 0).
    { lia. }
    apply nil_length_inv in H.
    rewrite H. reflexivity.
  - destruct l.
    { reflexivity. }
    destruct l.
    { reflexivity. }
    simpl.
    specialize (IHlen (a0::l)).
    assert (Hneq' : a0 :: l <> []).
    { discriminate. }
    simpl in IHlen.
    rewrite Nat.sub_0_r in IHlen.
    apply IHlen.
    simpl in Hlen. lia.
Qed.

Lemma equal_up_to_common_length {A : Type} {eqdec: EqDecision A} (l₁ l₂ : list A) :
  forall (n:nat),
    n < common_length l₁ l₂ ->
    l₁ !! n = l₂ !! n.
Proof.
  intros n.
  move: l₁ l₂.
  induction n; intros l₁ l₂ H.
  - destruct l₁,l₂; simpl.
    + reflexivity.
    + simpl in H. lia.
    + simpl in H. lia.
    + simpl in H. destruct (decide (a = a0)).
      * subst. reflexivity.
      * lia.
  - destruct l₁,l₂; simpl.
    + reflexivity.
    + simpl in H. lia.
    + simpl in H. lia.
    + simpl in H. destruct (decide (a = a0)).
      * subst. apply IHn. lia.
      * lia.
Qed.

Lemma last_tail {A : Type} (l : list A) (lst m : A) :
  last l = Some lst ->
  head (tail l) = Some m ->
  last (tail l) = Some lst.
Proof.
  remember (length l) as len.
  assert (Hlen: length l <= len).
  { lia. }
  clear Heqlen.

  move: l Hlen m.
  induction len; intros l Hlen m Hlast Hhd.
  - destruct l.
    + auto.
    + simpl in Hlen. lia.
  - destruct l.
    { simpl. auto. }
    simpl.
    simpl in Hhd.
    simpl in Hlast.
    simpl in Hlen.
    destruct l.
    { simpl in Hhd. inversion Hhd. }
    simpl in Hlen.
    assert (Hlen' : S (length l) <= len).
    { lia. }

    destruct l.
    { apply Hlast. }

    specialize (IHlen (a0::a1::l)).
    simpl in IHlen. simpl.
    apply IHlen with (m := a1).
    { simpl in Hlen. lia. }
    simpl in Hlast. apply Hlast.
    reflexivity.
Qed.

Lemma tail_zip_with {A B C : Type} (f : A -> B -> C) (l₁ : list A) (l₂ : list B) :
  tail (zip_with f l₁ l₂) = zip_with f (tail l₁) (tail l₂).
Proof.
  destruct l₁.
  { reflexivity. }
  destruct l₂.
  { simpl. rewrite zip_with_nil_r. reflexivity. }
  reflexivity.
Qed.

Lemma tail_zip {A : Type} (l₁ l₂ : list A) :
  tail (zip l₁ l₂) = zip (tail l₁) (tail l₂).
Proof.
  apply tail_zip_with.
Qed.

Lemma common_length_impl_eq {A : Type} {eqdec: EqDecision A} (l₁ l₂ : list A) :
  length l₁ = length l₂ ->
  common_length l₁ l₂ = length l₂ ->
  l₁ = l₂.
Proof.
  intros Hlength Hcommlength.
  eapply list_eq_same_length.
  2: apply Hlength.
  { reflexivity. }
  intros i x y Hi Hl₁ Hl₂.
  assert (H: Some x = Some y).
  { rewrite -Hl₁ -Hl₂.
    apply equal_up_to_common_length.
    lia.
  }
  inversion H.
  reflexivity.
Qed.


Lemma not_elem_of_larger_impl_not_elem_of {A C : Type} {H : ElemOf A C} (x : A) (S B : C) :
  S ⊆ B ->
  x ∉ B ->
  x ∉ S.
Proof.
  intros Hsub Hnotin.
  pose proof (Hsub' := (iffLR (elem_of_subseteq _ B) Hsub)).
  auto.
Qed.

Tactic Notation "solve_set_inclusion" int_or_var(depth) :=
  apply elem_of_subseteq;
  let x := fresh "x" in
  let H := fresh "Hxin" in
  (* TODO: maybe we need something like: *)
  (*rewrite -!union_assoc_L.*)
  (* We may also want to remove duplicates, at least those that are neighbors *)
  intros x H;
  repeat (
      match H with
      | ?L /\ ?R => fail "Not implemented: destruct H"
      | _ => eauto depth using @sets.elem_of_union_l, @sets.elem_of_union_r with typeclass_instances
      end
    ).

Lemma map_take {A B : Type} (f : A -> B) (l : list A) (n : nat) :
  map f (take n l) = take n (map f l).
Proof.
  move: n.
  induction l; intros n.
  - simpl. rewrite take_nil. simpl. rewrite take_nil. reflexivity.
  - simpl. destruct n; simpl.
    + reflexivity.
    + rewrite IHl. reflexivity.
Qed.

Lemma map_drop {A B : Type} (f : A -> B) (l : list A) (n : nat) :
  map f (drop n l) = drop n (map f l).
Proof.
  move: n.
  induction l; intros n.
  - simpl. rewrite drop_nil. simpl. rewrite drop_nil. reflexivity.
  - simpl. destruct n; simpl.
    + reflexivity.
    + rewrite IHl. reflexivity.
Qed.

Lemma foldr_andb_true_take n l:
  foldr andb true l ->
  foldr andb true (take n l).
Proof.
  intros H.
  move: n.
  induction l; intros n; simpl.
  - rewrite take_nil. exact H.
  - simpl in H. apply andb_prop in H. destruct H as [Ha H].
    subst a. destruct n.
    + reflexivity.
    + simpl. apply IHl. apply H.
Qed.  

Lemma foldr_andb_true_drop n l:
  foldr andb true l ->
  foldr andb true (drop n l).
Proof.
  intros H.
  move: n.
  induction l; intros n; simpl.
  - rewrite drop_nil. exact H.
  - simpl in H. apply andb_prop in H. destruct H as [Ha H].
    subst a. destruct n.
    + simpl. exact H.
    + simpl. apply IHl. apply H.
Qed.

Definition propset_fa_union {T C : Type} (f : C -> propset T) : propset T
  := PropSet (fun (x : T) => exists (c : C), x ∈ f c).


Lemma propset_fa_union_same {T C : Type} {LE : LeibnizEquiv (propset T)} (f f' : C -> propset T):
      (forall c, (f c) = (f' c)) ->
      (propset_fa_union f) = (propset_fa_union f').
Proof.
  intros H.
  unfold propset_fa_union.
  rewrite -> set_eq_subseteq.
  repeat rewrite -> elem_of_subseteq.
  split; intros x H'; rewrite -> elem_of_PropSet; rewrite -> elem_of_PropSet in H';
    destruct H' as [c Hc]; exists c.
  - rewrite <- H. exact Hc.
  - rewrite -> H. exact Hc.
Qed.

Lemma propset_fa_union_included : forall T C : Type, forall f f' : C -> propset T,
      (forall c, (f c) ⊆ (f' c)) ->
      (propset_fa_union f) ⊆ (propset_fa_union f').
Proof.
  intros.
  rewrite -> elem_of_subseteq. setoid_rewrite -> elem_of_subseteq in H.
  setoid_rewrite -> elem_of_PropSet. (*setoid_rewrite -> elem_of_PropSet in H.*)
  intros x H0.
  destruct H0 as [c Hc].
  apply H in Hc.
  eauto.
Qed.


Lemma Not_Empty_Contains_Elements {T : Type} {LE : LeibnizEquiv (propset T)} (S : propset T):
  S <> ∅ -> exists x : T, x ∈ S.
Proof.
  intros H.
  unfold not in H.

  rewrite -> set_eq_subseteq in H.
  apply not_and_or in H.
  inversion H.
  * pose (e := not_all_ex_not T (fun x => x ∈ S -> x ∈ ∅) H0).
    inversion e.
    apply imply_to_and in H1. inversion H1.
    eexists. exact H2.
  * pose (e := not_all_ex_not T (fun x => x ∈ ∅ -> x ∈ S) H0).
    inversion e.
    apply imply_to_and in H1. inversion H1.
    contradiction.
Qed.

Lemma Contains_Elements_Not_Empty {T : Type} (S : propset T):
    (exists x : T, x ∈ S) -> S <> ∅.
Proof.
  set_solver by fail.
Qed.

Lemma Not_Empty_iff_Contains_Elements {T : Type} {LE : LeibnizEquiv (propset T)} (S : propset T):
  S <> ∅ <->
  exists x : T, x ∈ S.
Proof.
  intros. split.
  - apply Not_Empty_Contains_Elements.
  - apply Contains_Elements_Not_Empty.
Qed.

Lemma Compl_Compl_propset {T : Type} {LE : LeibnizEquiv (propset T)} (A : propset T):
  (⊤ ∖ (⊤ ∖ A)) = A.
Proof.
  apply set_eq_subseteq. rewrite !elem_of_subseteq.
  split; intros x H.
  * set_unfold.
    assert (H0: ¬ (x ∉ A)) by firstorder.
    now apply NNPP in H0.
  * set_unfold. firstorder.
Qed.


Lemma Compl_Union_Compl_Inters_propset_alt {T : Type} {LE : LeibnizEquiv (propset T)} (L R : propset T):
  (⊤ ∖ ((⊤ ∖ L) ∪ (⊤ ∖ R))) = (L ∩ R).
Proof.
  set_unfold.
  intros x.
  split.
  - intros [_ H].
    assert (H1: ¬ (x ∉ L)) by firstorder.
    assert (H2: ¬ (x ∉ R)) by firstorder.
    apply NNPP in H1. apply NNPP in H2. split; assumption.
  - intros H.
    split;[exact I|].
    intros HContra.
    destruct HContra; firstorder.
Qed.

Lemma complement_full_iff_empty {T : Type} {LE : LeibnizEquiv (propset T)} (A : propset T):
  (⊤ ∖ A = ⊤) <-> (A = ∅).
Proof.
  set_solver by fail.
Qed.

Lemma complement_empty_iff_full {T : Type} {LE : LeibnizEquiv (propset T)} (A : propset T):
  (⊤ ∖ A = ∅) <-> (A = ⊤).
Proof.
  split; intros H.
  2:{ set_solver. }
  set_unfold. intros x; split; intros H1; try exact I.
  assert (¬ (x ∉ A)) by firstorder.
  apply NNPP in H0. exact H0.
Qed.

Lemma intersection_full_iff_both_full {T : Type} {LE : LeibnizEquiv (propset T)} (L R : propset T):
  (L ∩ R = ⊤) <-> (L = ⊤ /\ R = ⊤).
Proof.
  split; intros H; set_unfold; firstorder.
Qed.


Lemma union_with_complement {T : Type} {LE : LeibnizEquiv (propset T)} (X : propset T):
  (⊤ ∖ X) ∪ X = ⊤.
Proof.
  set_unfold. intros x. split; intros H. exact I.
  destruct (classic (x ∈ X)). right. assumption. left. auto.
Qed.
