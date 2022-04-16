From stdpp Require Import base sets propset.
From MatchingLogic.Utils Require Import stdpp_ext.


Class OrderedSet A : Type :=
  { leq : relation A;
    leq_order : order A leq;
  }.

Program Definition OrderedSet_dual {A : Type} (OS : OrderedSet A) : OrderedSet A :=
  {| leq := fun x y => @leq A OS y x;
     leq_order := {| ord_refl := _; ord_trans := _; ord_antisym := _; |};
  |}.
Next Obligation. unfold reflexive. intros.
                 apply (ord_refl A (@leq A OS) (@leq_order A OS)).
                 Defined.
Next Obligation. unfold transitive. intros.
                 remember (ord_trans A leq leq_order).
                 unfold transitive in t.
                 apply t with (y := y).
                 assumption. assumption.
Defined.
Next Obligation. unfold antisymmetric. intros.
                 remember (ord_antisym A leq leq_order).
                 unfold antisymmetric in a.
                 apply a. assumption. assumption.
Defined.

                 
Definition upperBound {A : Type} {OS : OrderedSet A} (X: propset A) (ub: A) : Prop :=
  forall (x: A), x ∈ X -> leq x ub.

Definition leastUpperBound {A : Type} {OS : OrderedSet A} (X: propset A) (lub: A) : Prop :=
  upperBound X lub /\
  forall (ub : A), upperBound X ub -> leq lub ub.

Definition lowerBound {A : Type} {OS : OrderedSet A} (X: propset A) (lb: A) : Prop :=
  forall (x : A), x ∈ X -> leq lb x.

Definition greatestLowerBound {A : Type} {OS : OrderedSet A} (X : propset A) (glb : A) : Prop :=
  lowerBound X glb /\
  forall (lb : A), lowerBound X lb -> leq lb glb.

Definition upperBoundsOf {A : Type} {OS : OrderedSet A} (X : propset A) : propset A :=
  PropSet (fun x => upperBound X x).

Definition lowerBoundsOf {A : Type} {OS : OrderedSet A} (X : propset A) : propset A :=
  PropSet (fun x => lowerBound X x).

Definition isMeet {A : Type} {OS : OrderedSet A} (meet : propset A -> A) : Prop :=
  forall (X : propset A), greatestLowerBound X (meet X).

Definition isJoin {A : Type} {OS : OrderedSet A} (join : propset A -> A) : Prop :=
  forall (X : propset A), leastUpperBound X (join X).

Definition joinFromMeet {A : Type} {OS : OrderedSet A} (meet : propset A -> A)
  : propset A -> A :=
  fun X => meet (upperBoundsOf X).

Lemma joinFromMeet_lub: forall (A : Type) (OS : OrderedSet A)
                                (meet : propset A -> A),
     isMeet meet -> isJoin (joinFromMeet meet).
Proof.
  intros. unfold isJoin. intros. unfold leastUpperBound.
   split.
   - (* upper bound *)
     unfold upperBound. intros.
     unfold joinFromMeet.
     assert (xlower: lowerBound (upperBoundsOf X) x).
     { unfold lowerBound. intros. unfold upperBoundsOf in H1. unfold In in H1.
       unfold In in H0. unfold upperBound in H1. rewrite -> elem_of_PropSet in H1.
       apply H1. apply H0.
     }
     unfold isMeet in H.
     assert (meetX_glb: greatestLowerBound (upperBoundsOf X) (meet (upperBoundsOf X))).
     apply H. unfold greatestLowerBound in meetX_glb. destruct meetX_glb. apply H2. apply xlower.
   - (* least *)
     intros. unfold joinFromMeet. unfold isMeet in H.
     specialize (H (upperBoundsOf X)).
     assert (ub_in : ub ∈ (upperBoundsOf X)).
     { apply H0. }
     destruct H. unfold lowerBound in H. apply H. apply ub_in.
Qed.

Definition meetFromJoin {A : Type} {OS : OrderedSet A} (join : propset A -> A)
   : propset A -> A :=
  fun X => join (lowerBoundsOf X).

(* Exactly a dual of joinFromMeet_lub. But there should be some way to avoid duplication. *)
Lemma meetFromJoin_glb: forall (A : Type) (OS : OrderedSet A)
                                (join : propset A -> A),
     isJoin join -> isMeet (meetFromJoin join).
Proof.
  intros. unfold isMeet. intros. unfold greatestLowerBound.
   split.
   - (* lower bound *)
     unfold lowerBound. intros.
     unfold meetFromJoin.
     assert (xupper: upperBound (lowerBoundsOf X) x).
     { unfold upperBound. intros. unfold lowerBoundsOf in H1.
       unfold In in H0. unfold lowerBound in H1. rewrite -> elem_of_PropSet in H1.
       apply H1. apply H0.
     }
     unfold isJoin in H.
     assert (meetX_lub: leastUpperBound (lowerBoundsOf X) (join (lowerBoundsOf X))).
     apply H. unfold leastUpperBound in meetX_lub. destruct meetX_lub. apply H2. apply xupper.
   - (* greatest *)
     intros. unfold meetFromJoin. unfold isJoin in H.
     specialize (H (lowerBoundsOf X)).
     assert (lb_in : lb ∈ (lowerBoundsOf X)).
     { apply H0. }
     destruct H. unfold upperBound in H. apply H. apply lb_in.
Qed.


Class CompleteLattice A `{OrderedSet A} :=
  {
    meet : propset A -> A;
    join : propset A -> A;
    meet_isMeet : isMeet meet;
    join_isJoin : isJoin join;
  }.

Program Definition CompleteLattice_dual {A : Type} {OS : OrderedSet A} (CL : CompleteLattice A)
  : @CompleteLattice A (@OrderedSet_dual A OS) :=
  {| meet := join;
     join := meet;
     meet_isMeet := _;
     join_isJoin := _
  |}.
Next Obligation. unfold isMeet.
                 unfold greatestLowerBound.
                 unfold lowerBound.
                 intros. simpl.
                 apply join_isJoin.
Defined.
Next Obligation. unfold isJoin.
                 unfold leastUpperBound.
                 unfold upperBound.
                 intros. simpl.
                 apply meet_isMeet.
Defined.


Definition MonotonicFunction {A : Type} {OS : OrderedSet A}
           (f : A -> A) :=
  forall (x y : A), leq x y -> leq (f x) (f y).

Definition AntiMonotonicFunction {A : Type} {OS : OrderedSet A}
           (f : A -> A) :=
  forall (x y : A), leq x y -> leq (f y) (f x).


Lemma MonotonicFunction_dual {A : Type} :
  forall (OS : OrderedSet A) (f : A -> A),
    @MonotonicFunction A OS f -> @MonotonicFunction A (OrderedSet_dual OS) f.
Proof.
  unfold MonotonicFunction.
  simpl.
  auto.
Qed.

Definition PrefixpointsOf {A : Type} {OS : OrderedSet A} (f : A -> A) : propset A :=
  PropSet (fun x => leq (f x) x).

Definition LeastFixpointOf {A : Type} {OS : OrderedSet A} {L : CompleteLattice A}
           (f : A -> A) : A :=
  meet (PrefixpointsOf f).

Arguments LeastFixpointOf : simpl never.


Definition PostfixpointsOf {A : Type} {OS : OrderedSet A} (f : A -> A) : propset A :=
  PropSet (fun x => leq x (f x)).

Definition GreatestFixpointOf {A : Type} {OS : OrderedSet A} {L : CompleteLattice A}
           (f : A -> A) : A :=
  join (PostfixpointsOf f).

Arguments GreatestFixpointOf : simpl never.

Lemma PrefixpointsOfDualArePostfixpoints {A : Type} :
  forall (OS : OrderedSet A) (f : A -> A),
    @PrefixpointsOf A (@OrderedSet_dual A OS) = @PostfixpointsOf A OS.
Proof.
  intros.
  unfold PrefixpointsOf.
  unfold PostfixpointsOf.
  simpl. auto.
Qed.

Lemma PostfixpointsOfDualArePrefixpoints {A : Type} :
  forall (OS : OrderedSet A) (f : A -> A),
    @PostfixpointsOf A (@OrderedSet_dual A OS) = @PrefixpointsOf A OS.
Proof.
  intros.
  unfold PrefixpointsOf.
  unfold PostfixpointsOf.
  simpl. auto.
Qed.

Lemma GreatestFixpointOnDualIsLeastFixpoint {A : Type} :
  forall (OS : OrderedSet A) (L : CompleteLattice A) (f : A -> A),
    @GreatestFixpointOf A (@OrderedSet_dual A OS) (@CompleteLattice_dual A OS L) f = LeastFixpointOf f.
Proof.
  intros. unfold GreatestFixpointOf. unfold LeastFixpointOf.
  simpl. rewrite -> PostfixpointsOfDualArePrefixpoints. auto. auto.
Qed.


Proposition GreatestFixpoint_greaterThanPostfixpoint:
  forall (A : Type) (OS : OrderedSet A) (L : CompleteLattice A) (f : A -> A) (x : A),
    leq x (f x) -> leq x (GreatestFixpointOf f).
Proof.
  intros.
  unfold GreatestFixpointOf.
  remember (@join_isJoin A OS L). clear Heqi.
  unfold isJoin in i.
  remember (i (PostfixpointsOf f)). clear Heql.
  unfold leastUpperBound in l. destruct l. clear H1.
  unfold upperBound in H0. apply H0.
  unfold PostfixpointsOf. unfold In. apply H.
Qed.


Proposition GreatestFixpoint_GreaterThanFixpoint :
  forall (A : Type) (OS : OrderedSet A) (L : CompleteLattice A) (f : A -> A) (x : A),
    x = (f x) -> leq x (GreatestFixpointOf f).
Proof.
  intros.
  apply GreatestFixpoint_greaterThanPostfixpoint.
  rewrite <- H.
  apply (ord_refl A leq leq_order x).
Qed.

Definition isFixpoint {A : Type} (f : A -> A) (p : A) : Prop :=
  f p = p.

Theorem GreatestFixpoint_fixpoint:
  forall (A : Type) (OS : OrderedSet A) (L : CompleteLattice A) (f : A -> A),
    MonotonicFunction f -> isFixpoint f (@GreatestFixpointOf A OS L f).
Proof.
  (* Wikipedia's proof: https://en.wikipedia.org/wiki/Knaster%E2%80%93Tarski_theorem *)
  intros. rename H into f_monotonic. unfold MonotonicFunction in f_monotonic.
  remember (PostfixpointsOf f) as D. remember (join D) as u.
  assert (f_x_in_D : forall x:A, x ∈ D -> (f x) ∈ D).
  intros.
  assert (f_x_leq_f_f_x : leq (f x) (f (f x))).
  apply f_monotonic. unfold In in H.
  rewrite -> HeqD in H. unfold PostfixpointsOf in H. apply H.
  unfold In. rewrite HeqD. unfold PostfixpointsOf. assumption.
  remember join_isJoin as J. unfold isJoin in J.

  (* introduce u_upper and u_least *)
  remember (J D) as J1. clear HeqJ1. destruct J1.
  rename H into u_upper. rewrite <- Hequ in u_upper. unfold upperBound in u_upper.
  rename H0 into u_least. rewrite <- Hequ in u_least.

  (* introduce f_u_upper_D *)
  assert (f_u_upper_D : upperBound D (f u)).
  unfold upperBound. intros.
  assert (x_le_u : leq x u). apply u_upper. assumption.
  assert (f_x_le_f_u : leq (f x) (f u)). apply f_monotonic. assumption.
  remember H as x_le_f_x. clear Heqx_le_f_x. rewrite -> HeqD in x_le_f_x.
  unfold In in x_le_f_x. unfold PostfixpointsOf in x_le_f_x.
  assert (x_le_f_u : leq x (f u)).
  remember (ord_trans A leq leq_order) as leq_transitive. clear Heqleq_transitive.
  unfold transitive in leq_transitive. 
  apply (leq_transitive x (f x) (f u) x_le_f_x f_x_le_f_u). assumption.
  
  (* u <= f(u) *)
  assert (u_le_fu : leq u (f u)). apply u_least. assumption.

  (* u \in D *)
  assert (u_in_D : u ∈ D). rewrite -> HeqD. unfold In. unfold PostfixpointsOf. assumption.

  (* f(u) <= f(f(u)) *)
  assert (f_u_le_f_f_u : leq (f u) (f (f u)) ). apply f_monotonic. assumption.
  
  (* f(u) \in D *)
  assert (f_u_in_D : (f u) ∈ D). rewrite -> HeqD. unfold In. unfold PostfixpointsOf. assumption.

  (* f(u) <= u *)
  assert (f_u_le_u : leq (f u) u). apply u_upper. assumption.

  (* f(u) = u *)
  assert (f_u_eq_u : f u = u).
  pose (leq_antisym := ord_antisym A leq leq_order).
  unfold antisymmetric in leq_antisym. auto.

  (* isFixpoint *)
  unfold isFixpoint. unfold GreatestFixpointOf. subst. assumption.
Qed.


Theorem LeastFixpoint_fixpoint:
  forall (A : Type) (OS : OrderedSet A) (L : CompleteLattice A) (f : A -> A),
    MonotonicFunction f -> isFixpoint f (@LeastFixpointOf A OS L f).
Proof.
  intros.
  rewrite <- GreatestFixpointOnDualIsLeastFixpoint.
  apply GreatestFixpoint_fixpoint.
  apply MonotonicFunction_dual.
  assumption.
Qed.


Proposition LeastFixpoint_LesserThanPrefixpoint:
  forall (A : Type) (OS : OrderedSet A) (L : CompleteLattice A) (f : A -> A) (x : A),
    leq (f x) x -> leq (LeastFixpointOf f) x.
Proof.
  intros.
  unfold LeastFixpointOf.
  remember (@meet_isMeet A OS L). clear Heqi.
  unfold isMeet in i.
  remember (i (PrefixpointsOf f)). clear Heqg.
  unfold greatestLowerBound in g. destruct g. clear H1.
  unfold lowerBound in H0. apply H0.
  unfold PrefixpointsOf. unfold In. apply H.
Qed.



Proposition LeastFixpoint_LesserThanFixpoint :
  forall (A : Type) (OS : OrderedSet A) (L : CompleteLattice A) (f : A -> A) (x : A),
    x = (f x) -> leq (LeastFixpointOf f) x.
Proof.
  intros.
  apply LeastFixpoint_LesserThanPrefixpoint.
  rewrite <- H.
  apply (ord_refl A leq leq_order x).
Qed.

Proposition LeastFixpoint_unique :
  forall (A : Type) (OS : OrderedSet A) (L : CompleteLattice A) (f : A -> A) (Sfix : A),
    leq (f Sfix) Sfix ->
    (forall x, leq (f x) x -> leq Sfix x) ->
    Sfix = LeastFixpointOf f.
Proof.
  intros A OS L f Sfix.
  intros Hprefix Hleast.

  assert (H2: Sfix ∈ (PrefixpointsOf f)).
  { unfold PrefixpointsOf. unfold In. apply Hprefix. }

  pose proof (H3 := meet_isMeet).
  unfold isMeet in H3.
  specialize (H3 (PrefixpointsOf f)).
  unfold greatestLowerBound in H3.
  destruct H3 as [H3 H3'].
  
  pose proof (H4 := H3 _ H2).
  fold (LeastFixpointOf f) in H4.

  eapply (@ord_antisym _ _ leq_order). 2: apply H4.
  apply H3'.

  unfold lowerBound. intros x H.
  unfold PrefixpointsOf in H. unfold In in H.
  apply Hleast. apply H.
Qed.

Proposition LeastFixpoint_unique_2 :
  forall (A : Type) (OS : OrderedSet A) (L : CompleteLattice A)
    (f : A -> A)
    (Sfix : A),
    (MonotonicFunction f) ->
    (f Sfix) = Sfix ->
    (forall x, (f x) = x -> Sfix = x) ->
    Sfix = LeastFixpointOf f.
Proof.
  intros A OS L f Sfix Hmono Hfix Hleast.
  apply (@ord_antisym _ _ leq_order).
  {
    specialize (Hleast (LeastFixpointOf f)).
    feed specialize Hleast.
    {
      apply LeastFixpoint_fixpoint.
      apply Hmono.
    }
    rewrite Hleast.
    apply (@ord_refl _ _ leq_order).
  }
  {
    apply LeastFixpoint_LesserThanFixpoint.
    symmetry.
    apply Hfix.
  }
Qed.

Lemma lfp_preserves_order {A : Type} (OS : OrderedSet A) (L : CompleteLattice A) (f g : A -> A) :
  MonotonicFunction f -> MonotonicFunction g ->
  (forall (x : A), leq (f x) (g x)) ->
  leq (LeastFixpointOf f) (LeastFixpointOf g).
Proof.
  intros.
  apply (LeastFixpoint_LesserThanPrefixpoint A OS L).
  assert (leq (f (LeastFixpointOf g)) (g (LeastFixpointOf g))).
  { apply H1. }
  assert (g (LeastFixpointOf g) = LeastFixpointOf g).
  { apply LeastFixpoint_fixpoint. assumption.  }
  remember (Relation_Definitions.ord_trans A (@leq A OS) (@leq_order A OS)). clear Heqt.
  unfold Relation_Definitions.transitive in t.
  apply t with (y := g (LeastFixpointOf g)).
  assumption. rewrite -> H3.
  remember (Relation_Definitions.ord_refl A (@leq A OS) (@leq_order A OS)). clear Heqr.
  unfold Relation_Definitions.reflexive in r. apply r.
Qed.

From Coq Require Import Logic.FunctionalExtensionality Logic.PropExtensionality.

Section propset_lattice.
  Variable U : Type.

  Locate "⊆".
  Program Definition PropsetOrderedSet : OrderedSet (propset U) :=
  {| leq := subseteq;
  |}.

  Next Obligation.
    constructor.
    * unfold reflexive.  auto.
    * unfold transitive. apply transitivity.
    * unfold antisymmetric.
      intros.
      destruct x,y. apply f_equal. apply functional_extensionality.
      intros x.
      rewrite -> elem_of_subseteq in H.
      rewrite -> elem_of_subseteq in H0.
      specialize (H x). specialize (H0 x).
      apply propositional_extensionality.
      split; auto.
  Qed.


  Definition propset_Meet (ee : propset (propset U)) : propset U :=
    PropSet (fun m => forall e : propset U,
        e ∈ ee -> m ∈ e).

  Lemma propset_Meet_is_meet : @isMeet (propset U) PropsetOrderedSet propset_Meet.
  Proof.
    unfold isMeet. unfold greatestLowerBound. unfold lowerBound.
    intro X. split.
    - intros. simpl. rewrite -> elem_of_subseteq.
      intros x0 H0. unfold propset_Meet in H0.
      rewrite -> elem_of_PropSet in H0.
      apply H0. apply H.
    - intros lb H. simpl.
      rewrite -> elem_of_subseteq.
      intros x H0. unfold leq in H. simpl in H.
      unfold propset_Meet. apply elem_of_PropSet. intros e.
      specialize (H e). intros H1. specialize (H H1).
      rewrite -> elem_of_subseteq in H. auto.
  Qed.

  Definition PowersetLattice : CompleteLattice (propset U) :=
    {| meet := propset_Meet;
       join := joinFromMeet propset_Meet;
       meet_isMeet := propset_Meet_is_meet;
       join_isJoin := joinFromMeet_lub (propset U) PropsetOrderedSet propset_Meet propset_Meet_is_meet;
    |}.

End propset_lattice.










  
