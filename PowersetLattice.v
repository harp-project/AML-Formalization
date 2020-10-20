Require Import Coq.Sets.Ensembles.
Require Import Coq.Relations.Relation_Definitions.
Require Import HARP.AML.KnasterTarski.

Variable U : Type.

Program Instance EnsembleOrderedSet : OrderedSet (Ensemble U) :=
  {| leq := Ensembles.Included U;
  |}.
Next Obligation.
  constructor.
  * unfold reflexive. unfold Included. auto.
  * unfold transitive. unfold Included. auto.
  * unfold antisymmetric. intros.
    apply Extensionality_Ensembles. split; auto.
Qed.

Definition Meet (ee : Ensemble (Ensemble U)) : Ensemble U :=
  fun m => forall e : Ensemble U,
      Ensembles.In (Ensemble U) ee e -> Ensembles.In U e m.

Lemma Meet_is_meet : isMeet Meet.
Proof.
  unfold isMeet. unfold greatestLowerBound. unfold lowerBound.
  intro X. split.
  - intros. simpl. unfold Included. intros. unfold In in H0. unfold Meet in H0.
    auto.
  - intros. simpl. unfold Included. intros. unfold leq in H. simpl in H.
    unfold In. unfold Meet. intros. unfold Included in H.
    unfold In in *.
    apply H. assumption. assumption.
Qed.

Instance PowersetLattice : CompleteLattice (Ensemble U) :=
  {| meet := Meet;
     join := joinFromMeet Meet;
     meet_isMeet := Meet_is_meet;
     join_isJoin := joinFromMeet_lub (Ensemble U) EnsembleOrderedSet Meet Meet_is_meet
  |}.
