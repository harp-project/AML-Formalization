Require Import Coq.Sets.Ensembles.
Require Import Coq.Relations.Relation_Definitions.
Require Import HARP.AML.KnasterTarski.

Section powerset_lattice.

Program Definition EnsembleOrderedSet (U : Type) : OrderedSet (Ensemble U) :=
  {| leq := Ensembles.Included U;
  |}.
Next Obligation.
  constructor.
  * unfold reflexive. unfold Included. auto.
  * unfold transitive. unfold Included. auto.
  * unfold antisymmetric. intros.
    apply Extensionality_Ensembles. split; auto.
Qed.

Definition Meet (U : Type) (ee : Ensemble (Ensemble U)) : Ensemble U :=
  fun m => forall e : Ensemble U,
      Ensembles.In (Ensemble U) ee e -> Ensembles.In U e m.

Lemma Meet_is_meet (U : Type) : @isMeet (Ensemble U) (EnsembleOrderedSet U) (Meet U).
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

Definition PowersetLattice (U : Type) : CompleteLattice (Ensemble U) :=
  {| meet := Meet U;
     join := joinFromMeet (Meet U);
     meet_isMeet := Meet_is_meet U;
     join_isJoin := joinFromMeet_lub (Ensemble U) (EnsembleOrderedSet U) (Meet U) (Meet_is_meet U)
  |}.

End powerset_lattice.
