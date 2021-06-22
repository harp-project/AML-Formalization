From Coq Require Import ssreflect ssrfun ssrbool.
From Coq Require Import Ensembles Logic.Classical_Prop.

From MatchingLogic Require Import Syntax Semantics DerivedOperators ProofSystem Helpers.FOL_helpers.
Import MatchingLogic.Syntax.Notations MatchingLogic.DerivedOperators.Notations.


Section ml_tauto.
  Open Scope ml_scope.

  Context {Σ : Signature}.

  (* TODO we need to add this to some Notations module in ProofSystem.v *)
  Notation "theory ⊢ pattern" := (@ML_proof_system Σ theory pattern) (at level 95, no associativity).

  Inductive PropPattern : Type :=
  | pp_false
  | pp_atomic (p : Pattern)
  | pp_imp (p1 p2 : PropPattern)
  .
  
  Fixpoint pp_flatten (pp : PropPattern) : Pattern :=
    match pp with
    | pp_false => patt_bott
    | pp_atomic p => p
    | pp_imp p1 p2 => patt_imp (pp_flatten p1) (pp_flatten p2)
    end.

  Fixpoint pp_toCoq (pp : PropPattern) : Prop :=
    match pp with
    | pp_false => False
    | pp_atomic p => ((Empty_set _) ⊢ p)
    | pp_imp p1 p2 => forall (prf : (pp_toCoq p1)), (pp_toCoq p2)
    end.

  Fixpoint abstract_pp (p : Pattern) : PropPattern :=
    match p with
    | patt_bott => pp_false
    | patt_imp p1 p2 => pp_imp (abstract_pp p1) (abstract_pp p2)
    | _ => pp_atomic p
    end.

  Lemma pp_flatten_abstract (p : Pattern) : pp_flatten (abstract_pp p) = p.
  Proof.
    induction p; simpl; auto.
    rewrite IHp1. rewrite IHp2. reflexivity.
  Qed.

  Lemma extractProof : forall (pp : PropPattern),
      (pp_toCoq pp -> ((Empty_set _) ⊢ (pp_flatten pp)))
      /\ (~(pp_toCoq pp) -> ((Empty_set _) ⊢ (patt_not (pp_flatten pp)))).
  Proof.
    induction pp; split; simpl; intros H.
    - inversion H.
    - (* should work *)
      admit.
    - exact H.
    - (* FAIL, cannot work. Maybe for predicate patterns..? *)
      admit.
    - destruct IHpp1 as [IHpp11 IHpp12].
      destruct IHpp2 as [IHpp21 IHpp22].
      destruct (classic (pp_toCoq pp1)).
      + specialize (H H0).
        specialize (IHpp11 H0).
        specialize (IHpp21 H).
        clear IHpp12 IHpp22 H H0.
        (* This should work *)
        admit.
      + specialize (IHpp12 H0).
        clear -IHpp12.
        (* This should work *)
        admit.
    - destruct IHpp1 as [IHpp11 IHpp12].
      destruct IHpp2 as [IHpp21 IHpp22].
      destruct (classic (pp_toCoq pp2)).
      + assert (H2 : pp_toCoq pp1 -> pp_toCoq pp2).
        { auto. }
        contradiction.
      + assert (H1 : pp_toCoq pp1).
        { tauto. }
        clear H.
        specialize (IHpp11 H1).
        clear IHpp12.
        clear IHpp21.
        specialize (IHpp22 H0).
        clear H0 H1.
        (* This should work *)
        admit.
  Abort.

  Lemma extractProof : forall (pp : PropPattern), pp_toCoq pp -> ((Empty_set _) ⊢ (pp_flatten pp)).
  Proof.
    induction pp; simpl; intros H.
    - inversion H.
    - exact H.
    - destruct (classic (pp_toCoq pp1)).
      + specialize (H H0).
        specialize (IHpp1 H0).
        specialize (IHpp2 H).
        clear H H0.
        (* This should work! *)
        admit.
  Abort.

End ml_tauto.
