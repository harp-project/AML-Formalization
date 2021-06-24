From Coq Require Import ssreflect ssrfun ssrbool.
From Coq Require Import Ensembles Logic.Classical_Prop.
From Coq.micromega Require Import Lia.

From Equations Require Import Equations.

From MatchingLogic Require Import Syntax Semantics DerivedOperators ProofSystem Helpers.FOL_helpers.
Import MatchingLogic.Syntax.Notations MatchingLogic.DerivedOperators.Notations.


Section ml_tauto.
  Open Scope ml_scope.

  Context {Σ : Signature}.

  (* TODO we need to add this to some Notations module in ProofSystem.v *)
  Notation "theory ⊢ pattern" := (@ML_proof_system Σ theory pattern) (at level 95, no associativity).

  Inductive PropPattern : Type :=
  | pp_atomic (p : Pattern) (wf : well_formed p)
  | pp_natomic (p : Pattern) (wf : well_formed p)
  | pp_and (p1 p2 : PropPattern)
  | pp_or (p1 p2 : PropPattern)
  .

  Fixpoint pp_flatten (pp : PropPattern) : Pattern :=
    match pp with
    | pp_atomic p _ => p
    | pp_natomic p _ => patt_not p
    | pp_and p1 p2 => patt_and (pp_flatten p1) (pp_flatten p2)
    | pp_or p1 p2 => patt_or (pp_flatten p1) (pp_flatten p2)
    end.

  Lemma pp_flatten_well_formed (pp : PropPattern) :
    well_formed (pp_flatten pp).
  Proof.
    induction pp; simpl; auto.
  Qed.
  
  Fixpoint pp_toCoq (pp : PropPattern) : Prop :=
    match pp with
    | pp_atomic p _ => ((Empty_set _) ⊢ p)
    | pp_natomic p _ => ((Empty_set _) ⊢ (patt_not p))
    | pp_and p1 p2 => (pp_toCoq p1) /\ (pp_toCoq p2)
    | pp_or p1 p2 => (pp_toCoq p1) \/ (pp_toCoq p2)
    end.

  Lemma extractProof : forall (pp : PropPattern), pp_toCoq pp -> ((Empty_set _) ⊢ (pp_flatten pp)).
  Proof.
    induction pp; simpl; intros H.
    - exact H.
    - exact H.
    - destruct H as [H1 H2].
      specialize (IHpp1 H1).
      specialize (IHpp2 H2).
      clear H1 H2.
      apply conj_intro_meta; auto using pp_flatten_well_formed.
    - destruct H as [H1|H2].
      + specialize (IHpp1 H1).
        clear IHpp2 H1.
        apply disj_left_intro_meta; auto using pp_flatten_well_formed.
      + specialize (IHpp2 H2).
        clear IHpp1 H2.
        apply disj_right_intro_meta; auto using pp_flatten_well_formed.
  Qed.


  #[tactic=simpl]
  Equations negate_eq (p : Pattern) : Pattern by wf (size p) lt :=
    negate_eq patt_bott := patt_not patt_bott ;
    negate_eq (patt_free_evar x) := patt_not (patt_free_evar x) ;
    negate_eq (patt_free_svar X) := patt_not (patt_free_svar X) ;
    negate_eq (patt_bound_evar n) := patt_not (patt_bound_evar n) ;
    negate_eq (patt_bound_svar n) := patt_not (patt_bound_svar n) ;
    negate_eq (patt_sym s) := patt_not (patt_sym s) ;
    negate_eq (patt_app phi1 phi2) := patt_not (patt_app phi1 phi2) ;
    negate_eq (patt_exists phi) := patt_not (patt_exists phi) ;
    negate_eq (patt_mu phi) := patt_not (patt_mu phi) ;
    
    negate_eq (patt_imp phi1 phi2) with
        (match_and (patt_imp phi1 phi2),
        match_or (patt_imp phi1 phi2),
        match_not (patt_imp phi1 phi2)) := {
      | (Some (a1, a2), _, _) := patt_or (negate_eq a1) (negate_eq a2) ;
      | (None, (Some (a1, a2)), _) := patt_and (negate_eq a1) (negate_eq a2) ;
      | (None, None, (Some p')) := p' ;
      | (None, None, None) :=
        (* This would not make the termination checker happy *)
        (* patt_and phi1 (negate_eq phi2) *)
        patt_not (patt_imp phi1 phi2) }.

    (*
    negate_eq (patt_imp phi1 phi2) with
        match_and (patt_imp phi1 phi2),
        match_or (patt_imp phi1 phi2),
        match_not (patt_imp phi1 phi2) => {
      negate_eq (patt_imp phi1 phi2) (Some (a1, a2)) _ _ => patt_or (negate_eq a1) (negate_eq a2) ;
      negate_eq (patt_imp phi1 phi2) None (Some (a1, a2)) _ => patt_and (negate_eq a1) (negate_eq a2) ;
      negate_eq (patt_imp phi1 phi2) None None (Some p') => p' ;
      negate_eq (patt_imp phi1 phi2) None None None :=
        (* This would not make the termination checker happy *)
        (* patt_and phi1 (negate_eq phi2) *)
        patt_not (patt_imp phi1 phi2) }.*)
  Proof.
    
    simpl. lia.
  Next Obligation.
    intros.
    symmetry in Heq_anonymous.
    apply match_and_size in Heq_anonymous.
    exact (proj1 Heq_anonymous).
  Defined.
  Next Obligation.
    intros.
    symmetry in Heq_anonymous.
    apply match_and_size in Heq_anonymous.
    exact (proj2 Heq_anonymous).
  Defined.
  Next Obligation.
    intros.
    symmetry in Heq_anonymous.
    apply match_or_size in Heq_anonymous.
    exact (proj1 Heq_anonymous).
  Defined.
  Next Obligation.
    intros.
    symmetry in Heq_anonymous.
    apply match_or_size in Heq_anonymous.
    exact (proj2 Heq_anonymous).
  Defined.
  Next Obligation.
    Tactics.program_simpl.
  Defined.

  
  (* Negates and to or and vice versa *)
  Program Fixpoint negate (p : Pattern) {measure (size p)} : Pattern :=
    match (match_and p) with
    | Some (p1, p2) => patt_or (negate p1) (negate p2)
    | None =>
      match (match_or p) with
      | Some (p1, p2) => patt_and (negate p1) (negate p2)
      | None =>
        match (match_not p) with
        | Some p' => p'
        | None => patt_not p
        end
      end
    end.
  Next Obligation.
    intros.
    symmetry in Heq_anonymous.
    apply match_and_size in Heq_anonymous.
    exact (proj1 Heq_anonymous).
  Defined.
  Next Obligation.
    intros.
    symmetry in Heq_anonymous.
    apply match_and_size in Heq_anonymous.
    exact (proj2 Heq_anonymous).
  Defined.
  Next Obligation.
    intros.
    symmetry in Heq_anonymous.
    apply match_or_size in Heq_anonymous.
    exact (proj1 Heq_anonymous).
  Defined.
  Next Obligation.
    intros.
    symmetry in Heq_anonymous.
    apply match_or_size in Heq_anonymous.
    exact (proj2 Heq_anonymous).
  Defined.
  Next Obligation.
    Tactics.program_simpl.
  Defined.

  (* TODO: prove that negation is equivalent to the negation of the original *)
  Lemma negate_equiv (p : Pattern) :
    (Empty_set _) ⊢ ((patt_not p) <---> (negate p)).
  Proof.
    remember (size p) as sz.
    assert (Hsz: size p <= sz).
    { lia. }
    clear Heqsz.
    induction sz.
    - destruct p; simpl in Hsz; try lia.
      
    induction p; simpl.
    - cbv [negate].
  Abort.
  

  (* TODO: a function [abstract : Pattern -> PropPattern] *)
End ml_tauto.
