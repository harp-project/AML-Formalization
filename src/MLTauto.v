From Coq Require Import ssreflect ssrfun ssrbool.
From Coq Require Import Ensembles Logic.Classical_Prop.
From Coq.micromega Require Import Lia.

From MatchingLogic Require Import Syntax Semantics DerivedOperators ProofSystem Helpers.FOL_helpers.
Import MatchingLogic.Syntax.Notations MatchingLogic.DerivedOperators.Notations.

(*
  Γ ⊢ patt_or A (patt_not A)
  ==> ((Γ ⊢ A) \/ ~ (Γ ⊢ A))
  ==> pp_toCoq (patt_or A (patt_not A)) = ((Γ ⊢ A) \/ ~ (Γ ⊢ A))
  ==> tauto
  ==>
  Lemma extractProof : forall (pp : PropPattern), pp_toCoq pp -> ((Empty_set _) ⊢ (pp_flatten pp)).
  (* TODO: a function [abstract : Pattern -> PropPattern] *)

  abstract: Pattern -> PropPattern
  A -> B ==> pp_or (pp_natomic A) (pp_atomic B)
  A \/ B == ~A -> B ==> pp_or (pp_atomic A) (pp_atomic B)
  ~A -> (B -> C) ==> A \/ (B -> C)

  Lemma flatten_abstract: ⊢ pp_flatten (abstract phi) <-> phi

  |- A <-> B ==> |- C[A] <-> C[B]

  Goal: Γ ⊢ patt_or A (patt_not A)

  Γ ⊢ pp_flatten ( pp_or (pp_atomic A) (pp_natomic A) )

Lemma extractProof : forall (pp : PropPattern), pp_toCoq pp -> ((Empty_set _) ⊢ (pp_flatten pp)).

 apply extractProof.


 *)

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
        | None =>
          match p with
          | patt_imp p1 p2 => patt_and p1 (negate p2)
          | _ => patt_not p
          end
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
    intros.
    subst. simpl. lia.
  Defined.
  Next Obligation.
    Tactics.program_simpl.
  Defined.
  Next Obligation.
    Tactics.program_simpl.
  Defined.
  Next Obligation.
    Tactics.program_simpl.
  Defined.
  Next Obligation.
    Tactics.program_simpl.
  Defined.
  Next Obligation.
    Tactics.program_simpl.
  Defined.
  Next Obligation.
    Tactics.program_simpl.
  Defined.
    Next Obligation.
    Tactics.program_simpl.
  Defined.
    Next Obligation.
    Tactics.program_simpl.
  Defined.
    Next Obligation.
    Tactics.program_simpl.
  Defined.
    Next Obligation.
    Tactics.program_simpl.
  Defined.    

  Lemma negate_free_evar_simpl x:
    negate (patt_free_evar x) = patt_not (patt_free_evar x).
  Proof.
    reflexivity.
  Qed.

  Lemma negate_free_svar_simpl X:
    negate (patt_free_svar X) = patt_not (patt_free_svar X).
  Proof.
    reflexivity.
  Qed.

  Lemma negate_bound_evar_simpl n:
    negate (patt_bound_evar n) = patt_not (patt_bound_evar n).
  Proof.
    reflexivity.
  Qed.

  Lemma negate_bound_svar_simpl n:
    negate (patt_bound_svar n) = patt_not (patt_bound_svar n).
  Proof.
    reflexivity.
  Qed.

  Lemma negate_sym_simpl s:
    negate (patt_sym s) = patt_not (patt_sym s).
  Proof.
    reflexivity.
  Qed.

  Lemma negate_bott_simpl:
    negate patt_bott = patt_not patt_bott.
  Proof.
    reflexivity.
  Qed.

  Lemma negate_app_simpl p1 p2:
    negate (patt_app p1 p2) = patt_not (patt_app p1 p2).
  Proof.
    reflexivity.
  Qed.

  Lemma negate_and_simpl p1 p2:
    negate (patt_and p1 p2) = patt_or (negate p1) (negate p2).
  Proof.
    unfold negate. rewrite Wf.fix_sub_eq.
    2: { Tactics.program_simpl. }
    intros x f g H.
    destruct x; auto.
    cbv [match_and]. cbv [match_or]. cbv [match_not].
    (* TODO improve performance *)
    destruct x1,x2; auto with f_equal;
      destruct x1_2;
      auto with f_equal;
      intros;
      destruct x1_1; auto with f_equal;
      destruct x1_1_2; auto with f_equal;
      destruct x1_1_1; auto with f_equal;
        try destruct x1_1_1_2; auto with f_equal.

    destruct x1_2_2; auto with f_equal.
  Qed.

  Lemma negate_or_simpl p1 p2:
    negate (patt_or p1 p2) = patt_and (negate p1) (negate p2).
  Proof.
    unfold negate.
    rewrite Wf.fix_sub_eq; unfold match_and; unfold match_or; unfold match_not;
      try destruct x; auto; try destruct x_2; auto.

    destruct x2; destruct x1; auto with f_equal; destruct x1_2; auto with f_equal;
      destruct x1_1; auto with f_equal; destruct x1_1_2; auto with f_equal;
        destruct x1_1_1; auto with f_equal; destruct x1_1_1_2; auto with f_equal.

    2: { unfold patt_or; destruct p2; auto. unfold patt_not. destruct p1; auto.
         destruct p1_2; auto. destruct p1_1; auto.
         destruct p1_1_2; auto.
    }

    destruct x1_2_2; auto. intros. auto with f_equal.
  Qed.
    

  Definition negate_simpl :=
    ( negate_free_evar_simpl,
      negate_free_svar_simpl,
      negate_bound_evar_simpl,
      negate_bound_svar_simpl,
      negate_sym_simpl,
      negate_bott_simpl,
      negate_app_simpl,
      negate_and_simpl,
      negate_or_simpl
    ).

  
  Lemma negate_equiv (p : Pattern) :
    well_formed p ->
    (Empty_set _) ⊢ ((patt_not p) <---> (negate p)).
  Proof.
    intros Hwfp.
    remember (size p) as sz.
    assert (Hsz: size p <= sz).
    { lia. }
    clear Heqsz.
    move: p Hwfp Hsz.
    induction sz; intros p Hwfp Hsz.
    - destruct p; simpl in Hsz; try lia; rewrite negate_simpl;
        apply conj_intro_meta; auto; apply A_impl_A; auto.
    - destruct p; simpl in Hsz;
       try (apply IHsz; auto; simpl; lia).
      + rewrite negate_app_simpl. apply conj_intro_meta; auto; apply A_impl_A; auto.
      + 
  Abort.
  

  (* TODO: a function [abstract : Pattern -> PropPattern] *)
End ml_tauto.
