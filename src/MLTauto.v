From Coq Require Import ssreflect ssrfun ssrbool.
From Coq Require Import Ensembles Logic.Classical_Prop.
From Coq Require Import Arith.Wf_nat Relations.Relation_Operators Wellfounded.Lexicographic_Product.
From Coq.micromega Require Import Lia.

From stdpp Require Import base option.

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

  Definition option_bimap {A B C : Type} (f : A -> B -> C) (x : option A) (y : option B) : option C :=
    match x with
    | Some a =>
      match y with
      | Some b => Some (f a b)
      | None => None
      end
    | None => None
    end.

  Fixpoint and_or_not_size' (fuel : nat) (p : Pattern) : option nat :=
    match fuel with
    | 0 => None
    | S fuel' =>
      match (match_and p) with
      | Some (p1, p2) => S <$> (option_bimap plus (and_or_not_size' fuel' p1) (and_or_not_size' fuel' p2))
      | None =>
        match (match_or p) with
        | Some (p1, p2) => S <$> (option_bimap plus (and_or_not_size' fuel' p1) (and_or_not_size' fuel' p2))
        | None =>
          match (match_not p) with
          | Some p' => S <$> (and_or_not_size' fuel' p')
          | None => Some 1
          end
        end
      end
    end.

  Definition and_or_not_size'_enough_fuel (p : Pattern) : nat := S (size p).
  
  Lemma and_or_not_size'_terminates (p : Pattern) :
    and_or_not_size' (and_or_not_size'_enough_fuel p) p <> None.
  Proof.
    unfold and_or_not_size'_enough_fuel.
    remember (S (size p)) as sz.
    assert (Hsz: 1 + size p <= sz).
    { lia. }
    clear Heqsz.

    move: p Hsz.
    induction sz.
    { intros. lia. }
    intros p Hsz.
    destruct p; simpl; try discriminate.

    remember (match_and (p1 ---> p2)) as a'.
    destruct a'.
    {
      destruct p as [p1' p2'].
      symmetry in Heqa'.
      pose proof (H := match_and_size Heqa').
      destruct H as [H1 H2].
      unfold option_bimap.
      remember (and_or_not_size' sz p1') as n1'.
      destruct n1'.
      2: {
        symmetry in Heqn1'. apply IHsz in Heqn1'. inversion Heqn1'.
        simpl in *. lia.
      }
      remember (and_or_not_size' sz p2') as n2'.
      destruct n2'.
      2: {
        symmetry in Heqn2'. apply IHsz in Heqn2'. inversion Heqn2'.
        simpl in *. lia.
      }
      simpl.
      discriminate.
    }

    remember (match_not p1) as b'.
    destruct b'.
    {
      symmetry in Heqb'.
      pose proof (H := match_not_size Heqb').
      unfold option_bimap.
      remember (and_or_not_size' sz p) as n1'.
      destruct n1'.
      2: {
        symmetry in Heqn1'. apply IHsz in Heqn1'. inversion Heqn1'.
        simpl in *. lia.
      }
      remember (and_or_not_size' sz p2) as n2'.
      destruct n2'.
      2: {
        symmetry in Heqn2'. apply IHsz in Heqn2'. inversion Heqn2'.
        simpl in *. lia.
      }
      discriminate.
    }
 
    remember (match p2 with Bot => Some p1 | _ => None end) as c'.
    destruct c'. 2: { discriminate. }

    unfold fmap. unfold option_fmap. unfold option_map.

    destruct p2; inversion Heqc'. subst p1.

    remember (and_or_not_size' sz p) as n'.
    destruct n'. discriminate.
    symmetry in Heqn'. apply IHsz in Heqn'. inversion Heqn'.
    simpl in *. lia.
  Qed.  
  
  Fixpoint negate' (fuel : nat) (p : Pattern) : option Pattern :=
    match fuel with
    | 0 => None
    | S fuel' =>
      match (match_and p) with
      | Some (p1, p2) => option_bimap patt_or (negate' fuel' p1) (negate' fuel' p2)
      | None =>
        match (match_or p) with
        | Some (p1, p2) => option_bimap patt_and (negate' fuel' p1) (negate' fuel' p2)
        | None =>
          match (match_not p) with
          | Some p' => Some p'
          | None =>
            match p with
            | patt_imp p1 p2 => (patt_and p1) <$> (negate' fuel' p2)
            | _ => Some (patt_not p)
            end
          end
        end
      end
    end.

  Definition negate'_enough_fuel (p : Pattern) : nat := S (size p).
  
  Lemma negate'_terminates (p : Pattern) :
    negate' (negate'_enough_fuel p) p <> None.
  Proof.
    unfold negate'_enough_fuel.
    remember (S (size p)) as sz.
    assert (Hsz: 1 + size p <= sz).
    { lia. }
    clear Heqsz.

    move: p Hsz.
    induction sz.
    { intros. lia. }
    intros p Hsz.
    destruct p; simpl; try discriminate.

    remember (match_and (p1 ---> p2)) as a'.
    destruct a'.
    {
      destruct p as [p1' p2'].
      symmetry in Heqa'.
      pose proof (H := match_and_size Heqa').
      destruct H as [H1 H2].
      unfold option_bimap.
      remember (negate' sz p1') as n1'.
      destruct n1'.
      2: {
        symmetry in Heqn1'. apply IHsz in Heqn1'. inversion Heqn1'.
        simpl in *. lia.
      }
      remember (negate' sz p2') as n2'.
      destruct n2'.
      2: {
        symmetry in Heqn2'. apply IHsz in Heqn2'. inversion Heqn2'.
        simpl in *. lia.
      }
      discriminate.
    }


    remember (match_not p1) as b'.
    destruct b'.
    {
      symmetry in Heqb'.
      pose proof (H := match_not_size Heqb').
      unfold option_bimap.
      remember (negate' sz p) as n1'.
      destruct n1'.
      2: {
        symmetry in Heqn1'. apply IHsz in Heqn1'. inversion Heqn1'.
        simpl in *. lia.
      }
      remember (negate' sz p2) as n2'.
      destruct n2'.
      2: {
        symmetry in Heqn2'. apply IHsz in Heqn2'. inversion Heqn2'.
        simpl in *. lia.
      }
      discriminate.
    }
 
    remember (match p2 with Bot => Some p1 | _ => None end) as c'.
    destruct c'. discriminate.

    unfold fmap. unfold option_fmap. unfold option_map.

    remember (negate' sz p2) as n'.
    destruct n'. discriminate.
    symmetry in Heqn'. apply IHsz in Heqn'. inversion Heqn'.
    simpl in *. lia.
  Qed.

  Lemma negate'_monotone (p : Pattern) (fuel fuel' : nat) :
    fuel >= negate'_enough_fuel p ->
    fuel' >= fuel ->
    negate' fuel' p = negate' fuel p.
  Proof.
    remember (size p) as sz.
    assert (Hsz: size p <= sz).
    lia.
    clear Heqsz.
    move: p fuel fuel' Hsz.
    induction sz;
    intros p fuel fuel' Hsz Henough Hmore;
    destruct p; simpl in Hsz; unfold negate'_enough_fuel in Henough; simpl in Henough; try lia;
      destruct fuel,fuel'; try lia; simpl; try reflexivity.

    remember (match_and (p1 ---> p2)) as q.
    destruct q.
    { destruct p.
      symmetry in Heqq. apply match_and_size in Heqq. simpl in Heqq. destruct Heqq as [Hsz1 Hsz2].
      rewrite -> IHsz with (fuel := fuel).
      2: { lia. }
      2: { unfold negate'_enough_fuel. lia. }
      2: { lia. }

      rewrite -> IHsz with (fuel':=fuel') (fuel := fuel).
      2: { lia. }
      2: { unfold negate'_enough_fuel. lia. }
      2: { lia. }
      reflexivity.
    }

    remember (match_not p1) as q2.
    destruct q2.
    {
      symmetry in Heqq2. apply match_not_size in Heqq2.
      rewrite -> IHsz with (fuel := fuel).
      2: { lia. }
      2: { unfold negate'_enough_fuel. lia. }
      2: { lia. }

      rewrite -> IHsz with (fuel':=fuel') (fuel := fuel).
      2: { lia. }
      2: { unfold negate'_enough_fuel. lia. }
      2: { lia. }
      reflexivity.
    }

    destruct p2; try reflexivity; unfold fmap,option_fmap,option_map; rewrite -> IHsz with (fuel := fuel);
      try reflexivity; unfold negate'_enough_fuel; try lia.
  Qed.

    
  Definition negate''(p : Pattern) : option Pattern := negate' (negate'_enough_fuel p) p.

  (*
  Definition negate (p : Pattern) : Pattern.
  Proof.
    remember (negate'' p) as np.
    destruct np.
    2: { symmetry in Heqnp. apply negate'_terminates in Heqnp. contradiction. }
    exact p0.
  Defined.
   *)

  Definition negate (p : Pattern) :=
    let np := negate'' p in
    let Heqnp : np = negate'' p := erefl np in
    match np as o return (o = negate'' p → Pattern) with
    | Some p0 => λ _, p0
    | None =>
      λ Heqnp0 : None = negate'' p,
                 match (negate'_terminates p (eq_sym Heqnp0)) with end
    end Heqnp.

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

  Lemma negate''_and_simpl p1 p2:
    negate'' (patt_and p1 p2) = option_bimap patt_or (negate'' p1) (negate'' p2).
  Proof.
    unfold negate'' at 1, negate'_enough_fuel at 1, negate' at 1.
    rewrite match_and_patt_and.
    fold negate'.
    erewrite negate'_monotone with (fuel := negate'_enough_fuel p1).
    fold (negate'' p1).
    erewrite negate'_monotone with (fuel := negate'_enough_fuel p2).
    fold (negate'' p2).
    reflexivity.
    all: simpl; unfold negate'_enough_fuel; lia.
  Qed.

  Lemma negate_from_negate'' p np:
    negate'' p = Some np ->
    negate p = np.
  Proof.
    intros H.
    unfold negate.
    (* < magic > *)
    move: (erefl (negate'' p)).
    case: {1 3}(negate'' p) => //.
    2: { intros e. destruct (negate'_terminates p (eq_sym e)). }
    (* </magic > *)
    intros a e.
    rewrite -e in H. clear e.
    inversion H. reflexivity.
  Qed.
  
  Lemma negate_and_simpl p1 p2:
    negate (patt_and p1 p2) = patt_or (negate p1) (negate p2).
  Proof.
    unfold negate at 1.
    (* < magic > *)
    move: (erefl (negate'' (p1 and p2))).
    case: {1 3}(negate'' (p1 and p2)) => //.
    2: { intros e. destruct (negate'_terminates (p1 and p2) (eq_sym e)). }
    (* </magic > *)
    intros. symmetry in e.
    pose proof (H := negate''_and_simpl p1 p2).
    rewrite e in H. unfold option_bimap in H.
    remember (negate'' p1) as np1.
    remember (negate'' p2) as np2.
    destruct np1, np2; inversion H; clear H; subst.
    unfold negate.
    (* < magic > *)
    move: (erefl (negate'' p1)).
    case: {1 3}(negate'' p1) => //.
    2: { intros e1. destruct (negate'_terminates p1 (eq_sym e1)). }
    (* </magic > *)
    intros.
    (* < magic > *)
    move: (erefl (negate'' p2)).
    case: {1 3}(negate'' p2) => //.
    2: { intros e2. destruct (negate'_terminates p2 (eq_sym e2)). }
      (* </magic > *)
    intros.
    congruence.
  Qed.

  Lemma negate''_or_simpl p1 p2:
    negate'' (patt_or p1 p2) = option_bimap patt_and (negate'' p1) (negate'' p2).
  Proof.
    unfold negate'' at 1, negate'_enough_fuel at 1, negate' at 1.
    rewrite match_and_patt_or. rewrite match_or_patt_or.
    fold negate'.
    erewrite negate'_monotone with (fuel := negate'_enough_fuel p1).
    fold (negate'' p1).
    erewrite negate'_monotone with (fuel := negate'_enough_fuel p2).
    fold (negate'' p2).
    reflexivity.
    all: simpl; unfold negate'_enough_fuel; lia.
  Qed.
  
  Lemma negate_or_simpl p1 p2:
    negate (patt_or p1 p2) = patt_and (negate p1) (negate p2).
  Proof.
    unfold negate at 1.
    (* < magic > *)
    move: (erefl (negate'' (p1 or p2))).
    case: {1 3}(negate'' (p1 or p2)) => //.
    2: { intros e. destruct (negate'_terminates (p1 or p2) (eq_sym e)). }
    (* </magic > *)
    intros. symmetry in e.
    pose proof (H := negate''_or_simpl p1 p2).
    rewrite e in H. unfold option_bimap in H.
    remember (negate'' p1) as np1.
    remember (negate'' p2) as np2.
    destruct np1, np2; inversion H; clear H; subst.
    unfold negate.
    (* < magic > *)
    move: (erefl (negate'' p1)).
    case: {1 3}(negate'' p1) => //.
    2: { intros e1. destruct (negate'_terminates p1 (eq_sym e1)). }
    (* </magic > *)
    intros.
    (* < magic > *)
    move: (erefl (negate'' p2)).
    case: {1 3}(negate'' p2) => //.
    2: { intros e2. destruct (negate'_terminates p2 (eq_sym e2)). }
      (* </magic > *)
    intros.
    congruence.
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

  Fixpoint count_general_implications' (fuel : nat) (p : Pattern) : option nat :=
    match fuel with
    | 0 => None
    | S fuel' =>
      match (match_and p) with
      | Some _ => Some 0
      | None =>
        match (match_or p) with
        | Some _ => Some 0
        | None =>
          match (match_not p) with
          | Some _ => Some 0
          | None =>
            match p with
            | patt_imp p1 p2 =>
              option_bimap
                plus
                (count_general_implications' fuel' p1)
                (count_general_implications' fuel' p2)
            | _ => Some 0
            end
          end
        end
      end
    end.
  
  Definition count_general_implications'_enough_fuel (p : Pattern) : nat := S (size p).

  Lemma count_general_implications'_terminates (p : Pattern) :
    count_general_implications' (count_general_implications'_enough_fuel p) p <> None.
  Proof.
    unfold count_general_implications'_enough_fuel.
    remember (S (size p)) as sz.
    assert (Hsz: 1 + size p <= sz).
    { lia. }
    clear Heqsz.

    move: p Hsz.
    induction sz.
    { intros. lia. }
    intros p Hsz.
    destruct p; simpl; try discriminate.

    remember (match_and (p1 ---> p2)) as a'.
    destruct a'.
    { discriminate. }


    remember (match_not p1) as b'.
    destruct b'.
    { discriminate. }
 
    remember (match p2 with Bot => Some p1 | _ => None end) as c'.
    destruct c'. discriminate.

    unfold option_bimap.
    remember (count_general_implications' sz p1) as c1.
    remember (count_general_implications' sz p2) as c2.
    simpl in Hsz.
    pose proof (IHsz p1 ltac:(lia)).
    pose proof (IHsz p2 ltac:(lia)).
    destruct c1,c2; try discriminate.
    { rewrite -Heqc2 in H0. contradiction. }
    { rewrite -Heqc1 in H. contradiction. }
    { rewrite -Heqc2 in H0. contradiction. }
  Qed.

  
  Lemma count_general_implications'_monotone (p : Pattern) (fuel fuel' : nat) :
    fuel >= count_general_implications'_enough_fuel p ->
    fuel' >= fuel ->
    count_general_implications' fuel' p = count_general_implications' fuel p.
  Proof.
    remember (size p) as sz.
    assert (Hsz: size p <= sz).
    lia.
    clear Heqsz.
    move: p fuel fuel' Hsz.
    induction sz;
    intros p fuel fuel' Hsz Henough Hmore;
    destruct p; simpl in Hsz; unfold count_general_implications'_enough_fuel in Henough; simpl in Henough; try lia;
      destruct fuel,fuel'; try lia; simpl; try reflexivity.

    remember (match_and (p1 ---> p2)) as q.
    destruct q.
    { reflexivity. }

    remember (match_not p1) as q2.
    destruct q2.
    { reflexivity. }

    destruct p2; try reflexivity; unfold option_bimap;
      remember (count_general_implications' fuel' p1) as c';
      remember (count_general_implications' fuel p1) as c;
      destruct c,c'; try reflexivity; simpl in *;
        rewrite -> IHsz with (fuel := fuel) in Heqc';
        try rewrite -Heqc' in Heqc; try inversion Heqc; subst; clear Heqc;
        unfold count_general_implications'_enough_fuel in *; try lia.

    all: rewrite -> IHsz with (fuel := fuel); simpl; try lia; auto.
  Qed.


  Definition count_general_implications''(p : Pattern) : option nat :=
    count_general_implications' (count_general_implications'_enough_fuel p) p.

  Definition count_general_implications (p : Pattern) :=
    let np := count_general_implications'' p in
    let Heqnp : np = count_general_implications'' p := erefl np in
    match np as o return (o = count_general_implications'' p → nat) with
    | Some p0 => λ _, p0
    | None =>
      λ Heqnp0 : None = count_general_implications'' p,
                 match (count_general_implications'_terminates p (eq_sym Heqnp0)) with end
    end Heqnp.

  Definition SizeRelation (p1 p2 : Pattern) : Prop :=
    size p1 < size p2.

  Lemma SizeRelation_wf : well_founded SizeRelation.
  Proof. apply well_founded_ltof. Defined.
  
  Definition GeneralImplicationCountRelation (p1 p2 : Pattern) : Prop :=
    count_general_implications p1 < count_general_implications p2.

  Lemma GeneralImplicationCountRelation_wf : well_founded GeneralImplicationCountRelation.
  Proof. apply well_founded_ltof. Defined.

  Definition CombinedRelation := lexprod Pattern (λ _ : Pattern, Pattern) GeneralImplicationCountRelation (λ _ : Pattern, SizeRelation).

  Lemma CombinedRelation_wf : well_founded CombinedRelation.
  Proof.
    apply (wf_lexprod
           Pattern
           (fun=> Pattern)
           GeneralImplicationCountRelation
           (fun=> SizeRelation)
           GeneralImplicationCountRelation_wf
           (fun=> SizeRelation_wf)
          ).
  Defined.
  
    
  Definition option_well_formed (op : option Pattern) : bool :=
    match op with
    | Some p => well_formed p
    | None => true
    end.

  Lemma option_well_formed_wf (op : option Pattern) (p : Pattern) :
    option_well_formed op ->
    op = Some p ->
    well_formed p.
  Proof.
    intros owf Hsome.
    destruct op; inversion Hsome. subst. simpl in owf. exact owf.
  Qed.
  
    
  Lemma option_bimap_and_wf oa ob:
    option_well_formed oa ->
    option_well_formed ob ->
    option_well_formed (option_bimap patt_and oa ob).
  Proof.
    intros Hoa Hob.
    destruct oa, ob; simpl in *; auto.
  Qed.
  

  Check sigT.
  Print sigT.
  Print CombinedRelation.
  Check existT.

  Lemma wf_negate' n p np:
    well_formed p ->
    negate' n p = Some np ->
    well_formed np.
  Proof.
    assert (forall x : {_ : Pattern & Pattern},
               let p := projT2 x in
                well_formed p -> forall n np, negate' n p = Some np -> well_formed np).
    {
      clear.
      apply (Fix CombinedRelation_wf (fun x => let p := projT2 x in
                                               well_formed p ->
                                               forall n np,
                                                 negate' n p = Some np ->
                                                 well_formed np)).
      simpl.
      intros x IH wfp n np Hsome.
      destruct x as [x0 x1]. simpl in *. rename x1 into p.
      destruct n; destruct p; unfold negate' in Hsome; try solve [(simpl in Hsome; inversion Hsome; auto)]; auto.
      fold negate' in Hsome.
      
      remember (match_and (p1 ---> p2)) as q1.
      remember (match_or (p1 ---> p2)) as q2.
      remember (match_not (p1 ---> p2)) as q3.
      pose proof (wfp1impp2 := wfp).
      unfold well_formed, well_formed_closed in wfp.
      simpl in wfp.
      apply andb_prop in wfp.
      destruct wfp as [wfp1 wfp2].
      apply andb_prop in wfp1. destruct wfp1 as [wfpp1 wfpp2].
      apply andb_prop in wfp2. destruct wfp2 as [wfcp1 wfcp2].
      assert (wfp1: well_formed p1).
      { unfold well_formed, well_formed_closed. rewrite wfpp1 wfcp1. reflexivity. }
      assert (wfp2: well_formed p2).
      { unfold well_formed, well_formed_closed. rewrite wfpp2 wfcp2. reflexivity. }

      (*
      simpl in Hsz. simpl in IHsz.
      assert (Hszp1: size p1 <= sz) by lia.
      assert (Hszp2: size p2 <= sz) by lia.
       *)
      destruct q1.
      { destruct p as [p1' p2'].
        remember (negate' n p1') as np1'.
        remember (negate' n p2') as np2'.
        symmetry in Heqq1.
        pose proof (H := match_and_size Heqq1).
        destruct H as [Hszp1' Hszp2'].
        
        destruct np1', np2'; simpl in Hsome; inversion Hsome.
        simpl.
        pose proof (H' := match_and_wf wfp1impp2 Heqq1).
        destruct H' as [wfp1' wfp2'].
        simpl in Hszp1'. simpl in Hszp2'.
        symmetry in Heqnp1'. symmetry in Heqnp2'.
        assert (HC1: CombinedRelation (existT x0 p1') (existT x0 (p1 ---> p2))).
        {
          unfold CombinedRelation.
          eapply right_lex. unfold SizeRelation. simpl. lia.
        }
        assert (HC2: CombinedRelation (existT x0 p2') (existT x0 (p1 ---> p2))).
        {
          unfold CombinedRelation.
          eapply right_lex. unfold SizeRelation. simpl. lia.
        }
        pose proof (IH1 := IH _ HC1 wfp1' _ _ Heqnp1').
        pose proof (IH2 := IH _ HC2 wfp2' _ _ Heqnp2').
        auto.
      }

      destruct q2.
      { destruct p as [q21 q22].
        symmetry in Heqq2.
        pose proof (H' := match_or_wf wfp1impp2 Heqq2).
        destruct H' as [wfq21 wfq22].
        eapply option_well_formed_wf.
        2: { apply Hsome. }

        pose proof (Hsome' := Hsome).
        unfold option_bimap in Hsome'.
        remember (negate' n q21) as nq21.
        remember (negate' n q22) as nq22.
        destruct nq21, nq22; inversion Hsome'. subst np. clear Hsome'.
        simpl.
        (* p, p0 are results of negate'. As such, they should be smaller???? *)
        Print negate'.
        pose proof (IHsz q21 wfq21).
        (* OLD COMMENT. Now it might somehow work. *)
        (* Oops. We cannot instantiate IHsz because we do not know whether q12 and q22 are smaller than sz.
         They may not be, because negate' can increase a size of a formula:
         it replaces a general implication with conjunction.
         *)
        
        
        admit.
      }
  Abort.
  
    
    
  
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
      + unfold negate.
        (* < magic > *)
        move: (erefl (negate'' (p1 ---> p2))).
        case: {1 3}(negate'' (p1 ---> p2)) => //.
        2: { intros e. destruct (negate'_terminates (p1 ---> p2) (eq_sym e)). }
        (* </magic > *)
        intros a Ha.
        unfold negate'',negate'_enough_fuel,negate' in Ha. fold negate' in Ha.
        remember (match_and (p1 ---> p2)) as q1.
        remember (match_or (p1 ---> p2)) as q2.
        remember (match_not (p1 ---> p2)) as q3.
        destruct q1.
        { destruct p as [p3 p4].
          pose proof (Hszp3p4 := match_and_size (eq_sym Heqq1)).
          simpl in Hszp3p4.
          destruct Hszp3p4 as [Hp3sz Hp4sz].
          rewrite -> negate'_monotone with (fuel := negate'_enough_fuel p3) in Ha.
          2: { lia. }
          2: { unfold negate'_enough_fuel. simpl. lia. }
          fold (negate'' p3) in Ha.
          rewrite -> negate'_monotone with (fuel := negate'_enough_fuel p4) in Ha.
          2: { lia. }
          2: { unfold negate'_enough_fuel. simpl. lia. }
          fold (negate'' p4) in Ha.
          unfold option_bimap in Ha.
          remember (negate'' p3) as q4.
          destruct q4.
          2: { inversion Ha. }
          remember (negate'' p4) as q5.
          destruct q5.
          2: { inversion Ha. }
          inversion Ha. clear Ha. subst a.
          symmetry in Heqq5. apply negate_from_negate'' in Heqq5. subst p0.
          symmetry in Heqq4. apply negate_from_negate'' in Heqq4. subst p.
          clear Hp4sz Hp3sz Heqq3 q3 Heqq2 q2.
          unfold match_and in Heqq1.
          unfold match_not in Heqq1.
          destruct p2; inversion Heqq1; clear Heqq1.
          remember (match_or p1) as q1.
          destruct q1.
          2: { inversion H0. }
          destruct p as [p5 p6].
          destruct p5; inversion H0; clear H0.
          destruct p5_2; inversion H1; clear H1.
          destruct p6; inversion H0; clear H0.
          destruct p6_2; inversion H1; clear H1.
          subst p5_1 p6_1.
          unfold match_or in Heqq1.
          destruct p1; inversion Heqq1; clear Heqq1.
          remember (match_not p1_1) as np1_1.
          destruct np1_1; inversion H0; subst.
          unfold match_not in Heqnp1_1. destruct p1_1; inversion Heqnp1_1; clear Heqnp1_1.
          destruct p1_1_2; inversion H1; clear H1. subst.
          clear H0.
          fold (patt_not p3) in *. fold (patt_not (patt_not p3)) in *.
          fold (patt_not p4) in *. fold (patt_or (patt_not p3) (patt_not p4)) in *.
          fold (patt_not (patt_or (patt_not p3) (patt_not p4))) in *.
          pose proof (Hwfp' := Hwfp).
          (* TODO automate this ugly thing *)
          unfold well_formed, well_formed_closed in Hwfp'. simpl in Hwfp'.
          rewrite !andbT in Hwfp'.
          apply andb_prop in Hwfp'. destruct Hwfp' as [Hwfp' Hwfc'].
          apply andb_prop in Hwfp'. destruct Hwfp' as [Hwfpp3 Hwfpp4].
          apply andb_prop in Hwfc'. destruct Hwfc' as [Hwfcp3 Hwfcp4].
          assert (Hwfp3: well_formed p3).
          { unfold well_formed, well_formed_closed. rewrite Hwfpp3 Hwfcp3. reflexivity. }
          assert (Hwfp4: well_formed p4).
          { unfold well_formed, well_formed_closed. rewrite Hwfpp4 Hwfcp4. reflexivity. }
          simpl in Hsz.
          pose proof (IHp3 := IHsz p3 ltac:(auto) ltac:(lia)).
          pose proof (IHp4 := IHsz p4 ltac:(auto) ltac:(lia)).

          remember (fresh_evar (¬ ¬ (¬ p3 or ¬ p4) <---> negate p3 or negate p4)) as star.
          Check prf_equiv_congruence_implicative_ctx.
          Search PatternCtx.
          remember (¬ ¬ (¬ p3 or ¬ p4) <---> (patt_free_evar star) or negate p4) as ctx'.
          assert (well_formed ctx'). { subst. auto 15. (*TODO we need well_formed (negate) *) *)
          eremember (@Build_PatternCtx _ star ctx' _) as ctx.
          simpl in Heqctx.
          
          (*Search evar.
          
          Print countable.Countable.*)
  Abort.
  

  (* TODO: a function [abstract : Pattern -> PropPattern] *)
End ml_tauto.
