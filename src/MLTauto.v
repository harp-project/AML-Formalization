From Coq Require Import ssreflect ssrfun ssrbool.
From Coq Require Import Ensembles Logic.Classical_Prop.
From Coq Require Import Arith.Wf_nat Relations.Relation_Operators Wellfounded.Lexicographic_Product.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq.micromega Require Import Lia.

From Equations Require Import Equations.
Show Obligation Tactic.

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

Global Set Transparent Obligations.
Derive NoConfusion for Pattern.
Derive Subterm for Pattern.


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

  (*
  Fixpoint and_or_size' (fuel : nat) (p : Pattern) : option nat :=
    match fuel with
    | 0 => None
    | S fuel' =>
      match (match_and p) with
      | Some (p1, p2) => S <$> (option_bimap plus (and_or_size' fuel' p1) (and_or_size' fuel' p2))
      | None =>
        match (match_or p) with
        | Some (p1, p2) => S <$> (option_bimap plus (and_or_size' fuel' p1) (and_or_size' fuel' p2))
        | None =>
          match (match_not p) with
          | Some p' => and_or_size' fuel' p'
          | None =>
            match p with
            | p1 ---> p2
              => (* we treat the implication as [¬(p1 and ¬p2)], or as [¬ p1 or p2] -
                    that is, there is one and/or connective *)
              S <$> (option_bimap plus (and_or_size' fuel' p1) (and_or_size' fuel' p2))
            | _ => Some 1
            end
          end
        end
      end
    end.


  Check existT.
  Print existT.
  Print Decision.
  Check sum.
  Print sum.

  Print Decision.
   *)

  Equations e_match_not (p : Pattern)
    : ({ p' : Pattern & p = patt_not p'}) + (forall p', p <> patt_not p')
    :=
      e_match_not (p' ---> ⊥) := inl _ ;
      e_match_not _ := inr _ .
  Solve Obligations with Tactics.program_simplify; CoreTactics.equations_simpl.
  Next Obligation.
    intros. eapply existT. reflexivity.
  Defined.
  
  (*
  Lemma e_match_not (p : Pattern) : ({ p' : Pattern & p = patt_not p'}) + (forall p', p <> patt_not p').
  Proof.
    destruct p; try (right;intros;discriminate).
    destruct p2;try (right;intros;discriminate).
    left.
    eapply existT. reflexivity.
  Defined.
   *)
  
  Lemma e_match_not_patt_not p: is_inl (e_match_not (patt_not p)).
  Proof.
    funelim (e_match_not _). simpl. reflexivity.
  Qed.

  Equations e_match_or (p : Pattern)
    : ({ p1 : Pattern & {p2 : Pattern & p = patt_or p1 p2}}) + (forall p1 p2, p <> patt_or p1 p2)
    :=
      e_match_or (p1 ---> p2) with e_match_not p1 => {
        | inl (existT p1' e) => inl _
        | inr _ => inr _
      } ;      
      e_match_or _ := inr _.
  Solve Obligations with Tactics.program_simplify; CoreTactics.equations_simpl.
  Next Obligation.
    intros. inversion e. subst. eapply existT. eapply existT. reflexivity.
  Defined.
  Next Obligation.
    intros.
    unfold patt_or.
    assert (p1 <> patt_not p0). auto.
    congruence.
  Defined.  

  (*
  Lemma e_match_or (p : Pattern) :
    ({ p1 : Pattern & {p2 : Pattern & p = patt_or p1 p2}})
    + (forall p1 p2, p <> patt_or p1 p2).
  Proof.
    destruct p; try (right;intros;discriminate).
    pose proof (X := e_match_not p1).
    destruct X.
    2: { right. intros. unfold patt_or.
         assert (p1 <> patt_not p0). auto.
         congruence.
    }
    destruct s. subst.
    left.
    eapply existT. eapply existT. reflexivity.
  Defined.
  *)

  Lemma e_match_or_patt_or p1 p2: is_inl (e_match_or (patt_or p1 p2)).
  Proof. reflexivity. Qed.

  Equations?  e_match_and (p : Pattern)
    : ({ p1 : Pattern & {p2 : Pattern & p = patt_and p1 p2}}) + (forall p1 p2, p <> patt_and p1 p2)
    :=
      e_match_and p with e_match_not p => {
        | inr _ := inr _ ;
        | inl (existT p' e') with e_match_or p' => {
            | inr _ := inr _ ;
            | inl (existT p1 (existT p2 e12)) with e_match_not p1 => {
                | inr _ := inr _ ;
                | inl (existT np1 enp1) with e_match_not p2 => {
                    | inr _ := inr _ ;
                    | inl (existT np2 enp2) := inl _
                  }
              }
          }                                        
      }.
  Proof.
    - subst. eapply existT. eapply existT. reflexivity.
    - subst. intros. unfold not. intros Hcontra. inversion Hcontra.
      subst. specialize (n p0). contradiction.
    - subst. intros. unfold not. intros Hcontra. inversion Hcontra.
      subst. specialize (n p0). contradiction.
    - subst. intros. unfold not. intros Hcontra. inversion Hcontra.
      subst. specialize (n (patt_not p1) (patt_not p2)). contradiction.
    - intros. unfold not. intros Hcontra. subst.
      specialize (n ((patt_or (patt_not p1) (patt_not p2)))). contradiction.
  Defined.
  (*
  
  Lemma e_match_and (p : Pattern) :
    ({ p1 : Pattern & {p2 : Pattern & p = patt_and p1 p2}})
    + (forall p1 p2, p <> patt_and p1 p2).
  Proof.
    pose proof (X := e_match_not p).
    destruct X.
    2: {
      right. intros. firstorder.
    }
    destruct s. subst p.

    pose proof (Y := e_match_or x).
    destruct Y.
    2: {
      right. intros. unfold patt_and.
      specialize (n (patt_not p1) (patt_not p2)).
      intros Hcontra. inversion Hcontra. contradiction.
    }
    destruct s. destruct s. subst x.

    pose proof (Z := e_match_not x0).
    destruct Z.
    2: {
      right. intros. unfold not. intros Hcontra.
      inversion Hcontra. subst. specialize (n p1). contradiction.
    }

    pose proof (T := e_match_not x1).
    destruct T.
    2: {
      right. intros. unfold not. intros Hcontra.
      inversion Hcontra. subst. specialize (n p2). contradiction.
    }

    destruct s, s0. subst.
    left. eapply existT. eapply existT. reflexivity.
  Defined.
   *)
  

  Lemma e_match_and_patt_and p1 p2: is_inl (e_match_and (patt_and p1 p2)).
  Proof. reflexivity. Qed.

  Lemma e_match_and_patt_or p1 p2: is_inl (e_match_and (patt_or p1 p2)) = false.
  Proof.
    funelim (e_match_and _); try reflexivity.
    subst. inversion e'.
  Qed.

  Equations e_match_imp (p : Pattern)
    : ({ p1 : Pattern & {p2 : Pattern & p = patt_imp p1 p2}}) + (forall p1 p2, p <> patt_imp p1 p2)
    :=
      e_match_imp (p1 ---> p2) := inl _ ;
      e_match_imp _ := inr _.
  Solve Obligations with Tactics.program_simplify; CoreTactics.equations_simpl.
  Next Obligation.
    intros. eapply existT. eapply existT. reflexivity.
  Defined.

  Equations e_and_or_imp_size (p : Pattern) : nat by wf p (Pattern_subterm Σ) :=
    e_and_or_imp_size p with e_match_and p => {
      | inl (existT p1' (existT p2' e)) := 1 + (e_and_or_imp_size p1') + (e_and_or_imp_size p2') ;
      | inr _ 
          with e_match_or p => {
            | inl (existT p1' (existT p2' e)) := 1 + (e_and_or_imp_size p1') + (e_and_or_imp_size p2') ;
            | inr _
                with e_match_not p => {
                | inl (existT p1' e) := e_and_or_imp_size p1' ;
                | inr _
                  with e_match_imp p => {
                    | inl (existT p1 (existT p2 _)) := 1 + (e_and_or_imp_size p1) + (e_and_or_imp_size p2) ;
                    | inr _ => 0
                  }
              }                                        
        }
    }.
  Solve All Obligations with
      (intros; Tactics.program_simplify; CoreTactics.equations_simpl; try Tactics.program_solve_wf).

  (*Transparent e_and_or_imp_size.*)

  Compute (e_and_or_imp_size ((patt_bound_evar 0) and (patt_bound_evar 1))).
  Example ex1: e_and_or_imp_size ((patt_bound_evar 0) and (patt_bound_evar 1)) = 1.
  Proof.
    (* [reflexivity] just works, but we want to test the functional elimination principle *)
    (* reflexivity. *)

    funelim (e_and_or_imp_size _).
    - inversion e. subst.
      repeat simp e_and_or_imp_size.
      simp e_match_and.
      simp e_match_not.
      simpl e_match_and_clause_1.
      simpl e_and_or_imp_size_unfold_clause_1.
      simp e_match_or.
      simpl e_and_or_imp_size_unfold_clause_1_clause_2.
      simp e_match_not.
      simpl e_and_or_imp_size_unfold_clause_1_clause_2_clause_2.
      simp e_match_imp.
      simpl e_and_or_imp_size_unfold_clause_1_clause_2_clause_2_clause_2.
      lia.
    - inversion Heq0.
    - inversion Heq1.
    - inversion Heq2.
    - inversion Heq2.
  Qed.


  Equations e_negate (p : Pattern) : Pattern by wf p (Pattern_subterm Σ) :=
    e_negate p with e_match_and p => {
      | inl (existT p1' (existT p2' e)) := patt_or (e_negate p1') (e_negate p2') ;
      | inr _
          with e_match_or p => {
          | inl (existT p1' (existT p2' e)) := patt_and (e_negate p1') (e_negate p2') ;
          | inr _
              with e_match_not p => {
              | inl (existT p1' e) := p1';
              | inr _
                  with e_match_imp p => {
                  | inl (existT p1 (existT p2 _)) := patt_and p1 (e_negate p2) ;
                  | inr _ => patt_not p
                }
            }
        }
    }.
  Solve Obligations with
      (Tactics.program_simplify; CoreTactics.equations_simpl; try Tactics.program_solve_wf).

  Example simple: e_negate ((patt_bound_evar 0) and (patt_bound_evar 1)) =
                  patt_or (patt_not (patt_bound_evar 0)) (patt_not (patt_bound_evar 1)).
  Proof.
    reflexivity.
  Qed.

  
  (* This is an alternative function measuring the size of a pattern.
     The advantage is that the result is never zero, and therefore
     when doing induction on the size' of a pattern, the base cases are all trivially
     solvable by lia.
   *)
  Fixpoint size' (p : Pattern) : nat :=
    match p with
    | ls $ rs | ls ---> rs => 1 + size' ls + size' rs
    | ex , p' | mu , p' => 1 + size' p'
    | _ => 1
    end.
  
  Lemma inr_impl_not_is_inl {A B : Type} (x : A + B) (b : B) :
    x = inr b ->
    is_inl x = false.
  Proof.
    intros. rewrite H. reflexivity.
  Qed.

  Ltac solve_match_impossibilities :=
    repeat (
        match goal with
        | H : e_match_or (patt_or ?A ?B) = inr _ |- _
          =>
          let HC1 := fresh "HC1" in
          pose proof (HC1 := e_match_or_patt_or A B);
          pose proof (HC2 := (inr_impl_not_is_inl _ _ H));
          rewrite HC1 in HC2;
          inversion HC2
        | H : e_match_and (patt_and ?A ?B) = inr _ |- _
          =>
          let HC1 := fresh "HC1" in
          pose proof (HC1 := e_match_and_patt_and A B);
          pose proof (HC2 := (inr_impl_not_is_inl _ _ H));
          rewrite HC1 in HC2;
          inversion HC2
        end
      ).


  Lemma wf_e_negate p:
    well_formed p ->
    well_formed (e_negate p).
  Proof.
    intros wfp.
    remember (size' p) as sz.
    assert (Hsz : size' p <= sz).
    { lia. }
    clear Heqsz.
    move: p Hsz wfp.
    induction sz; intros p Hsz wfp; destruct p; simpl in *; try lia;
      funelim (e_negate _); auto; try inversion e; subst.
    - simpl in Hsz.
      unfold well_formed, well_formed_closed in wfp.
      simpl in wfp.

      rewrite !andbT in wfp.
      apply andb_prop in wfp. destruct wfp as [wfp1 wfp2].
      apply andb_prop in wfp1. destruct wfp1 as [wfp11 wfp12].
      apply andb_prop in wfp2. destruct wfp2 as [wfp21 wfp22].
      assert (well_formed p1').
      { unfold well_formed, well_formed_closed. rewrite wfp11 wfp21. reflexivity. }
      assert (well_formed p2').
      { unfold well_formed, well_formed_closed. rewrite wfp12 wfp22. reflexivity. }
      pose proof (IHsz p1' ltac:(lia) H1).
      pose proof (IHsz p2' ltac:(lia) H2).
      auto.
    - simpl in Hsz.
      unfold well_formed, well_formed_closed in wfp.
      simpl in wfp.
      rewrite !andbT in wfp.
      apply andb_prop in wfp. destruct wfp as [wfp1 wfp2].
      apply andb_prop in wfp1. destruct wfp1 as [wfp11 wfp12].
      apply andb_prop in wfp2. destruct wfp2 as [wfp21 wfp22].
      assert (well_formed p1').
      { unfold well_formed, well_formed_closed. rewrite wfp11 wfp21. reflexivity. }
      assert (well_formed p2').
      { unfold well_formed, well_formed_closed. rewrite wfp12 wfp22. reflexivity. }
      pose proof (IHsz p1' ltac:(lia) H1).
      pose proof (IHsz p2' ltac:(lia) H2).
      auto.
    - simpl.
      unfold well_formed, well_formed_closed in wfp.
      simpl in wfp.
      rewrite !andbT in wfp.
      fold (well_formed_closed p1') in wfp.
      fold (well_formed p1') in wfp.
      auto.
    - unfold well_formed, well_formed_closed in wfp.
      simpl in wfp.
      apply andb_prop in wfp. destruct wfp as [wfp1 wfp2].
      apply andb_prop in wfp1. destruct wfp1 as [wfp11 wfp12].
      apply andb_prop in wfp2. destruct wfp2 as [wfp21 wfp22].
      assert (well_formed p1).
      { unfold well_formed, well_formed_closed. rewrite wfp11 wfp21. reflexivity. }
      assert (well_formed p2).
      { unfold well_formed, well_formed_closed. rewrite wfp12 wfp22. reflexivity. }
      pose proof (IHsz p2 ltac:(lia) H1).
      auto.
  Qed.

  #[local] Hint Resolve wf_e_negate : core.
  

  Lemma negate_count_evar_occurrences p x :
    count_evar_occurrences x (e_negate p) = count_evar_occurrences x p.
  Proof.
    remember (size' p) as sz.
    assert (Hsz: size' p <= sz).
    { lia. }
    clear Heqsz.
    move: p Hsz.
    induction sz; intros p Hsz; destruct p; simpl in Hsz; try lia;
      funelim (e_negate _); try inversion e; subst; simpl; auto.
    - simpl in Hsz. rewrite IHsz. lia. rewrite IHsz. lia. lia.
    - simpl in Hsz. rewrite IHsz. lia. rewrite IHsz. lia. lia.
    - simpl in Hsz. rewrite IHsz. lia. lia.
  Qed.

  (*
  Check prf_equiv_congruence_implicative_ctx.
  Lemma prf_equiv_congruence_implicative_ctx_alt Γ:
    forall (C : PatternCtx),
      is_implicative_context C ->
      forall (p q : Pattern),
        well_formed p ->
        well_formed q *)

  (* So that we can do: [apply (Modus_ponens_alt _ _ _ Hctx); auto] *)
  Lemma Modus_ponens_alt Γ phi1 phi2:
    Γ ⊢ (phi1 ---> phi2) ->
    well_formed phi1 ->
    well_formed (phi1 ---> phi2) ->
    Γ ⊢ phi1 ->
    Γ ⊢ phi2.
  Proof.
    intros.
    eapply Modus_ponens. 4: apply H. all: auto.
  Qed. 

  Lemma negate_equiv (p : Pattern) :
    well_formed p ->
    (Empty_set _) ⊢ ((patt_not p) <---> (e_negate p)).
  Proof.
    intros Hwfp.
    remember (size' p) as sz.
    assert (Hsz: size' p <= sz).
    { lia. }
    clear Heqsz.


    Tactic Notation "make_step" ident(star) constr(p) constr(q) constr(ctx_expr) tactic(simpl_tactic) :=
      set (ctx' := ctx_expr);
      assert (wfctx': well_formed ctx');          
      [unfold ctx'; unfold patt_iff; auto 15|];
      assert (countstar: count_evar_occurrences star ctx' = 1);
      [unfold ctx'; simpl; destruct (evar_eqdec star star); [|contradiction];
       simpl; rewrite ?negate_count_evar_occurrences;
       simpl_tactic;
       (*          rewrite ?Hcount_p1' Hcount_p2';*)
       lia|
      ];
      set (ctx := (@Build_PatternCtx _ star ctx' wfctx' countstar));
      assert (Himpl: is_implicative_context ctx);
      [ unfold ctx; unfold is_implicative_context;
        rewrite [pcEvar _]/=; rewrite [pcPattern _]/=;
                unfold ctx';
        unfold patt_and; unfold patt_not at 1;
        unfold is_implicative_context';
        (* This generates a long goal. We need some better reasoning about this. *)
        cbn;
        simpl_tactic;
        (*rewrite Hcount_p1' Hcount_p2' Hcount_np1' Hcount_np2'.*)
        destruct (evar_eqdec star star); [|contradiction];
        simpl;
        reflexivity
       |];
      assert (Hctx: (Empty_set Pattern ⊢ (emplace ctx p <---> emplace ctx q)));
      [apply prf_equiv_congruence_implicative_ctx;auto|];
      apply pf_iff_proj1 in Hctx;
      [idtac|apply well_formed_free_evar_subst; auto|apply well_formed_free_evar_subst; auto];
      unfold ctx in Hctx; unfold ctx' in Hctx; simpl in Hctx; unfold emplace in Hctx; simpl in Hctx;
      destruct (evar_eqdec star star); [|contradiction]; simpl in Hctx;
      repeat (rewrite -> free_evar_subst_no_occurrence in Hctx by assumption);
      simpl in Hctx;
      apply (Modus_ponens_alt _ _ _ Hctx); auto 20
    .

    
    move: p Hwfp Hsz.
    induction sz; intros p Hwfp Hsz; destruct p; simpl in Hsz; try lia;
      funelim (e_negate _); try inversion e; subst;
        try apply pf_iff_equiv_refl; auto.
    - unfold well_formed, well_formed_closed in Hwfp.
      simpl in Hwfp.
      rewrite !andbT in Hwfp.
      apply andb_prop in Hwfp. destruct Hwfp as [Hwf1 Hwf2].
      apply andb_prop in Hwf1. destruct Hwf1 as [Hwf11 Hwf12].
      apply andb_prop in Hwf2. destruct Hwf2 as [Hwf21 Hwf22].
      assert (wfp1': well_formed p1').
      { unfold well_formed, well_formed_closed. rewrite Hwf11 Hwf21. reflexivity. }
      assert (wfp2': well_formed p2').
      { unfold well_formed, well_formed_closed. rewrite Hwf12 Hwf22. reflexivity. }

      simpl in Hsz.
      pose proof (IHp1' := IHsz p1' ltac:(auto) ltac:(lia)).
      pose proof (IHp2' := IHsz p2' ltac:(auto) ltac:(lia)).

      assert(Hwfnegp1': well_formed (e_negate p1')).
      { auto. }
      assert(Hwfnegp2': well_formed (e_negate p2')).
      { auto. }
      assert(Hwfnp1': well_formed (patt_not p1')).
      { auto. }
      assert(Hwfnp2': well_formed (patt_not p2')).
      { auto. }

      remember (fresh_evar (¬ ((¬ p1' or ¬ p2') ---> ⊥) <---> e_negate p1' or e_negate p2')) as star.

      assert (Hcount_p1': count_evar_occurrences star p1' = 0).
      {
        rewrite count_evar_occurrences_0.
        subst.
        eapply evar_is_fresh_in_richer'.
        2: apply set_evar_fresh_is_fresh'.
        solve_free_evars_inclusion 5.
        reflexivity.
      }

      assert (Hcount_p2': count_evar_occurrences star p2' = 0).
      {
        rewrite count_evar_occurrences_0.
        subst.
        eapply evar_is_fresh_in_richer'.
        2: apply set_evar_fresh_is_fresh'.
        solve_free_evars_inclusion 5.
        reflexivity.
      }

      assert (Hcount_np1': count_evar_occurrences star (e_negate p1') = 0).
      { rewrite negate_count_evar_occurrences. apply Hcount_p1'. }

      assert (Hcount_np2': count_evar_occurrences star (e_negate p2') = 0).
      { rewrite negate_count_evar_occurrences. apply Hcount_p2'. }
      
      unfold patt_iff. unfold patt_iff in Heqstar.
      
      assert (Step1: (Empty_set Pattern ⊢
                                ((¬ (¬ p1' or ¬ p2' ---> ⊥) ---> (¬ p1') or e_negate p2')
                                   and (e_negate p1' or e_negate p2' ---> ¬ (¬ p1' or ¬ p2' ---> ⊥)))
                     ->
                     (Empty_set Pattern ⊢ ((¬ (¬ p1' or ¬ p2' ---> ⊥) ---> e_negate p1' or e_negate p2')
                                             and (e_negate p1' or e_negate p2' ---> ¬ (¬ p1' or ¬ p2' ---> ⊥)))))
             ).
      {
        intros BigH.
        

        make_step
          star
          (¬ p1')
          (e_negate p1')
          ((¬ (¬ p1' or ¬ p2' ---> ⊥) ---> (patt_free_evar star) or e_negate p2')
             and (e_negate p1' or e_negate p2' ---> ¬ (¬ p1' or ¬ p2' ---> ⊥)))
          (rewrite ?Hcount_p1' ?Hcount_p2' ?Hcount_np1' ?Hcount_np2')
        .
      }
      apply Step1. clear Step1.

      assert (Step2: (Empty_set Pattern ⊢
                                ((¬ (¬ p1' or ¬ p2' ---> ⊥) ---> (¬ p1') or ¬ p2')
                                   and (e_negate p1' or e_negate p2' ---> ¬ (¬ p1' or ¬ p2' ---> ⊥)))
                     ->
                     (Empty_set Pattern ⊢ ((¬ (¬ p1' or ¬ p2' ---> ⊥) ---> ¬ p1' or e_negate p2')
                                             and (e_negate p1' or e_negate p2' ---> ¬ (¬ p1' or ¬ p2' ---> ⊥)))))
             ).
      {
        intros BigH.

        make_step
          star
          (¬ p2')
          (e_negate p2')
          ((¬ (¬ p1' or ¬ p2' ---> ⊥) ---> ¬ p1' or (patt_free_evar star))
             and (e_negate p1' or e_negate p2' ---> ¬ (¬ p1' or ¬ p2' ---> ⊥)))
          (rewrite ?Hcount_p1' ?Hcount_p2' ?Hcount_np1' ?Hcount_np2')
        .
      }
      apply Step2. clear Step2.

      assert (Step3: (Empty_set Pattern ⊢
                                ((¬ (¬ p1' or ¬ p2' ---> ⊥) ---> (¬ p1') or ¬ p2')
                                   and (¬ p1' or e_negate p2' ---> ¬ (¬ p1' or ¬ p2' ---> ⊥)))
                      ->
                      (Empty_set Pattern ⊢ ((¬ (¬ p1' or ¬ p2' ---> ⊥) ---> ¬ p1' or ¬ p2')
                                              and (e_negate p1' or e_negate p2' ---> ¬ (¬ p1' or ¬ p2' ---> ⊥)))))
             ).
      {
        intros BigH.

        make_step
          star
          (¬ p1')
          (e_negate p1')
          ((¬ (¬ p1' or ¬ p2' ---> ⊥) ---> ¬ p1' or ¬ p2')
             and ((patt_free_evar star) or e_negate p2' ---> ¬ (¬ p1' or ¬ p2' ---> ⊥)))
          (rewrite ?Hcount_p1' ?Hcount_p2' ?Hcount_np1' ?Hcount_np2')
        .          
      }
      apply Step3. clear Step3.


      assert (Step4: (Empty_set Pattern ⊢
                                ((¬ (¬ p1' or ¬ p2' ---> ⊥) ---> (¬ p1') or ¬ p2')
                                   and (¬ p1' or ¬ p2' ---> ¬ (¬ p1' or ¬ p2' ---> ⊥)))
                      ->
                      (Empty_set Pattern ⊢ ((¬ (¬ p1' or ¬ p2' ---> ⊥) ---> ¬ p1' or ¬ p2')
                                              and (¬ p1' or e_negate p2' ---> ¬ (¬ p1' or ¬ p2' ---> ⊥)))))
             ).
      {
        intros BigH.

        make_step
          star
          (¬ p2')
          (e_negate p2')
          ((¬ (¬ p1' or ¬ p2' ---> ⊥) ---> ¬ p1' or ¬ p2')
             and (¬ p1' or (patt_free_evar star) ---> ¬ (¬ p1' or ¬ p2' ---> ⊥)))
          (rewrite ?Hcount_p1' ?Hcount_p2' ?Hcount_np1' ?Hcount_np2')
        .          
      }
      apply Step4. clear Step4.

      apply conj_intro_meta; auto.
      + apply not_not_elim. auto.
      + apply not_not_intro. auto.
    - (*(¬ (¬ p1' ---> p2') <---> e_negate p1' and e_negate p2') *)

      unfold well_formed, well_formed_closed in Hwfp.
      simpl in Hwfp.
      rewrite !andbT in Hwfp.
      apply andb_prop in Hwfp. destruct Hwfp as [Hwf1 Hwf2].
      apply andb_prop in Hwf1. destruct Hwf1 as [Hwf11 Hwf12].
      apply andb_prop in Hwf2. destruct Hwf2 as [Hwf21 Hwf22].
      assert (wfp1': well_formed p1').
      { unfold well_formed, well_formed_closed. rewrite Hwf11 Hwf21. reflexivity. }
      assert (wfp2': well_formed p2').
      { unfold well_formed, well_formed_closed. rewrite Hwf12 Hwf22. reflexivity. }

      simpl in Hsz.
      pose proof (IHp1' := IHsz p1' ltac:(auto) ltac:(lia)).
      pose proof (IHp2' := IHsz p2' ltac:(auto) ltac:(lia)).

      assert(Hwfnegp1': well_formed (e_negate p1')).
      { auto. }
      assert(Hwfnegp2': well_formed (e_negate p2')).
      { auto. }
      assert(Hwfnp1': well_formed (patt_not p1')).
      { auto. }
      assert(Hwfnp2': well_formed (patt_not p2')).
      { auto. }

      remember (fresh_evar (¬ (¬ p1' ---> p2') <---> e_negate p1' and e_negate p2')) as star.

      assert (Hcount_p1': count_evar_occurrences star p1' = 0).
      {
        rewrite count_evar_occurrences_0.
        subst.
        eapply evar_is_fresh_in_richer'.
        2: apply set_evar_fresh_is_fresh'.
        solve_free_evars_inclusion 5.
        reflexivity.
      }

      assert (Hcount_p2': count_evar_occurrences star p2' = 0).
      {
        rewrite count_evar_occurrences_0.
        subst.
        eapply evar_is_fresh_in_richer'.
        2: apply set_evar_fresh_is_fresh'.
        solve_free_evars_inclusion 5.
        reflexivity.
      }

      assert (Hcount_np1': count_evar_occurrences star (e_negate p1') = 0).
      { rewrite negate_count_evar_occurrences. apply Hcount_p1'. }

      assert (Hcount_np2': count_evar_occurrences star (e_negate p2') = 0).
      { rewrite negate_count_evar_occurrences. apply Hcount_p2'. }
      
      unfold patt_iff. unfold patt_iff in Heqstar.

      assert (Step1: (Empty_set Pattern ⊢
                                ((¬ (¬ p1' ---> p2') ---> ¬ p1' and e_negate p2')
                                   and (e_negate p1' and e_negate p2' ---> ¬ (¬ p1' ---> p2'))))
                     ->
                      (Empty_set Pattern ⊢
                                ((¬ (¬ p1' ---> p2') ---> e_negate p1' and e_negate p2')
                                   and (e_negate p1' and e_negate p2' ---> ¬ (¬ p1' ---> p2'))))
                                
             ).
      {
        intros BigH.

        make_step
          star
          (¬ p1')
          (e_negate p1')
          ((¬ (¬ p1' ---> p2') ---> (patt_free_evar star) and e_negate p2')
             and (e_negate p1' and e_negate p2' ---> ¬ (¬ p1' ---> p2')))
          (rewrite ?Hcount_p1' ?Hcount_p2' ?Hcount_np1' ?Hcount_np2')
        .
      }
      apply Step1. clear Step1.

      assert (Step2: (Empty_set Pattern ⊢
                                ((¬ (¬ p1' ---> p2') ---> ¬ p1' and ¬ p2')
                                   and (e_negate p1' and e_negate p2' ---> ¬ (¬ p1' ---> p2'))))
                     ->
                      (Empty_set Pattern ⊢
                                ((¬ (¬ p1' ---> p2') ---> ¬ p1' and e_negate p2')
                                   and (e_negate p1' and e_negate p2' ---> ¬ (¬ p1' ---> p2'))))
                                
             ).
      {
        intros BigH.

        make_step
          star
          (¬ p2')
          (e_negate p2')
          ((¬ (¬ p1' ---> p2') ---> ¬ p1' and (patt_free_evar star))
             and (e_negate p1' and e_negate p2' ---> ¬ (¬ p1' ---> p2')))
          (rewrite ?Hcount_p1' ?Hcount_p2' ?Hcount_np1' ?Hcount_np2')
        .
      }
      apply Step2. clear Step2.

      assert (Step3: (Empty_set Pattern ⊢
                                ((¬ (¬ p1' ---> p2') ---> ¬ p1' and ¬ p2')
                                   and (¬ p1' and e_negate p2' ---> ¬ (¬ p1' ---> p2'))))
                     ->
                      (Empty_set Pattern ⊢
                                ((¬ (¬ p1' ---> p2') ---> ¬ p1' and ¬ p2')
                                   and (e_negate p1' and e_negate p2' ---> ¬ (¬ p1' ---> p2'))))
                                
             ).
      {
        intros BigH.

        make_step
          star
          (¬ p1')
          (e_negate p1')
          ((¬ (¬ p1' ---> p2') ---> ¬ p1' and ¬ p2')
             and ((patt_free_evar star) and e_negate p2' ---> ¬ (¬ p1' ---> p2')))
          (rewrite ?Hcount_p1' ?Hcount_p2' ?Hcount_np1' ?Hcount_np2')
        .
      }
      apply Step3. clear Step3.

      assert (Step4: (Empty_set Pattern ⊢
                                ((¬ (¬ p1' ---> p2') ---> ¬ p1' and ¬ p2')
                                   and (¬ p1' and ¬ p2' ---> ¬ (¬ p1' ---> p2'))))
                     ->
                      (Empty_set Pattern ⊢
                                ((¬ (¬ p1' ---> p2') ---> ¬ p1' and ¬ p2')
                                   and (¬ p1' and e_negate p2' ---> ¬ (¬ p1' ---> p2'))))
                                
             ).
      {
        intros BigH.

        make_step
          star
          (¬ p2')
          (e_negate p2')
          ((¬ (¬ p1' ---> p2') ---> ¬ p1' and ¬ p2')
             and ( ¬ p1' and (patt_free_evar star) ---> ¬ (¬ p1' ---> p2')))
          (rewrite ?Hcount_p1' ?Hcount_p2' ?Hcount_np1' ?Hcount_np2')
        .
      }
      apply Step4. clear Step4.
      apply and_of_negated_iff_not_impl; auto.
    - 
      
      
  Abort.
  


  
  Lemma e_and_or_imp_size_bott:
    e_and_or_imp_size ⊥ = 0.
  Proof.
    reflexivity.
  Qed.
  
  Lemma e_and_or_imp_size_or p q:
    e_and_or_imp_size (patt_or p q) = 1 + e_and_or_imp_size p + e_and_or_imp_size q.
  Proof.
    funelim (e_and_or_imp_size (p or q)).
    - inversion e.
    - inversion e. subst.
      reflexivity.
    - solve_match_impossibilities.
    - solve_match_impossibilities.
    - solve_match_impossibilities.
  Qed.
  
  
  Lemma e_and_or_imp_size_not p:
    e_and_or_imp_size (patt_not p) = e_and_or_imp_size p.
  Proof.
    remember (size' p) as sz.
    assert (Hsz : size' p <= sz).
    { lia. }
    clear Heqsz.

    move: p Hsz.
    induction sz; intros p Hsz; destruct p; simpl in *; try lia;
      funelim (e_and_or_imp_size _); inversion Heq; try reflexivity.
    - inversion e. subst.
      funelim (e_and_or_imp_size (¬ ¬ p1' ---> ¬ p2')).
      + inversion e.
      + inversion e. subst.
        simpl in Hsz.
        rewrite IHsz. lia.
        rewrite IHsz. lia.
        reflexivity.
      + inversion e.
      + inversion e. subst.
        simpl in Hsz.
        rewrite IHsz. simpl. lia.
        rewrite IHsz. lia.
        rewrite IHsz. lia.
        reflexivity.
      + fold (patt_or (patt_not p1') (patt_not p2')) in Heq1.
        solve_match_impossibilities.
    - inversion e. subst.
      funelim (e_and_or_imp_size (p1' ---> ⊥)).
      + inversion e. subst.
        rewrite e_and_or_imp_size_bott.
        rewrite e_and_or_imp_size_or.
        simpl in Hsz.
        rewrite IHsz. lia.
        rewrite IHsz. lia.
        (* Oops. This does not hold! *)
  Abort.
  
          
  
  Lemma and_or_imp_size_negate p:
    e_and_or_imp_size (e_negate p) = e_and_or_imp_size p.
  Proof.
    remember (size' p) as sz.
    assert (Hsz : size' p <= sz).
    { lia. }
    clear Heqsz.

    move: p Hsz.
    induction sz; intros p Hsz; destruct p; simpl in *; try lia.
    - funelim (e_negate _); inversion Heq.
      funelim (e_and_or_imp_size _); inversion Heq.
      reflexivity.
    - funelim (e_negate _); inversion Heq.
      funelim (e_and_or_imp_size _); inversion Heq.
      reflexivity.
    - funelim (e_negate _); inversion Heq.
      funelim (e_and_or_imp_size _); inversion Heq.
      reflexivity.
    - funelim (e_negate _); inversion Heq.
      funelim (e_and_or_imp_size _); inversion Heq.
      reflexivity.
    - funelim (e_negate _); inversion Heq.
      funelim (e_and_or_imp_size _); inversion Heq.
      reflexivity.
    - funelim (e_negate _); inversion Heq.
      funelim (e_and_or_imp_size _); inversion Heq.
      reflexivity.
    - funelim (e_negate _); inversion Heq.
      funelim (e_and_or_imp_size _); inversion Heq.
      reflexivity.
    - funelim (e_negate _).
      + funelim (e_and_or_imp_size _).
        * pose proof (H3 := e_match_and_patt_or (e_negate p1'0) (e_negate p2'0)).
          assert (H4 : is_inl (e_match_and (e_negate p1'0 or e_negate p2'0))).
          { rewrite Heq. reflexivity. }
          rewrite H3 in H4. inversion H4.
        * funelim (e_and_or_imp_size (¬ p1'0 or ¬ p2'0 ---> ⊥)).
          -- simpl in Hsz.
             rewrite IHsz. lia. rewrite IHsz. lia.
             inversion e. reflexivity.
          -- inversion e.
          -- inversion e. subst.
             pose proof (e_match_and_patt_and (p1'0) (p2'0)).
             assert (is_inl (e_match_and (¬ p1'0 or ¬ p2'0 ---> ⊥)) = false).
             { rewrite Heq1. reflexivity. }
             rewrite H4 in H5.
             inversion H5.
          -- inversion e. subst.
             pose proof (e_match_and_patt_and (p1'0) (p2'0)).
             assert (is_inl (e_match_and (¬ p1'0 or ¬ p2'0 ---> ⊥)) = false).
             { rewrite Heq2. reflexivity. }
             rewrite -> H5 in H6.
             inversion H6.
          -- pose proof (e_match_and_patt_and (p1'0) (p2'0)).
             assert (is_inl (e_match_and (¬ p1'0 or ¬ p2'0 ---> ⊥)) = false).
             { rewrite Heq2. reflexivity. }
             rewrite H3 in H4.
             inversion H4.
        * pose proof (e_match_or_patt_or (e_negate p1'0) (e_negate p2')).
          assert (is_inl (e_match_or (e_negate p1'0 or e_negate p2')) = false).
          { rewrite Heq0. reflexivity. }
          rewrite H2 in H3.
          inversion H3.
        * inversion e. subst.
          simpl in Hsz.
          rewrite IHsz. lia.
          funelim (e_and_or_imp_size (¬ p1' or ¬ p2' ---> ⊥)).
          -- inversion e. subst.
             pose proof (HC1 := e_match_or_patt_or (e_negate p1') (e_negate p2')).
             pose proof (HC2 := (inr_impl_not_is_inl _ _ Heq2)).
             rewrite HC1 in HC2.
             inversion HC2.
          -- inversion e.
          -- inversion e. subst.
             solve_match_impossibilities.
          -- inversion e. subst.
             solve_match_impossibilities.
          -- solve_match_impossibilities.
        * funelim (e_and_or_imp_size (¬ p1' or ¬ p2' ---> ⊥)).
          -- inversion e. subst.
             solve_match_impossibilities.
          -- inversion e.
          -- inversion e. subst.
             solve_match_impossibilities.
          -- inversion e. subst.
             solve_match_impossibilities.
          -- solve_match_impossibilities.
      + inversion e. subst.
        simpl in Hsz.
        funelim (e_and_or_imp_size (e_negate p1' and e_negate p2')).
        * inversion e. subst.
          rewrite IHsz. lia.
          rewrite IHsz. lia.
          funelim (e_and_or_imp_size (¬ p1'0 ---> p2'0)).
          -- inversion e.
          -- inversion e. subst.
             reflexivity.
          -- inversion e. subst.
             funelim (e_and_or_imp_size ⊥); try inversion e.
             funelim (e_and_or_imp_size (¬ p1'0)).
             ++ inversion e. subst.
                funelim (e_and_or_imp_size (¬ p1' or ¬ p2')).
                ** clear H.
                   inversion e.
                ** clear H.
                   inversion e.
                   subst.
                   admit.
                ** inversion e.
                   
        
             
          
      admit.
    - funelim (e_negate _); inversion Heq.
      funelim (e_and_or_imp_size _); inversion Heq.
      reflexivity.
    - funelim (e_negate _); inversion Heq.
      funelim (e_and_or_imp_size _); inversion Heq.
      reflexivity.
  Qed.
  

  
  (* (* This does not scale :-( Since we have formulas of depth 6, it generates 800 obligations
        and proof search cannot solve them because the subpatterns are too deep. I guess.
      *)
  Equations e_and_or_imp_size (p : Pattern) : nat by wf p (Pattern_subterm Σ) :=
    (* patt_and p1 p2 *)
    e_and_or_imp_size ((((p1 ---> ⊥) ---> ⊥) ---> p2 ---> ⊥) ---> ⊥)
      := 1 + (e_and_or_imp_size p1) + (e_and_or_imp_size p2) ;
    e_and_or_imp_size ((p1 ---> ⊥) ---> p2)
      := 1 + (e_and_or_imp_size p1) + (e_and_or_imp_size p2) ;
    e_and_or_imp_size (p1 ---> p2)
      := 1 + (e_and_or_imp_size p1) + (e_and_or_imp_size p2) ;
    e_and_or_imp_size _ := 1.
  Solve Obligations with Tactics.program_simplify; CoreTactics.equations_simpl; try Tactics.program_solve_wf.
  *)
  

  Definition and_or_size'_enough_fuel (p : Pattern) : nat := S (size p).
  
  Lemma and_or_size'_terminates (p : Pattern) :
    and_or_size' (and_or_size'_enough_fuel p) p <> None.
  Proof.
    unfold and_or_size'_enough_fuel.
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
      unfold option_bimap.
      remember (and_or_size' sz p1') as n1'.
      destruct n1'.
      2: {
        symmetry in Heqn1'. apply IHsz in Heqn1'. inversion Heqn1'.
        simpl in *.
        lia.
      }
      remember (and_or_size' sz p2') as n2'.
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
      remember (and_or_size' sz p) as n1'.
      destruct n1'.
      2: {
        symmetry in Heqn1'. apply IHsz in Heqn1'. inversion Heqn1'.
        simpl in *. lia.
      }
      remember (and_or_size' sz p2) as n2'.
      destruct n2'.
      2: {
        symmetry in Heqn2'. apply IHsz in Heqn2'. inversion Heqn2'.
        simpl in *. lia.
      }
      discriminate.
    }

    simpl in Hsz.
    pose proof (IHp1 := IHsz p1 ltac:(lia)).
    pose proof (IHp2 := IHsz p2 ltac:(lia)).
    unfold option_bimap.
    remember (and_or_size' sz p1) as szp1.
    remember (and_or_size' sz p2) as szp2.
    destruct szp2.
    2: { contradiction. }
    destruct szp1.
    2: { contradiction. }
    unfold fmap,option_fmap,option_map.
 
    remember (match p2 with Bot => Some p1 | _ => None end) as c'.
    destruct c'. 2: { discriminate. }
    apply IHsz.
    destruct p2; inversion Heqc'. subst. lia.
  Qed.

  Lemma and_or_size'_monotone (p : Pattern) (fuel fuel' : nat) :
    fuel >= and_or_size'_enough_fuel p ->
    fuel' >= fuel ->
    and_or_size' fuel' p = and_or_size' fuel p.
  Proof.
    remember (size p) as sz.
    assert (Hsz: size p <= sz).
    lia.
    clear Heqsz.
    move: p fuel fuel' Hsz.
    induction sz;
    intros p fuel fuel' Hsz Henough Hmore;
    destruct p; simpl in Hsz; unfold and_or_size'_enough_fuel in Henough; simpl in Henough; try lia;
      destruct fuel,fuel'; try lia; simpl; try reflexivity.

    remember (match_and (p1 ---> p2)) as q.
    destruct q.
    { destruct p.
      symmetry in Heqq. apply match_and_size in Heqq. simpl in Heqq.
      rewrite -> IHsz with (fuel := fuel).
      2: { lia. }
      2: { unfold and_or_size'_enough_fuel. lia. }
      2: { lia. }

      rewrite -> IHsz with (fuel':=fuel') (fuel := fuel).
      2: { lia. }
      2: { unfold and_or_size'_enough_fuel. lia. }
      2: { lia. }
      reflexivity.
    }

    remember (match_not p1) as q2.
    destruct q2.
    {
      symmetry in Heqq2. apply match_not_size in Heqq2.
      rewrite -> IHsz with (fuel := fuel).
      2: { lia. }
      2: { unfold and_or_size'_enough_fuel. lia. }
      2: { lia. }

      rewrite -> IHsz with (fuel':=fuel') (fuel := fuel).
      2: { lia. }
      2: { unfold and_or_size'_enough_fuel. lia. }
      2: { lia. }
      reflexivity.
    }

    rewrite -> IHsz with (fuel := fuel).
    4: { lia. }
    3: { unfold and_or_size'_enough_fuel. lia. }
    2: { lia. }

    rewrite -> IHsz with (p := p2)(fuel := fuel).
    4: { lia. }
    3: { unfold and_or_size'_enough_fuel. lia. }
    2: { lia. }

    destruct p2; auto.
    rewrite -> IHsz with (p := p1)(fuel := fuel).
    4: { lia. }
    3: { unfold and_or_size'_enough_fuel. lia. }
    2: { lia. }
    reflexivity.
  Qed.


  Definition and_or_size''(p : Pattern) : option nat := and_or_size' (and_or_size'_enough_fuel p) p.

  Definition and_or_size (p : Pattern) : nat :=
    let np := and_or_size'' p in
    let Heqnp : np = and_or_size'' p := erefl np in
    match np as o return (o = and_or_size'' p → nat) with
    | Some p0 => λ _, p0
    | None =>
      λ Heqnp0 : None = and_or_size'' p,
                 match (and_or_size'_terminates p (eq_sym Heqnp0)) with end
    end Heqnp.
  
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
          | Some p' => Some (patt_not (patt_not p'))
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
      symmetry in Heqq. apply match_and_size in Heqq. simpl in Heqq.
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

  
  Ltac remember_and_destruct exp :=
    let Heq := fresh "Heq" in
    remember exp as Heq;
    destruct Heq.


  Ltac inverts_and_destructs :=
    match goal with
    | pts : Pattern * Pattern |- _ => destruct pts
    | H : Some _ = None |- _ => inversion H
    | H : None = Some _ |- _ => inversion H
    | H : Some _ = Some _ |- _ => inversion H; clear H
    end.
  Ltac remember_and_destruct_2 exp := remember_and_destruct exp; repeat inverts_and_destructs.
  
  
  Lemma size_negate' fuel p np:
    negate' fuel p = Some np ->
    size np > size p.
  Proof.
    intros Hn.

    move: p np Hn.
    induction fuel; intros p np Hn; destruct p; simpl in *;
      simpl in Hn; inversion Hn as [H'n]; clear Hn; subst;
        simpl; try lia.

    remember_and_destruct_2 (match_and (p1 ---> p2)).
    { remember_and_destruct_2 (negate' fuel p);
        remember_and_destruct_2 (negate' fuel p0);
        simpl in H'n; inversion H'n; clear H'n.

      subst np.
      pose proof (Htmp := match_and_size (eq_sym HeqHeq)).
      simpl in Htmp.

      pose proof (IH1 := IHfuel _ _ (eq_sym HeqHeq0)).
      pose proof (IH2 := IHfuel _ _ (eq_sym HeqHeq1)).
      simpl. rewrite Htmp.
      Print negate'.
      Fail lia.
      (* But this does not hold! Because for patt_not phi, it just strips the patt_not.
         So the result is sometimes smaller! *)
  Abort.
  
  (*
  Compute (and_or_size (patt_bound_evar 0 ---> patt_bound_evar 1)).
  Compute (and_or_size (patt_not (patt_bound_evar 0 ---> patt_bound_evar 1))).
  Compute (and_or_size (negate (patt_bound_evar 0 ---> patt_bound_evar 1))).
   *)
  
  Lemma and_or_size_negate' (fuel fuel' fuel'' : nat) (p np : Pattern) (sz sz' : nat) :
    fuel' >= fuel ->
    fuel >= and_or_size'_enough_fuel p ->
    fuel' >= and_or_size'_enough_fuel np ->
    fuel'' >= negate'_enough_fuel p ->
    and_or_size' fuel p = Some sz ->
    (negate' fuel'' p) = Some np ->
    and_or_size' fuel' np = Some sz' ->
    sz = sz'.
  Proof.
    intros Hfuel'gtfuel Hfuel Hfuel' Hfuel'' Hsz Hnp Hsz'.
    remember (size p) as isz.
    assert (Hisz: size p <= isz).
    { lia. }
    clear Heqisz.
    move: p np fuel Hfuel fuel' Hfuel' Hfuel'gtfuel fuel'' Hfuel'' sz Hsz sz' Hsz' Hnp Hisz.
    induction isz; intros p np fuel Hfuel fuel' Hfuel' Hfuel'gtfuel fuel'' Hfuel'' sz Hsz sz' Hsz' Hnp Hisz; destruct fuel,fuel',fuel'',p; simpl in *; try lia;
      inversion Hsz; inversion Hnp; inversion Hsz'; try subst sz; try subst np; clear Hsz Hnp Hsz';
        simpl in *.

    all: unfold fmap, option_fmap,option_map in H2; destruct fuel'; simpl in H2; inversion H2; clear H2;
      unfold fmap, option_fmap,option_map in H0; destruct fuel; simpl in H0; inversion H0; clear H0; auto.


    Ltac match_and_destruct :=
      match goal with
      | pts : Pattern * Pattern |- _ => destruct pts
      | H : Some _ = None |- _ => inversion H
      | H : None = Some _ |- _ => inversion H
      | H : Some _ = Some _ |- _ => inversion H; clear H
      | H : context C [(match ?p with _ => _ end)]  |- _
        => idtac "Hypothesis " H;
           remember_and_destruct p
      end.

    Ltac instantiate_IH IHisz :=
      match goal with
      | H : Some (?q1, ?q2) = match_and (?p1 ---> ?p2) |- _
        => let IHx := fresh "IH" in
           pose proof (IHx := IHisz (p1 ---> p2));
           rewrite -H in IHx;
           unfold option_bimap in IHx;
           unfold and_or_size'_enough_fuel,negate'_enough_fuel in *;
           simpl in *;
           specialize (IHx ltac:(lia) ltac:(lia) ltac:(lia))
      end.
    
    unfold and_or_size'_enough_fuel in Hfuel. simpl in Hfuel.
    unfold and_or_size'_enough_fuel in Hfuel'. simpl in Hfuel'.
    unfold negate'_enough_fuel in Hfuel''. simpl in Hfuel''.
    
    (* Solve subgoal 1 *)
    repeat match_and_destruct.

    (* Work on subgoal 2 *)
    {
      remember_and_destruct_2 (match_and (p1 ---> p2)).
      - pose proof (Htmpsz := match_and_size (eq_sym HeqHeq)).
        simpl in Htmpsz.
        destruct Htmpsz as [Hszp Hszp0].
        remember_and_destruct_2 (negate' fuel'' p).
        2: { simpl in H1. inversion H1. }
        simpl in H1.
        remember_and_destruct_2 (negate' fuel'' p0).
        subst np.
        remember_and_destruct_2 (match_and (p3 or p4)).
        remember_and_destruct_2 (match_or (p3 or p4)).
        rewrite match_or_patt_or in HeqHeq3. inversion HeqHeq3.
      - remember_and_destruct_2 (match_not p1).
        + pose proof (Hszp := match_not_size (eq_sym HeqHeq0)).
          simpl in Hszp.
          remember_and_destruct_2 (negate' fuel'' p).
          2: { simpl in H1. inversion H1. }
          remember_and_destruct_2 (negate' fuel'' p2).
          2: { simpl in H1. inversion H1. }
          simpl in H1. inversion H1. subst np. clear H1.
          remember_and_destruct_2 (match_and (p0 and p3)).
          rewrite match_and_patt_and in HeqHeq3. inversion HeqHeq3.
        + remember_and_destruct_2 (match p2 with | ⊥ => Some p1 | _ => None end).
          * subst np.
            remember_and_destruct_2 (match_and p).
            remember_and_destruct_2 (match_or p).
            remember_and_destruct_2 (match_not p).
            destruct p,p2; inversion H3; inversion H2; auto.
          * remember_and_destruct_2 (negate' fuel'' p2).
            2: { simpl in H1. inversion H1. }
            simpl in H1. inversion H1. subst np. clear H1.
            remember_and_destruct_2 (match_and (p1 and p)).
            (* A contradiction. *)
            simpl. Search match_and.
            rewrite match_and_patt_and in HeqHeq3. inversion HeqHeq3.
    }

    (* Subgoal 3 *)
    {
      remember_and_destruct_2 (match_and (p1 ---> p2)).
      remember_and_destruct_2 (match match_not p1 with | Some p1 => Some (p1, p2) | None => None end).
      remember_and_destruct_2 (match p2 with | ⊥ => Some p1 | _ => None end).
    }

    (* Subgoal 4 *)
    {
      remember_and_destruct_2 (match_and (p1 ---> p2)).
      + admit.
      + remember_and_destruct_2 (match match_not p1 with | Some p1 => Some (p1, p2) | None => None end).
        * admit.
        * remember_and_destruct_2 (match p2 with | ⊥ => Some p1 | _ => None end).
          -- admit.
          -- remember_and_destruct_2 (match_and np).
             ++ remember_and_destruct_2 (negate' fuel'' p2).
                2: { simpl in H1. inversion H1. }
                simpl in H1. inversion H1. subst np. clear H1.
                match type of H2 with
                | (match ?exp with _ => _ end) = _ => remember_and_destruct_2 exp
                end.
                match type of H3 with
                | (match ?exp with _ => _ end) = _ => remember_and_destruct_2 exp
                end.
                subst sz sz'.
                
                match type of HeqHeq5 with
                | _ = (option_bimap _ ?e1 ?e2)
                  => remember_and_destruct_2 e1;
                       remember_and_destruct_2 e2
                end; simpl in HeqHeq5; inversion HeqHeq5.
                subst n0.
                match type of HeqHeq4 with
                | _ = (option_bimap _ ?e1 ?e2)
                  => remember_and_destruct_2 e1;
                       remember_and_destruct_2 e2
                end; simpl in HeqHeq4; inversion HeqHeq4.
                subst n.
                clear HeqHeq4.

                remember_and_destruct_2 (match_and p);
                remember_and_destruct_2 (match_and p0);
                remember_and_destruct_2 (match_and p1);
                remember_and_destruct_2 (match_and p2).
                **
                  
                  remember_and_destruct_2 (and_or_size' fuel' p4);
                    remember_and_destruct_2 (and_or_size' fuel' p5);
                    remember_and_destruct_2 (and_or_size' fuel' p6);
                    remember_and_destruct_2 (and_or_size' fuel' p7);
                    remember_and_destruct_2 (and_or_size' fuel p8);
                    remember_and_destruct_2 (and_or_size' fuel p9);
                    remember_and_destruct_2 (and_or_size' fuel p10);
                    remember_and_destruct_2 (and_or_size' fuel p11);
                    simpl in *.
                  all: repeat inverts_and_destructs.
                  subst.
                  rewrite match_and_patt_and in HeqHeq2.
                  inversion HeqHeq2. clear HeqHeq2. subst.

                  pose proof (IH1 := IHisz p2 p3).
                  specialize (IH1 (and_or_size'_enough_fuel p2) ltac:(lia)).
                  specialize (IH1 (and_or_size'_enough_fuel p3) ltac:(lia)).
                  unfold and_or_size'_enough_fuel in IH1 at 1 2.
                  (* TODO We need to prove a lemma saying that size of negated formula is larger. *)
                  Check IH1.
                  specialize (IH1 (negate'_enough_fuel p2) ltac:(lia)).
                  assert (Hszp2: size p2 <= isz).
                  { lia. }
                  assert (Hp2fuel: negate'_enough_fuel p2 <= fuel'').
                  { unfold negate'_enough_fuel in *. simpl in *.  lia. }

                  rewrite <- negate'_monotone with (fuel' := fuel'') in IH1.
                  2,3: lia.
                  rewrite <- HeqHeq3 in IH1.
                  rewrite [and_or_size' _ p3]/= in IH1.
                  rewrite -HeqHeq9 in IH1.

                  pose proof (Htmp := match_and_size (eq_sym HeqHeq9)).
                  destruct Htmp as [Hszp6p3 Hszp7p3].
                  rewrite <- and_or_size'_monotone with (fuel := size p3)(fuel' := fuel') in IH1.
                  3: { unfold and_or_size'_enough_fuel in *. simpl in *. lia. }
                  2: { unfold and_or_size'_enough_fuel in *. simpl in *. lia. }
                  rewrite <- HeqHeq14 in IH1.
                  rewrite <- and_or_size'_monotone with (fuel := size p3)(fuel' := fuel') in IH1.
                  3: { unfold and_or_size'_enough_fuel in *. simpl in *. lia. }
                  2: { unfold and_or_size'_enough_fuel in *. simpl in *. lia. }
                  rewrite <- HeqHeq15 in IH1.
                  rewrite [_ <$> _ ]/= in IH1.

                  rewrite [and_or_size' _ _]/= in IH1.
                  rewrite -HeqHeq11 in IH1.


                  pose proof (Htmp := match_and_size (eq_sym HeqHeq11)).
                  destruct Htmp as [Hszp10p2 Hszp11p2].
                  rewrite <- and_or_size'_monotone with (fuel := size p2) (fuel' := fuel) in IH1.
                  3: { unfold and_or_size'_enough_fuel in *. simpl in *. lia. }
                  2: { unfold and_or_size'_enough_fuel in *. simpl in *. lia. }
                  rewrite -HeqHeq18 in IH1.
                  rewrite <- and_or_size'_monotone with (fuel := size p2) (fuel' := fuel) in IH1.
                  3: { unfold and_or_size'_enough_fuel in *. simpl in *. lia. }
                  2: { unfold and_or_size'_enough_fuel in *. simpl in *. lia. }
                  rewrite -HeqHeq19 in IH1.
                  rewrite [_ <$> _ ]/= in IH1.
                  specialize (IH1 (S(n9 + n10)) (eq_refl _)).
                  specialize (IH1 (S(n5 + n6)) (eq_refl _)).
                  specialize (IH1 (eq_refl _) Hszp2).
                  rewrite IH1.

                  (* Now I need to connect n7,n8 with n,n4; that is, p8,p9 with p4,p5 *)
                  rewrite -HeqHeq4  in HeqHeq10.
                  inversion HeqHeq10. subst p8 p9. clear HeqHeq10.

                  pose proof (Htmp := match_and_size (eq_sym HeqHeq4)).
                  destruct Htmp as [Hszp4p1 Hszp5p1].

                  
                  assert (and_or_size' fuel' p4 = and_or_size' fuel p4).
                  
                  { unfold and_or_size'_enough_fuel in *.
                    apply and_or_size'_monotone.
                    simpl in *.  unfold and_or_size'_enough_fuel in *. lia.
                    unfold negate'_enough_fuel in *. simpl in *. lia.
                  
                  rewrite -HeqHeq12 in HeqHeq16.


                  (* Proof ends here *)
                  unfold and_or_size' in IH1 at 1.
                  Search p2.
                  
                  

                  remember (patt_not (patt_or (patt_not p1) (patt_not p3))) as P.
                  
                  remember_and_destruct_2 (match_not p1). clear HeqHeq0.
                  apply IHisz.
                                        
                ** remember_and_destruct_2 (and_or_size' fuel p4); simpl in HeqHeq5.
                   2: { inversion HeqHeq5. }
                   remember_and_destruct_2 (and_or_size' fuel p5); simpl in HeqHeq5.
                   2: { inversion HeqHeq5. }
                   inversion HeqHeq5. subst n3. clear HeqHeq5.

                   remember_and_destruct_2 (match_and p1)
                   admit.
                ** 
    }
    
    
    

    }
    
    
    do 2 match_and_destruct.

    {
      instantiate_IH IHisz.
      remember_and_destruct_2 (match_and p).
      - pose proof (Htmpsz := match_and_size (eq_sym HeqHeq)).
        simpl in Htmpsz.
        destruct Htmpsz as [Hszp Hszp0].
        pose proof (Htmpsz := match_and_size (eq_sym HeqHeq0)).
        simpl in Htmpsz.
        destruct Htmpsz as [Hszp3 Hszp4].
        remember_and_destruct_2 (match_and p0).
        + pose proof (Htmpsz := match_and_size (eq_sym HeqHeq1)).
          simpl in Htmpsz.
          destruct Htmpsz as [Hszp5 Hszp6].
          remember_and_destruct_2 (option_bimap
                                     Nat.add
                                     (S <$> option_bimap Nat.add (and_or_size' fuel p3) (and_or_size' fuel p4))
                                     (S <$> option_bimap Nat.add (and_or_size' fuel p5) (and_or_size' fuel p6))).
          remember_and_destruct_2 (and_or_size' fuel p3);
            remember_and_destruct_2 (and_or_size' fuel p4);
            remember_and_destruct_2 (and_or_size' fuel p5);
            remember_and_destruct_2 (and_or_size' fuel p6);
            simpl in HeqHeq2;
            inversion HeqHeq2;
            clear HeqHeq2.
          destruct sz; try lia. inversion H0; clear H0. subst sz. subst n.
          simpl in IH.
          specialize (IH (eq_refl _)).
          remember_and_destruct_2 (match_and np).
          remember_and_destruct_2 (match_or np).
          remember_and_destruct_2 (match_not np).
          pose proof (IH' := flip IH). clear IH.
          specialize (IH' ltac:(lia)).

          destruct np; inversion H3.
          
          remember_and_destruct_2 (negate' fuel'' p).
          
          apply IH.
          
          * subst sz.
            unfold option_bimap in HeqHeq2.
            remember_and_destruct_2 (and_or_size' fuel p3).
            2: { pose proof (Htmp := and_or_size'_terminates).
                 unfold and_or_size'_enough_fuel in Htmp.
                 specialize (Htmp p3).
                 Check match_and_size.
                 pose proof (Htmpsz := match_and_size (eq_sym HeqHeq0)).
                 destruct Htmpsz as [Hszp3 Hszp4].
                 assert (fuel >= S (size p3)).
                 specialize (Htmp ltac:(lia)).
              remember_and_destruct_2 (and_or_size' fuel p4).
                                     

      4: {
      
      1:{ remember_and_destruct_2 (option_bimap
                                     Nat.add
                                     (S <$> option_bimap Nat.add (and_or_size' fuel p3) (and_or_size' fuel p4))
                                     (S <$> option_bimap Nat.add (and_or_size' fuel p5) (and_or_size' fuel p6))).
      }
      
      3: {
                                
      

      
      destruct p,p0; simpl in *; specialize (IH H2); inversion H2; try subst sz; clear H2;
        destruct fuel''; simpl in *; inversion H1; try subst np.
      all: try specialize (IH (eq_refl _ )); simpl in *; try specialize (IH ltac:(lia)); auto.
      (* 20 subgoals left *)
      all: try lia.
      all: (do 2 match_and_destruct); repeat inverts_and_destructs; subst.
      (* solves 9 subgoals out of 39 *)
      all: try specialize (IH (eq_refl _ )); simpl in *; try specialize (IH ltac:(lia)); auto.

      all: destruct fuel''; simpl in *; inversion H1; clear H1.
      all: try (remember (option_bimap Nat.add (S <$> option_bimap Nat.add (and_or_size' fuel p) (and_or_size' fuel p0)) (Some 1)) as obm; destruct obm; inversion H0; clear H0).



      try inversion H2; try subst np; clear H2.
        remember_and_destruct (match_and (p0_1 ---> p0_2)).
      
      
      do 4 (try instantiate_IH IHisz; match_and_destruct).
      Search and_or_size'.
      Search p.
      specialize (IH ).
      
    match type of IH with
    | context C [match and_or_size' ?fuel ?p with _ => _ end]
      => let Hsz := fresh "Hsz" in
         remember (and_or_size' fuel p) as Hsz;
           destruct Hsz
    end.
    }
    
    unfold option_bimap in IH.
    
      pose proof (IHisz (p1 ---> p2)) as IH1. rewrite -HeqHeq in IH1.
    do 5 match_and_destruct.
    
    (* Second subgoal *)
    {
      unfold option_bimap in *; simpl in *.
      do 5 (unfold option_bimap in *; simpl in *; match_and_destruct; subst; try lia).
    }
    
    
     (*
    
    - remember (match_and (p1 ---> p2)) as q1; destruct q1 as [[q1 q2]|];
        remember (match_and (patt_not (p1 ---> p2))) as qtmp; destruct qtmp as [[q3 q4]|]; inversion H2;
          (*pose proof (IH1 := IHisz (p1 ---> p2)); rewrite -Heqqtmp in IH1; rewrite -Heqq1 in IH1;*)
            clear H2;
            remember (match_not (p1 ---> p2)) as q3; destruct q3; destruct p2; inversion H0.
    - remember (match_and (p1 ---> p2)) as q1; destruct q1 as [[q1 q2]|];
        remember (match_and (patt_not (p1 ---> p2))) as qtmp; destruct qtmp as [[q3 q4]|]; inversion H2; clear H2;
          pose proof (IH1 := IHisz (p1 ---> p2)); rewrite -Heqqtmp in IH1; rewrite -Heqq1 in IH1;
            remember (match_and np) as q5; destruct q5 as [[q5 q6]|]; inversion H3; clear H3;
              remember (match_or np) as q7; destruct q7 as [[q7 q8]|]; inversion H2; clear H2;
                remember (match_not np) as nnp; destruct nnp; inversion H3; clear H3; subst sz'.

      + remember (match_and q3) as aq3; destruct aq3 as [[q9 q10]|];
          remember (match_and q4) as aq4; destruct aq4 as [[q11 q12]|].
        * remember (option_bimap
                      Nat.add (S <$> option_bimap Nat.add (and_or_not_size' fuel q9) (and_or_not_size' fuel q10))
                      (S <$> option_bimap Nat.add (and_or_not_size' fuel q11) (and_or_not_size' fuel q12))) as Big.
          destruct Big; inversion H0. subst sz.
          unfold option_bimap in HeqBig.
          remember (and_or_not_size' fuel q9) as szq9.
          remember (and_or_not_size' fuel q10) as szq10.
          remember (and_or_not_size' fuel q11) as szq11.
          remember (and_or_not_size' fuel q12) as szq12.
          destruct szq9,szq10,szq11,szq12; unfold fmap,option_fmap,option_map in HeqBig;
            inversion HeqBig; clear HeqBig; subst n.
          apply IH1.
          
                   
      *)
    
      
      
     
  
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
