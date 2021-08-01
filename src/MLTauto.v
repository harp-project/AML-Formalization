From Coq Require Import ssreflect ssrfun ssrbool.
From Coq Require Import Ensembles Logic.Classical_Prop.
From Coq Require Import Arith.Wf_nat Relations.Relation_Operators Wellfounded.Wellfounded.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq.micromega Require Import Lia.

From Equations Require Import Equations.

From stdpp Require Import base option.

From MatchingLogic Require Import Utils.wflexprod Syntax Semantics DerivedOperators ProofSystem Helpers.FOL_helpers.
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


  Equations match_not (p : Pattern)
    : ({ p' : Pattern & p = patt_not p'}) + (forall p', p <> patt_not p')
    :=
      match_not (p' ---> ⊥) := inl _ ;
      match_not _ := inr _ .
  Solve Obligations with Tactics.program_simplify; CoreTactics.equations_simpl.
  Next Obligation.
    intros. eapply existT. reflexivity.
  Defined.
  
  Lemma match_not_patt_not p: is_inl (match_not (patt_not p)).
  Proof.
    funelim (match_not _). simpl. reflexivity.
  Qed.

  Equations match_or (p : Pattern)
    : ({ p1 : Pattern & {p2 : Pattern & p = patt_or p1 p2}}) + (forall p1 p2, p <> patt_or p1 p2)
    :=
      match_or (p1 ---> p2) with match_not p1 => {
        | inl (existT p1' e) => inl _
        | inr _ => inr _
      } ;      
      match_or _ := inr _.
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

  Lemma match_or_patt_or p1 p2: is_inl (match_or (patt_or p1 p2)).
  Proof. reflexivity. Qed.

  Equations?  match_and (p : Pattern)
    : ({ p1 : Pattern & {p2 : Pattern & p = patt_and p1 p2}}) + (forall p1 p2, p <> patt_and p1 p2)
    :=
      match_and p with match_not p => {
        | inr _ := inr _ ;
        | inl (existT p' e') with match_or p' => {
            | inr _ := inr _ ;
            | inl (existT p1 (existT p2 e12)) with match_not p1 => {
                | inr _ := inr _ ;
                | inl (existT np1 enp1) with match_not p2 => {
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

  Lemma match_and_patt_and p1 p2: is_inl (match_and (patt_and p1 p2)).
  Proof. reflexivity. Qed.

  Lemma match_and_patt_or p1 p2: is_inl (match_and (patt_or p1 p2)) = false.
  Proof.
    funelim (match_and _); try reflexivity.
    subst. inversion e'.
  Qed.

  Equations match_imp (p : Pattern)
    : ({ p1 : Pattern & {p2 : Pattern & p = patt_imp p1 p2}}) + (forall p1 p2, p <> patt_imp p1 p2)
    :=
      match_imp (p1 ---> p2) := inl _ ;
      match_imp _ := inr _.
  Solve Obligations with Tactics.program_simplify; CoreTactics.equations_simpl.
  Next Obligation.
    intros. eapply existT. eapply existT. reflexivity.
  Defined.

  Lemma match_imp_patt_imp p1 p2: is_inl (match_imp (patt_imp p1 p2)).
  Proof. reflexivity. Qed.

  Equations match_bott (p : Pattern)
    : (p = patt_bott) + (p <> patt_bott)
    :=
      match_bott patt_bott := inl _ ;
      match_bott _ := inr _.
  Solve Obligations with Tactics.program_simplify; CoreTactics.equations_simpl.
  Next Obligation. reflexivity. Defined.
  

  Equations negate (p : Pattern) : Pattern by wf p (Pattern_subterm Σ) :=
    negate p with match_and p => {
      | inl (existT p1' (existT p2' e)) := patt_or (negate p1') (negate p2') ;
      | inr _
          with match_or p => {
          | inl (existT p1' (existT p2' e)) := patt_and (negate p1') (negate p2') ;
          | inr _
              with match_not p => {
              | inl (existT p1' e) := p1';
              | inr _
                  with match_imp p => {
                  | inl (existT p1 (existT p2 _)) := patt_and p1 (negate p2) ;
                  | inr _ => patt_not p
                }
            }
        }
    }.
  Solve Obligations with
      (Tactics.program_simplify; CoreTactics.equations_simpl; try Tactics.program_solve_wf).

  Example simple: negate ((patt_bound_evar 0) and (patt_bound_evar 1)) =
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

  Lemma wf_negate p:
    well_formed p ->
    well_formed (negate p).
  Proof.
    intros wfp.
    remember (size' p) as sz.
    assert (Hsz : size' p <= sz).
    { lia. }
    clear Heqsz.
    move: p Hsz wfp.
    induction sz; intros p Hsz wfp; destruct p; simpl in *; try lia;
      funelim (negate _); auto; try inversion e; subst.
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

  #[local] Hint Resolve wf_negate : core.
  

  Lemma negate_count_evar_occurrences p x :
    count_evar_occurrences x (negate p) = count_evar_occurrences x p.
  Proof.
    remember (size' p) as sz.
    assert (Hsz: size' p <= sz).
    { lia. }
    clear Heqsz.
    move: p Hsz.
    induction sz; intros p Hsz; destruct p; simpl in Hsz; try lia;
      funelim (negate _); try inversion e; subst; simpl; auto.
    - simpl in Hsz. rewrite IHsz. lia. rewrite IHsz. lia. lia.
    - simpl in Hsz. rewrite IHsz. lia. rewrite IHsz. lia. lia.
    - simpl in Hsz. rewrite IHsz. lia. lia.
  Qed.

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
    (Empty_set _) ⊢ ((patt_not p) <---> (negate p)).
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
      funelim (negate _); try inversion e; subst;
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

      assert(Hwfnegp1': well_formed (negate p1')).
      { auto. }
      assert(Hwfnegp2': well_formed (negate p2')).
      { auto. }
      assert(Hwfnp1': well_formed (patt_not p1')).
      { auto. }
      assert(Hwfnp2': well_formed (patt_not p2')).
      { auto. }

      remember (fresh_evar (¬ ((¬ p1' or ¬ p2') ---> ⊥) <---> negate p1' or negate p2')) as star.

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

      assert (Hcount_np1': count_evar_occurrences star (negate p1') = 0).
      { rewrite negate_count_evar_occurrences. apply Hcount_p1'. }

      assert (Hcount_np2': count_evar_occurrences star (negate p2') = 0).
      { rewrite negate_count_evar_occurrences. apply Hcount_p2'. }
      
      unfold patt_iff. unfold patt_iff in Heqstar.
      
      assert (Step1: (Empty_set Pattern ⊢
                                ((¬ (¬ p1' or ¬ p2' ---> ⊥) ---> (¬ p1') or negate p2')
                                   and (negate p1' or negate p2' ---> ¬ (¬ p1' or ¬ p2' ---> ⊥)))
                     ->
                     (Empty_set Pattern ⊢ ((¬ (¬ p1' or ¬ p2' ---> ⊥) ---> negate p1' or negate p2')
                                             and (negate p1' or negate p2' ---> ¬ (¬ p1' or ¬ p2' ---> ⊥)))))
             ).
      {
        intros BigH.
        

        make_step
          star
          (¬ p1')
          (negate p1')
          ((¬ (¬ p1' or ¬ p2' ---> ⊥) ---> (patt_free_evar star) or negate p2')
             and (negate p1' or negate p2' ---> ¬ (¬ p1' or ¬ p2' ---> ⊥)))
          (rewrite ?Hcount_p1' ?Hcount_p2' ?Hcount_np1' ?Hcount_np2')
        .
      }
      apply Step1. clear Step1.

      assert (Step2: (Empty_set Pattern ⊢
                                ((¬ (¬ p1' or ¬ p2' ---> ⊥) ---> (¬ p1') or ¬ p2')
                                   and (negate p1' or negate p2' ---> ¬ (¬ p1' or ¬ p2' ---> ⊥)))
                     ->
                     (Empty_set Pattern ⊢ ((¬ (¬ p1' or ¬ p2' ---> ⊥) ---> ¬ p1' or negate p2')
                                             and (negate p1' or negate p2' ---> ¬ (¬ p1' or ¬ p2' ---> ⊥)))))
             ).
      {
        intros BigH.

        make_step
          star
          (¬ p2')
          (negate p2')
          ((¬ (¬ p1' or ¬ p2' ---> ⊥) ---> ¬ p1' or (patt_free_evar star))
             and (negate p1' or negate p2' ---> ¬ (¬ p1' or ¬ p2' ---> ⊥)))
          (rewrite ?Hcount_p1' ?Hcount_p2' ?Hcount_np1' ?Hcount_np2')
        .
      }
      apply Step2. clear Step2.

      assert (Step3: (Empty_set Pattern ⊢
                                ((¬ (¬ p1' or ¬ p2' ---> ⊥) ---> (¬ p1') or ¬ p2')
                                   and (¬ p1' or negate p2' ---> ¬ (¬ p1' or ¬ p2' ---> ⊥)))
                      ->
                      (Empty_set Pattern ⊢ ((¬ (¬ p1' or ¬ p2' ---> ⊥) ---> ¬ p1' or ¬ p2')
                                              and (negate p1' or negate p2' ---> ¬ (¬ p1' or ¬ p2' ---> ⊥)))))
             ).
      {
        intros BigH.

        make_step
          star
          (¬ p1')
          (negate p1')
          ((¬ (¬ p1' or ¬ p2' ---> ⊥) ---> ¬ p1' or ¬ p2')
             and ((patt_free_evar star) or negate p2' ---> ¬ (¬ p1' or ¬ p2' ---> ⊥)))
          (rewrite ?Hcount_p1' ?Hcount_p2' ?Hcount_np1' ?Hcount_np2')
        .          
      }
      apply Step3. clear Step3.


      assert (Step4: (Empty_set Pattern ⊢
                                ((¬ (¬ p1' or ¬ p2' ---> ⊥) ---> (¬ p1') or ¬ p2')
                                   and (¬ p1' or ¬ p2' ---> ¬ (¬ p1' or ¬ p2' ---> ⊥)))
                      ->
                      (Empty_set Pattern ⊢ ((¬ (¬ p1' or ¬ p2' ---> ⊥) ---> ¬ p1' or ¬ p2')
                                              and (¬ p1' or negate p2' ---> ¬ (¬ p1' or ¬ p2' ---> ⊥)))))
             ).
      {
        intros BigH.

        make_step
          star
          (¬ p2')
          (negate p2')
          ((¬ (¬ p1' or ¬ p2' ---> ⊥) ---> ¬ p1' or ¬ p2')
             and (¬ p1' or (patt_free_evar star) ---> ¬ (¬ p1' or ¬ p2' ---> ⊥)))
          (rewrite ?Hcount_p1' ?Hcount_p2' ?Hcount_np1' ?Hcount_np2')
        .          
      }
      apply Step4. clear Step4.

      apply conj_intro_meta; auto.
      + apply not_not_elim. auto.
      + apply not_not_intro. auto.
    - (*(¬ (¬ p1' ---> p2') <---> negate p1' and negate p2') *)

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

      assert(Hwfnegp1': well_formed (negate p1')).
      { auto. }
      assert(Hwfnegp2': well_formed (negate p2')).
      { auto. }
      assert(Hwfnp1': well_formed (patt_not p1')).
      { auto. }
      assert(Hwfnp2': well_formed (patt_not p2')).
      { auto. }

      remember (fresh_evar (¬ (¬ p1' ---> p2') <---> negate p1' and negate p2')) as star.

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

      assert (Hcount_np1': count_evar_occurrences star (negate p1') = 0).
      { rewrite negate_count_evar_occurrences. apply Hcount_p1'. }

      assert (Hcount_np2': count_evar_occurrences star (negate p2') = 0).
      { rewrite negate_count_evar_occurrences. apply Hcount_p2'. }
      
      unfold patt_iff. unfold patt_iff in Heqstar.

      assert (Step1: (Empty_set Pattern ⊢
                                ((¬ (¬ p1' ---> p2') ---> ¬ p1' and negate p2')
                                   and (negate p1' and negate p2' ---> ¬ (¬ p1' ---> p2'))))
                     ->
                      (Empty_set Pattern ⊢
                                ((¬ (¬ p1' ---> p2') ---> negate p1' and negate p2')
                                   and (negate p1' and negate p2' ---> ¬ (¬ p1' ---> p2'))))
                                
             ).
      {
        intros BigH.

        make_step
          star
          (¬ p1')
          (negate p1')
          ((¬ (¬ p1' ---> p2') ---> (patt_free_evar star) and negate p2')
             and (negate p1' and negate p2' ---> ¬ (¬ p1' ---> p2')))
          (rewrite ?Hcount_p1' ?Hcount_p2' ?Hcount_np1' ?Hcount_np2')
        .
      }
      apply Step1. clear Step1.

      assert (Step2: (Empty_set Pattern ⊢
                                ((¬ (¬ p1' ---> p2') ---> ¬ p1' and ¬ p2')
                                   and (negate p1' and negate p2' ---> ¬ (¬ p1' ---> p2'))))
                     ->
                      (Empty_set Pattern ⊢
                                ((¬ (¬ p1' ---> p2') ---> ¬ p1' and negate p2')
                                   and (negate p1' and negate p2' ---> ¬ (¬ p1' ---> p2'))))
                                
             ).
      {
        intros BigH.

        make_step
          star
          (¬ p2')
          (negate p2')
          ((¬ (¬ p1' ---> p2') ---> ¬ p1' and (patt_free_evar star))
             and (negate p1' and negate p2' ---> ¬ (¬ p1' ---> p2')))
          (rewrite ?Hcount_p1' ?Hcount_p2' ?Hcount_np1' ?Hcount_np2')
        .
      }
      apply Step2. clear Step2.

      assert (Step3: (Empty_set Pattern ⊢
                                ((¬ (¬ p1' ---> p2') ---> ¬ p1' and ¬ p2')
                                   and (¬ p1' and negate p2' ---> ¬ (¬ p1' ---> p2'))))
                     ->
                      (Empty_set Pattern ⊢
                                ((¬ (¬ p1' ---> p2') ---> ¬ p1' and ¬ p2')
                                   and (negate p1' and negate p2' ---> ¬ (¬ p1' ---> p2'))))
                                
             ).
      {
        intros BigH.

        make_step
          star
          (¬ p1')
          (negate p1')
          ((¬ (¬ p1' ---> p2') ---> ¬ p1' and ¬ p2')
             and ((patt_free_evar star) and negate p2' ---> ¬ (¬ p1' ---> p2')))
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
                                   and (¬ p1' and negate p2' ---> ¬ (¬ p1' ---> p2'))))
                                
             ).
      {
        intros BigH.

        make_step
          star
          (¬ p2')
          (negate p2')
          ((¬ (¬ p1' ---> p2') ---> ¬ p1' and ¬ p2')
             and ( ¬ p1' and (patt_free_evar star) ---> ¬ (¬ p1' ---> p2')))
          (rewrite ?Hcount_p1' ?Hcount_p2' ?Hcount_np1' ?Hcount_np2')
        .
      }
      apply Step4. clear Step4.
      apply and_of_negated_iff_not_impl; auto.
    - unfold well_formed, well_formed_closed in Hwfp.
      simpl in Hwfp.
      rewrite !andbT in Hwfp.
      fold (well_formed_closed p1') in Hwfp.
      fold (well_formed p1') in Hwfp.
      apply conj_intro_meta; auto.
      + apply not_not_elim; auto.
      + apply not_not_intro; auto.
    - (* (¬ (p1 ---> p2) <---> p1 and negate p2) *)
      unfold well_formed, well_formed_closed in Hwfp.
      simpl in Hwfp.
      apply andb_prop in Hwfp. destruct Hwfp as [Hwf1 Hwf2].
      apply andb_prop in Hwf1. destruct Hwf1 as [Hwf11 Hwf12].
      apply andb_prop in Hwf2. destruct Hwf2 as [Hwf21 Hwf22].
      assert (wfp1: well_formed p1).
      { unfold well_formed, well_formed_closed. rewrite Hwf11 Hwf21. reflexivity. }
      assert (wfp2: well_formed p2).
      { unfold well_formed, well_formed_closed. rewrite Hwf12 Hwf22. reflexivity. }

      simpl in Hsz.
      pose proof (IHp2 := IHsz p2 ltac:(auto) ltac:(lia)).

      assert(Hwfnegp2: well_formed (negate p2)).
      { auto. }
      assert(Hwfnp2: well_formed (patt_not p2)).
      { auto. }

      remember (fresh_evar (¬ (p1 ---> p2) <---> p1 and negate p2)) as star.

      assert (Hcount_p1: count_evar_occurrences star p1 = 0).
      {
        rewrite count_evar_occurrences_0.
        subst.
        eapply evar_is_fresh_in_richer'.
        2: apply set_evar_fresh_is_fresh'.
        solve_free_evars_inclusion 5.
        reflexivity.
      }

      assert (Hcount_p2: count_evar_occurrences star p2 = 0).
      {
        rewrite count_evar_occurrences_0.
        subst.
        eapply evar_is_fresh_in_richer'.
        2: apply set_evar_fresh_is_fresh'.
        solve_free_evars_inclusion 5.
        reflexivity.
      }

      assert (Hcount_np2: count_evar_occurrences star (negate p2) = 0).
      { rewrite negate_count_evar_occurrences. apply Hcount_p2. }
      
      unfold patt_iff. unfold patt_iff in Heqstar.

      assert (Step1: (Empty_set Pattern ⊢ ((¬ (p1 ---> p2) ---> p1 and ¬ p2)
                                and (p1 and negate p2 ---> ¬ (p1 ---> p2))))
                     ->
                     (Empty_set Pattern ⊢ ((¬ (p1 ---> p2) ---> p1 and negate p2)
                                and (p1 and negate p2 ---> ¬ (p1 ---> p2))))
                       
             ).
      {
        intros BigH.

        make_step
          star
          (¬ p2)
          (negate p2)
          ((¬ (p1 ---> p2) ---> p1 and (patt_free_evar star))
             and (p1 and negate p2 ---> ¬ (p1 ---> p2)))
          (rewrite ?Hcount_p1 ?Hcount_p2 ?Hcount_np2)
        .
      }
      apply Step1. clear Step1.

      assert (Step2: (Empty_set Pattern ⊢ ((¬ (p1 ---> p2) ---> p1 and ¬ p2)
                                             and (p1 and ¬ p2 ---> ¬ (p1 ---> p2))))
                     ->
                     (Empty_set Pattern ⊢ ((¬ (p1 ---> p2) ---> p1 and ¬ p2)
                                             and (p1 and negate p2 ---> ¬ (p1 ---> p2))))
                       
             ).
      {
        intros BigH.

        make_step
          star
          (¬ p2)
          (negate p2)
          ((¬ (p1 ---> p2) ---> p1 and ¬ p2)
             and (p1 and (patt_free_evar star) ---> ¬ (p1 ---> p2)))
          (rewrite ?Hcount_p1 ?Hcount_p2 ?Hcount_np2)
        .
      }
      apply Step2. clear Step2.
      apply and_impl_2; auto.
  Qed.    

  (* Huh, not true for p = ¬ ⊥ *)
  Lemma negate_not_bot p:
    negate p <> patt_bott.
  Proof.
    funelim (negate p); try inversion e; subst; try discriminate.
  Abort.


  (* The key property I want is that [and_or_imp_size (negate p) = and_or_imp_size p].
     For this to hold, we need to resolve the not/or overlap in both functions
     in the same way.
   *)
  Equations and_or_imp_size (p : Pattern) : nat by wf p (Pattern_subterm Σ) :=
    and_or_imp_size p with match_and p => {
      | inl (existT p1' (existT p2' e)) := 1 + (and_or_imp_size p1') + (and_or_imp_size p2') ;
      | inr _
          with match_or p => {
          | inl (existT p1' (existT p2' e)) := 1 + (and_or_imp_size p1') + (and_or_imp_size p2') ;
          | inr _
              with match_not p => {
              | inl (existT p1' e) := and_or_imp_size p1';
              | inr _
                  with match_imp p => {
                  | inl (existT p1 (existT p2 _)) := 1 + (and_or_imp_size p1) + (and_or_imp_size p2) ;
                  | inr _ => 1
                }
            }
        }
    }.
  Solve Obligations with
      (Tactics.program_simplify; CoreTactics.equations_simpl; try Tactics.program_solve_wf).


  (* This may come handy later. If not, I can always delete that later. *)
  Ltac solve_match_impossibilities :=
    repeat (
        match goal with
        | H : match_or (patt_or ?A ?B) = inr _ |- _
          =>
          let HC1 := fresh "HC1" in
          pose proof (HC1 := match_or_patt_or A B);
          let HC2 := fresh "HC2" in
          pose proof (HC2 := (inr_impl_not_is_inl _ _ H));
          rewrite HC1 in HC2;
          inversion HC2
        | H : match_and (patt_and ?A ?B) = inr _ |- _
          =>
          let HC1 := fresh "HC1" in
          pose proof (HC1 := match_and_patt_and A B);
          let HC2 := fresh "HC2" in
          pose proof (HC2 := (inr_impl_not_is_inl _ _ H));
          rewrite HC1 in HC2;
          inversion HC2
        | H : match_imp (patt_imp ?A ?B) = inr _ |- _
          =>
          let HC1 := fresh "HC1" in
          pose proof (HC1 := match_imp_patt_imp A B);
          let HC2 := fresh "HC2" in
          pose proof (HC2 := (inr_impl_not_is_inl _ _ H));
          rewrite HC1 in HC2;
          inversion HC2
        | H : match_not (patt_not ?A) = inr _ |- _
          =>
          let HC1 := fresh "HC1" in
          pose proof (HC1 := match_not_patt_not A);
          let HC2 := fresh "HC2" in
          pose proof (HC2 := (inr_impl_not_is_inl _ _ H));
          rewrite HC1 in HC2;
          inversion HC2
        end
      ).

  Lemma negate_other_than_imp p neq:
    match_imp p = inr neq ->
    negate p = ¬ p.
  Proof.
    intros H.
    funelim (negate p); try inversion e; subst;
      unfold patt_and in *; unfold patt_or in *; unfold patt_not in *;
        solve_match_impossibilities.
    reflexivity.
  Qed.
  


  (*
  Lemma and_or_imp_size_not p :
    and_or_imp_size (patt_not p) = 2 + and_or_imp_size p.
  Proof.
    remember (size' p) as sz.
    assert (Hsz: size' p <= sz).
    { lia. }
    clear Heqsz.

    move: p Hsz.
    induction sz; intros p Hsz; destruct p; simpl in Hsz; try lia;
      funelim (and_or_imp_size _); try inversion e; subst; auto; solve_match_impossibilities.
    - funelim (and_or_imp_size (¬ ¬ p1' ---> ¬ p2')); try inversion e; subst.
      + simpl in Hsz. repeat rewrite IHsz. lia. lia. reflexivity.
      + simpl in Hsz. repeat rewrite IHsz. simpl. lia. lia. lia. reflexivity.
      + solve_match_impossibilities.
    - solve_match_impossibilities.
    - solve_match_impossibilities.
    - solve_match_impossibilities.
  Qed.
   *)
  
  Lemma and_or_imp_size_negate p:
    and_or_imp_size (negate p) = and_or_imp_size p.
  Proof.
    remember (size' p) as sz.
    assert (Hsz: size' p <= sz).
    { lia. }
    clear Heqsz.

    move: p Hsz.
    induction sz; intros p Hsz; destruct p; simpl in Hsz; try lia;
      funelim (negate _); try inversion e; subst; auto.
    - clear e H H0 Heq.
      funelim (and_or_imp_size _); try inversion e; subst; solve_match_impossibilities.
      clear e n H Heq H0 Heq0.
      simpl in Hsz.
      repeat (rewrite IHsz; [lia|]).
      replace (¬ p1'0 or ¬ p2'0 ---> ⊥) with (p1'0 and p2'0) by reflexivity.
      funelim (and_or_imp_size (_ and _)); try inversion e; subst; solve_match_impossibilities.
      clear e H H0 Heq.
      reflexivity.
    - clear e n H H0 Heq Heq0.
      funelim (and_or_imp_size _); try inversion e; subst; solve_match_impossibilities.
      clear e H Heq H0.
      simpl in Hsz.
      repeat (rewrite IHsz; [lia|]).
      replace (¬ p1'0 ---> p2'0) with (p1'0 or p2'0) by reflexivity.
      funelim (and_or_imp_size (_ or _)); try inversion e; subst; solve_match_impossibilities.
      reflexivity.
    - replace (p1' ---> ⊥) with (¬ p1') by reflexivity.
      funelim (and_or_imp_size (¬ p1')); try inversion e; subst; solve_match_impossibilities.
      + clear e H H0 n0 Heq Heq0 Heq1.
        fold (¬ (¬ p1' or ¬ p2')) in Heq2. fold (p1' and p2') in Heq2.
        solve_match_impossibilities.
      + fold (p1' or ⊥) in Heq2. solve_match_impossibilities.
      + reflexivity.
    - clear e Heq.
      (*clear e n1 n0 n H Heq Heq0 Heq1 Heq2.*)
      funelim (and_or_imp_size _); try inversion e; subst; solve_match_impossibilities.
      clear e H Heq H0.
      rewrite IHsz; [lia|].
      funelim (and_or_imp_size (p1' ---> p2)); try inversion e; subst; solve_match_impossibilities.
      + fold (¬ (¬ p1' or ¬ p2')) in Heq0. solve_match_impossibilities.
      + fold (p1' or p2') in Heq1. solve_match_impossibilities.
      + fold (¬ p1') in Heq4. solve_match_impossibilities.
      + reflexivity.
    - pose proof (n2 p1 p2). contradiction.
  Qed.

  Compute (size' (¬ (patt_bound_evar 0))).
  Compute (size' ((patt_bound_evar 0 and patt_bound_evar 1))).
  

  (* mns (¬ s1 and s2) = 
     mns (s₁ or s₂) = mns (¬ s₁ ---> s₂) = max ( mns (¬ s₁), mns (s₂) ) = max (size s₁, mns (s₂))

     max_negation_size (¬ (p1 ---> p2)) > max_negation_size (negate (p1 ---> p2))

     mns (¬ (s₁ or s₂)) = size (s₁ or s₂) = size s₁ + size s₂ + k
     mns (negate (s₁ or s₂)) = mns (negate s₁ and negate s₂) = mns (¬ s₁ and ¬ s₂) = max (size s₁, size s₂)

     mns (¬ (s₁ and s₂)) = size (s₁ and s₂) = size s₁ + size s₂ + k
     mns (negate (s₁ and s₂)) = mns (negate s₁ or negate s₂) = mns (¬ (negate s₁) ---> negate s₂) = mns (¬¬ s₁ ---> ¬ s₂) = max (size (¬ s₁), size (s₂))

                                                             = mns (¬ s₁ or ¬ s₂) = max (size s₁, size s₂)

     mns (negate (s₁ and s₂))
     = mns (negate s₁ or negate s₂)
     = mns (¬ (negate s₁) ---> negate s₂)
     = mns (¬¬ s₁ ---> ¬ s₂)
     = max (size (¬ s₁), size (s₂))
     = max (2 + size s₁, size s₂)
     <? size s₁ + size s₂ + k
     = size (s₁ and s₂)
     = mns (¬ (s₁ and s₂))


     mns (negate (s₁ or s₂))
     = mns (negate s₁ and negate s₂)
     = mns (¬ (¬ negate s₁ or ¬ negate s₂))
     = size (¬ negate s₁ or ¬ negate s₂)
     <?
     = size (s₁ or s₂)
     mns (¬ (s₁ or s₂)


    mns (¬ ¬ p)
    ¬ ¬ p = p or ⊥
   *)
  Equations max_negation_size (p : Pattern) : nat by wf p (Pattern_subterm Σ) :=
    max_negation_size p with match_and p => {
      | inl (existT p1 (existT p2 e)) := Nat.max (max_negation_size p1) (max_negation_size p2);
      | inr _ with match_or p => {
          | inl (existT p1 (existT p2 e)) := Nat.max (max_negation_size p1) (max_negation_size p2);
          | inr _  with match_not p => {
              | inl (existT p1' e) := size' p1';
              | inr _ with match_imp p => {
                  | inl (existT p1 (existT p2 _)) :=
                    Nat.max (max_negation_size p1) (max_negation_size p2);
                  | inr _ => 0
                }
            (**)}(**)
        }
    }.
  Solve Obligations with
      (Tactics.program_simplify; CoreTactics.equations_simpl; try Tactics.program_solve_wf).


  Lemma max_negation_size_lt p:
    max_negation_size p < size' p.
  Proof.
    remember (size' p) as sz.
    rewrite Heqsz.
    assert (Hsz: size' p <= sz) by lia.
    clear Heqsz.
    move: p Hsz.
    induction sz; intros p Hsz; destruct p; simpl in *; try lia;
      funelim (max_negation_size _); try inversion e; subst; solve_match_impossibilities; try lia.
    - simpl in *.
      pose proof (IH1 := IHsz p1 ltac:(lia)).
      pose proof (IH2 := IHsz p2 ltac:(lia)).
      lia.
    - simpl in *.
      pose proof (IH1 := IHsz p1 ltac:(lia)).
      pose proof (IH2 := IHsz p2 ltac:(lia)).
      lia.
    - simpl in *.
      pose proof (IH1 := IHsz p1 ltac:(lia)).
      pose proof (IH2 := IHsz p2 ltac:(lia)).
      lia.
  Qed.
  
  (* if p == ¬ p',
     then mns (¬ p) = mns (¬ ¬ p) = mns (p or ⊥) = max (mns p) (mns ⊥)
     TODO: this works only if we assume that ¬ p is not and
   *)
  Lemma max_negation_size_not p:
    max_negation_size (¬ p) <= size' p.
  Proof.
    funelim (max_negation_size (¬ p)); try inversion e; subst; solve_match_impossibilities.
    3: { lia. }
    2: {
      clear.
      funelim (max_negation_size ⊥); try inversion e; subst; solve_match_impossibilities.
      pose proof (Hszp1 := max_negation_size_lt p1).
      simpl. lia.
    }
    1: {
      pose proof (Hszp1 := max_negation_size_lt p1).
      pose proof (Hszp2 := max_negation_size_lt p2).
      simpl. lia.
    }
  Qed.  
  
  Definition aoisz_mns_lexprod' :=
    @lexprod'
      nat
      nat
      lt
      lt
  .
  (*
      (ltof _ and_or_imp_size)
      (ltof _ max_negation_size)
  .*)

  Lemma wf_aoisz_mns_lexprod' : well_founded aoisz_mns_lexprod'.
  Proof.
    apply wf_lexprod'.
    - apply well_founded_ltof.
    - apply well_founded_ltof.
  Defined.

  Check aoisz_mns_lexprod'.
  Definition aoisz_mns_lexprod p q :=
    aoisz_mns_lexprod'
      (and_or_imp_size p, max_negation_size p)
      (and_or_imp_size q, max_negation_size q).

  Lemma wf_aoisz_mns_lexprod : well_founded aoisz_mns_lexprod.
  Proof.
    unfold aoisz_mns_lexprod.
    apply (wf_inverse_image _ _ _ (fun x => (and_or_imp_size x, max_negation_size x))).
    apply wf_aoisz_mns_lexprod'.
  Defined.
  

  Instance wf_aoisz_mns_lexprod_ins : WellFounded aoisz_mns_lexprod.
  Proof.
    apply wf_aoisz_mns_lexprod.
  Defined.
  
  
  Lemma negate_is_bot p:
    negate p = ⊥ ->
    p = ¬ ⊥.
  Proof.
    intros H.
    destruct p; inversion H.
    assert (p2 = ⊥).
    {
      clear H1.
      funelim (negate (p1 ---> p2)); try inversion e; subst; auto.
      - rewrite -Heqcall in H1. inversion H1.
      - rewrite H0 in Heqcall. inversion Heqcall.
      - rewrite H in Heqcall. inversion Heqcall.
    }
    subst p2.

    assert (p1 = ⊥).
    {
      clear H1.
      funelim (negate (p1 ---> ⊥)); try inversion e; subst; auto.
      - clear H H0.
        simp negate in H1. rewrite Heq in H1.
        unfold negate_unfold_clause_1 in H1.
        inversion H1.
      - clear H H0.
        simp negate in H1. rewrite Heq0 in H1.
        simpl in H1. rewrite Heq in H1. simpl in H1.
        inversion H1.
      - clear H.
        simp negate in H0.
        rewrite Heq2 in H0. simpl in H0.
        rewrite Heq1 in H0. simpl in H0.
        rewrite Heq0 in H0. simpl in H0.
        rewrite Heq in H0. simpl in H0.
        inversion H0.
      - rewrite -Heqcall in H. inversion H.
    }
    subst p1.
    clear H H1.
    reflexivity.
  Qed.

(*
  Lemma and_or_imp_size_negate_and p q:
    and_or_imp_size (negate (p and q)) = and_or_imp_size (p and q).
  Proof.
    funelim (negate (p and q)); try inversion e; subst; solve_match_impossibilities.
    clear e H H0 Heq.
    funelim (and_or_imp_size (negate p1' or negate p2')); try inversion e; subst; solve_match_impossibilities.
  Abort.
  
  Lemma and_or_imp_size_not_negate p:
    and_or_imp_size (¬ (negate p)) = and_or_imp_size p.
  Proof.
    funelim (and_or_imp_size (¬ (negate p))); try inversion e; subst; solve_match_impossibilities;
      [clear e H H0 Heq | clear e n H Heq Heq0]; funelim (negate p0); try inversion e; subst.
    - (* this would work under two conditions: (1) and_or_imp_size (negate (p and q)) = and_or_imp_size (p and q) *)
  Abort.
  
  
  Lemma negate_is_neg_of_impl_impl_result_smaller p q r:
    negate p = patt_not (q ---> r) ->
    and_or_imp_size (q ---> r) <= and_or_imp_size p.
  Proof.
    intros H.
    funelim (negate p); subst.
    - clear H H0 Heq.
      rewrite -Heqcall in H1. inversion H1. subst.
      funelim (and_or_imp_size (p1' and p2')); try inversion e; subst; solve_match_impossibilities.
      clear e H H0 H3 Heq.
      rewrite H1. apply negate_is_bot in H1. rewrite H1.
      funelim (and_or_imp_size (¬ ⊥)); try inversion e; subst; solve_match_impossibilities.
      clear e n Heq H Heq0.
      funelim (and_or_imp_size (⊥)); try inversion e; subst; solve_match_impossibilities.
      clear.
      Search and_or_imp_size patt_not.
      funelim (and_or_imp_size (negate p1'0 ---> ⊥)); try inversion e; subst; solve_match_impossibilities.
      + 
      
  Abort.
  
  
  Check match_not.
  Lemma max_negation_size_negate p:
    is_inl (match_imp p) ->
    max_negation_size (negate p) < max_negation_size (patt_not p).
  Proof.
    intros Himp.
    remember (size' p) as sz.
    assert (Hsz: size' p <= sz).
    { lia. }
    clear Heqsz.

    move: p Himp Hsz.
    induction sz; intros p Himp Hsz; destruct p; simpl in Hsz; try lia; try inversion Himp.

    clear Himp.
    funelim (negate _); try inversion e; subst.
    - clear e H H0 Heq.
      funelim (max_negation_size _); try inversion e; subst.
      + clear e Heq.
        rewrite max_negation_size_not.
        rewrite H1.
        (* (¬ (negate p1'0)) can be patt_and *)
        (* the RHS is patt_and *)

        
        funelim (and_or_imp_size (¬ p1'0 or ¬ p2' ---> ⊥)); try inversion e; subst.
        4: {
          fold (patt_not (¬ p1'0 or ¬ p2')) in Heq1.
          solve_match_impossibilities.
        }
        3: {
          fold (patt_not (¬ p1'0 or ¬ p2')) in Heq2.
          fold (patt_and p1'0 p2') in Heq2.
          solve_match_impossibilities.
        }
        2: {
          fold (patt_not (¬ p1'0 or ¬ p2')) in Heq0.
          fold (patt_and p1'0 p2') in Heq0.
          solve_match_impossibilities.
        }
        clear e H H0 Heq.

        
        funelim (and_or_imp_size (¬ negate p1')); try inversion e; subst;
          solve_match_impossibilities.
        * clear e H H0 Heq.
          funelim (negate p1'0); try inversion e; subst.
          5: { rewrite -Heqcall in H3. inversion H3. }
          4: { rewrite -Heqcall in H3. inversion H3. }
          3: { rewrite H3 in H.
               pose proof (n p1'1 p2'). rewrite H in H0. contradiction.
          }
          2: {
            rewrite -Heqcall in H3. inversion H3.
          }
          clear H2.
          rewrite -Heqcall in H3. inversion H3.
          clear H H0 Heq.
          simpl in Hsz.
          remember (match_imp p1'1) as Hmip1'1.
          remember (match_imp p2'0) as Hmip2'0.
          
          destruct Hmip1'1, Hmip2'0.
          -- symmetry in HeqHmip1'1.
             symmetry in HeqHmip2'0.
             assert (Htmp: match_imp p1'1).
             { rewrite HeqHmip1'1. reflexivity. }
             pose proof (IH1 := IHsz p1'1 Htmp).
             clear Htmp.
             assert (Htmp: match_imp p2'0).
             { rewrite HeqHmip2'0. reflexivity. }
             pose proof (IH2 := IHsz p2'0 Htmp).
             clear Htmp.
             destruct s0 as [p1 [p2 Hp1p2]].
             subst p2'0.
             destruct s as [p1'' [p2'' Hp1p2'']].
             subst p1'1.
             
             rewrite H4 in H3. rewrite H5 in H3. clear H3.

             clear HeqHmip1'1. clear HeqHmip2'0.

             apply negate_is_bot in H1.
             subst p2'1.
             simpl in *.
             (* I want to prove that and_or_imp_size (p1'' ---> p2'') < and_or_imp_size p1',
               given that negate p1' = (¬ (p1'' ---> p2'')) *)
             (* I want a lemma saying that if negate x = ¬ (p ---> q),
                then size' p < size' x and size' q < size' x. *)
             (* ¬ (a -> b) = p and q = ¬ (¬ p or ¬ q)
                <==>
                a -> b = ¬ p or ¬ q = ¬ ¬ p ---> ¬ p

                ¬ (a -> b) = p or q = ¬ p ---> q
                (a ---> b) ---> ⊥ = (p ---> ⊥) ---> q
                a = p /\ b = ⊥ /\ q = ⊥
             *)
                
  Abort.
  *)


  Lemma negate_not_imp_is_not p:
    (forall p1 p2, p <> (p1 ---> p2)) ->
    negate p = ¬ p.
  Proof.
    intro H.
    funelim (negate p); try inversion e; subst; solve_match_impossibilities.
    5: { reflexivity. }
    4: {
      pose proof (Htmp := H0 p1 p2). contradiction.
    }
    3: {
      pose proof (Htmp := H p1' ⊥). contradiction.
    }
    2: {
      pose proof (Htmp := H1 (¬ p1') p2'). contradiction.
    }
    1: {
      unfold patt_and, patt_or in H1.
      unfold patt_not in H1 at 1.
      pose proof (Htmp := H1 (¬ ¬ p1' ---> ¬ p2') ⊥). contradiction.
    }
  Qed.
  
    
    
    
    
  
  (* p1 ---> (⊥ and ⊥) ==> ¬ p1 or (⊥ and ⊥) *)
  (* abstract (p1 ---> p2) where p2 <> \bot  ===> abstract (¬ p1) = abstract (p1 ---> ⊥)   *)
  (* abstract (¬ (p1 ---> p2)) ==> abstract (negate (p1 ---> p2))
     max_negation_size (¬ (p1 ---> p2)) > max_negation_size (negate (p1 ---> p2))
  *)
  Equations? abstract'
           (ap : Pattern)
           (wfap : well_formed ap)
           (p : Pattern)
           (wfp : well_formed p)
    : PropPattern by wf p aoisz_mns_lexprod :=
    abstract' ap wfap p wfp with match_and p => {
      | inl (existT p1 (existT p2 e)) := pp_and (abstract' ap wfap p1 _) (abstract' ap wfap p2 _) ;
      | inr _ with match_or p => {
          | inl (existT p1 (existT p2 e)) := pp_or (abstract' ap wfap p1 _) (abstract' ap wfap p2 _) ;
          | inr _  with match_not p => {
              | inl (existT p' e) with match_imp p' => {
                  | inl _ :=
                    let np' := negate p' in
                    abstract' ap wfap np' _ ;
                  | inr _ := pp_natomic p' _
                }
              | inr _
                  with match_imp p => {
                  | inl (existT p1 (existT p2 _)) :=
                    pp_or (abstract' ap wfap (¬ p1) _) (abstract' ap wfap p2 _)
                  | inr _ with match_bott p => {
                      | inl e := pp_and (pp_atomic ap wfap) (pp_natomic ap wfap) ;
                      | inr _ := pp_atomic p wfp
                    }
                }                 
            }
        }
    }.
  Proof.
    - admit.
    - subst. clear abstract'.
      unfold aoisz_mns_lexprod.
      unfold aoisz_mns_lexprod'.
      apply left_lex'.
      funelim (and_or_imp_size (p1 and p2)); try inversion e; subst; solve_match_impossibilities.
      lia.
    - admit.
    - subst. clear abstract'.
      unfold aoisz_mns_lexprod.
      unfold aoisz_mns_lexprod'.
      apply left_lex'. unfold ltof.
      funelim (and_or_imp_size (p1 and p2)); try inversion e; subst; solve_match_impossibilities.
      lia.
    - admit.
    - subst. clear abstract'.
      unfold aoisz_mns_lexprod.
      unfold aoisz_mns_lexprod'.
      apply left_lex'. unfold ltof.
      funelim (and_or_imp_size (p1 or p2)); try inversion e; subst; solve_match_impossibilities.
      lia.
    - admit.
    - subst. clear abstract'.
      unfold aoisz_mns_lexprod.
      unfold aoisz_mns_lexprod'.
      apply left_lex'. unfold ltof.
      funelim (and_or_imp_size (p1 or p2)); try inversion e; subst; solve_match_impossibilities.
      lia.
    - admit.
    - subst. clear abstract'.
      unfold np'. clear np'.
      destruct s as [p1 [p2 Heqp']].
      subst.
      unfold aoisz_mns_lexprod.
      unfold aoisz_mns_lexprod'.
      rewrite and_or_imp_size_negate.
      funelim (and_or_imp_size (¬ (p1 ---> p2))); try inversion e; subst; solve_match_impossibilities.
      + pose proof (Htmp := n p1' p2').
        rewrite e in Htmp. contradiction.
      + pose proof (Htmp := n0 p1' ⊥).
        rewrite e in Htmp. contradiction.
      + apply right_lex'.
        clear e n0 n Heq H Heq0 Heq1.
        funelim (max_negation_size (¬ (p1 ---> p2))); try inversion e; subst; solve_match_impossibilities.
        { pose proof (Htmp := n2 p1 p2). contradiction. }
        { pose proof (Htmp := n1 p1 ⊥). contradiction. }
        clear.


        remember (p1 ---> p2) as p1ip2.
        remember (size' p1ip2) as sz. rewrite Heqsz.
        assert (Hsz: size' p1ip2 <= sz) by lia.
        clear Heqsz.

        subst.
        move: p1 p2 Hsz.
        induction sz; intros p1 p2 Hsz; subst; simpl in Hsz; try lia.
        simpl.
        funelim (negate (p1 ---> p2)); try inversion e; subst; solve_match_impossibilities.
        * clear e H H0 Heq.
          remember (match_imp p1') as mip1'.
          remember (match_imp p2') as mip2'.
          destruct mip1',mip2'.
          -- destruct s as [a [b Hab]].
             destruct s0 as [c [d Hcd]].
             subst. simpl in Hsz.
             pose proof (IH1 := IHsz a b ltac:(simpl; lia)).
             pose proof (IH2 := IHsz c d ltac:(simpl; lia)).
             funelim (max_negation_size (negate (a ---> b) or negate (c ---> d)));
               try inversion e; subst; solve_match_impossibilities.
             clear -IH1 IH2.
             simpl in *. lia.
          -- admit.
          -- admit.
          -- simpl in *. clear -n n0.
             Check negate_not_imp_is_not.
             apply negate_not_imp_is_not in n.
             apply negate_not_imp_is_not in n0.
             rewrite n n0.
             funelim (max_negation_size (¬ p1' or ¬ p2')); try inversion e; subst;
               solve_match_impossibilities.
             
             clear.
             
             funelim (max_negation_size (¬ p1')); try inversion e; subst;
               solve_match_impossibilities;
             funelim (max_negation_size (¬ p2')); try inversion e; subst;
               solve_match_impossibilities; simpl in *; try lia.
        * 
      
  Abort.
  

  
  
  (* normalize (s1 and s2) = (normalize s1) and (normalize s2) *)
  (* normalize (s1 or s2) = normalize (¬ s1 ---> s2)*)
  Equations? normalize' (ap : Pattern) (p : Pattern) : Pattern by wf (max_negation_size p) lt :=
    normalize' ap p with match_and p => {
      | inl (existT p1 (existT p2 e)) := patt_and (normalize' ap p1) (normalize' ap p2) ;
      | inr _  with match_not p => {
          | inl (existT p' e) with match_imp p' => {
              | inl _ :=
                let np' := negate p' in
                normalize' ap np' ;
              | inr _ := p
            }
          | inr _
              with match_imp p => {
              | inl (existT p1 (existT p2 _)) := patt_imp (normalize' ap p1) (normalize' ap p2) ;
              | inr _ with match_bott p => {
                  | inl e := patt_and ap (patt_not ap) ;
                  | inr _ := p
                }               
            }                     
        }
    }.
  Proof.
    - subst p.
      funelim (max_negation_size (p1 and p2)); try inversion e; subst; solve_match_impossibilities.
      lia.
    - subst p.
      funelim (max_negation_size (p1 and p2)); try inversion e; subst; solve_match_impossibilities.
      lia.
    - admit.
    - subst p.
      funelim (max_negation_size (p1 ---> p2)); try inversion e; subst; solve_match_impossibilities.
      
      3: { lia. }
      2: {
        clear.
        destruct p1'; simpl in *; funelim (max_negation_size _); try inversion e; subst; solve_match_impossibilities; simpl in *; try lia.
      }
      

      destruct s as [p1 [p2 Himp]]. subst p'.
      unfold np'.
      clear.
      remember (size' (p1 ---> p2)) as sz.
      assert (Hsz: (size' (p1 ---> p2)) <= sz).
      { lia. }
      clear Heqsz.

      move: p1 p2 Hsz.
      induction sz; intros p1 p2 Hsz; simpl in *; try lia.
      
      funelim (max_negation_size (¬ (p1 ---> p2))); try inversion e; subst; solve_match_impossibilities.
      simpl.
      funelim (negate (p1 ---> p2)); try inversion e; subst; solve_match_impossibilities.
      + clear -IHsz Hsz. 
        funelim (max_negation_size (negate p1' or negate p2')); try inversion e; subst.
        * simpl. rewrite H1.
          apply negate_is_bot in H1. subst p2'. simpl in *.
          clear -IHsz Hsz.
          pose proof (IH1 := IHsz p1'0 (⊥)  ltac:(simpl; lia)).
          funelim (max_negation_size (¬ (p1'0 ---> ⊥))); try inversion e; subst; solve_match_impossibilities.
          clear e Heq. clear Heqcall.
          funelim (max_negation_size (negate (p1'0 ---> ⊥))); try inversion e; subst; solve_match_impossibilities.
          3: {
            (* Heqcall should imply that p1'0 is an atomic proposition - a symbol or variable *)
            clear -Heqcall.

            destruct p1'0; simpl in *; funelim (negate _); try inversion e; subst; solve_match_impossibilities; simpl in *; try lia.

            (*
            (((~p1') or (~p2')) –> bot) –> bot
            ~(~(~p1' or ~p2'))
            ~(p1' and p2')
            maxₙegationₛize (p1' and p2')
            ~(s1' and s2') ==> negate (s1' and s2') = ¬ (¬ s1' or ¬ s2') = s1' and s2'
            ~s1' or ~s2'
             *)
                                               
            
            funelim (negate (p1'0 ---> ⊥)); try inversion e; subst; solve_match_impossibilities.
          }
          
          
          assert (size' (negate p1'0) < size' p1'0) by admit.
          simpl. 
      unfold size'.
      unfold max_negation_size.
  Defined.
  


  (* TODO: a function [abstract : Pattern -> PropPattern] *)
End ml_tauto.
