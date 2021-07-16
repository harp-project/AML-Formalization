From Coq Require Import ssreflect ssrfun ssrbool.
From Coq Require Import Ensembles Logic.Classical_Prop.
From Coq Require Import Arith.Wf_nat Relations.Relation_Operators Wellfounded.Lexicographic_Product.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq.micromega Require Import Lia.

From Equations Require Import Equations.

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

  Equations and_or_imp_size (p : Pattern) : nat by wf p (Pattern_subterm Σ) :=
    and_or_imp_size p with match_and p => {
      | inl (existT p1' (existT p2' e)) := 1 + (and_or_imp_size p1') + (and_or_imp_size p2') ;
      | inr _
          with match_not p => {
          | inl (existT p1' e) := and_or_imp_size p1';
          | inr _
              with match_or p => {
              | inl (existT p1' (existT p2' e)) := 1 + (and_or_imp_size p1') + (and_or_imp_size p2') ;
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


  
  Lemma and_or_imp_size_not p :
    and_or_imp_size (patt_not p) = and_or_imp_size p.
  Proof.
    remember (size' p) as sz.
    assert (Hsz: size' p <= sz).
    { lia. }
    clear Heqsz.

    move: p Hsz.
    induction sz; intros p Hsz; destruct p; simpl in Hsz; try lia;
      funelim (and_or_imp_size _); try inversion e; subst; auto.
    - funelim (and_or_imp_size (¬ ¬ p1' ---> ¬ p2')); try inversion e; subst.
      + simpl in Hsz. repeat rewrite IHsz. lia. lia. reflexivity.
      + simpl in Hsz. repeat rewrite IHsz. simpl. lia. lia. lia. reflexivity.
      + solve_match_impossibilities.
    - solve_match_impossibilities.
    - solve_match_impossibilities.
    - solve_match_impossibilities.
  Qed.
  
  
  Equations max_negation_size (p : Pattern) : nat by wf p (Pattern_subterm Σ) :=
    max_negation_size p with match_not p => {
      | inl (existT p1' e) := and_or_imp_size p1';
      | inr _
          with match_imp p => {
          | inl (existT p1 (existT p2 _)) := Nat.max (max_negation_size p1) (max_negation_size p2)
          | inr _ => 0
        }
    }.
  Solve Obligations with
      (Tactics.program_simplify; CoreTactics.equations_simpl; try Tactics.program_solve_wf).
  
  Lemma max_negation_size_not p:
    max_negation_size (patt_not p) = and_or_imp_size p.
  Proof.
    funelim (max_negation_size _); try inversion e; subst.
    + reflexivity.
    + solve_match_impossibilities.
    + solve_match_impossibilities.
  Qed.
  
  Lemma max_negation_size_negate p q :
    max_negation_size (negate (p ---> q)) < max_negation_size (patt_not (p ---> q)).
  Proof.
    funelim (negate _); try inversion e; subst;
      funelim (max_negation_size _); try inversion e; subst; solve_match_impossibilities;
        funelim (max_negation_size _); try inversion e; subst; solve_match_impossibilities.

    - rewrite H3.
      clear Heq0 Heq1.
    
    

    remember (size' (p ---> q)) as sz.
    assert (Hsz: size' (p ---> q) <= sz).
    { lia. }
    clear Heqsz.

    induction p; funelim (negate _); try inversion e; subst;
      rewrite ?max_negation_size_not; simpl; solve_match_impossibilities.

    - funelim (max_negation_size _); try inversion e; subst.
      funelim (and_or_imp_size _); try inversion e; subst.
      funelim (and_or_imp_size _); try inversion e; subst.
      lia. lia. lia.
    - 
      
    try (funelim (max_negation_size _); try inversion e; lia).
    12: {

    (* Does not hold *)
  Abort.
  
  
  Equations? normalize' (ap : Pattern) (p : Pattern) : Pattern by wf (max_negation_size p) lt :=
    normalize' ap p with match_not p => {
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
    }.
  Proof.
    - subst p.
  Defined.
  


  (* TODO: a function [abstract : Pattern -> PropPattern] *)
End ml_tauto.
