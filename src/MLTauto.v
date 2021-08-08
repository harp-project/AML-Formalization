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

  Lemma negate_equiv Γ (p : Pattern) :
    well_formed p ->
    Γ ⊢ ((patt_not p) <---> (negate p)).
  Proof.
    intros Hwfp.
    remember (size' p) as sz.
    assert (Hsz: size' p <= sz).
    { lia. }
    clear Heqsz.


    Tactic Notation "make_step" ident(Γ) ident(star) constr(p) constr(q) constr(ctx_expr) tactic(simpl_tactic) :=
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
      assert (Hctx: (Γ ⊢ (emplace ctx p <---> emplace ctx q)));
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
      
      assert (Step1: (Γ ⊢
                                ((¬ (¬ p1' or ¬ p2' ---> ⊥) ---> (¬ p1') or negate p2')
                                   and (negate p1' or negate p2' ---> ¬ (¬ p1' or ¬ p2' ---> ⊥)))
                     ->
                     (Γ ⊢ ((¬ (¬ p1' or ¬ p2' ---> ⊥) ---> negate p1' or negate p2')
                                             and (negate p1' or negate p2' ---> ¬ (¬ p1' or ¬ p2' ---> ⊥)))))
             ).
      {
        intros BigH.
        

        make_step
          Γ
          star
          (¬ p1')
          (negate p1')
          ((¬ (¬ p1' or ¬ p2' ---> ⊥) ---> (patt_free_evar star) or negate p2')
             and (negate p1' or negate p2' ---> ¬ (¬ p1' or ¬ p2' ---> ⊥)))
          (rewrite ?Hcount_p1' ?Hcount_p2' ?Hcount_np1' ?Hcount_np2')
        .
      }
      apply Step1. clear Step1.

      assert (Step2: (Γ ⊢
                                ((¬ (¬ p1' or ¬ p2' ---> ⊥) ---> (¬ p1') or ¬ p2')
                                   and (negate p1' or negate p2' ---> ¬ (¬ p1' or ¬ p2' ---> ⊥)))
                     ->
                     (Γ ⊢ ((¬ (¬ p1' or ¬ p2' ---> ⊥) ---> ¬ p1' or negate p2')
                                             and (negate p1' or negate p2' ---> ¬ (¬ p1' or ¬ p2' ---> ⊥)))))
             ).
      {
        intros BigH.

        make_step
          Γ
          star
          (¬ p2')
          (negate p2')
          ((¬ (¬ p1' or ¬ p2' ---> ⊥) ---> ¬ p1' or (patt_free_evar star))
             and (negate p1' or negate p2' ---> ¬ (¬ p1' or ¬ p2' ---> ⊥)))
          (rewrite ?Hcount_p1' ?Hcount_p2' ?Hcount_np1' ?Hcount_np2')
        .
      }
      apply Step2. clear Step2.

      assert (Step3: (Γ ⊢
                                ((¬ (¬ p1' or ¬ p2' ---> ⊥) ---> (¬ p1') or ¬ p2')
                                   and (¬ p1' or negate p2' ---> ¬ (¬ p1' or ¬ p2' ---> ⊥)))
                      ->
                      (Γ ⊢ ((¬ (¬ p1' or ¬ p2' ---> ⊥) ---> ¬ p1' or ¬ p2')
                                              and (negate p1' or negate p2' ---> ¬ (¬ p1' or ¬ p2' ---> ⊥)))))
             ).
      {
        intros BigH.

        make_step
          Γ
          star
          (¬ p1')
          (negate p1')
          ((¬ (¬ p1' or ¬ p2' ---> ⊥) ---> ¬ p1' or ¬ p2')
             and ((patt_free_evar star) or negate p2' ---> ¬ (¬ p1' or ¬ p2' ---> ⊥)))
          (rewrite ?Hcount_p1' ?Hcount_p2' ?Hcount_np1' ?Hcount_np2')
        .          
      }
      apply Step3. clear Step3.


      assert (Step4: (Γ ⊢
                                ((¬ (¬ p1' or ¬ p2' ---> ⊥) ---> (¬ p1') or ¬ p2')
                                   and (¬ p1' or ¬ p2' ---> ¬ (¬ p1' or ¬ p2' ---> ⊥)))
                      ->
                      (Γ ⊢ ((¬ (¬ p1' or ¬ p2' ---> ⊥) ---> ¬ p1' or ¬ p2')
                                              and (¬ p1' or negate p2' ---> ¬ (¬ p1' or ¬ p2' ---> ⊥)))))
             ).
      {
        intros BigH.

        make_step
          Γ
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

      assert (Step1: (Γ ⊢
                                ((¬ (¬ p1' ---> p2') ---> ¬ p1' and negate p2')
                                   and (negate p1' and negate p2' ---> ¬ (¬ p1' ---> p2'))))
                     ->
                      (Γ ⊢
                                ((¬ (¬ p1' ---> p2') ---> negate p1' and negate p2')
                                   and (negate p1' and negate p2' ---> ¬ (¬ p1' ---> p2'))))
                                
             ).
      {
        intros BigH.

        make_step
          Γ
          star
          (¬ p1')
          (negate p1')
          ((¬ (¬ p1' ---> p2') ---> (patt_free_evar star) and negate p2')
             and (negate p1' and negate p2' ---> ¬ (¬ p1' ---> p2')))
          (rewrite ?Hcount_p1' ?Hcount_p2' ?Hcount_np1' ?Hcount_np2')
        .
      }
      apply Step1. clear Step1.

      assert (Step2: (Γ ⊢
                                ((¬ (¬ p1' ---> p2') ---> ¬ p1' and ¬ p2')
                                   and (negate p1' and negate p2' ---> ¬ (¬ p1' ---> p2'))))
                     ->
                      (Γ ⊢
                                ((¬ (¬ p1' ---> p2') ---> ¬ p1' and negate p2')
                                   and (negate p1' and negate p2' ---> ¬ (¬ p1' ---> p2'))))
                                
             ).
      {
        intros BigH.

        make_step
          Γ
          star
          (¬ p2')
          (negate p2')
          ((¬ (¬ p1' ---> p2') ---> ¬ p1' and (patt_free_evar star))
             and (negate p1' and negate p2' ---> ¬ (¬ p1' ---> p2')))
          (rewrite ?Hcount_p1' ?Hcount_p2' ?Hcount_np1' ?Hcount_np2')
        .
      }
      apply Step2. clear Step2.

      assert (Step3: (Γ ⊢
                                ((¬ (¬ p1' ---> p2') ---> ¬ p1' and ¬ p2')
                                   and (¬ p1' and negate p2' ---> ¬ (¬ p1' ---> p2'))))
                     ->
                      (Γ ⊢
                                ((¬ (¬ p1' ---> p2') ---> ¬ p1' and ¬ p2')
                                   and (negate p1' and negate p2' ---> ¬ (¬ p1' ---> p2'))))
                                
             ).
      {
        intros BigH.

        make_step
          Γ
          star
          (¬ p1')
          (negate p1')
          ((¬ (¬ p1' ---> p2') ---> ¬ p1' and ¬ p2')
             and ((patt_free_evar star) and negate p2' ---> ¬ (¬ p1' ---> p2')))
          (rewrite ?Hcount_p1' ?Hcount_p2' ?Hcount_np1' ?Hcount_np2')
        .
      }
      apply Step3. clear Step3.

      assert (Step4: (Γ ⊢
                                ((¬ (¬ p1' ---> p2') ---> ¬ p1' and ¬ p2')
                                   and (¬ p1' and ¬ p2' ---> ¬ (¬ p1' ---> p2'))))
                     ->
                      (Γ ⊢
                                ((¬ (¬ p1' ---> p2') ---> ¬ p1' and ¬ p2')
                                   and (¬ p1' and negate p2' ---> ¬ (¬ p1' ---> p2'))))
                                
             ).
      {
        intros BigH.

        make_step
          Γ
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

      assert (Step1: (Γ ⊢ ((¬ (p1 ---> p2) ---> p1 and ¬ p2)
                                and (p1 and negate p2 ---> ¬ (p1 ---> p2))))
                     ->
                     (Γ ⊢ ((¬ (p1 ---> p2) ---> p1 and negate p2)
                                and (p1 and negate p2 ---> ¬ (p1 ---> p2))))
                       
             ).
      {
        intros BigH.

        make_step
          Γ
          star
          (¬ p2)
          (negate p2)
          ((¬ (p1 ---> p2) ---> p1 and (patt_free_evar star))
             and (p1 and negate p2 ---> ¬ (p1 ---> p2)))
          (rewrite ?Hcount_p1 ?Hcount_p2 ?Hcount_np2)
        .
      }
      apply Step1. clear Step1.

      assert (Step2: (Γ ⊢ ((¬ (p1 ---> p2) ---> p1 and ¬ p2)
                                             and (p1 and ¬ p2 ---> ¬ (p1 ---> p2))))
                     ->
                     (Γ ⊢ ((¬ (p1 ---> p2) ---> p1 and ¬ p2)
                                             and (p1 and negate p2 ---> ¬ (p1 ---> p2))))
                       
             ).
      {
        intros BigH.

        make_step
          Γ
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

  Lemma negate_is_bot p:
    negate p = patt_bott ->
    p = ¬ ⊥.
  Proof.
    intros H.
    funelim (negate p); try inversion e; subst; try discriminate.
    - rewrite -Heqcall in H1. inversion H1.
    - rewrite H. reflexivity.
    - rewrite -Heqcall in H0. inversion H0.
    - rewrite -Heqcall in H. inversion H.
  Qed.


  (* The key property I want is that [and_or_imp_size (negate p) = and_or_imp_size p].
     > For this to hold, we need to resolve the not/or overlap in both functions
     > in the same way.
     Really? Actually, I thin the reason is different: see the comment in the proof
     of [and_or_imp_size_negate].
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
                  | inr _ => 0
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
      (* here we need the [patt_or] at the LHS to *not* be interpreted as [patt_not],
         because if it is interpreted as patt_not, then the lhs is equal to 
         [aoisz (negate p1')] and the lhs to [1 + aoisz p1' + aoisz p2'].
         For example, if [p1 = ¬ s₁] and [p2 = ¬ ⊥], then
         and_or_imp_size (negate (¬ s1 or ¬ ⊥))
         = and_or_imp_size (negate (¬ s1) or negate (¬ ⊥))
         =(1) and_or_imp_size (s₁ or ⊥)
         = and_or_imp_size (¬ ¬ s₁)
         = and_or_imp_size (¬ s₁)
         = and_or_imp_size s₁
         < 1 + and_or_imp_size (¬ s₁) + and_or_imp_size ⊥
         = and_or_imp_size (¬ s₁ or ¬ ⊥).
       *)

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
            }
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
                    abstract' ap wfap (negate p') _ ;
                  | inr _ := pp_natomic p' _
                }
              | inr _
                  with match_imp p => {
                  | inl (existT p1 (existT p2 _)) :=
                    pp_or (abstract' ap wfap (negate p1) _) (abstract' ap wfap p2 _)
                  | inr _ with match_bott p => {
                      | inl e := pp_and (pp_atomic ap wfap) (pp_natomic ap wfap) ;
                      | inr _ := pp_atomic p wfp
                    }
                }                 
            }
        }
    }.
  Proof.
    - subst. clear abstract'.
      unfold well_formed,well_formed_closed in wfp.
      simpl in wfp.
      rewrite !andbT in wfp.
      apply andb_prop in wfp. destruct wfp as [wf1 wf2].
      apply andb_prop in wf1. destruct wf1 as [wf11 wf12].
      apply andb_prop in wf2. destruct wf2 as [wf21 wf22].
      unfold well_formed,well_formed_closed.
      rewrite wf11 wf21. reflexivity.
    - subst. clear abstract'.
      unfold aoisz_mns_lexprod.
      unfold aoisz_mns_lexprod'.
      apply left_lex'.
      funelim (and_or_imp_size (p1 and p2)); try inversion e; subst; solve_match_impossibilities.
      lia.
    - subst. clear abstract'.
      unfold well_formed,well_formed_closed in wfp.
      simpl in wfp.
      rewrite !andbT in wfp.
      apply andb_prop in wfp. destruct wfp as [wf1 wf2].
      apply andb_prop in wf1. destruct wf1 as [wf11 wf12].
      apply andb_prop in wf2. destruct wf2 as [wf21 wf22].
      unfold well_formed,well_formed_closed.
      rewrite wf12 wf22. reflexivity.
    - subst. clear abstract'.
      unfold aoisz_mns_lexprod.
      unfold aoisz_mns_lexprod'.
      apply left_lex'. unfold ltof.
      funelim (and_or_imp_size (p1 and p2)); try inversion e; subst; solve_match_impossibilities.
      lia.
    - subst. clear abstract'.
      unfold well_formed,well_formed_closed in wfp.
      simpl in wfp.
      rewrite !andbT in wfp.
      apply andb_prop in wfp. destruct wfp as [wf1 wf2].
      apply andb_prop in wf1. destruct wf1 as [wf11 wf12].
      apply andb_prop in wf2. destruct wf2 as [wf21 wf22].
      unfold well_formed,well_formed_closed.
      rewrite wf11 wf21. reflexivity.
    - subst. clear abstract'.
      unfold aoisz_mns_lexprod.
      unfold aoisz_mns_lexprod'.
      apply left_lex'. unfold ltof.
      funelim (and_or_imp_size (p1 or p2)); try inversion e; subst; solve_match_impossibilities.
      lia.
    - subst. clear abstract'.
      unfold well_formed,well_formed_closed in wfp.
      simpl in wfp.
      rewrite !andbT in wfp.
      apply andb_prop in wfp. destruct wfp as [wf1 wf2].
      apply andb_prop in wf1. destruct wf1 as [wf11 wf12].
      apply andb_prop in wf2. destruct wf2 as [wf21 wf22].
      unfold well_formed,well_formed_closed.
      rewrite wf12 wf22. reflexivity.
    - subst. clear abstract'.
      unfold aoisz_mns_lexprod.
      unfold aoisz_mns_lexprod'.
      apply left_lex'. unfold ltof.
      funelim (and_or_imp_size (p1 or p2)); try inversion e; subst; solve_match_impossibilities.
      lia.
    - subst. clear -wfp.
      unfold well_formed,well_formed_closed in wfp.
      simpl in wfp.
      rewrite !andbT in wfp.
      apply wf_negate.
      apply andb_prop in wfp. destruct wfp as [wf1 wf2].
      unfold well_formed,well_formed_closed.
      rewrite wf1 wf2. reflexivity.
    - subst. clear abstract'.
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
             clear Heqmip1' Heqmip2'.
             funelim (max_negation_size (negate (a ---> b) or negate (c ---> d)));
               try inversion e; subst; solve_match_impossibilities.
             clear -IH1 IH2.
             simpl in *. lia.
          -- destruct s as [a [b Hab]].
             subst. simpl in Hsz.
             clear Heqmip1' Heqmip2'.
             pose proof (IH1 := IHsz a b ltac:(simpl; lia)).
             pose proof (Hn := negate_not_imp_is_not _ n).
             clear n IHsz.
             funelim (max_negation_size (negate (a ---> b) or negate p2'));
               try inversion e; subst; solve_match_impossibilities.
             clear -IH1 Hn.
             rewrite Hn.
             pose proof (Hsznp2' := max_negation_size_not p2').
             simpl in *. lia.
          -- destruct s as [a [b Hab]].
             subst. simpl in Hsz.
             clear Heqmip1' Heqmip2'.
             pose proof (IH1 := IHsz a b ltac:(simpl; lia)).
             pose proof (Hn := negate_not_imp_is_not _ n).
             clear IHsz n.
             funelim (max_negation_size (negate p1' or negate (a ---> b)));
               try inversion e; subst; solve_match_impossibilities.
             clear -IH1 Hn.
             rewrite Hn.
             pose proof (Isznp1' := max_negation_size_not p1').
             simpl in *. lia.
          -- simpl in *. clear -n n0.
             apply negate_not_imp_is_not in n.
             apply negate_not_imp_is_not in n0.
             rewrite n n0.
             clear n n0.
             funelim (max_negation_size (¬ p1' or ¬ p2')); try inversion e; subst;
               solve_match_impossibilities.
             
             clear.
             pose proof (Hsznp1' := max_negation_size_not p1').
             pose proof (Hsznp2' := max_negation_size_not p2').
             lia.
        * 
          remember (match_imp p1') as mip1'.
          remember (match_imp p2') as mip2'.
          destruct mip1',mip2'.
          -- destruct s as [a [b Hab]].
             destruct s0 as [c [d Hcd]].
             subst. simpl in Hsz.
             pose proof (IH1 := IHsz a b ltac:(simpl; lia)).
             pose proof (IH2 := IHsz c d ltac:(simpl; lia)).
             clear IHsz Hsz Heqmip1' Heqmip2' Heq0 H0 Heq e n H.
             funelim (max_negation_size (negate (a ---> b) and negate (c ---> d)));
               try inversion e; subst; solve_match_impossibilities.
             clear -IH1 IH2.
             simpl in *. lia.
          -- destruct s as [a [b Hab]].
             subst. simpl in Hsz.
             pose proof (IH1 := IHsz a b ltac:(simpl; lia)).
             pose proof (Hn := negate_not_imp_is_not _ n0).
             clear IHsz Hsz Heqmip1' Heqmip2' H n e H0 Heq0 Heq n0.
             funelim (max_negation_size (negate (a ---> b) and negate p2'));
               try inversion e; subst; solve_match_impossibilities.
             clear -IH1 Hn.
             rewrite Hn.
             pose proof (Hsznp2' := max_negation_size_not p2').
             simpl in *. lia.
          -- destruct s as [a [b Hab]].
             subst. simpl in Hsz.
             pose proof (IH1 := IHsz a b ltac:(simpl; lia)).
             pose proof (Hn := negate_not_imp_is_not _ n0).
             clear IHsz Hsz Heqmip1' Heqmip2' Heq0 Heq H H0 e n n0.
             funelim (max_negation_size (negate p1' and negate (a ---> b)));
               try inversion e; subst; solve_match_impossibilities.
             clear -IH1 Hn.
             rewrite Hn.
             pose proof (Isznp1' := max_negation_size_not p1').
             simpl in *. lia.
          -- simpl in *. clear -n0 n1.
             apply negate_not_imp_is_not in n0.
             apply negate_not_imp_is_not in n1.
             rewrite n0 n1. clear n0 n1.
             funelim (max_negation_size (¬ p1' and ¬ p2')); try inversion e; subst;
               solve_match_impossibilities.
             
             clear.
             pose proof (Hsznp1' := max_negation_size_not p1').
             pose proof (Hsznp2' := max_negation_size_not p2').
             lia.
        * clear.
          pose proof (max_negation_size_lt p1').
          lia.
        * remember (match_imp p2) as mip2.
          destruct mip2.
          -- destruct s as [a [b Hab]].
             subst. simpl in Hsz.
             pose proof (IH := IHsz a b ltac:(simpl; lia)).
             clear e Heq H IHsz Hsz Heqmip2.
             clear Heq0 Heq1 Heq2 n n0 n1.
             funelim (max_negation_size (p1 and negate (a ---> b)));
               try inversion e; subst; solve_match_impossibilities.
             pose proof (Hszp1 := max_negation_size_lt p1).
             clear e H Heq H0.
             lia.
          -- simpl in *. clear -n2.
             apply negate_not_imp_is_not in n2.
             rewrite n2. clear n2.
             funelim (max_negation_size (p1 and ¬ p2));
               try inversion e; subst; solve_match_impossibilities.
             clear.
             pose proof (max_negation_size_lt p1).
             pose proof (max_negation_size_not p3).
             lia.

    - subst.
      clear abstract' n n0.
      unfold well_formed,well_formed_closed in wfp.
      simpl in wfp.
      rewrite !andbT in wfp.
      apply andb_prop in wfp. destruct wfp as [wf1 wf2].
      unfold well_formed,well_formed_closed.
      rewrite wf1 wf2. reflexivity.
    - subst.
      clear abstract' n0 n1.
      apply wf_negate.
      unfold well_formed,well_formed_closed in wfp.
      simpl in wfp.
      apply andb_prop in wfp. destruct wfp as [wf1 wf2].
      apply andb_prop in wf1. destruct wf1 as [wf11 wf12].
      apply andb_prop in wf2. destruct wf2 as [wf21 wf22].
      unfold well_formed,well_formed_closed.
      rewrite wf11 wf21. reflexivity.
    - subst.
      clear abstract'.
      unfold aoisz_mns_lexprod,aoisz_mns_lexprod'.
      apply left_lex'.
      funelim (and_or_imp_size (p1 ---> p2));
        try inversion e; subst; solve_match_impossibilities.
      3: { pose proof (n3 p1'). contradiction. }
      2: { pose proof (n1 p1' p2'). contradiction. }
      1: { unfold patt_and in n. unfold patt_not at 3 in n.
           pose proof (n p1' p2'). contradiction.
      }
      clear.
      rewrite and_or_imp_size_negate. lia.
    - subst.
      clear abstract' n n0 n1.
      unfold well_formed,well_formed_closed in wfp.
      simpl in wfp.
      apply andb_prop in wfp. destruct wfp as [wf1 wf2].
      apply andb_prop in wf1. destruct wf1 as [wf11 wf12].
      apply andb_prop in wf2. destruct wf2 as [wf21 wf22].
      unfold well_formed,well_formed_closed.
      rewrite wf12 wf22. reflexivity.
    - subst.
      clear abstract'.
      apply left_lex'.
      funelim (and_or_imp_size (p1 ---> p2));
        try inversion e; subst; solve_match_impossibilities.
      3: { pose proof (n3 p1'). contradiction. }
      2: { pose proof (n1 p1' p2'). contradiction. }
      1: { pose proof (n p1' p2'). contradiction. }
      clear.
      lia.
  Defined.


  Lemma wf_and_proj1 p q:
    well_formed (p and q) ->
    well_formed p.
  Proof.
    intros wfp'.
    unfold well_formed,well_formed_closed in wfp'.
    simpl in wfp'.
    rewrite !andbT in wfp'.
    apply andb_prop in wfp'.
    destruct wfp' as [wf'p wf'c].
    apply andb_prop in wf'p. apply andb_prop in wf'c.
    destruct wf'p as [wf'p1 wf'p2]. destruct wf'c as [wf'c1 wf'c2].
    unfold well_formed, well_formed_closed.
    rewrite wf'p1 wf'c1.
    reflexivity.
  Qed.

  Lemma wf_and_proj2 p q:
    well_formed (p and q) ->
    well_formed q.
  Proof.
    intros wfp'.
    unfold well_formed,well_formed_closed in wfp'.
    simpl in wfp'.
    rewrite !andbT in wfp'.
    apply andb_prop in wfp'.
    destruct wfp' as [wf'p wf'c].
    apply andb_prop in wf'p. apply andb_prop in wf'c.
    destruct wf'p as [wf'p1 wf'p2]. destruct wf'c as [wf'c1 wf'c2].
    unfold well_formed, well_formed_closed.
    rewrite wf'p2 wf'c2.
    reflexivity.
  Qed.


  Lemma wf_or_proj1 p q:
    well_formed (p or q) ->
    well_formed p.
  Proof.
    intros wfp'.
    unfold well_formed,well_formed_closed in wfp'.
    simpl in wfp'.
    rewrite !andbT in wfp'.
    apply andb_prop in wfp'.
    destruct wfp' as [wf'p wf'c].
    apply andb_prop in wf'p. apply andb_prop in wf'c.
    destruct wf'p as [wf'p1 wf'p2]. destruct wf'c as [wf'c1 wf'c2].
    unfold well_formed, well_formed_closed.
    rewrite wf'p1 wf'c1.
    reflexivity.
  Qed.

  Lemma wf_or_proj2 p q:
    well_formed (p or q) ->
    well_formed q.
  Proof.
    intros wfp'.
    unfold well_formed,well_formed_closed in wfp'.
    simpl in wfp'.
    rewrite !andbT in wfp'.
    apply andb_prop in wfp'.
    destruct wfp' as [wf'p wf'c].
    apply andb_prop in wf'p. apply andb_prop in wf'c.
    destruct wf'p as [wf'p1 wf'p2]. destruct wf'c as [wf'c1 wf'c2].
    unfold well_formed, well_formed_closed.
    rewrite wf'p2 wf'c2.
    reflexivity.
  Qed.

  Lemma wf_not_proj p:
    well_formed (¬ p) ->
    well_formed p.
  Proof.
    intros wfp.
    unfold well_formed,well_formed_closed in *.
    simpl in wfp.
    rewrite !andbT in wfp.
    exact wfp.
  Qed.
  
  Lemma wf_imp_proj1 p q:
    well_formed (p ---> q) ->
    well_formed p.
  Proof.
    intros wfp'.
    unfold well_formed,well_formed_closed in wfp'.
    simpl in wfp'.
    apply andb_prop in wfp'.
    destruct wfp' as [wf'p wf'c].
    apply andb_prop in wf'p. apply andb_prop in wf'c.
    destruct wf'p as [wf'p1 wf'p2]. destruct wf'c as [wf'c1 wf'c2].
    unfold well_formed, well_formed_closed.
    rewrite wf'p1 wf'c1.
    reflexivity.
  Qed.

  Lemma wf_imp_proj2 p q:
    well_formed (p ---> q) ->
    well_formed q.
  Proof.
    intros wfp'.
    unfold well_formed,well_formed_closed in wfp'.
    simpl in wfp'.
    apply andb_prop in wfp'.
    destruct wfp' as [wf'p wf'c].
    apply andb_prop in wf'p. apply andb_prop in wf'c.
    destruct wf'p as [wf'p1 wf'p2]. destruct wf'c as [wf'c1 wf'c2].
    unfold well_formed, well_formed_closed.
    rewrite wf'p2 wf'c2.
    reflexivity.
  Qed.

  
  #[local] Hint Resolve pp_flatten_well_formed : core.
  
  Lemma abstract'_correct Γ ap ϕ
    (wfap : well_formed ap)
    (wfϕ : well_formed ϕ):
    Γ ⊢ (ϕ <---> (pp_flatten (abstract' ap wfap ϕ wfϕ))).
  Proof.
    funelim (abstract' _ _ _ _); try inversion e; subst; solve_match_impossibilities.
    - pose proof (wfp1 := wf_and_proj1 _ _ wfp).
      pose proof (wfp2 := wf_and_proj2 _ _ wfp).
      rewrite -Heqcall.
      simpl.
      match goal with
      | |- (_ ⊢ ((_) <---> (?a and ?b))) => remember a as p1'; remember b as p2'
      end.
      apply and_of_equiv_is_equiv; subst; auto 10.
    - pose proof (wfp1 := wf_or_proj1 _ _ wfp).
      pose proof (wfp2 := wf_or_proj2 _ _ wfp).
      rewrite -Heqcall. simpl.
      match goal with
      | |- (_ ⊢ ((_) <---> (?a or ?b))) => remember a as p1'; remember b as p2'
      end.
      apply or_of_equiv_is_equiv; subst; auto.
    - pose proof (wfp' := wf_not_proj _ wfp).
      rewrite -Heqcall. simpl.
      eapply pf_iff_equiv_trans.
      5: { apply H0. }
      all: auto.
      apply negate_equiv; auto.
    - rewrite -Heqcall.
      simpl.
      apply pf_iff_equiv_refl; auto.
    - pose proof (wfp1 := wf_imp_proj1 _ _ wfp).
      pose proof (wfp2 := wf_imp_proj2 _ _ wfp).
      rewrite -Heqcall.
      simpl.
      match goal with
      | |- (_ ⊢ ((_) <---> (?a or ?b))) => remember a as p1'; remember b as p2'
      end.
      eapply pf_iff_equiv_trans.
      5: {
        apply or_of_equiv_is_equiv. 6: apply H1. 5: apply H0. all: subst; auto.
      }
      all: auto.
      { subst; auto. }
      eapply pf_iff_equiv_trans.
      5: {
        apply or_of_equiv_is_equiv. 6: apply pf_iff_equiv_refl. 5: apply negate_equiv; auto.
        all: auto.
      }
      all: auto.
      
      
      
  Abort.
  
  
End ml_tauto.
