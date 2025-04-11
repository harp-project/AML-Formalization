From MatchingLogic.Theories Require Export FOEquality_ProofSystem.
Require Import MatchingLogic.Theories.Definedness_Semantics.
(* From MatchingLogic.Experimental Require Export Unification. *)
Import MatchingLogic.Logic.Notations.
Import MatchingLogic.Theories.Definedness_Syntax.Notations.

Set Default Proof Mode "Classic".

Close Scope equations_scope. (* Because of [!] *)

Open Scope ml_scope.
Open Scope string_scope.
Open Scope list_scope.

Section Anti.
  Context {Σ : Signature} {syntax : Syntax}.

  Definition many_ex n φ := Nat.iter n patt_exists φ.

  Definition index_predicate' n l := foldr patt_and Top (zip_with (patt_equal ∘ patt_bound_evar) (seq n (length l)) l).
  Definition index_predicate := index_predicate' 0.

  Record AUP : Set := mkAUP {
    termAUP : Pattern;
    subsAUP : list (Pattern * Pattern);
    (* wfTermAUP : well_formed_closed_mu_aux termAUP 0 /\ well_formed_closed_ex_aux termAUP (length subsAUP) /\ well_formed_positive termAUP; *)
  }.

  Record wfAUP (x : AUP) : Set := mkwfAUP {
    wfTermAUP : well_formed_xy (length (subsAUP x)) 0 (termAUP x);
    wfSubsAUP : wf (map fst (subsAUP x)) /\ wf (map snd (subsAUP x));
  }.

Definition predAUP (x : AUP) := many_ex (length (subsAUP x)) (termAUP x and ((index_predicate (map fst (subsAUP x))) or (index_predicate (map snd (subsAUP x))))).

  Reserved Notation "a ~> b" (at level 70, no associativity).
  Inductive antiunification_step : AUP -> AUP -> Set := 
    | decAUS t xs ys a b c d : {| termAUP := t; subsAUP := xs ++ (a ⋅ b, c ⋅ d) :: ys |} ~> {| termAUP := (nest_ex_aux (S (length xs)) 2 t)^[evar: length xs ↦ patt_bound_evar (length xs) ⋅ patt_bound_evar (S (length xs))]; subsAUP := xs ++ (a, c) :: (b, d) :: ys |}
    | deleteAUS t xs ys x : {| termAUP := t; subsAUP := xs ++ (x, x) :: ys |} ~> {| termAUP := t^[evar: length xs ↦ x]; subsAUP := xs ++ ys |}
    | rgvAUS t xs x y ys zs : {| termAUP := t; subsAUP := xs ++ (x, y) :: ys ++ (x, y) :: zs |} ~> {| termAUP := t^[evar: S (length xs + length ys) ↦ patt_bound_evar (length xs)]; subsAUP := xs ++ (x, y) :: ys ++ zs |}
  where "a ~> b" := (antiunification_step a b).

  Arguments decAUS {t} xs {ys a b c d} : assert.
  Arguments deleteAUS {t} xs {ys x} : assert.
  Arguments rgvAUS {t} xs {x y} ys {zs} : assert.

  (* Goal forall x y, exists f, x ~> y -> wfTermAUP y = f (wfTermAUP x). *)
  (* Proof. *)
  (*   intros [] []. *)
  (*   eexists. *)
  (*   intros. *)
  (*   inversion H; subst. clear H. *)
  (*   simpl in *. *)
  (*   destruct wfTermAUP1 as [? [] ]. *)
  (*   destruct wfTermAUP0 as [? [] ]. *)
  (* Abort. *)

  Lemma decompose_xy x y p : well_formed_xy x y p <-> well_formed_positive p /\ well_formed_closed_ex_aux p x /\ well_formed_closed_mu_aux p y.
  Proof.
    unfold well_formed_xy.
    split; intros.
    now repeat apply andb_prop in H as [H ?].
    decompose record H.
    now repeat (apply andb_true_intro; split).
  Defined.

  Tactic Notation "simplify_length" :=
    rewrite_strat (fix f := (try choice length_app length_cons; try subterms f; (fix g := try (Nat.add_succ_r; subterms (g; try Nat.add_assoc))))).

  Tactic Notation "simplify_length" "in" hyp(H) :=
    rewrite_strat (fix f := (try choice length_app length_cons; try subterms f; (fix g := try (Nat.add_succ_r; subterms (g; try Nat.add_assoc))))) in H.

  Tactic Notation "simplify_map" :=
    rewrite_strat fix f := (try choice map_app (map_cons; eval simpl); try subterms f).

  Tactic Notation "simplify_map" "in" hyp(H) :=
    rewrite_strat fix f := (try choice map_app (map_cons; eval simpl); try subterms f) in H.

  Tactic Notation "decompose_wf" :=
    repeat match goal with
           | [ |- _ /\ _ ] => split
           | [ |- is_true (wf _) ] => unfold is_true
           | [ |- wf (_ ++ _) = true ] => apply wf_app
           | [ |- wf (_ :: _) = true ] => apply wf_cons
           end.

  Tactic Notation "decompose_wf_in_hyp" :=
    repeat match goal with
           | [ H : _ /\ _ |- _ ] => destruct H
           | [ H : is_true (wf _) |- _ ] => unfold is_true in H
           | [ H : wf (_ ++ _) = true |- _ ] => apply wf_app in H
           | [ H : wf (_ :: _) = true |- _ ] => apply wf_cons in H
           end.

  Lemma wf_aup_prop a b : a ~> b -> wfAUP a -> wfAUP b.
  Proof.
    intros.
    destruct H0.
    inversion H; subst; clear H; simpl in *.
    {
      simplify_length in wfTermAUP0; apply decompose_xy in wfTermAUP0 as [? [] ].
      simplify_map in wfSubsAUP0; decompose_wf_in_hyp.
      split; simpl;
      [simplify_length; apply decompose_xy; repeat split | simplify_map; decompose_wf];
      try solve [assumption | wf_auto2].
      apply wfc_ex_aux_bsvar_subst_le. lia.
      apply wfc_ex_nest_ex'. lia.
      simpl. assumption.
      simpl. rewrite !decide_True; lia.
    }
    {
      simplify_length in wfTermAUP0; apply decompose_xy in wfTermAUP0 as [? [] ].
      simplify_map in wfSubsAUP0; decompose_wf_in_hyp.
      split; simpl;
      [simplify_length; apply decompose_xy; repeat split | simplify_map; decompose_wf];
      try solve [assumption | wf_auto2].
      apply wfc_ex_aux_bsvar_subst_le.
      lia. assumption.
      apply well_formed_closed_ex_aux_ind with (ind_evar1 := 0).
      apply le_0_n. wf_auto2.
    }
    {
      simplify_length in wfTermAUP0; apply decompose_xy in wfTermAUP0 as [? [] ].
      simplify_map in wfSubsAUP0; decompose_wf_in_hyp.
      split; simpl;
      [simplify_length; apply decompose_xy; repeat split | simplify_map; decompose_wf];
      try solve [assumption | wf_auto2].
      apply wfc_ex_aux_bsvar_subst_le. lia. assumption.
      simpl. rewrite decide_True; lia.
    }
  Defined.
    
  Lemma index_predicate_cons n x xs : index_predicate' n (x :: xs) = (patt_bound_evar n =ml x and index_predicate' (S n) xs).
  Proof.
    auto.
  Defined.

  Lemma wf_index_predicate a n : wf a -> well_formed_xy (n + length a) 0 (index_predicate' n a).
  Proof.
    intros. revert n.
    induction a; intros.
    unfold index_predicate'.
    simpl. wf_auto2.
    apply wf_cons in H as [].
    specialize (IHa H0 (S n)). rewrite index_predicate_cons.
    simplify_length.
    wf_auto2.
    rewrite decide_True. lia. reflexivity.
  Defined.
    
  Lemma well_formed_many_ex n m k p : well_formed_xy (k + n) m p -> well_formed_xy n m (many_ex k p).
  Proof.
    revert p.
    induction k; intros; simpl in *. assumption.
    pose proof Nat.iter_swap k _ patt_exists p.
    fold (many_ex k p) in H0. fold (many_ex k (ex, p)) in H0.
    rewrite <- H0. apply IHk. clear H0 IHk.
    apply decompose_xy in H as [? [] ].
    apply decompose_xy; repeat split; wf_auto2.
  Defined.

  Lemma wf_predAUP a : wfAUP a -> well_formed (predAUP a).
  Proof.
    intros.
    destruct H.
    apply decompose_xy in wfTermAUP0 as [? [] ].
    destruct wfSubsAUP0.
    unfold predAUP.
    rewrite wf_wfxy00.
    apply well_formed_many_ex. rewrite Nat.add_0_r.
    pose proof wf_index_predicate (map fst (subsAUP a)) 0 H2.
    pose proof wf_index_predicate (map snd (subsAUP a)) 0 H3.
    simpl in H4, H5. fold index_predicate in H4, H5.
    rewrite !length_map in H4, H5.
    apply decompose_xy in H4 as [? [] ], H5 as [? [] ].
    apply decompose_xy; repeat split; wf_auto2.
  Defined.

  Reserved Notation "a ~>* b" (at level 70, no associativity).
  Inductive antiunification_full : AUP -> AUP -> Set := 
    | doneAUS a : a ~>* a
    | stepAUS a b c : a ~> b -> b ~>* c -> a ~>* c
  where "a ~>* b" := (antiunification_full a b).

  Goal forall (a b c d : evar) (cons : symbols), a ≠ c -> b ≠ d -> a ≠ b -> { x : AUP & {| termAUP := b0; subsAUP := [(patt_sym cons ⋅ patt_free_evar a ⋅ patt_free_evar b, patt_sym cons ⋅ patt_free_evar c ⋅ patt_free_evar d)] |} ~>* x & forall y, x ~> y -> False }.
  Proof.
    intros.
    eexists.
    eright. apply (decAUS []). simpl.
    eright. apply (decAUS []). simpl.
    eright. apply (deleteAUS []). simpl.
    left.

    intros. inversion H2; subst; clear H2.
    destruct xs; simpl in H5; inversion H5.
    destruct xs; simpl in H4; inversion H4.
    destruct xs; simpl in H7; inversion H7.
    destruct xs; simpl in H5; inversion H5.
    inversion H4. contradiction.
    destruct xs; simpl in H4; inversion H4.
    inversion H7. contradiction.
    destruct xs; simpl in H7; inversion H7.
    destruct xs; simpl in H5; inversion H5.
    destruct ys; simpl in H6; inversion H6.
    contradiction.
    destruct ys; simpl in H8; inversion H8.
    destruct xs; simpl in H4; inversion H4.
    destruct ys; simpl in H8; inversion H8.
    destruct xs; simpl in H7; inversion H7.
  Qed.

  Goal forall (a b : evar) (cons : symbols), a ≠ b -> { x : AUP & {| termAUP := b0; subsAUP := [(patt_sym cons ⋅ patt_free_evar a ⋅ patt_free_evar a, patt_sym cons ⋅ patt_free_evar b ⋅ patt_free_evar b)] |} ~>* x & forall y, x ~> y -> False }.
  Proof.
    intros. eexists.
    eright. apply (decAUS []). simpl.
    eright. apply (decAUS []). simpl.
    eright. apply (deleteAUS []). simpl.
    eright. apply (rgvAUS [] []). simpl.
    left.

    intros.
    inversion H0; subst; clear H0.
    destruct xs; inversion H3.
    destruct xs; inversion H2.
    destruct xs; inversion H3.
    inversion H2. contradiction.
    destruct xs; inversion H2.
    destruct xs; inversion H3.
    destruct ys; inversion H4.
    destruct xs; inversion H2.
  Qed.

  Lemma free_evars_many_ex p n : free_evars (many_ex n p) = free_evars p.
  Proof.
    induction n; auto.
  Defined.

  Lemma free_evars_index_predicate_nm n m l : free_evars (index_predicate' n l) = free_evars (index_predicate' m l).
  Proof.
    revert n m.
    induction l; intros; simpl.
    reflexivity.
    rewrite !union_empty_r_L !union_empty_l_L.
    fold (index_predicate' (S n) l).
    fold (index_predicate' (S m) l).
    rewrite (IHl (S n) (S m)). reflexivity.
  Defined.

  Lemma free_evars_index_predicate n l : free_evars (index_predicate' n l) = free_evars_of_list l.
  Proof.
    induction l; simpl. auto.
    rewrite !union_empty_r_L !union_empty_l_L.
    fold (index_predicate' (S n) l).
    replace (free_evars_of_list (a :: l)) with (free_evars a ∪ free_evars_of_list l) by auto.
    replace (free_evars a ∪ free_evars a) with (free_evars a) by set_solver.
    rewrite <- IHl, free_evars_index_predicate_nm with (m := n).
    reflexivity.
  Defined.

  Lemma many_ex_evar_open : forall n m p p', (many_ex n p)^{evar:m ↦ p'} = many_ex n (p^{evar:n + m ↦ p'}).
  Proof.
    induction n; simpl; intros.
    reflexivity.
    mlSimpl.
    specialize (IHn (S m) p p'). rewrite IHn.
    do 3 f_equal. lia.
  Defined.

  Goal forall Γ x y, wfAUP x -> x ~> y -> Γ ⊢ predAUP x <---> predAUP y.
  Proof.
    intros.
    toMLGoal. clear Halmost. simpl. apply well_formed_iff; apply wf_predAUP.
    assumption.
    eapply wf_aup_prop; eassumption.
    inversion H0; subst.
    - unfold predAUP. simpl.
      simplify_map. simplify_length. simpl.
      (* unfold index_predicate, index_predicate'. *)

      mlSplitAnd; mlIntro.
      epose proof (EmptyFreshMan (t :: a :: b :: c :: d :: map fst xs ++ map snd xs ++ map fst ys ++ map snd ys) [] []) as FM.
      apply FreshMan_fresh_evar in FM as [x FM].
      mlDestructExManual "0" as x.
      try_solve_pile.
      fm_solve.
      fm_solve.
      (* rewrite free_evars_many_ex. simpl. rewrite !free_evars_index_predicate. unfold free_evars_of_list, union_list. simplify_map. *)
      (* fm_solve. *)
      (* fm_solve. *)
      admit. admit.
      rewrite many_ex_evar_open Nat.add_0_r. mlSimpl.
      Search patt_exists patt_and.
  Admitted.

  Goal forall Γ t1 t2, theory ⊆ Γ -> well_formed t1 -> well_formed t2 -> Γ ⊢ predAUP (mkAUP b0 [(t1, t2)]) <---> (t1 or t2).
  Proof.
    intros.
    unfold predAUP. simpl.
    unfold index_predicate, index_predicate'. simpl.
    toMLGoal. wf_auto2.
    mlSplitAnd; mlIntro.
    mlDestructEx "0" as x. mlSimpl.
    replace (b0^{evar:0 ↦ x}) with (patt_free_evar x) by auto.
    rewrite !evar_open_not_occur. 1,2: wf_auto2.
    mlDestructAnd "0". mlDestructOr "2".
    mlDestructAnd "0". mlLeft. mlRevert "3". mlRewriteBy <- "2" at 1.
    mlIntro. mlAssumption.
    mlRight. mlDestructAnd "3". mlRevert "2". mlRewriteBy <- "0" at 1.
    mlIntro. mlAssumption.
    Search derives_using patt_free_evar.


  (* From Coq.Classes Require Import CRelationClasses CMorphisms CEquivalence. *)

  (* Definition derives_iff Γ : crelation Pattern := λ a b, well_formed a -> well_formed b -> Γ ⊢ a <---> b. *)

  (* Instance diff_eq Γ : Equivalence (derives_iff Γ). *)
  (* Proof. *)
  (*   split. *)
  (*   unfold Reflexive, derives_iff. intros. *)
  (*   aapply pf_iff_equiv_refl. assumption. *)
  (*   unfold Symmetric, derives_iff. intros. *)
  (*   apply pf_iff_equiv_sym_meta, H; assumption. *)
  (*   unfold Transitive, derives_iff. intros. *)
  (*   eapply pf_iff_equiv_trans. *)
  (*   4: apply H. 6: apply H0. all: try assumption. *)

  (* (1* if derives was in Prop, this could be done with Add Morphism *1) *)
  (* Goal forall Γ, Proper (antiunification_step ==> derives_iff Γ) predAUP. *)
  (* Proof. *)
  (*   intros. *)
  (*   unfold Proper, respectful, derives_iff, predAUP. *)
  (*   intros [] [] ?. simpl. *)
  (*   inversion H; subst. *)
  (*   rewrite !length_app !length_cons !Nat.add_succ_r !map_app !map_cons. simpl. *)








  Definition plotkin (aup : AUP) : sigT (λ '(xs, a, b, c, d, ys), subsAUP aup = xs ++ (a ⋅ b, c ⋅ d) :: ys) -> AUP.
  Proof.
    intros [[[[[[xs a] b] c] d] ys] H].
    remember (length xs) as z.
unshelve esplit.
    exact ((nest_ex_aux (S z) 2 (termAUP aup))^[evar:z↦patt_bound_evar z ⋅ patt_bound_evar (S z)]).
    exact (xs ++ (a, c) :: (b, d) :: ys).
    decompose record (wfTermAUP aup). wf_auto2.
    replace (length (xs ++ (a, c) :: (b, d) :: ys)) with (S (varsAUP aup)) by (unfold varsAUP; now rewrite H ! length_app ! length_cons).
    assert (length xs < (varsAUP aup)).
    unfold varsAUP. rewrite H length_app length_cons. lia.
    apply wfc_ex_aux_bsvar_subst_le. lia.
    wf_auto2. rewrite Nat.sub_0_r. auto.
    wf_auto2; case_match; auto. lia.
    decompose record (wfSubsAUP aup). rewrite H in H0, H1.
    rewrite ! map_app ! map_cons in H0, H1 |- *. simpl in H0, H1 |- *.
    wf_auto2.
  Defined.

  Definition delete (aup : AUP) : sigT (λ '(xs, a, ys), subsAUP aup = xs ++ (a, a) :: ys) -> AUP.
  Proof.
    intros [[[xs a] ys] H].
    remember (length xs) as z.
    unshelve esplit.
    exact ((termAUP aup)^[evar:z↦a]). exact (xs ++ ys).
    decompose record (wfTermAUP aup).
    decompose record (wfSubsAUP aup). rewrite H ! map_app ! map_cons in H1, H4. simpl in H1, H4.
    wf_auto2.
    apply wfc_ex_aux_bsvar_subst_le. rewrite length_app. lia.
    replace (S (length (xs ++ ys))) with (varsAUP aup). auto.
    unfold varsAUP. rewrite H ! length_app length_cons. lia.
    eapply well_formed_closed_ex_aux_ind. 2: eassumption. lia.
    decompose record (wfSubsAUP aup). rewrite H ! map_app ! map_cons in H0, H1 |- *. simpl in H0, H1 |- *. wf_auto2.
  Defined.

  (* Section Example. *)
  (*   Parameter (succSym : symbols). *)
  (*   Definition succ x := patt_sym succSym ⋅ x. *)

  (*   Parameter (consSym : symbols). *)
  (*   Definition cons x y := patt_sym consSym ⋅ x ⋅ y. *)

  (*   Parameter (zeroSym : symbols). *)
  (*   Definition zero := patt_sym zeroSym. *)

  (*   Parameter (x₁ x₂ l₁ l₂ : evar). *)

  (*   Definition t₁ := cons (succ (patt_free_evar x₁)) (cons zero (patt_free_evar l₁)). *)
  (*   Definition t₂ := cons (patt_free_evar x₂) (cons (succ (patt_free_evar x₂)) (patt_free_evar l₂)). *)

  (*   Goal True. *)
  (*   Proof. *)
  (*     unshelve epose (mkAUP b0 [(t₁, t₂)] _ _). 1-2: wf_auto2. *)
  (*     remember (conj _ _) as w in a. clear Heqw. *)
  (*     remember (conj _ _) as w0 in a. clear Heqw0. *)
  (*     unshelve epose (plotkin a _). simpl. *)
  (*     eexists ([],_,_,_,_,_). reflexivity. simpl in a0. *)
  (*     remember (and_ind _) as w1 in a0. clear Heqw1. *)
  (*     remember (and_ind _) as w2 in a0. clear Heqw2. *)
  (*     unshelve epose (plotkin a0 _). simpl. *)
  (*     eexists ([], _, _, _, _, _). reflexivity. simpl in a1. *)
  (*     remember (and_ind _) as w3 in a1. clear Heqw3. *)
  (*     remember (and_ind _) as w4 in a1. clear Heqw4. *)
  (*     unshelve epose (plotkin a1 _). simpl. *)
  (*     eexists ([_;_],_,_,_,_,_). reflexivity. simpl in a2. *)
  (*     remember (and_ind _) as w5 in a2. clear Heqw5. *)
  (*     remember (and_ind _) as w6 in a2. clear Heqw6. *)
  (*     unshelve epose (plotkin a2 _). simpl. *)
  (*     eexists ([_;_],_,_,_,_,_). reflexivity. simpl in a3. *)
  (*     remember (and_ind _) as w7 in a3. clear Heqw7. *)
  (*     remember (and_ind _) as w8 in a3. clear Heqw8. *)
  (*     unshelve epose (delete a3 _). simpl. *)
  (*     eexists ([],_,_). reflexivity. simpl in a4. *)
  (*     remember (and_ind _) as w9 in a4. clear Heqw9. *)
  (*     remember (and_ind _) as w10 in a4. clear Heqw10. *)
  (*     unshelve epose (delete a4 _). simpl. *)
  (*     eexists ([_],_,_). reflexivity. simpl in a5. *)
  (*     remember (and_ind _) as w11 in a5. clear Heqw11. *)
  (*     remember (and_ind _) as w12 in a5. clear Heqw12. *)
  (*     fold (cons b1 b2) in a5. *)
  (*     fold (cons b0 (cons b1 b2)) in a5. *)
  (*     pose (predAUP a5). cbv [predAUP index_predicate] in p. simpl in p. *)
  (*     split. *)
  (*   Qed. *)

  (* End Example. *)

  Definition MyDec (T : Type) : Type := T + (T -> False).

  Lemma precond_dec aup : MyDec (sigT (λ '(xs, a, b, c, d, ys), subsAUP aup = xs ++ (a ⋅ b, c ⋅ d) :: ys)).
  Proof.
    intros. unfold MyDec.
    destruct aup. simpl. clear. induction subsAUP0.
    right. intros [[[[[[xs a] b] c] d] ys] H].
    now apply app_cons_not_nil in H.
    destruct a.
    assert (∀ p, MyDec (sigT (λ '(a, b), p = a ⋅ b))). {
      intros. unfold MyDec. destruct p1.
      6: left; exists (p1_1, p1_2); reflexivity.
      all: right; intros [[] ?]; discriminate.
    }
    destruct (X p) as [[[] ?] | ?]. destruct (X p0) as [[[] ?] ? | ?].
    left. exists ([], p1, p2, p3, p4, subsAUP0).
    simpl. subst. reflexivity.

    all: destruct IHsubsAUP0 as [[[[[[[xs a] b] c] d] ys] H] | ?];
    [
      left; exists ((p, p0) :: xs, a, b, c, d, ys);
      subst; simpl; reflexivity
    |
      right; intros [[[[[[[] a] b] c] d] ys] H];
      simpl in H; injection H; intros;
      [
        apply f; eexists (_,_)
      |
        apply f0; exists (l, a, b, c, d, ys)
      ]; eassumption
    ].
  Defined.

  Fixpoint count_apps (p : Pattern) : nat :=
    match p with
    | patt_free_evar x => 0
    | patt_free_svar x => 0
    | patt_bound_evar n => 0
    | patt_bound_svar n => 0
    | patt_sym sigma => 0
    | patt_app phi1 phi2 => 1 + count_apps phi1 + count_apps phi2
    | patt_bott => 0
    | patt_imp phi1 phi2 => count_apps phi1 + count_apps phi2
    | patt_exists phi => count_apps phi
    | patt_mu phi => count_apps phi
    end.

  Definition count_apps_aup (aup : AUP) : nat := list_sum (map (λ '(a, b), count_apps a + count_apps b) (subsAUP aup)).

  Program Fixpoint plotkin_full (aup : AUP) {measure (count_apps_aup aup)} : AUP :=
    match precond_dec aup with
    | inl x => plotkin_full (plotkin aup x)
    | _ => aup
    end.

  Next Obligation.
    intros. destruct aup, x as [[[[[[xs a] b] c] d] ys] H].
    clear. unfold count_apps_aup. simpl in *. subst.
    rewrite ! map_app ! map_cons ! list_sum_app. simpl.
    lia.
  Defined.

  Next Obligation.
    intros. discriminate.
  Defined.

  Next Obligation.
    apply measure_wf, lt_wf.
  Defined.

  Lemma delete_precond_dec aup : MyDec (sigT (λ '(xs, a, ys), subsAUP aup = xs ++ (a, a) :: ys)).
  Proof.
    intros. destruct aup. simpl. clear.
    induction subsAUP0.
    right. intros [[[] ?] ?]. now apply app_cons_not_nil in y.
    destruct a.
    destruct (decide (p = p0)).
    subst. left. exists ([], p0, subsAUP0). simpl. reflexivity.
    destruct IHsubsAUP0 as [[[[xs a] ys] H] | ?].
    left. exists ((p, p0) :: xs, a, ys). simpl. subst. reflexivity.
    right. intros [[[[] a] ys] H]; simpl in H; inversion H; intros.
    apply n. transitivity a; [| symmetry]; assumption.
    apply f. exists (l, a, ys). assumption.
  Defined.

  Program Fixpoint delete_full aup {measure (length (subsAUP aup))} : AUP :=
    match delete_precond_dec aup with
    | inl x => delete aup x
    | _ => aup
    end.

  Next Obligation.
    intros. discriminate.
  Defined.

  Next Obligation.
    apply measure_wf, lt_wf.
  Defined.

  Lemma plotkin_progress aup (x : sigT (eq (precond_dec aup) ∘ inl)) : plotkin_full aup = plotkin_full (plotkin aup (projT1 x)).
  Proof.
    intros. destruct x. simpl in *. unfold plotkin_full.
    Search Fix_sub.
    rewrite WfExtensionality.fix_sub_eq_ext. simpl. rewrite ! c.
    reflexivity.
  Defined.
    
  Lemma plotkin_finished aup : sigT (eq (precond_dec aup) ∘ inr) -> plotkin_full aup = aup.
  Proof.
    intros. destruct H. simpl in c. unfold plotkin_full.
    rewrite WfExtensionality.fix_sub_eq_ext. simpl. rewrite ! c.
    reflexivity.
  Defined.
  
  Goal ∀ aup Γ, Γ ⊢ predAUP aup <---> predAUP (plotkin_full aup).
  Proof.
    intros.
    destruct_with_eqn (precond_dec aup).
    rewrite (plotkin_progress aup (s ↾ Heqm)).
    shelve.
    rewrite (plotkin_finished aup (f ↾ Heqm)). aapply pf_iff_equiv_refl.
    admit.
  Abort.
End Anti.
