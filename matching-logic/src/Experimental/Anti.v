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

  Definition index_predicate l := foldr patt_and Top (zip_with (patt_equal ∘ patt_bound_evar) (seq 0 (length l)) l).

  Record AUP : Set := mkAUP {
    termAUP : Pattern;
    subsAUP : list (Pattern * Pattern);
    varsAUP := length subsAUP;
    wfTermAUP : well_formed_closed_mu_aux termAUP 0 /\ well_formed_closed_ex_aux termAUP varsAUP /\ well_formed_positive termAUP;
    wfSubsAUP : wf (map fst subsAUP) /\ wf (map snd subsAUP);
    predAUP := many_ex varsAUP (termAUP and ((index_predicate (map fst subsAUP)) or (index_predicate (map snd subsAUP))));
  }.

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
