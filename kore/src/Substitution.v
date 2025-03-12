From Kore Require Export Syntax.

Import Kore.Syntax.Notations.

Section Substitution.
  Context {Σ : Signature}.
  Open Scope kore_scope.

  Fixpoint bevar_subst (ps : Pattern) (x : nat)
    (p : Pattern) : Pattern :=
  match p with
   | kore_top _ | kore_bot _ | kore_fevar _ | kore_fsvar _ | kore_bsvar _ => p
   | kore_bevar n =>
     match compare_nat n x with
     | Nat_less _ _ _ => kore_bevar n
     | Nat_equal _ _ _ => ps
     | _ => kore_bevar n (* kore_bevar (Nat.pred n) *)
     end
   | kore_not φ  => kore_not (bevar_subst ps x φ)
   | kore_imp φ1 φ2  => kore_imp (bevar_subst ps x φ1) (bevar_subst ps x φ2)
   | kore_iff φ1 φ2  => kore_iff (bevar_subst ps x φ1) (bevar_subst ps x φ2)
   | kore_and φ1 φ2  => kore_and (bevar_subst ps x φ1) (bevar_subst ps x φ2)
   | kore_or φ1 φ2   => kore_or (bevar_subst ps x φ1) (bevar_subst ps x φ2)
   | kore_app σ args => kore_app σ (map (bevar_subst ps x) args)
   | kore_exists s φ => kore_exists s (bevar_subst ps (S x) φ)
   | kore_forall s φ => kore_forall s (bevar_subst ps (S x) φ)
   | kore_mu s φ     => kore_mu s (bevar_subst ps x φ)
   | kore_nu s φ     => kore_nu s (bevar_subst ps x φ)
   | kore_ceil s1 s2 φ => kore_ceil s1 s2 (bevar_subst ps x φ)
   | kore_floor s1 s2 φ => kore_floor s1 s2 (bevar_subst ps x φ)
   | kore_equals s1 s2 φ1 φ2 => kore_equals s1 s2 (bevar_subst ps x φ1) (bevar_subst ps x φ2)
   | kore_in s1 s2 φ1 φ2 => kore_in s1 s2 (bevar_subst ps x φ1) (bevar_subst ps x φ2)
  end.

  Fixpoint bsvar_subst (ps : Pattern) (x : nat)
    (p : Pattern) : Pattern :=
  match p with
   | kore_top _ | kore_bot _ | kore_fevar _ | kore_fsvar _ | kore_bevar _ => p
   | kore_bsvar n =>
     match compare_nat n x with
     | Nat_less _ _ _ => kore_bsvar n
     | Nat_equal _ _ _ => ps
     | _ => kore_bsvar n (* kore_bsvar (Nat.pred n) *)
     end
   | kore_not φ  => kore_not (bsvar_subst ps x φ)
   | kore_imp φ1 φ2  => kore_imp (bsvar_subst ps x φ1) (bsvar_subst ps x φ2)
   | kore_iff φ1 φ2  => kore_iff (bsvar_subst ps x φ1) (bsvar_subst ps x φ2)
   | kore_and φ1 φ2  => kore_and (bsvar_subst ps x φ1) (bsvar_subst ps x φ2)
   | kore_or φ1 φ2   => kore_or (bsvar_subst ps x φ1) (bsvar_subst ps x φ2)
   | kore_app σ args => kore_app σ (map (bsvar_subst ps x) args)
   | kore_exists s φ => kore_exists s (bsvar_subst ps x φ)
   | kore_forall s φ => kore_forall s (bsvar_subst ps x φ)
   | kore_mu s φ     => kore_mu s (bsvar_subst ps (S x) φ)
   | kore_nu s φ     => kore_nu s (bsvar_subst ps (S x) φ)
   | kore_ceil s1 s2 φ => kore_ceil s1 s2 (bsvar_subst ps x φ)
   | kore_floor s1 s2 φ => kore_floor s1 s2 (bsvar_subst ps x φ)
   | kore_equals s1 s2 φ1 φ2 => kore_equals s1 s2 (bsvar_subst ps x φ1) (bsvar_subst ps x φ2)
   | kore_in s1 s2 φ1 φ2 => kore_in s1 s2 (bsvar_subst ps x φ1) (bsvar_subst ps x φ2)
  end.

End Substitution.

Module Notations.

  Notation "p '^[' 'evar:' x ↦ t ']'" :=
    (bevar_subst t x p) : kore_scope.
  Notation "p '^[' 'svar:' x ↦ t ']'" :=
    (bsvar_subst t x p) : kore_scope.

End Notations.

Section Substitution.
  Import Notations.
  Open Scope kore_scope.

  Context {Σ : Signature}.

  Lemma bevar_subst_opml_size :
    forall φ x n,
      pat_size (bevar_subst (kore_fevar x) n φ) = pat_size φ.
  Proof.
    induction φ using Pat_ind; simpl; intros; try reflexivity.
    all: try by erewrite ->IHφ1, ->IHφ2.
    all: try by erewrite ->IHφ.
    * by case_match.
    * f_equal. induction H; simpl.
      reflexivity.
      rewrite IHForall.
      erewrite H.
      reflexivity.
  Defined.

  Lemma bsvar_subst_opml_size :
    forall φ X n,
      pat_size (bsvar_subst (kore_fsvar X) n φ) = pat_size φ.
  Proof.
    induction φ using Pat_ind; simpl; intros; try reflexivity.
    all: try by erewrite ->IHφ1, ->IHφ2.
    all: try by erewrite ->IHφ.
    * by case_match.
    * f_equal. induction H; simpl.
      reflexivity.
      rewrite IHForall.
      erewrite H.
      reflexivity.
  Defined.

  Lemma well_sorted_bevar_subst :
    forall φ ψ s s' fe fs n,
    well_sorted fe fs s φ ->
    well_sorted default default s' ψ ->
    fe n = Some s' ->
    well_sorted (update n None fe) fs s (φ^[evar: n ↦ ψ]).
  Proof.
    induction φ using Pat_ind; intros; simpl in *; trivial.
    * case_match; simpl.
      - destruct decide in H. 2: by simpl in H.
        unfold update.
        destruct decide.
        + lia.
        + simpl. rewrite e.
          rewrite decide_eq_same. reflexivity.
      - subst. rewrite H1 in H.
        destruct decide. 2: by simpl in H.
        inversion e. subst.
        eapply well_sorted_weaken. 3: eassumption.
        apply default_is_strongest.
        apply default_is_strongest.
      - destruct decide. 2: by simpl in H.
        unfold update.
        destruct decide.
        + lia.
        + simpl. rewrite e.
          rewrite decide_eq_same. reflexivity.
    * apply andb_split_1 in H0 as WF1. rewrite WF1.
      clear WF1. simpl.
      apply andb_split_2 in H0.
      {
        remember (arg_sorts σ) as xs.
        clear Heqxs. generalize dependent xs.
        induction H; simpl; intros. assumption.
        case_match.
        - congruence.
        - apply andb_split_1 in H3 as H31.
          apply andb_split_2 in H3.
          erewrite H, IHForall; try eassumption.
          reflexivity.
      }
    * erewrite IHφ; try by eassumption.
      reflexivity.
    * erewrite IHφ1, IHφ2; try by eassumption.
      reflexivity.
      by apply andb_split_2 in H.
      by apply andb_split_1 in H.
    * erewrite IHφ1, IHφ2; try by eassumption.
      reflexivity.
      by apply andb_split_2 in H.
      by apply andb_split_1 in H.
    * erewrite IHφ1, IHφ2; try by eassumption.
      reflexivity.
      by apply andb_split_2 in H.
      by apply andb_split_1 in H.
    * erewrite IHφ1, IHφ2; try by eassumption.
      reflexivity.
      by apply andb_split_2 in H.
      by apply andb_split_1 in H.
    * simpl in *.
      rewrite shift_update.
      erewrite IHφ; try by eauto.
    * simpl in *.
      rewrite shift_update.
      erewrite IHφ; try by eauto.
    * simpl in *.
      erewrite IHφ; try by eauto.
    * simpl in *.
      erewrite IHφ; try by eauto.
    * erewrite IHφ; try by eassumption.
      by apply andb_split_2 in H.
      by apply andb_split_1 in H.
    * erewrite IHφ; try by eassumption.
      by apply andb_split_2 in H.
      by apply andb_split_1 in H.
    * erewrite IHφ1, IHφ2; try by eassumption.
        by apply andb_split_2 in H.
        by apply andb_split_1, andb_split_2 in H.
        by apply andb_split_1, andb_split_1 in H.
    * erewrite IHφ1, IHφ2; try by eassumption.
        by apply andb_split_2 in H.
        by apply andb_split_1, andb_split_2 in H.
        by apply andb_split_1, andb_split_1 in H.
  Defined.

  Lemma well_sorted_bsvar_subst :
    forall φ ψ s s' fe fs n,
    well_sorted fe fs s φ ->
    well_sorted default default s' ψ ->
    fs n = Some s' ->
    well_sorted fe (update n None fs) s (φ^[svar: n ↦ ψ]).
  Proof.
    induction φ using Pat_ind; intros; simpl in *; trivial.
    * case_match; simpl.
      - destruct decide in H. 2: by simpl in H.
        unfold update.
        destruct decide.
        + lia.
        + simpl. rewrite e.
          rewrite decide_eq_same. reflexivity.
      - subst. rewrite H1 in H.
        destruct decide. 2: by simpl in H.
        inversion e. subst.
        eapply well_sorted_weaken. 3: eassumption.
        apply default_is_strongest.
        apply default_is_strongest.
      - destruct decide. 2: by simpl in H.
        unfold update.
        destruct decide.
        + lia.
        + simpl. rewrite e.
          rewrite decide_eq_same. reflexivity.
    * apply andb_split_1 in H0 as WF1. rewrite WF1.
      clear WF1. simpl.
      apply andb_split_2 in H0.
      {
        remember (arg_sorts σ) as xs.
        clear Heqxs. generalize dependent xs.
        induction H; simpl; intros. assumption.
        case_match.
        - congruence.
        - apply andb_split_1 in H3 as H31.
          apply andb_split_2 in H3.
          erewrite H, IHForall; try eassumption.
          reflexivity.
      }
    * erewrite IHφ; try by eassumption.
      reflexivity.
    * erewrite IHφ1, IHφ2; try by eassumption.
      reflexivity.
      by apply andb_split_2 in H.
      by apply andb_split_1 in H.
    * erewrite IHφ1, IHφ2; try by eassumption.
      reflexivity.
      by apply andb_split_2 in H.
      by apply andb_split_1 in H.
    * erewrite IHφ1, IHφ2; try by eassumption.
      reflexivity.
      by apply andb_split_2 in H.
      by apply andb_split_1 in H.
    * erewrite IHφ1, IHφ2; try by eassumption.
      reflexivity.
      by apply andb_split_2 in H.
      by apply andb_split_1 in H.
    * simpl in *.
      erewrite IHφ; try by eauto.
    * simpl in *.
      erewrite IHφ; try by eauto.
    * simpl in *.
      rewrite shift_update.
      erewrite IHφ; try by eauto.
    * simpl in *.
      rewrite shift_update.
      erewrite IHφ; try by eauto.
    * erewrite IHφ; try by eassumption.
      by apply andb_split_2 in H.
      by apply andb_split_1 in H.
    * erewrite IHφ; try by eassumption.
      by apply andb_split_2 in H.
      by apply andb_split_1 in H.
    * erewrite IHφ1, IHφ2; try by eassumption.
        by apply andb_split_2 in H.
        by apply andb_split_1, andb_split_2 in H.
        by apply andb_split_1, andb_split_1 in H.
    * erewrite IHφ1, IHφ2; try by eassumption.
        by apply andb_split_2 in H.
        by apply andb_split_1, andb_split_2 in H.
        by apply andb_split_1, andb_split_1 in H.
  Defined.

End Substitution.