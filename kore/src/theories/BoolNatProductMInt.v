From stdpp Require Import finite.
From MatchingLogic Require Export stdpp_ext.
From Kore Require Export Semantics DVParsers.
Import Signature.StringVariables.
Import Kore.Syntax.Notations.

From Coq Require Import ZArith.

Open Scope kore_scope.
Open Scope hlist_scope.
Open Scope string_scope.

Module Syntax.

  Inductive Sorts := bool_s | nat_s
                   | prod_s (s1 s2 : Sorts)
                   | mint_s (n : nat).
  Inductive Symbols := o | s | plus | isZero
                    | tt | ff | andb
                    | pi1 (s1 s2 : Sorts) | pi2 (s1 s2 : Sorts) | pair (s1 s2 : Sorts)
                    | len (n : nat) | neg (n : nat) | toUnsigned (n : nat) | fromUnsigned (n : nat).

  #[global]
  Instance sorts_eqdec : EqDecision Sorts.
  Proof.
    solve_decision.
  Defined.

  #[global]
  Instance symbols_eqdec : EqDecision Symbols.
  Proof.
    solve_decision.
  Defined.

  Inductive Subsort : CRelationClasses.crelation Sorts :=.

  Program Instance Sig : Signature := {|
    sorts := {|
      sort := Sorts;
      subsort := Subsort;
    |};
    variables := StringVariables;
    symbols := {|
      symbol := Symbols;
      arg_sorts :=
        fun x =>
          match x with
          | o => []
          | s => [nat_s]
          | plus => [nat_s; nat_s]
          | isZero => [nat_s]
          | tt => []
          | ff => []
          | andb => [bool_s; bool_s]
          | pi1 s1 s2 => [prod_s s1 s2]
          | pi2 s1 s2 => [prod_s s1 s2]
          | pair s1 s2 => [s1; s2]
          | len n => [mint_s n]
          | neg n => [mint_s n]
          | toUnsigned n => [mint_s n]
          | fromUnsigned n => [nat_s]
          end;
      ret_sort :=
        fun x =>
          match x with
          | o => nat_s
          | s => nat_s
          | plus => nat_s
          | isZero => bool_s
          | tt => bool_s
          | ff => bool_s
          | andb => bool_s
          | pi1 s1 s2 => s1
          | pi2 s1 s2 => s2
          | pair s1 s2 => prod_s s1 s2
          | len n => nat_s
          | neg n => mint_s n
          | toUnsigned n => nat_s
          | fromUnsigned n => mint_s n
          end;
    |};
  |}.
Fail Next Obligation.

  Definition theory_functional : @Theory Sig :=
      PropSet (fun pat =>
      exists R, pat =
        existT R (
          kore_exists nat_s (o ⋅ ⟨⟩ =k{R} kore_bevar (In_nil)
      )) \/
      exists R, pat =
        existT R (kore_forall nat_s (
          kore_exists nat_s (s ⋅ ⟨kore_bevar (In_cons In_nil)⟩ =k{R} kore_bevar (In_nil)
      ))) \/
      exists R, pat =
        existT R (kore_forall nat_s (kore_forall nat_s (
          kore_exists nat_s (plus ⋅ ⟨kore_bevar (In_cons (In_cons In_nil));
                                     kore_bevar (In_cons In_nil)⟩ =k{R} kore_bevar (In_nil)
      )))) \/
      exists R, pat =
        existT R (kore_forall nat_s (
          kore_exists bool_s (isZero ⋅ ⟨kore_bevar (In_cons In_nil)⟩ =k{R} kore_bevar (In_nil)
      ))) \/
      exists R, pat =
        existT R (
          kore_exists bool_s (tt ⋅ ⟨⟩ =k{R} kore_bevar (In_nil)
      )) \/
      exists R, pat =
        existT R (
          kore_exists bool_s (ff ⋅ ⟨⟩ =k{R} kore_bevar (In_nil)
      )) \/
      exists R, pat =
        existT R (kore_forall bool_s (kore_forall bool_s (
          kore_exists bool_s (andb ⋅ ⟨kore_bevar (In_cons (In_cons In_nil));
                                     kore_bevar (In_cons In_nil)⟩ =k{R} kore_bevar (In_nil)
      )))) \/
      exists s1, exists s2, exists R, pat =
        existT R (
           kore_forall (prod_s s1 s2) (
             kore_exists s1 (pi1 s1 s2 ⋅ ⟨kore_bevar (In_cons In_nil)⟩ =k{R} kore_bevar (In_nil))
           )
      ) \/
      exists s1, exists s2, exists R, pat =
        existT R (
           kore_forall (prod_s s1 s2) (
             kore_exists s2 (pi2 s1 s2 ⋅ ⟨kore_bevar (In_cons In_nil)⟩ =k{R} kore_bevar (In_nil))
           )
      ) \/
      exists s1, exists s2, exists R, pat =
        existT R (
           kore_forall s1 (kore_forall s2 (
             kore_exists (prod_s s1 s2) (pair s1 s2 ⋅ ⟨kore_bevar (In_cons (In_cons In_nil));kore_bevar (In_cons In_nil)⟩ =k{R} kore_bevar (In_nil))
           ))
      ) \/
      exists R, exists n, pat =
        existT R (kore_forall (mint_s n) (
          kore_exists nat_s (len n ⋅ ⟨kore_bevar (In_cons In_nil)⟩ =k{R} kore_bevar (In_nil)
      ))) \/
      exists R, exists n, pat =
        existT R (kore_forall (mint_s n)
          (kore_exists (mint_s n) (neg n ⋅ ⟨kore_bevar (In_cons In_nil)⟩ =k{R} kore_bevar (In_nil)
      ))) \/
      exists R, exists n, pat =
        existT R (kore_forall (mint_s n) (
          kore_exists nat_s (toUnsigned n ⋅ ⟨kore_bevar (In_cons In_nil)⟩ =k{R} kore_bevar (In_nil)
      ))) \/
      exists R, exists n, pat =
        existT R (kore_forall nat_s (
          kore_exists (mint_s n) (fromUnsigned n ⋅ ⟨kore_bevar (In_cons In_nil)⟩ =k{R} kore_bevar (In_nil)
      )))
      ).

  Fixpoint make_n {ex mu} (n : nat) : Pattern ex mu nat_s :=
  match n with
  | O => o ⋅ ⟨⟩
  | S n' => s ⋅ ⟨make_n n'⟩
  end.

  Lemma make_n_bevar_subst ex {ex' mu s'} x n:
    (@bevar_subst _ ex ex' mu _ s' x
            (make_n n)) = make_n n.
  Proof.
    induction n; cbn. reflexivity.
    f_equal. by rewrite IHn.
  Qed.

  Definition theory_rest : @Theory Sig :=
      PropSet (fun pat =>
        exists R, pat = existT R (
          kore_top nat_s =k{R} kore_mu (o ⋅ ⟨⟩ or s ⋅ ⟨kore_bsvar In_nil⟩)
        ) \/
        exists R, pat = existT R (
          kore_top bool_s =k{R} (tt ⋅ ⟨⟩ or ff ⋅ ⟨⟩)
        ) \/
        exists R, pat = existT R (
          kore_not (tt ⋅ ⟨⟩ =k{R} ff ⋅ ⟨⟩)
        ) \/
        exists R, pat = existT R (
          kore_forall nat_s (kore_not (o ⋅ ⟨⟩ =k{R} s ⋅ ⟨kore_bevar In_nil⟩))
        ) \/
        exists R, pat = existT R (
          kore_forall nat_s (kore_forall nat_s (
            s ⋅ ⟨kore_bevar (In_cons In_nil)⟩ =k{R} s ⋅ ⟨kore_bevar In_nil⟩ --->ₖ kore_bevar (In_cons In_nil) =k{R} kore_bevar In_nil
          ))
        ) \/
        exists R, pat = existT R (
          kore_forall nat_s (
            plus ⋅ ⟨o ⋅ ⟨⟩; kore_bevar In_nil⟩ =k{R} kore_bevar In_nil
          )
        ) \/
        exists R, pat = existT R (
          kore_forall nat_s (kore_forall nat_s (
            plus ⋅ ⟨s ⋅ ⟨kore_bevar (In_cons In_nil)⟩; kore_bevar In_nil⟩ =k{R} s ⋅ ⟨plus ⋅ ⟨kore_bevar (In_cons In_nil); kore_bevar In_nil⟩⟩
          ))
        ) \/
        exists R, pat = existT R (
          kore_forall bool_s (
            andb ⋅ ⟨tt ⋅ ⟨⟩; kore_bevar In_nil⟩ =k{R} kore_bevar In_nil
          )
        ) \/
        exists R, pat = existT R (
          kore_forall bool_s (
            andb ⋅ ⟨ff ⋅ ⟨⟩; kore_bevar In_nil⟩ =k{R} ff ⋅ ⟨⟩
          )
        ) \/
        exists R, pat = existT R (
            isZero ⋅ ⟨o ⋅ ⟨⟩⟩ =k{R} tt ⋅ ⟨⟩
        ) \/
        exists R, pat = existT R (
          kore_forall nat_s (
            isZero ⋅ ⟨s ⋅ ⟨kore_bevar In_nil⟩⟩ =k{R} ff ⋅ ⟨⟩
          )
        ) \/
        exists s1, exists s2, exists R, pat = existT R (
          kore_forall s1 (kore_forall s2 (
            pi1 s1 s2 ⋅ ⟨pair s1 s2 ⋅ ⟨kore_bevar (In_cons In_nil);kore_bevar In_nil⟩⟩ =k{R} kore_bevar (In_cons In_nil)
          ))
        ) \/
        exists s1, exists s2, exists R, pat = existT R (
          kore_forall s1 (kore_forall s2 (
            pi2 s1 s2 ⋅ ⟨pair s1 s2 ⋅ ⟨kore_bevar (In_cons In_nil);kore_bevar In_nil⟩⟩ =k{R} kore_bevar In_nil
          ))
        )  \/
        exists s1, exists s2, exists R, pat = existT R (
          kore_forall (prod_s s1 s2) (
            pair s1 s2 ⋅ ⟨pi1 s1 s2 ⋅ ⟨kore_bevar In_nil⟩; pi2 s1 s2 ⋅ ⟨kore_bevar In_nil⟩⟩ =k{R} kore_bevar In_nil
          )
        ) \/
        exists n, exists R, pat = existT R (
          kore_forall (mint_s n) (
            len n ⋅ ⟨kore_bevar In_nil⟩ =k{R} make_n n
          )
        ) \/
        exists n, exists R, pat = existT R (
          kore_forall (mint_s n) (
            fromUnsigned n ⋅ ⟨ toUnsigned n ⋅ ⟨kore_bevar In_nil⟩⟩ =k{R} kore_bevar In_nil
          )
        )
        (** TODO: inductive domains for MInt *)
     ).

End Syntax.


Module Semantics.
  Import Syntax.

  Fixpoint carrier (s : Sorts) : Set :=
  match s with
  | nat_s => nat
  | bool_s => bool
  | prod_s s1 s2 => carrier s1 * carrier s2
  | mint_s n => vec bool n
  end.

  Fixpoint negate {n : nat}
    (l : vec bool n) : vec bool n :=
    match l with
    | vnil => vnil
    | vcons x xs => vcons (negb x) (negate xs)
    end.

  Fixpoint bin_to_nat {n : nat} (l : vec bool n) : nat :=
    match l with
    | vnil => 0
    | b ::: t =>
        (if b then 1 else 0) + 2 * bin_to_nat t
    end.  

  Fixpoint nat_to_bin (n len : nat) : vec bool len :=
    match len with
    | 0 => vnil
    | S k' =>
        Nat.odd n ::: nat_to_bin (Nat.div2 n) k'
    end.
  Opaque Nat.div2.
  Lemma nat_to_bin_eq {n} (v : vec bool n):
    nat_to_bin (bin_to_nat v) n = v.
  Proof.
    induction v as [| b n' t IH].
    - reflexivity.
    - simpl.
      destruct b; simpl.
      + rewrite Nat.odd_succ.
        rewrite Nat.add_0_r.
        replace (bin_to_nat t + bin_to_nat t) with
          (2 * bin_to_nat t) by lia.
        rewrite Nat.even_even. f_equal.
        by rewrite Nat.div2_succ_double.
      + rewrite Nat.add_0_r.
        replace (bin_to_nat t + bin_to_nat t) with
          (2 * bin_to_nat t) by lia.
        rewrite Nat.odd_even. f_equal.
        by rewrite Nat.div2_even.
  Qed.
  Transparent Nat.div2.

  Program Definition model : @Model Sig :=
    mkModel_singleton
      carrier
      (fun σ : Symbols =>
        match σ with
        | o => 0
        | s => S
        | plus => Nat.add
        | isZero => fun n =>
            if Nat.eqb n 0 then true else false
        | tt => true
        | ff => false
        | andb => Datatypes.andb
        | pi1 s1 s2 => fst
        | pi2 s1 s2 => snd
        | pair s1 s2 => fun x y => (x, y)
        | len n => fun x => n
        | neg n => negate
        | toUnsigned n => bin_to_nat
        | fromUnsigned n => fun m => nat_to_bin m n
        end
      )
      ltac:(induction s0; simpl; typeclasses eauto)
      ltac:(intros; destruct X)
      (fun _ => None_parser).

  Lemma eval_make_n {ex mu}:
    forall n ρ, @eval _ model ex mu _ ρ (make_n n) = ({[n]} : propset (model nat_s)).
  Proof.
    induction n; intros; simpl.
    * eval_simplifier.
      by rewrite_app_ext.
    * eval_simplifier.
      rewrite IHn.
      by rewrite_app_ext. 
  Qed.

  Goal satT theory_functional model.
  Proof.
    unfold satT, satM, theory_functional. intros.
    unfold_elem_of; repeat (destruct_or!; destruct_ex?); subst; cbn.
    * solve_functional_axiom.
    * eval_simplifier. cbn.
      apply propset_fa_intersection_full. intros.
      solve_functional_axiom.
    * eval_simplifier. cbn.
      apply propset_fa_intersection_full. intros.
      eval_simplifier. cbn.
      apply propset_fa_intersection_full. intros.
      solve_functional_axiom.
    * eval_simplifier. cbn.
      apply propset_fa_intersection_full. intros.
      solve_functional_axiom.
    * solve_functional_axiom.
    * solve_functional_axiom.
    * eval_simplifier. cbn.
      apply propset_fa_intersection_full. intros.
      eval_simplifier. cbn.
      apply propset_fa_intersection_full. intros.
      solve_functional_axiom.
    * eval_simplifier. cbn.
      apply propset_fa_intersection_full. intros.
      solve_functional_axiom.
    * eval_simplifier. cbn.
      apply propset_fa_intersection_full. intros.
      solve_functional_axiom.
    * eval_simplifier. cbn.
      apply propset_fa_intersection_full. intros.
      eval_simplifier. cbn.
      apply propset_fa_intersection_full. intros.
      solve_functional_axiom.
    * eval_simplifier. cbn.
      apply propset_fa_intersection_full. intros.
      solve_functional_axiom.
    * eval_simplifier. cbn.
      apply propset_fa_intersection_full. intros.
      solve_functional_axiom.
    * eval_simplifier. cbn.
      apply propset_fa_intersection_full. intros.
      solve_functional_axiom.
    * eval_simplifier. cbn.
      apply propset_fa_intersection_full. intros.
      solve_functional_axiom.
  Qed.

Ltac autorewrite_set :=
  repeat (
    rewrite intersection_top_l_L +
    rewrite intersection_top_r_L +
    rewrite union_empty_l_L +
    rewrite union_empty_r_L +
    rewrite propset_difference_neg +
    rewrite propset_union_simpl +
    rewrite propset_intersection_simpl +
    rewrite singleton_subseteq_l +
    rewrite fmap_propset_singleton
  ).

  Goal satT theory_rest model.
  Proof.
    unfold satT, satM, theory_rest. intros.
    unfold_elem_of; repeat (destruct_or!; destruct_ex?); subst; cbn.
    * eval_simplifier. cbn.
      apply propset_top_elem_of_2. intros.
      apply elem_of_PropSet.
      eval_simplifier. cbn.
      eval_simplifier. cbn.
      unfold LeastFixpointOf, PrefixpointsOf.
      unfold Lattice.meet. simpl.
      unfold propset_Meet. symmetry.
      apply propset_top_elem_of_2. intros.
      apply elem_of_PropSet. intros.
      rewrite elem_of_PropSet in H.
      revert H.
      repeat eval_simplifier. cbn.
      case_match; try congruence. cbn.
      case_match; try congruence. cbn.
      2: { cbn in n. clear H0.
           epose proof Eqdep.EqdepTheory.UIP_refl _ _ e0.
        rewrite H0 in n. cbn in n. exfalso. apply n. reflexivity. }
      epose proof Eqdep.EqdepTheory.UIP_refl _ _ e0.
      rewrite H1. cbn.
      unshelve (erewrite app_ext_singleton).
      { constructor. }
      simpl.
      clear. intros.
      (* induction *)
      induction t0. set_solver.
      assert (S t0 ∈ app_ext s ⟨ e : propset (model nat_s) ⟩). {
        unfold app_ext in *.
        exists (⟨t0 : model nat_s⟩). cbn.
        set_solver.
      }
      set_solver.
    * repeat eval_simplifier. cbn.
      repeat rewrite_app_ext.
      simpl.
      apply propset_top_elem_of_2. intros.
      apply elem_of_PropSet.
      symmetry. apply propset_top_elem_of_2.
      intros. destruct t0; set_solver.
    * repeat eval_simplifier. cbn.
      repeat rewrite_app_ext.
      simpl. rewrite propset_difference_neg.
      apply propset_top_elem_of_2. intros.
      apply elem_of_PropSet.
      set_solver.
    * repeat eval_simplifier. cbn.
      apply propset_fa_intersection_full. intros.
      repeat eval_simplifier. cbn.
      repeat rewrite_app_ext.
      simpl. rewrite propset_difference_neg.
      apply propset_top_elem_of_2. intros.
      apply elem_of_PropSet.
      set_solver.
    * repeat eval_simplifier. cbn.
      apply propset_fa_intersection_full. intros.
      remember (fresh_evar _ _) as f1. clear Heqf1.
      repeat eval_simplifier. cbn.
      apply propset_fa_intersection_full. intros.
      remember (fresh_evar _ _) as f2.
      assert (f1 <> f2). { subst f2.
        epose proof (fresh_evar_is_fresh nat_s (s ⋅ ⟨ kore_fevar f1 ⟩ =k{x3} s ⋅ 
     ⟨ kore_bevar In_nil ⟩ --->ₖ kore_fevar f1 =k{x3} 
     kore_bevar In_nil)). cbn in H. case_match; try congruence.
     epose proof Eqdep.EqdepTheory.UIP_refl _ _ e.
     rewrite H1 in H. cbn in H. intro. rewrite <- H2 in H. set_solver.
      }
      repeat eval_simplifier. case_match; try congruence.
      repeat rewrite_app_ext.
      simpl. autorewrite_set.
      apply propset_top_elem_of_2. intros.
      apply elem_of_PropSet.
      apply Classical_Prop.imply_to_or. set_solver.
    * repeat eval_simplifier. cbn.
      apply propset_fa_intersection_full. intros.
      remember (fresh_evar _ _) as f1. clear Heqf1.
      repeat eval_simplifier. cbn.
      repeat rewrite_app_ext.
      simpl. set_solver.
    * repeat eval_simplifier. cbn.
      apply propset_fa_intersection_full. intros.
      remember (fresh_evar _ _) as f1. clear Heqf1.
      repeat eval_simplifier. cbn.
      apply propset_fa_intersection_full. intros.
      remember (fresh_evar _ _) as f2.
      assert (f1 <> f2). { subst f2.
        epose proof (fresh_evar_is_fresh nat_s (plus ⋅ ⟨ s ⋅ ⟨ kore_fevar f1 ⟩; 
            kore_bevar In_nil ⟩ =k{x5} s ⋅ 
     ⟨ plus ⋅ ⟨ kore_fevar f1; kore_bevar In_nil ⟩ ⟩)). cbn in H. case_match; try congruence.
     epose proof Eqdep.EqdepTheory.UIP_refl _ _ e.
     rewrite H1 in H. cbn in H. intro. rewrite <- H2 in H. set_solver.
      }
      repeat eval_simplifier. case_match; try congruence.
      repeat rewrite_app_ext.
      simpl. set_solver.
    * repeat eval_simplifier. cbn.
      apply propset_fa_intersection_full. intros.
      remember (fresh_evar _ _) as f1. clear Heqf1.
      repeat eval_simplifier.
      repeat rewrite_app_ext.
      cbn. set_solver.
    * repeat eval_simplifier. cbn.
      apply propset_fa_intersection_full. intros.
      remember (fresh_evar _ _) as f1. clear Heqf1.
      repeat eval_simplifier.
      repeat rewrite_app_ext.
      cbn. set_solver.
    * repeat eval_simplifier. cbn.
      repeat rewrite_app_ext.
      cbn. set_solver.
    * repeat eval_simplifier. cbn.
      apply propset_fa_intersection_full. intros.
      remember (fresh_evar _ _) as f1. clear Heqf1.
      repeat eval_simplifier.
      repeat rewrite_app_ext.
      cbn. set_solver.
    * repeat eval_simplifier. cbn.
      apply propset_fa_intersection_full. intros.
      remember (fresh_evar _ _) as f1. clear Heqf1.
      repeat eval_simplifier.
      apply propset_fa_intersection_full. intros.
      remember (fresh_evar _ _) as f2.
      assert (f1 <> f2 \/ x10 <> x11). {
        destruct (decide (x10 = x11)).
        * subst.
          epose proof (fresh_evar_is_fresh x11 (pi1 x11 x11 ⋅ ⟨ pair x11 x11 ⋅ 
                   ⟨ kore_fevar f1;
                   kore_bevar In_nil ⟩ ⟩ =k{x12} 
     kore_fevar f1)). left.
          intro. cbn in H. case_match; try congruence.
          epose proof Eqdep.EqdepTheory.UIP_refl _ _ e.
          rewrite H2 in H. cbn in H.
          setoid_rewrite <- H0 in H.
          set_solver.
        * by right.
      } clear Heqf2.
      repeat eval_simplifier. cbn.
      (* transports *)
      destruct (decide (x11 = x10)); subst.
      - destruct H; try congruence.
        case_match; try congruence.
        case_match.
        + epose proof Eqdep.EqdepTheory.UIP_refl _ _ e.
          clear H1. rewrite H2 in e0. cbn in e0.
          congruence.
        + clear H1. case_match.
          2: { clear H1.
            epose proof Eqdep.EqdepTheory.UIP_refl _ _ e. rewrite H1 in n0. cbn in n0.
            congruence.
          }
          clear -H.
          (* up to this point, transports
             However, this is the same as in the next "-" bullet.
          *)
          repeat eval_simplifier. cbn.
          case_match; try congruence.
          case_match; try congruence.
          case_match; try congruence; clear H2.
          2: {
            epose proof Eqdep.EqdepTheory.UIP_refl _ _ e0. rewrite H2 in n0. cbn in n0.
            congruence.
          }
          epose proof Eqdep.EqdepTheory.UIP_refl _ _ e. rewrite H2. cbn.
          epose proof Eqdep.EqdepTheory.UIP_refl _ _ e0. rewrite H3. cbn.
          repeat rewrite_app_ext.
          cbn. set_solver.
      - repeat eval_simplifier. cbn.
        case_match; try congruence.
        case_match; try congruence.
        case_match; try congruence; clear H2.
        2: {
          epose proof Eqdep.EqdepTheory.UIP_refl _ _ e. rewrite H2 in n1. cbn in n1.
          congruence.
        }
        epose proof Eqdep.EqdepTheory.UIP_refl _ _ e. rewrite H2. cbn.
        repeat rewrite_app_ext.
      cbn. set_solver.
    * repeat eval_simplifier. cbn.
      apply propset_fa_intersection_full. intros.
      remember (fresh_evar _ _) as f1. clear Heqf1.
      repeat eval_simplifier.
      apply propset_fa_intersection_full. intros.
      remember (fresh_evar _ _) as f2.
      assert (f1 <> f2 \/ x13 <> x14). {
        destruct (decide (x13 = x14)).
        * subst.
          epose proof (fresh_evar_is_fresh x14 (pi2 x14 x14 ⋅ ⟨ pair x14 x14 ⋅ 
                   ⟨ kore_fevar f1;
                   kore_bevar In_nil ⟩ ⟩ =k{x15} 
     kore_bevar In_nil)). left.
          intro. cbn in H. case_match; try congruence.
          epose proof Eqdep.EqdepTheory.UIP_refl _ _ e.
          rewrite H2 in H. cbn in H.
          setoid_rewrite <- H0 in H.
          set_solver.
        * by right.
      } clear Heqf2.
      repeat eval_simplifier. cbn.
      (* transports *)
      destruct (decide (x13 = x14)); subst.
      - destruct H; try congruence.
        case_match; try congruence.
        case_match.
        2: { epose proof Eqdep.EqdepTheory.UIP_refl _ _ e.
          clear H1. rewrite H2 in n. cbn in n.
          congruence.
        }
        clear H1.
        clear -H.
        (* up to this point, transports
             However, this is the same as in the next "-" bullet.
          *)
          repeat eval_simplifier. cbn.
          case_match; try congruence.
          case_match; try congruence.
          case_match; try congruence; clear H2.
          2: {
            epose proof Eqdep.EqdepTheory.UIP_refl _ _ e0. rewrite H2 in n0. cbn in n0.
            congruence.
          }
          epose proof Eqdep.EqdepTheory.UIP_refl _ _ e. rewrite H2. cbn.
        epose proof Eqdep.EqdepTheory.UIP_refl _ _ e0. rewrite H3. cbn.
        repeat rewrite_app_ext.
        cbn. set_solver.
    - repeat eval_simplifier. cbn.
      case_match; try congruence.
      case_match; try congruence.
      case_match; try congruence; clear H2.
      2: {
        epose proof Eqdep.EqdepTheory.UIP_refl _ _ e. rewrite H2 in n1. cbn in n1.
        congruence.
      }
      epose proof Eqdep.EqdepTheory.UIP_refl _ _ e. rewrite H2. cbn.
      repeat rewrite_app_ext.
      cbn. set_solver.
    * repeat eval_simplifier. cbn.
      apply propset_fa_intersection_full. intros.
      remember (fresh_evar _ _) as f1. clear Heqf1.
      repeat eval_simplifier.
      case_match; try congruence.
      2: {
        exfalso. apply n. cbn. reflexivity.
      }
      repeat rewrite_app_ext.
      cbn. destruct c. simpl. set_solver.
    * repeat eval_simplifier. cbn.
      apply propset_fa_intersection_full. intros.
      remember (fresh_evar _ _) as f1. clear Heqf1.
      repeat eval_simplifier.
      case_match; try congruence.
      2: {
        cbn in n. congruence.
      }
      repeat eval_simplifier.
      repeat rewrite_app_ext.
      rewrite make_n_bevar_subst.
      rewrite eval_make_n.
      set_solver.
    * repeat eval_simplifier. cbn.
      apply propset_fa_intersection_full. intros.
      remember (fresh_evar _ _) as f1. clear Heqf1.
      repeat eval_simplifier.
      case_match; try congruence.
      2: {
        cbn in n. congruence.
      }
      repeat eval_simplifier.
      repeat rewrite_app_ext. cbn.
      rewrite nat_to_bin_eq. set_solver.
  Qed.

End Semantics.
