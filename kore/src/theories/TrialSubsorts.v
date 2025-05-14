From MatchingLogic Require Export stdpp_ext.
From Kore Require Export Semantics.
Import Signature.StringVariables.
Import Kore.Syntax.Notations.

From Coq Require Import ZArith.

Open Scope kore_scope.
Open Scope hlist_scope.
Open Scope string_scope.

Ltac autorewrite_set :=
  repeat (
    rewrite intersection_top_l_L +
    rewrite intersection_top_r_L +
    rewrite union_empty_l_L +
    rewrite union_empty_r_L +
    rewrite propset_difference_neg +
    rewrite propset_union_simpl +
    rewrite propset_intersection_simpl +
    rewrite singleton_subseteq_l
  ).

Ltac basic_simplify_krule :=
  simpl;
  eval_helper;
  repeat rewrite_app_ext;
  autorewrite_set.
Ltac simplify_krule :=
  basic_simplify_krule;
  apply propset_top_elem_of_2;
  intro;
  apply elem_of_PropSet;
  repeat rewrite elem_of_PropSet;
  repeat rewrite singleton_subseteq;
  repeat rewrite singleton_eq.


Ltac abstract_var := 
  match goal with
    | [|- context [evar_valuation ?σ ?s]] =>
      let x := fresh "var" in
      let Hx := fresh "Hvar" in
        remember (evar_valuation σ s) as x eqn:Hx (*;
        clear Hx;
        revert x *)
    end.

Module T.

  (* We have two sorts: natural numbers and bools *)
  Inductive DemoSorts :=
  | SortNat
  | SortBool
  | SortK
  | SortKItem
  | SortList.

  (* We prove decidable equality and finiteness of the type above. *)
  Instance DemoSorts_eq_dec : EqDecision DemoSorts.
  Proof. solve_decision. Defined.
  Program Instance DemoSorts_finite : finite.Finite DemoSorts := {
    enum := [SortNat; SortBool; SortK; SortKItem; SortList];
  }.
  Next Obligation. compute_done. Defined.
  Final Obligation. destruct x; set_solver. Defined.


  Inductive DemoSyms :=
  | SymZero
  | SymSucc
  | SymAdd
  | SymTrue
  | SymFalse
  | SymIsList
  | SymNil
  | SymCons
  | SymInList
  | SymAppend.

  (* We prove decidable equality and finiteness of the type above. *)
  Instance DemoSyms_eq_dec : EqDecision DemoSyms.
  Proof. solve_decision. Defined.
  Program Instance DemoSyms_finite : finite.Finite DemoSyms := {
    enum := [SymZero;SymSucc;SymAdd;SymTrue;
    SymFalse;SymIsList;SymNil;SymCons;SymInList;SymAppend];
  }.
  Next Obligation. compute_done. Defined.
  Final Obligation. destruct x; set_solver. Defined.

  Inductive Demo_subsort : CRelationClasses.crelation DemoSorts :=
  | subsorts_refl s : Demo_subsort s s
  | kitem_is_top s : s ≠ SortK -> s ≠ SortKItem -> Demo_subsort s SortKItem.

  Instance Demo_subsort_PreOrder : CRelationClasses.PreOrder Demo_subsort.
  Proof.
    split.
    cbv. intro. left.
    cbv. intros. inversion H; subst. assumption.
    inversion H0; subst. assumption. assumption.
  Defined.

  Instance Demo_subsort_PartialOrder : CRelationClasses.PartialOrder eq Demo_subsort.
  Proof.
    cbv. intros. split; intros. rewrite H. repeat constructor.
    destruct H. inversion d; subst. reflexivity.
    inversion d0; subst; reflexivity.
  Defined.

  (* In the signature, we need to define the sorts, the variable types,
     and the typing/sorting rules for symbols: *)
  Program Instance DemoSignature : Signature := {|
    sorts := {|
      sort := DemoSorts;
      subsort := Demo_subsort
    |};
    variables := StringVariables;
    symbols := {|
      symbol := DemoSyms;
      arg_sorts :=
        fun σ => match σ with
                 | SymZero => []
                 | SymSucc => [SortNat]
                 | SymAdd => [SortNat; SortNat]
                 | SymTrue => []
                 | SymFalse => []
                 | SymIsList => [SortK]
                 | SymNil => []
                 | SymCons => [SortKItem; SortList]
                 | SymInList => [SortKItem; SortList]
                 | SymAppend => [SortList; SortList]
                 end;
      ret_sort := fun σ => match σ with
                           | SymZero | SymSucc | SymAdd => SortNat
                           | SymTrue | SymFalse => SortBool
                           | SymNil | SymCons | SymAppend => SortList
                           | SymInList | SymIsList => SortBool
                           end;
    |};
  |}.

  Inductive carrier : DemoSorts -> Set :=
  | c_nat (n : nat) : carrier SortNat
  | c_bool (b : bool) : carrier SortBool
  (* | c_nil : carrier SortList *)
  (* | c_cons : carrier SortKItem -> carrier SortList -> carrier SortList *)
  | c_list (l : list (carrier SortKItem)) : carrier SortList
  | c_subsort (s1 s2 : DemoSorts) (P : subsort s1 s2) (x : carrier s1) : carrier s2
  (* This should match the subsort relation *)
  (* | c_kitem {A} : A ≠ SortK -> carrier A -> carrier SortKItem *)
  | c_dotk : carrier SortK.

  (* Check c_nat 1. *)
  (* Check c_nil. *)
  (* Check c_cons (c_kitem (eq_ind SortNat (λ x, if x is SortNat then True else False) I _) (c_nat 1)) c_nil. *)
  (* Check c_cons (c_nat 1) (c_cons (c_bool false) c_nil). *)
  (* Check c_cons (c_nat 1) (c_cons (c_bool false) (c_cons (c_cons (c_nat 1) c_nil) c_nil)). *)

  Lemma neqs_eq {A} {a b : A} (p q : a ≠ b) : p = q.
  Proof.
    apply functional_extensionality. intros. destruct (p x).
  Defined.

  Lemma subsort_unique {s1 s2} (p1 p2 : Demo_subsort s1 s2) : p1 = p2.
  Proof.
    dependent induction p1; dependent destruction p2.
    reflexivity.
    destruct n0. reflexivity.
    destruct n0. reflexivity.
    f_equal; apply neqs_eq.
  Defined.

  Instance carrier_eqdec A : EqDecision (carrier A).
  Proof.
    unfold EqDecision, Decision.
    (* No induction principle if the type appears in another *)
    (* type (list here). As usual... *)
    revert A. fix IH 2.
    intros.
    dependent destruction x; dependent destruction y; try ((right; discriminate) + (left; reflexivity)).
    * destruct (decide (n = n0)) as [-> | ?]; [left; reflexivity | right; congruence].
    * destruct (decide (b = b0)) as [-> | ?]; [left; reflexivity | right; congruence].
    * pose proof @list_eq_dec _ (IH SortKItem) l l0 as [-> | ?]; [left; reflexivity | right; congruence].
      Guarded.
    * destruct (decide (s0 = s1)) as [-> | ?].
      - destruct (IH _ x y) as [-> | ?].
        + rewrite (subsort_unique P P0); by left.
        + right. intro. inversion H. inversion_sigma H2.
          rewrite <- Eqdep.EqdepTheory.eq_rect_eq in H2_0.
          congruence.
      - right. intro. inversion H. congruence.
  Qed.

  Definition inb {A} {_ : EqDecision A} (x : A) (xs : list A) : bool.
  Proof.
    induction xs. exact false.
    exact (if decide (x = a) then true else false).
  Defined.

  Program Definition DemoModel : @Model DemoSignature := mkModel_singleton
    carrier
    _
    (λ s, match s with
           | SortNat   => populate (c_nat 0)
           | SortBool  => populate (c_bool false)
           | SortK     => populate (c_dotk)
           | SortKItem => populate (c_subsort _ _ _ (c_nat 0))
           | SortList  => populate (c_list [])
           end)
    (λ s1 s2 P, match P with
                | subsorts_refl s => id
                | kitem_is_top s ne ne' => c_subsort s SortKItem (kitem_is_top s ne ne')
                end)
  .
  Next Obligation.
    refine (λ s, match s with
                  | SymZero   => c_nat 0
                  | SymSucc   => λ n, _
                  | SymAdd    => λ n n', _
                  | SymTrue   => c_bool true
                  | SymFalse  => c_bool false
                  | SymIsList => λ k, c_bool false
                  | SymNil    => c_list []
                  | SymCons   => λ x xs, _
                  | SymInList => λ x xs, _
                  | SymAppend => λ xs ys, _
                  end
    ).
    * dependent induction n. exact (c_nat (S n)).
      inversion P; subst. exact (IHn erefl).
    * dependent induction n. dependent induction n'.
      exact (c_nat (n + n0)).
      inversion P; subst. exact (IHn' erefl).
      inversion P; subst. exact (IHn erefl n'). (* ? *)
    * dependent induction xs.
      exact (c_list (x :: l)).
      inversion P; subst. exact (IHxs erefl).
    * dependent induction xs. exact (c_bool (inb x l)).
      inversion P; subst. exact (IHxs erefl).
    * dependent induction xs.
      dependent induction ys.
      exact (c_list (l ++ l0)).
      inversion P; subst. exact (IHys erefl).
      inversion P; subst. exact (IHxs erefl ys). (* ? *)
  Defined.
  Next Obligation.
    constructor; discriminate.
  Defined.

  Program Definition test : @Theory DemoSignature := PropSet (λ pat,
    (* 0 ∈ [1; 0] *)
    exists R, pat = existT R (SymTrue ⋅ ⟨ ⟩ =k{R} (let zero := SymZero ⋅ ⟨ ⟩ in let zero_i := kore_inj _ _ zero in kore_app SymInList ⟨ zero_i ; (SymCons ⋅ ⟨ (kore_inj _ _ (SymSucc ⋅ ⟨ zero ⟩)) ; SymCons ⋅ ⟨ zero_i ; SymNil ⋅ ⟨ ⟩ ⟩ ⟩) ⟩)) \/
    (* [] ++ x = x *)
    exists R, pat = existT R (SymAppend ⋅ ⟨ SymNil ⋅ ⟨ ⟩ ; kore_fevar "x" ⟩ =k{R} kore_fevar "x") \/
    (* x ++ [] = x *)
    exists R, pat = existT R (SymAppend ⋅ ⟨ kore_fevar "x" ; SymNil ⋅ ⟨ ⟩ ⟩ =k{R} kore_fevar "x")
  ).
  Solve Obligations with (constructor; discriminate).

  Goal satT test DemoModel.
  Proof.
    unfold satT, satM, test. intros.
    inversion H. clear H.
    destruct H0; subst; simpl.
    simplify_krule. give_up.
    destruct H; destruct H; subst; simpl.
    simplify_krule. unfold block, solution_left, eq_rec_r, eq_rect_r. simpl. give_up.
    destruct H; subst; simpl.
    simplify_krule. unfold block, solution_left, eq_rec_r, eq_rect_r, carrier_rec. simpl. give_up.
  Abort.

  (* Program Definition DemoModel : @Model DemoSignature := *)
  (*   mkModel_singleton *)
  (*     carrier *)
  (*     (DemoSyms_rect _ *)
  (*       (c_nat 0) *)
  (*       _ *)
  (*       _ *)
  (*       _ *)
  (*       _ *)
  (*       _ *)
  (*       _ *)
  (*       _ *)
  (*       _ *)
  (*     ) *)
  (*     _ *)
  (*     _. *)
  (* Next Obligation. *)
  (*   simpl. *)
  (*   intro. inversion H. *)
  (*   exact (c_nat (S n)). *)
  (*   inversion P. *)
  (* Defined. *)
  (* Next Obligation. *)
  (*   simpl. *)
  (*   intros. inversion H. inversion H0. *)
  (*   exact (c_nat (n + n0)). *)
  (* Defined. *)
  (* Next Obligation. *)
  (*   simpl. *)
  (*   exact (c_bool true). *)
  (* Defined. *)
  (* Next Obligation. *)
  (*   simpl. *)
  (*   exact (c_bool false). *)
  (* Defined. *)
  (* Next Obligation. *)
  (*   simpl. *)
  (*   Print DemoSyms. *)
  (*   intros. *)
  (*   inversion H. (1* TODO *1) *)
  (* Defined. *)
  (* Next Obligation. *)
  (*   simpl. *)
  (*   exact (c_nil). *)
  (* Defined. *)
  (* Next Obligation. *)
  (*   simpl. *)
  (*   intros. *)
  (*   exact (c_cons H H0). *)
  (* Defined. *)
  (* Next Obligation. *)

