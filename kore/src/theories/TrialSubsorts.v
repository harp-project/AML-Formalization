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
  | SymInList.

  (* We prove decidable equality and finiteness of the type above. *)
  Instance DemoSyms_eq_dec : EqDecision DemoSyms.
  Proof. solve_decision. Defined.
  Program Instance DemoSyms_finite : finite.Finite DemoSyms := {
    enum := [SymZero;SymSucc;SymAdd;SymTrue;
    SymFalse;SymIsList;SymNil;SymCons;SymInList];
  }.
  Next Obligation. compute_done. Defined.
  Final Obligation. destruct x; set_solver. Defined.

  Inductive Demo_subsort : DemoSorts -> DemoSorts -> Prop :=
  | subsorts_refl s : Demo_subsort s s
  | kitem_is_top s : s ≠ SortK -> Demo_subsort s SortKItem.

  Instance Demo_subsort_PartialOrder : PartialOrder Demo_subsort.
  Proof.
    apply Build_PartialOrder.
    apply Build_PreOrder.
    * intro s. constructor.
    * intros s1 s2 s3 H H0.
      invt H; invt H0; try by constructor.
    * intros s1 s2 H H0.
      invt H; invt H0; reflexivity.
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
                 end;
      ret_sort := fun σ => match σ with
                           | SymZero | SymSucc | SymAdd => SortNat
                           | SymTrue | SymFalse => SortBool
                           | SymNil | SymCons => SortList
                           | SymInList | SymIsList => SortBool
                           end;
    |};
  |}.

  Inductive carrier : DemoSorts -> Set :=
  | c_nat (n : nat) : carrier SortNat
  | c_bool (b : bool) : carrier SortBool
  | c_nil : carrier SortList
  | c_cons : carrier SortKItem -> carrier SortList -> carrier SortList
  | c_subsort (s1 s2 : DemoSorts) (P : subsort s1 s2) (x : carrier s1) : carrier s2.

  Check c_nat 1.
  Check c_nil.
  Check c_cons (c_subsort _ _ _ (c_nat 1)) c_nil.
(*   Check c_cons (c_nat 1) (c_cons (c_bool false) c_nil).
  Check c_cons (c_nat 1) (c_cons (c_bool false) (c_cons (c_cons (c_nat 1) c_nil) c_nil)). *)


  Program Definition DemoModel : @Model DemoSignature :=
    mkModel_singleton
      carrier
      (DemoSyms_rect _
        (c_nat 0)
        _
        _
        _
        _
        _
        _
        _
        _
      )
      _
      _.
  Next Obligation.
    simpl.
    intro. inversion H.
    exact (c_nat (S n)).
    inversion P.
  Defined.
  Next Obligation.
    simpl.
    intros. inversion H. inversion H0.
    exact (c_nat (n + n0)).
  Defined.
  Next Obligation.
    simpl.
    exact (c_bool true).
  Defined.
  Next Obligation.
    simpl.
    exact (c_bool false).
  Defined.
  Next Obligation.
    simpl.
    Print DemoSyms.
    intros.
    inversion H. (* TODO *)
  Defined.
  Next Obligation.
    simpl.
    exact (c_nil).
  Defined.
  Next Obligation.
    simpl.
    intros.
    exact (c_cons H H0).
  Defined.
  Next Obligation.

