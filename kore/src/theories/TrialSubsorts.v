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

  (* In the signature, we need to define the sorts, the variable types,
     and the typing/sorting rules for symbols: *)
  Program Instance DemoSignature : Signature := {|
    sorts := {|
      sort := DemoSorts;
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

  (* Definition carrier s :=
    match s with
    | SortNat => nat
    | SortBool => bool
    | SortList => ?
    | SortK => ?
    | SortKItem => ?
    end. *)
  Inductive carrier : DemoSorts -> Set :=
(*   | c_true : carrier SortBool
  | c_false : carrier SortBool
  | c_zero : carrier SortNat
  | c_succ : carrier SortNat -> carrier SortNat *)
  | c_nat (n : nat) : carrier SortNat
  | c_bool (b : bool) : carrier SortBool
  | c_nil : carrier SortList
  | c_cons {A} : carrier A -> carrier SortList -> carrier SortList.

  Check c_nat 1.
  Check c_nil.
  Check c_cons (c_nat 1) c_nil.
  Check c_cons (c_nat 1) (c_cons (c_bool false) c_nil).
  Check c_cons (c_nat 1) (c_cons (c_bool false) (c_cons (c_cons (c_nat 1) c_nil) c_nil)).

