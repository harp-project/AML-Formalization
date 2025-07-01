From MatchingLogic Require Export stdpp_ext.
From Kore Require Export Semantics.
Import Signature.StringVariables.
Import Kore.Syntax.Notations.

From Coq Require Import ZArith.

Open Scope kore_scope.
Open Scope hlist_scope.
Open Scope string_scope.

(**
   This is copied from the other file.
 *)
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

Ltac basic_simplify_krule :=
  eval_helper2;
  simpl sort_inj;
  repeat (rewrite_app_ext; try rewrite fmap_propset_singleton);
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

  Import CRelationClasses.

  Inductive Sorts : Set :=
    | SortNat
    | SortBool
  .

  Instance MintSorts_eqdecision : EqDecision Sorts.
  Proof. solve_decision. Defined.

  Inductive Subsort : crelation Sorts := .

  Inductive SortNat_carrier : Set :=
    c_nat (n : nat)
  with SortBool_carrier : Set :=
    c_bool (b : bool)
  .

  Definition carrier (s : Sorts) : Set :=
    match s with
    | SortNat  => SortNat_carrier
    | SortBool => SortBool_carrier
    end.

  Instance carrier_inhabited : forall s, Inhabited (carrier s).
  Proof.
    intros []; repeat unshelve econstructor.
  Defined.

  Inductive Symbols : Set :=
    | SymZero
    | SymSucc
    | SymPlus
    | SymFalse
    | SymTrue
  .

  Program Instance Sig : Signature := {|
    sorts := {| sort := Sorts; subsort := Subsort |};
    variables := StringVariables;
    symbols := {|
      symbol := Symbols;
      arg_sorts := λ x, match x with
                        | SymZero  => []
                        | SymSucc  => [SortNat]
                        | SymPlus  => [SortNat; SortNat]
                        | SymFalse => []
                        | SymTrue  => []
                        end;
      ret_sort := λ x, match x with
                       | SymZero  => SortNat
                       | SymSucc  => SortNat
                       | SymPlus  => SortNat
                       | SymFalse => SortBool
                       | SymTrue  => SortBool
                       end;
    |}
  |}.

  Definition SortBool_parser (str : string) : option (carrier SortBool) :=
    match str with
    | "false" => Some (c_bool false)
    | "true"  => Some (c_bool true)
    | _       => None
    end.

  (**
     This is a very hacky ascii-based parser. There is zero validation
     here, it will happily parse any string as a number. But it does work
     for actual numbers. Which funnily enough probably means that this is
     as good of a parser as we'll ever need for generated models.
   *)
  Definition SortNat_parser (str : string) : option (carrier SortNat) := let fix F n s := if s is String x xs then F (10 * n + Ascii.nat_of_ascii x - 48) xs else n in Some (c_nat (F 0 str)).

  Definition parser s : string -> option (carrier s) :=
    match s with
    | SortNat  => SortNat_parser
    | SortBool => SortBool_parser
    end.

  Compute SortNat_parser "7".
  Compute SortNat_parser "123".
  Compute SortNat_parser "".
  Compute SortNat_parser "{@}".

  Definition Mod : @Model Sig := mkModel_singleton
    carrier
    (λ x, match x with
           | SymZero  => c_nat 0
           | SymSucc  => λ '(c_nat n), c_nat (S n)
           | SymPlus  => λ '(c_nat n) '(c_nat m), c_nat (n + m)
           | SymFalse => c_bool false
           | SymTrue  => c_bool true
           end
    )
    _
    (λ s s' H, match H with end)
    parser.

  Definition test : @Theory Sig := PropSet (λ pat,
  (* dv SortBool "false" \/ dv SortBool "true" *)
  pat = existT SortBool (kore_or (kore_dv SortBool "false") (kore_dv SortBool "true")) \/
  (* dv SortNat "123" + dv SortNat "456" = dv SortNat "579" *)
  exists R, pat = existT R (SymPlus ⋅ ⟨ kore_dv SortNat "123" ; kore_dv SortNat "456" ⟩ =k{R} kore_dv SortNat "579")
  ).

  Goal satT test Mod.
  Proof.
    unfold satT, satM, test. intros.
    (* Generate a goal for each axiom: *)
    unfold_elem_of; destruct_or?; destruct_ex?; subst; cbn.
    - simplify_krule.
      destruct t, b; auto.
    - by simplify_krule.
  Qed.

End T.
