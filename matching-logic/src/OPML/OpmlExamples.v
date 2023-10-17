From Coq Require Import ssreflect ssrfun ssrbool.

From stdpp Require Import base finite list list_numbers strings propset.
(* This is unset by stdpp. We need to set it again.*)
Set Transparent Obligations.

From Equations Require Import Equations.
(* Set Equations Transparent. *)

From MatchingLogic.Utils Require Import Surj.
From MatchingLogic.OPML Require Import OpmlSignature OpmlModel.

Module example01.

    Inductive Sort :=
    | sort_bool
    | sort_list_bool
    .

    #[global]
    Instance Sort_eqdec: EqDecision Sort.
    Proof.
        solve_decision.
    Defined.

    #[global]
    Program Instance Sort_finite: Finite Sort := {|
        enum := [sort_bool; sort_list_bool];
    |}.
    Next Obligation.
        compute_done.
    Qed.
    Next Obligation.
        destruct x; compute_done.
    Qed.

    Program Definition Sorts : OPMLSorts := {|
        opml_sort := Sort ;
        opml_subsort := eq ;
    |}.
    Next Obligation.
        repeat split.
        {
            intros x y z Hxy Hyz.
            subst. reflexivity.
        }
        {
            intros x y Hxy Hyx.
            subst. reflexivity.
        }
    Qed.

    Definition Vars : @OPMLVariables Sorts := {|
        opml_evar := fun s => string;
        opml_svar := fun s => string;
    |}.

    Inductive MySymbols :=
    | ms_bool_true
    | ms_bool_false
    | ms_list_bool_nil
    | ms_list_bool_cons
    .

    #[global]
    Instance MySymbols_eqdec: EqDecision MySymbols.
    Proof.
        solve_decision.
    Defined.

    #[global]
    Program Instance MySymbols_finite: Finite MySymbols := {|
        enum := [ms_bool_true; ms_bool_false; ms_list_bool_nil; ms_list_bool_cons];
    |}.
    Next Obligation.
        compute_done.
    Qed.
    Next Obligation.
        destruct x; compute_done.
    Qed.

    Definition Symbols : @OPMLSymbols Sorts := {|
        opml_symbol := MySymbols ;
        opml_arg_sorts := fun s =>
            match s with
            | ms_bool_true => []
            | ms_bool_false => []
            | ms_list_bool_nil => []
            | ms_list_bool_cons => [(sort_list_bool:@opml_sort Sorts)]
            end ;
        opml_ret_sort := fun s =>
            match s with
            | ms_bool_true => sort_bool
            | ms_bool_false => sort_bool
            | ms_list_bool_nil => sort_list_bool
            | ms_list_bool_cons => sort_list_bool
            end ;
    |}.

    Definition Σ : OPMLSignature := {|
        opml_sorts := Sorts ;
        opml_variables := Vars ;
        opml_symbols := Symbols ;
    |}.

    Inductive CarrierSet :=
    | cs_bool (b : bool)
    | cs_list_bool (lb : list bool)
    .

End example01.

