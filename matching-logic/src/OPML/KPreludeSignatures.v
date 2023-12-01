From Coq Require Import ssreflect ssrfun ssrbool.

From stdpp Require Import base finite list list_numbers propset strings.
(* This is unset by stdpp. We need to set it again.*)
Set Transparent Obligations.

From Equations Require Import Equations.
(* Set Equations Transparent. *)

Require Import Coq.Program.Equality. (* Dependent destruction *)
Require Import Coq.Logic.Classical_Prop. (* Proof irrelevance *)

From MatchingLogic.OPML Require Import
    OpmlSignature
.

#[global]
Instance eq_partial_order (A : Type) : PartialOrder (@eq A).
Proof.
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


Module bool.

    Inductive Sorts_t : Set :=
    | SortBool
    .

    Instance Sorts_eqdec : EqDecision Sorts_t.
    Proof. solve_decision. Defined.

    Program Instance Sorts_finite : Finite Sorts_t := {|
        enum := [SortBool] ;
    |}.
    Next Obligation. compute_done. Qed.
    Next Obligation. destruct x; compute_done. Qed.
    Fail Next Obligation.

    Program Definition Sorts : OPMLSorts := {|
        opml_sort := Sorts_t ;
        opml_subsort := eq ;
    |}.
    Fail Next Obligation.

    Inductive Symbols_t : Set :=
    | btrue
    | bfalse
    .

    Instance Symbols_t_eqdec : EqDecision Symbols_t.
    Proof. solve_decision. Defined.

    Program Instance Symbols_t_finite : Finite Symbols_t := {|
        enum := [btrue;bfalse]
    |}.
    Next Obligation. compute_done. Qed.
    Next Obligation. destruct x; compute_done. Qed.
    Fail Next Obligation.

    Definition Vars : @OPMLVariables Sorts := {|
        opml_evar := fun s => string;
        opml_svar := fun s => string;
    |}.
    Fail Next Obligation.

    Definition Symbols_t_arg_sorts (s : Symbols_t) : list (@opml_sort Sorts) :=
        match s with
        | btrue => []
        | bfalse => []
        end
    .

    Definition Symbols_t_return_sort (s : Symbols_t) : @opml_sort Sorts :=
        match s with
        | btrue => SortBool
        | bfalse => SortBool
        end 
    .

    Definition Symbols : @OPMLSymbols Sorts := {|
        opml_symbol := Symbols_t ;
        opml_arg_sorts := Symbols_t_arg_sorts ;
        opml_ret_sort := Symbols_t_return_sort ;
    |}.

    #[global]
    Instance Σ : OPMLSignature := {|
        opml_sorts := Sorts ;
        opml_variables := Vars ;
        opml_symbols := Symbols ;
    |}.

End bool.



