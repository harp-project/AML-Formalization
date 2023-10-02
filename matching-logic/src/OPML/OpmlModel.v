From Coq Require Import ssreflect ssrfun ssrbool.

From stdpp Require Import base list list_numbers propset.
(* This is unset by stdpp. We need to set it again.*)
Set Transparent Obligations.

From Equations Require Import Equations.
(* Set Equations Transparent. *)

From MatchingLogic.OPML Require Import OpmlSignature.

Polymorphic Cumulative
Record OpmlModel {Σ : OPMLSignature} := {
    om_unified_carrier :
        Type ;

    om_carrier :
        opml_sort -> propset om_unified_carrier ;

    om_subsort_1 :
        forall
            (from to : opml_sort)
            (subsort : opml_subsort from to),
            om_carrier from ⊆ om_carrier to ;
    
    om_subsort_2 :
        forall
            (from to : opml_sort)
            (not_subsort : not (opml_subsort from to)),
            om_carrier from ## om_carrier to ;
    
    om_app :
        opml_symbol ->
        list om_unified_carrier ->
        propset om_unified_carrier ;
    
    om_app_wellsorted :
        forall
            (sym : opml_symbol)
            (args : list om_unified_carrier)
            (args_ws : forall i arg sort,
                args !! i = Some arg ->
                (opml_arg_sorts sym) !! i = Some sort ->
                arg ∈ om_carrier sort
            ),
            (om_app sym args) ⊆ (om_carrier (opml_ret_sort sym)) ;
}.