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

    Definition MySymbols_arg_sorts (s : MySymbols) :=
        match s with
        | ms_bool_true => []
        | ms_bool_false => []
        | ms_list_bool_nil => []
        | ms_list_bool_cons => [(sort_list_bool:@opml_sort Sorts)]
        end
    .

    Definition MySymbols_return_sort (s : MySymbols) :=
        match s with
        | ms_bool_true => sort_bool
        | ms_bool_false => sort_bool
        | ms_list_bool_nil => sort_list_bool
        | ms_list_bool_cons => sort_list_bool
        end 
    .

    Definition Symbols : @OPMLSymbols Sorts := {|
        opml_symbol := MySymbols ;
        opml_arg_sorts := MySymbols_arg_sorts ;
        opml_ret_sort := MySymbols_return_sort ;
    |}.

    Instance Σ : OPMLSignature := {|
        opml_sorts := Sorts ;
        opml_variables := Vars ;
        opml_symbols := Symbols ;
    |}.

    Inductive CarrierSet :=
    | cs_bool (b : bool)
    | cs_list_bool (lb : list bool)
    .

    Definition _carrier := fun (s : opml_sort) =>
        match s with
        | sort_bool =>
            {[ x | exists (b : bool), x = cs_bool b ]}
        | sort_list_bool =>
            {[ x | exists (lb : list bool), x = cs_list_bool lb ]}
        end
    .

    Definition _app (s : opml_symbol) (args : list CarrierSet) : propset CarrierSet
    :=
        match s with
        | ms_bool_true => {[ cs_bool true ]}
        | ms_bool_false => {[ cs_bool false ]}
        | ms_list_bool_nil => {[ cs_list_bool [] ]}
        | ms_list_bool_cons =>
            match args with
            | (cs_bool b)::(cs_list_bool bs)::[] =>
                {[ cs_list_bool (b::bs) ]}
            | _ => ∅
            end
        end
    .

    Program Definition M : @OPMLModel Σ := {|
        om_unified_carrier := CarrierSet ;

        om_carrier := _carrier ;

        om_app := _app ;
    |}.
    Next Obligation.
        destruct m as [b|lb].
        {
            exists sort_bool.
            simpl.
            rewrite elem_of_PropSet.
            exists b.
            reflexivity.
        }
        {
            exists sort_list_bool.
            simpl.
            rewrite elem_of_PropSet.
            exists lb.
            reflexivity.
        }
    Qed.
    Next Obligation.
        destruct sym; simpl in H.
        {
            rewrite elem_of_PropSet in H.
            subst x.
            simpl.
            rewrite elem_of_PropSet.
            exists true.
            reflexivity.
        }
        {
            rewrite elem_of_PropSet in H.
            subst x.
            simpl.
            rewrite elem_of_PropSet.
            exists false.
            reflexivity.
        }
        {
            rewrite elem_of_PropSet in H.
            subst x.
            simpl.
            rewrite elem_of_PropSet.
            exists [].
            reflexivity.
        }
        {
            destruct args as [|a1 args].
            {
                rewrite elem_of_empty in H.
                inversion H.
            }
            destruct args as [|a2 args].
            {
                destruct a1;
                    rewrite elem_of_empty in H;
                    inversion H.
            }
            {
                destruct a1,a2.
                {
                    rewrite elem_of_empty in H;
                        inversion H.
                }
                {
                    destruct args as [|a3 args].
                    {
                        rewrite elem_of_PropSet in H.
                        subst x.
                        simpl.
                        rewrite elem_of_PropSet.
                        eexists. reflexivity.
                    }
                    {
                        rewrite elem_of_empty in H;
                        inversion H.
                    }
                }
                {
                    rewrite elem_of_empty in H;
                        inversion H.
                }
                {
                    rewrite elem_of_empty in H;
                        inversion H.
                }
            }
        }
    Qed.

End example01.

