
From stdpp Require Export finite strings.
(* This is unset by stdpp. We need to set it again.*)
Set Transparent Obligations.

From MatchingLogic.OPML Require Export OpmlSignature.

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

Definition Identity_relation (A : Type) : relation A := fun x y => x = y.

#[global]
Instance Identity_relation_partial_order (A : Type) : PartialOrder (Identity_relation A).
Proof.
    repeat split.
    {
        intros x y z Hxy Hyz.
        inversion Hxy; inversion Hyz; subst; assumption.
    }
    {
        intros x y Hxy Hyx.
        inversion Hxy; inversion Hyx; subst; assumption.
    }
Qed.


Module bool_syntax.

    Inductive Sorts_t : Set :=
    | SortBool
    .

    #[global]
    Instance Sorts_eqdec : EqDecision Sorts_t.
    Proof. solve_decision. Defined.

    #[global]
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

    #[global]
    Instance Symbols_t_eqdec : EqDecision Symbols_t.
    Proof. solve_decision. Defined.

    #[global]
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

End bool_syntax.

Module bool_common.

    Inductive Symbols_t : Set :=
    | notBool
    | andBool
    | andThenBool
    | xorBool
    | orBool
    | orElseBool
    | impliesBool
    | equalsBool
    | notEqualsBool
    .

    #[global]
    Instance Symbols_t_eqdec : EqDecision Symbols_t.
    Proof. solve_decision. Defined.

    #[global]
    Program Instance Symbols_t_finite : Finite Symbols_t := {|
        enum := [notBool;andBool;andThenBool;xorBool;orBool;orElseBool;impliesBool;equalsBool;notEqualsBool]
    |}.
    Next Obligation. compute_done. Qed.
    Next Obligation. destruct x; compute_done. Qed.
    Fail Next Obligation.

    Definition extension_of_bool
        : @OPMLSignatureExtension
            (@opml_sorts bool_syntax.Σ)
            (@opml_variables bool_syntax.Σ)
    := {|
        ose_new_sort := Empty_set ;
        ose_new_sort_eqdec := _ ;
        ose_new_sort_countable := _ ;
        ose_new_subsort := Identity_relation Empty_set ;
        ose_new_subsort_po := _ ;
        ose_new_evar := fun _ => string ;
        ose_new_evar_eqdec := fun _ => _ ;
        ose_new_evar_countable := fun _ => _ ;
        ose_new_svar := fun _ => string ;
        ose_new_svar_eqdec := fun _ => _ ;
        ose_new_svar_countable := fun _ => _ ;
        ose_new_symbol := Symbols_t ;
        ose_new_sym_eqdec := _ ;
        ose_new_sym_countable := _ ;
        ose_new_arg_sorts := fun s =>
            match s return list (Empty_set + bool_syntax.Sorts_t) with
            | notBool => [inr bool_syntax.SortBool]
            | andBool => [inr bool_syntax.SortBool;inr bool_syntax.SortBool]
            | andThenBool => [inr bool_syntax.SortBool;inr bool_syntax.SortBool]
            | xorBool => [inr bool_syntax.SortBool;inr bool_syntax.SortBool]
            | orBool => [inr bool_syntax.SortBool;inr bool_syntax.SortBool]
            | orElseBool => [inr bool_syntax.SortBool;inr bool_syntax.SortBool]
            | impliesBool => [inr bool_syntax.SortBool;inr bool_syntax.SortBool]
            | equalsBool => [inr bool_syntax.SortBool;inr bool_syntax.SortBool]
            | notEqualsBool => [inr bool_syntax.SortBool;inr bool_syntax.SortBool]
            end;
        ose_new_ret_sort := fun s =>
            match s with
            | notBool => inr bool_syntax.SortBool
            | andBool => inr bool_syntax.SortBool
            | andThenBool => inr bool_syntax.SortBool
            | xorBool => inr bool_syntax.SortBool
            | orBool => inr bool_syntax.SortBool
            | orElseBool => inr bool_syntax.SortBool
            | impliesBool => inr bool_syntax.SortBool
            | equalsBool => inr bool_syntax.SortBool
            | notEqualsBool => inr bool_syntax.SortBool
            end;
    |}.

    Definition Σ : OPMLSignature := opml_signature_extend bool_syntax.Σ extension_of_bool.

    Definition bool_syntax_to_this : OPMLSignatureMorphism bool_syntax.Σ Σ
        := opml_signature_extend_morphism bool_syntax.Σ extension_of_bool
    .

End bool_common.

