(* TODO I probably don't need half of these *)

From Equations Require Import Equations.
From Coq Require Import ssreflect ssrfun ssrbool.

Require Import Logic.Classical_Prop Coq.Logic.FunctionalExtensionality.

From stdpp
Require Import
    base
    decidable
    propset
    fin_maps
    fin_sets
.

From MatchingLogic
Require Import
    Utils.extralibrary
    Utils.stdpp_ext
    Pattern
    Syntax
    Semantics
    DerivedOperators_Syntax
    DerivedOperators_Semantics
    PrePredicate
    monotonic
    Theories.Definedness_Syntax
    Theories.Definedness_Semantics
    Theories.Sorts_Syntax
    Theories.Sorts_Semantics
    Theories.DefaultModels
.


Import MatchingLogic.Logic.Notations.
Import MatchingLogic.Semantics.Notations.
Import MatchingLogic.Semantics.

Open Scope ml_scope.

Section helpers.
  Context
    {Σ₁ Σ₂ : Signature}
    (M₁ : @Model Σ₁)
    (M₂ : @Model Σ₂)
  .

  (* Add extra context arguments here *)
  Record ModelCombiners := {
    oneToTwo : Domain M₁ -> Domain M₂ -> propset (Domain M₁ + Domain M₂)%type;
    twoToOne : Domain M₂ -> Domain M₁ -> propset (Domain M₁ + Domain M₂)%type;
    (* Ignore these for now, come back when you reached
     * the long comment later *)
    (* oneToOneOverride : Domain M₁ -> Domain M₁ -> option (propset (Domain M₁ M₂)); *)
    (* twoToTwoOverride : Domain M₂ -> Domain M₂ -> option (propset (Domain M₁ M₂)); *)
  }.
End helpers.

Section test.
  Context
    {Σ₁ Σ₂ : Signature}
    (M₁ : @Model Σ₁)
    (M₂ : @Model Σ₂)
    (mc : ModelCombiners M₁ M₂)
  .

  Instance Σext : Signature := {
    (* TODO this definitely needs to change *)
    variables := StringMLVariables;
    ml_symbols := {|
        symbols := @symbols (@ml_symbols Σ₁) + @symbols (@ml_symbols Σ₂)
      |}
  }.

  Program Definition Mext : @Model Σext := {|
    Domain := (Domain M₁ + Domain M₂)%type;
    Domain_inhabited := sum_inhabited_l (Domain_inhabited M₁);
  |}.
  Next Obligation.
    destruct mc.
    intros [] [].
    exact (inl <$> app_interp M₁ d d0).
    exact (oneToTwo0 d d0).
    exact (twoToOne0 d d0).
    exact (inr <$> app_interp M₂ d d0).
  Defined.
  Next Obligation.
    intros [].
    exact (inl <$> sym_interp M₁ s).
    exact (inr <$> sym_interp M₂ s).
  Defined.
End test.

Section natbool.
  Definition NatBoolModel := Mext BoolModel NatModel {|
    (* Not sure if this is necessarily correct.
     * 0 andThen True might arise and should not be empty set.
     * Then again, our andThen is not standard, this is probably
     * the same issue we have with definedness later. *)
    oneToTwo _ _ := ∅; (* <something from bool> $ <smth from nat> *)
    twoToOne _ _ := ∅; (* <nat> $ <bool> *)
  |}.

  Instance PlainDefinedness_Σ : Signature := {
    variables := StringMLVariables;
    ml_symbols := {| symbols := unit |};
  }.

  Definition PlainDefinedness : @Model PlainDefinedness_Σ := {|
    Domain := unit;
    app_interp _ _ := ⊤;
    sym_interp _ := singleton ();
  |}.

  Definition DefinedNatBoolModel := Mext NatBoolModel PlainDefinedness {|
    oneToTwo _ _ := ∅; (* <smth from nat or bool> $ def *)
    twoToOne _ _ := ⊤; (* def $ <natbool> *)
  |}.

  (* These get complicated, let Coq figure it out for us *)
  Definition get_signature {Σ : Signature} (m : @Model Σ) : Signature := Σ.

  Instance def_syntax : @Definedness_Syntax.Syntax (get_signature DefinedNatBoolModel) := {
    sym_inj _ := inr ();
  }.

  Goal DefinedNatBoolModel ⊨ᵀ Definedness_Syntax.theory.
  Abort.
End natbool.

Section transformers.
  (* TODO *)
End transformers.
