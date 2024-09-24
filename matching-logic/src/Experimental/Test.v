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
    inj _ := inr ();
  }.

  Goal DefinedNatBoolModel ⊨ᵀ Definedness_Syntax.theory.
  Proof.
    unfold theory, named_axioms, theory_of_NamedAxioms. simpl.
    unfold satisfies_theory. intros. apply elem_of_PropSet in H.
    destruct H, x. subst. cbn. unfold satisfies_model. intros.
    unfold patt_defined, p_x, ev_x. simp eval.
    unfold app_ext. simpl. unshelve eapply leibniz_equiv.
    exact (@propset_leibniz_equiv _ DefinedNatBoolModel).
    eapply set_equiv. intros. split; intros. set_solver.
    rewrite elem_of_PropSet.
    exists (inr ()), (evar_valuation ρ (evar_fresh [])).
    split. set_solver. split. set_solver.
    case_match. set_solver.
    (* This condition is unsolvable. It comes from
     * Mext def -> obligation 1 -> case 4 and
     * PlainDefinedness def -> app_interp.
     * These definitions both seen sensible on their own.
     * Use the second models app_interp if both elements are
     * from the second model, then wrap it in inr. Also
     * def $ def is full set (right?). However, when we combine
     * these, we get something wrong. I suspect this is because
     * def $ def needs to be full set even AFTER gluing the models,
     * and not inr <$> full set. We could take as extra params in
     * ModelCombiners two functions that specifiy these special
     * behaviours, maybe even functions returning options,
     * so we retain the default behaviour of delegating to
     * the sets underlying app_interp. This raises two questions:
     * - Are there any other cases where this is needed or is this
     * special to definedness? Should definedness be treated as
     * special and we don't need this change elsewhere?
     * ∙ PB: Yes, potentially generic datatypes would raise this issue too.
       For example, lists, maps, sets. Depending on the element's sort
       you might need to extend the behaviour of list/set/etc. symbols.
     * - If we override the models original app_interp, do we not
     * lose any reasoning we did about the original one? Is there
     * a way to retain the proofs and allow special behaviour?
     * ∙ PB: This is a main question. I think, you can only retain the original
         behaviour, if you override (or rather, extend) the behaviour in a
         correct way. For example, in case of definedness, you extend its
         interpretation in M₂ to full.
     *)
  Abort.
End natbool.

Section transformers.
  (* TODO *)
End transformers.
