From Coq Require Import Classes.Morphisms_Prop.
From MatchingLogic Require Export Sorts_Semantics
                                  Bool_Syntax.
Import MatchingLogic.Logic.Notations
       MatchingLogic.Theories.Definedness_Syntax.Notations
       MatchingLogic.Theories.Sorts_Syntax.Notations.

Section with_model.
  Context
    {Σ : Signature}
    {syntax : Bool_Syntax.Syntax}
    {M : Model}.
  Open Scope ml_scope.

  Hypothesis M_satisfies_theory : M ⊨ᵀ Bool_Syntax.theory.

End with_model.

(* Section bool_model.

  Instance default_boolΣ : Signature := {
    variables := StringMLVariables;
    ml_symbols := Build_MLSymbols Symbols _ _;
  }.

  Instance default_bool_syntax : Bool_Syntax.Syntax := {
     inj := id;
     imported_sorts := 
  }.

End bool_model. *)