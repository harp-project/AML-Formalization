From MatchingLogic Require Export Syntax
                                  IndexManipulation
                                  Semantics
                                  StringSignature
                                  wftactics
                                  DerivedOperators_Syntax
                                  DerivedOperators_Semantics
                                  NamedAxioms
                                  ProofInfo.

Module Notations.
  Export MatchingLogic.Syntax.Notations
         MatchingLogic.Substitution.Notations
         MatchingLogic.DerivedOperators_Syntax.Notations
         MatchingLogic.ApplicationContext.Notations
         MatchingLogic.ProofInfo.Notations
         MatchingLogic.Semantics.Notations.
  Export Pattern.BoundVarSugar.
End Notations.

Open Scope string_scope.
Open Scope ml_scope.
Open Scope list_scope.
