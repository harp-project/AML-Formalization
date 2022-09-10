From MatchingLogic Require Export Syntax
                                  IndexManipulation
                                  Semantics
                                  ProofSystem
                                  StringSignature
                                  wftactics
                                  DerivedOperators_Syntax
                                  DerivedOperators_Semantics
                                  NamedAxioms.

Module Notations.
  Export MatchingLogic.Syntax.Notations
         MatchingLogic.Substitution.Notations
         MatchingLogic.DerivedOperators_Syntax.Notations
         MatchingLogic.ProofSystem.Notations
         MatchingLogic.ApplicationContext.Notations.
  Export Syntax.BoundVarSugar.
End Notations.