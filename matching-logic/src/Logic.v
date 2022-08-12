From MatchingLogic Require Export Syntax
                                  IndexManipulation
                                  Semantics
                                  ProofSystem
                                  StringSignature
                                  wftactics
                                  DerivedOperators_Syntax
                                  NamedAxioms.

Module Notations.
  Export MatchingLogic.Syntax.Notations
         MatchingLogic.Substitution.Notations
         MatchingLogic.DerivedOperators_Syntax.Notations
         MatchingLogic.ProofSystem.Notations.
End Notations.