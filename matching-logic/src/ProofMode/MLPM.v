From Coq Require Export ssrbool ssreflect ssrfun.
From stdpp Require Export list fin_sets.

From MatchingLogic Require Export
  Logic
  ProofInfo
  BasicProofSystemLemmas.
From MatchingLogic.ProofMode Require Export Basics
                                            Propositional
                                            Firstorder
                                            FixPoint
                                            Reshaper
                                            Misc.
From Coq Require Import String.

(** Importing this file opens the necessary scope for the proof mode to work
    properly! *)
Open Scope ml_scope.
Open Scope string_scope.
Open Scope list_scope.

Export
  MatchingLogic.Logic.Notations
  MatchingLogic.DerivedOperators_Syntax.Notations
  MatchingLogic.ProofInfo.Notations
.

Set Default Proof Mode "Classic".
