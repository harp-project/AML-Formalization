From Coq Require Export ssrbool.
From stdpp Require Export list fin_sets.

From MatchingLogic Require Export
  Logic
  ProofMode_base
  ProofInfo
  BasicProofSystemLemmas
  ProofMode_propositional
  ProofMode_firstorder
  ProofMode_fixpoint
  ProofMode_reshaper
  ProofMode_misc
.


From Coq Require Import String.

(** Importing this file opens the necessary scope for the proof mode to work
    properly! *)
Open Scope ml_scope.
Open Scope string_scope.
Open Scope list_scope.

Import
  MatchingLogic.Logic.Notations
  MatchingLogic.DerivedOperators_Syntax.Notations
.

Set Default Proof Mode "Classic".
