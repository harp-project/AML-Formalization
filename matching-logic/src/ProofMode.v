From MatchingLogic Require Export
  Logic
  ProofMode_base
  ProofInfo
  ProofMode_propositional
  ProofMode_firstorder
  ProofMode_fixpoint
  ProofMode_reshaper
  ProofMode_misc
.

(** Importing this file opens the necessary scope for the proof mode to work
    properly! *)
Open Scope ml_scope.
Open Scope string_scope.
Open Scope list_scope.