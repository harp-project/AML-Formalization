From MatchingLogic.ProofMode Require Export Basics
                                            Propositional
                                            Firstorder
                                            FixPoint
                                            Reshaper
                                            Misc.

(** Importing this file opens the necessary scope for the proof mode to work
    properly! *)
Open Scope ml_scope.
Open Scope string_scope.
Open Scope list_scope.

Export MatchingLogic.Logic.Notations.

Set Default Proof Mode "Classic".
