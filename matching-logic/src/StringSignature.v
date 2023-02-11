Require Import Arith.
Require Import ZArith.
Require Import List.
Require Import String.
Require Import Coq.micromega.Lia.

Require Import MatchingLogic.Syntax.
Require Import extralibrary.

From stdpp Require Import countable infinite strings.

Definition StringMLVariables : MLVariables :=
  {| evar := string;
     svar := string;
     string2evar := @id string;
     string2svar := @id string;
  |}.
