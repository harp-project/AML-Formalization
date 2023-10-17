From Coq Require Import ssreflect ssrfun ssrbool.

Require Import Setoid.
From Coq Require Import Unicode.Utf8.
From Coq.Logic Require Import Classical_Prop FunctionalExtensionality.
From Coq.Classes Require Import Morphisms_Prop.

From stdpp Require Import base sets.

From MatchingLogic Require Import Logic.
Import MatchingLogic.Logic.Notations.
Require Import MatchingLogic.Theories.Bool_Syntax.

Import MatchingLogic.Theories.Definedness_Syntax.Notations.
Import MatchingLogic.Theories.Bool_Syntax.Notations.
Import BoundVarSugar.