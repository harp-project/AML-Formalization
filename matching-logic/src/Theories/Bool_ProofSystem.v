From Coq Require Import ssreflect ssrfun ssrbool.

From Ltac2 Require Import Ltac2.

From Coq Require Import String Ensembles Setoid.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.Classical_Prop.
From Coq.Logic Require Import FunctionalExtensionality Eqdep_dec.
From Coq.Classes Require Import Morphisms_Prop.
From Coq.Unicode Require Import Utf8.
From Coq.micromega Require Import Lia.

From MatchingLogic Require Export Logic ProofMode.MLPM.
From MatchingLogic.Theories Require Export Definedness_Syntax Definedness_ProofSystem.
From MatchingLogic.Utils Require Export stdpp_ext.

Require Export MatchingLogic.wftactics.

From stdpp Require Import base fin_sets sets propset proof_irrel option list.

Import extralibrary.

Import MatchingLogic.Logic.Notations.
Import MatchingLogic.Theories.Definedness_Syntax.Notations.

Set Default Proof Mode "Classic".

Require Import MatchingLogic.Theories.DeductionTheorem.

Require MatchingLogic.Theories.Sorts_Syntax.
Export MatchingLogic.Theories.Sorts_Syntax.Notations.

From Coq Require Import ssreflect ssrfun ssrbool.

Require Import Setoid.
From Coq Require Import Unicode.Utf8.
From Coq.Logic Require Import Classical_Prop FunctionalExtensionality.
From Coq.Classes Require Import Morphisms_Prop.

From stdpp Require Import base sets.

From MatchingLogic Require Import Logic MLPM.
Import MatchingLogic.Logic.Notations.
Require Import MatchingLogic.Theories.Bool_Syntax.

Import MatchingLogic.Theories.Definedness_Syntax.Notations.
Import MatchingLogic.Theories.Bool_Syntax.Notations.
Import BoundVarSugar.

Set Default Proof Mode "Classic".

Section bools.
Context
  { Σ : Signature}
  { syntax : Syntax}.

Open Scope ml_scope.
Open Scope string_scope.
Open Scope list_scope.
  
Theorem double_neg : forall Γ , theory ⊆ Γ ->
        Γ ⊢ all mlBool,   !b !b b0 =ml b0.
Proof.
intros.
toMLGoal.
wf_auto2.
mlIntroAll x.
simpl.
mlIntro "H".
Abort. 
(* Continue from here *)


End bools.
Close Scope ml_scope.
Close Scope string_scope.
Close Scope list_scope.
