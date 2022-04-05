(* In this module we define the definedness symbol and use it to build derived notions
   like totality and equality.
 *)
From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Ltac2 Require Import Ltac2.

Require Import Equations.Prop.Equations.

From Coq Require Import String Ensembles Setoid.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.Classical_Prop.
From Coq.Logic Require Import FunctionalExtensionality Eqdep_dec.
From Coq.Classes Require Import Morphisms_Prop.
From Coq.Unicode Require Import Utf8.
From Coq.micromega Require Import Lia.

From MatchingLogic Require Import Syntax NamedAxioms Semantics DerivedOperators ProofSystem ProofMode IndexManipulation.
From MatchingLogic.Utils Require Import stdpp_ext.

From stdpp Require Import base fin_sets sets propset proof_irrel option list.

Import extralibrary.

Import MatchingLogic.Syntax.Notations.
Import MatchingLogic.Semantics.Notations.
Import MatchingLogic.DerivedOperators.Notations.
Import MatchingLogic.Syntax.BoundVarSugar.
Import MatchingLogic.ProofSystem.Notations.

Set Default Proof Mode "Classic".

Close Scope equations_scope. (* Because of [!] *)

Import Notations.



End definedness.
  
#[export]
 Hint Resolve well_formed_defined : core.
#[export]
 Hint Resolve well_formed_total : core.
#[export]
 Hint Resolve well_formed_equal : core.
#[export]
 Hint Resolve well_formed_subseteq : core.
#[export]
 Hint Resolve well_formed_in : core.


  
