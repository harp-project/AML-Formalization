From Coq Require Import ssreflect ssrfun ssrbool.

From Coq.Vectors Require Import Vector.

From stdpp Require Import
    base
    gmap
    natmap
    option
    vector
.
From MatchingLogic Require Import
    Signature
    Pattern
.

Require Import String.

Inductive A :=
| a_a
| a_b (b: B)
with
B :=
| b_b
| b_a (a : A)
.

Definition VarName := string.

(*
 So what notations we want to support?
 ¬ϕ ≡ ϕ ---> ⊥
 ϕ₁ \/ ϕ₂ ≡ ¬ϕ₁ ---> ϕ₂
 ∀ x. ϕ ≡ ¬ ∃ x. ¬ ϕ
 So, a notation is parametric in
 (1) how many patterns it takes as an argument.
 (2) how many element variables it binds
 (3) how many set variables it binds.
*)
Record MLNotation {Σ : Signature} := {
    (*mln_level : nat ;*)
    mln_arity : nat ;
    mln_ebinder_arity : nat;
    mln_sbinder_arity : nat;
    mln_expand :
      vec Pattern mln_arity -> (* patterns *)
      vec VarName mln_ebinder_arity -> (* bound evars*)
      vec VarName mln_sbinder_arity -> (* bound svars*)
      Pattern ;
}.

Inductive PMPattern {Σ : Signature} : Set :=
(* Direct constructors of a ML pattern *)
| pmpatt_evar (x : string)
| pmpatt_svar (X : string)
| pmpatt_sym (sigma : symbols)
| pmpatt_app (phi1 phi2 : PMPattern)
| pmpatt_bott
| pmpatt_imp (phi1 phi2 : PMPattern)
| pmpatt_exists (x : string) (phi : PMPattern)
| pmpatt_mu (X : string) (phi : PMPattern)
(* Indirect constructor - through notations  *)
| pmpatt_notation
    (notation : MLNotation)
    (args : vec PMPattern (mln_arity notation))
    (bound_evars : vec VarName (mln_ebinder_arity notation))
    (bound_svars : vec VarName (mln_sbinder_arity notation))
.

Fixpoint pmp2ln_aux
    {Σ : Signature}
    (ϕ : PMPattern)
    (evm : gmap VarName nat)
    (svm : gmap VarName nat)
    : Pattern