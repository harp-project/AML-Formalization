From Coq Require Import ssreflect ssrfun ssrbool.

From Coq.Vectors Require Import Vector.

From Equations Require Import Equations.

From stdpp Require Import
    base
    gmap
    infinite
    natmap
    option
    strings
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

Definition incr_values
    (vm : gmap VarName nat)
    : gmap VarName nat
:= fmap (fun n => S n) vm.

Section sec.
    Context
        {Σ : Signature}
        {string2evar : string -> evar}
        {string2evar_inj : Inj (=) (=) string2evar}
        {string2svar : string -> svar}
        {string2svar_inj : Inj (=) (=) string2svar}
    .

    Check insert.



    Fixpoint pmp2ln_aux
        (evm : gmap VarName nat)
        (svm : gmap VarName nat)
        (ϕ : PMPattern)
        : Pattern :=
        match ϕ with
        | pmpatt_evar x =>
            match evm !! x with
            | Some n => patt_bound_evar n
            | None => patt_free_evar (string2evar x)
            end
        | pmpatt_svar x =>
            match svm !! x with
            | Some n => patt_bound_svar n
            | None => patt_free_svar (string2svar x)
            end
        | pmpatt_sym s => patt_sym s
        | pmpatt_bott => patt_bott
        | pmpatt_app ϕ₁ ϕ₂ =>
            patt_app
                (pmp2ln_aux evm svm ϕ₁)
                (pmp2ln_aux evm svm ϕ₂)
        | pmpatt_imp ϕ₁ ϕ₂ =>
            patt_imp
                (pmp2ln_aux evm svm ϕ₁)
                (pmp2ln_aux evm svm ϕ₂)
        | pmpatt_exists name ϕ' =>
            patt_exists
                (pmp2ln_aux
                    (<[name := 0]>(incr_values evm))
                    svm ϕ')
        | pmpatt_mu name ϕ' =>
            patt_mu
                (pmp2ln_aux
                    evm
                    (<[name := 0]>(incr_values svm))
                    ϕ')
        | pmpatt_notation notation args bound_evars bound_svars =>
            mln_expand
                notation
                (vmap (fun ϕ' => pmp2ln_aux evm svm) args)
                bound_evars
                bound_svars
        end
        .
    Admitted.

    Definition pmp2ln
        {Σ : Signature}
        (ϕ : PMPattern)
        : Pattern :=
        pmp2ln_aux ϕ ∅ ∅.


