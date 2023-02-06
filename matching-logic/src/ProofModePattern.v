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
Definition EVarName := VarName.
Definition SVarName := VarName.


Definition incr_values
    (vm : gmap VarName nat)
    : gmap VarName nat
:= fmap (fun n => S n) vm.


Record PContext := mkPContext {
    pc_evm : gmap EVarName nat ;
    pc_svm : gmap SVarName nat ;
}.

Definition pc_add_ename
    (ctx : PContext)
    (name : EVarName) :=
    mkPContext ((<[name := 0]>(incr_values (pc_evm ctx)))) (pc_svm ctx)
.

Definition pc_add_sname
    (ctx : PContext)
    (name : SVarName) :=
    mkPContext (pc_evm ctx) ((<[name := 0]>(incr_values (pc_svm ctx))))
.

Definition Pattern_in_context
    {Σ : Signature} :=
    PContext -> Pattern
.

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
Record MLConstruct {Σ : Signature} := {
    (*mlc_level : nat ;*)
    mlc_arity : nat ;
    mlc_ebinder_arity : nat;
    mlc_sbinder_arity : nat;
    mlc_expand :
      vec Pattern_in_context mlc_arity -> (* patterns *)
      vec VarName mlc_ebinder_arity -> (* bound evars*)
      vec VarName mlc_sbinder_arity -> (* bound svars*)
      Pattern_in_context ;
}.

Section sec.
    Context
        {Σ : Signature}
        {string2evar : string -> evar}
        {string2evar_inj : Inj (=) (=) string2evar}
        {string2svar : string -> svar}
        {string2svar_inj : Inj (=) (=) string2svar}
    .
    Definition mlc_sym
        (s : symbols)
        : MLConstruct := {|
            mlc_arity := 0 ;
            mlc_ebinder_arity := 0 ;
            mlc_sbinder_arity := 0 ;
            mlc_expand :=
                fun _ =>
                fun _ =>
                fun _ => (
                    fun _ =>
                    patt_sym s
                )
        |}
    .

    Definition mlc_bott
        : MLConstruct := {|
            mlc_arity := 0 ;
            mlc_ebinder_arity := 0 ;
            mlc_sbinder_arity := 0 ;
            mlc_expand :=
                fun _ =>
                fun _ =>
                fun _ => (
                    fun _ =>
                    patt_bott
                )
        |}
    .
        

    Definition mlc_evar
        {name : EVarName}
        : MLConstruct := {|
            mlc_arity := 0 ;
            mlc_ebinder_arity := 0 ;
            mlc_sbinder_arity := 0 ;
            mlc_expand :=
                fun _ =>
                fun _ =>
                fun _ => (
                    fun ctx =>
                    match (pc_evm ctx) !! name with
                    | Some n => patt_bound_evar n
                    | None => patt_free_evar (string2evar name)
                    end
                )
        |}
    .

    Definition mlc_svar
        {name : SVarName}
        : MLConstruct := {|
            mlc_arity := 0 ;
            mlc_ebinder_arity := 0 ;
            mlc_sbinder_arity := 0 ;
            mlc_expand :=
                fun _ =>
                fun _ =>
                fun _ => (
                    fun ctx =>
                    match (pc_svm ctx) !! name with
                    | Some n => patt_bound_svar n
                    | None => patt_free_svar (string2svar name)
                    end
                )
        |}
    .

    Definition mlc_app
        : MLConstruct := {|
            mlc_arity := 2 ;
            mlc_ebinder_arity := 0 ;
            mlc_sbinder_arity := 0 ;
            mlc_expand :=
                fun ps =>
                fun _ =>
                fun _ => (
                    fun ctx =>
                    patt_app
                        ((ps !!! (0)%fin) ctx)
                        ((ps !!! (1)%fin) ctx)
                )
        |}
    .

    Definition mlc_imp
        : MLConstruct := {|
            mlc_arity := 2 ;
            mlc_ebinder_arity := 0 ;
            mlc_sbinder_arity := 0 ;
            mlc_expand :=
                fun ps =>
                fun _ =>
                fun _ => (
                    fun ctx =>
                    patt_imp
                        ((ps !!! (0)%fin) ctx)
                        ((ps !!! (1)%fin) ctx)
                )
        |}
    .

    Definition mlc_exists
        : MLConstruct := {|
            mlc_arity := 1 ;
            mlc_ebinder_arity := 1 ;
            mlc_sbinder_arity := 0 ;
            mlc_expand :=
                fun ps =>
                fun evs =>
                fun _ => (
                    fun ctx =>
                        let name := evs !!! (0)%fin in
                        let ctx' := pc_add_ename ctx name in
                        let ϕ_in_context := ps !!! (0)%fin in
                        let ϕ := ϕ_in_context ctx' in
                        patt_exists ϕ
                )
        |}
    .

    Definition mlc_mu
        : MLConstruct := {|
            mlc_arity := 1 ;
            mlc_ebinder_arity := 0 ;
            mlc_sbinder_arity := 1 ;
            mlc_expand :=
                fun ps =>
                fun _ =>
                fun svs => (
                    fun ctx =>
                        let name := svs !!! (0)%fin in
                        let ctx' := pc_add_sname ctx name in
                        let ϕ_in_context := ps !!! (0)%fin in
                        let ϕ := ϕ_in_context ctx' in
                        patt_mu ϕ
                )
        |}
    .


(*
  Example:
  ∀ x. ∃ y. x ---> y
  ∀ x. ∃ y. x /\ y
*)

Inductive PMPattern {Σ : Signature} : Set :=
| pmpatt_mu (X : string) (phi : PMPattern)
| pmpatt_construct
    (construct : MLConstruct)
    (args : vec PMPattern (mlc_arity construct))
    (bound_evars : vec VarName (mlc_ebinder_arity construct))
    (bound_svars : vec VarName (mlc_sbinder_arity construct))
.

Equations? PMPattern_size
    {Σ : Signature}
    (ϕ : PMPattern)
    : nat :=
    PMPattern_size (pmpatt_evar _) := 1 ;
    PMPattern_size (pmpatt_svar _) := 1 ;
    PMPattern_size (pmpatt_sym _) := 1 ;
    PMPattern_size (pmpatt_bott) := 1 ;
    PMPattern_size (pmpatt_app ϕ₁ ϕ₂) :=
        S ((PMPattern_size ϕ₁) + (PMPattern_size ϕ₂)) ;
    PMPattern_size (pmpatt_imp ϕ₁ ϕ₂) :=
        S ((PMPattern_size ϕ₁) + (PMPattern_size ϕ₂)) ;
    PMPattern_size (pmpatt_exists _ ϕ') := 
        S (PMPattern_size ϕ') ;
    PMPattern_size (pmpatt_mu _ ϕ') := 
        S (PMPattern_size ϕ') ;
    PMPattern_size (pmpatt_notation _ args _ _) :=
        PMPatt
    .


Check sum_list.
Check vec_to_list.
Fixpoint PMPattern_size
    {Σ : Signature}
    (ϕ : PMPattern)
    : nat :=
    match ϕ with
    | pmpatt_evar _ => 1
    | pmpatt_svar _ => 1
    | pmpatt_sym _ => 1
    | pmpatt_bott => 1
    | pmpatt_app ϕ₁ ϕ₂ =>
        1 + (PMPattern_size ϕ₁) + (PMPattern_size ϕ₂)
    | pmpatt_imp ϕ₁ ϕ₂ =>
        1 + (PMPattern_size ϕ₁) + (PMPattern_size ϕ₂)
    | pmpatt_exists _ ϕ' => 1 + (PMPattern_size ϕ')
    | pmpatt_mu _ ϕ' => 1 + (PMPattern_size ϕ')
    | pmpatt_notation _ args _ _ =>
        1 + sum_list (fmap PMPattern_size (vec_to_list args))
    end
.

Equations Derive NoConfusion for PMPattern.
Equations Derive Subterm for PMPattern.

Check PMPattern_subterm.


    Check insert.

    Print PMPattern_direct_subterm.

    Equations? pmp2ln_aux 
        (ϕ : PMPattern)
    : Pattern by wf ϕ (PMPattern_direct_subterm Σ) :=
    pmp2ln_aux (pmpatt_evar x) := patt_bound_evar 0 ;
    pmp2ln_aux _ := patt_bound_evar 0 .


    Equations? pmp2ln_aux 
        (evm : gmap VarName nat)
        (svm : gmap VarName nat)
        (ϕ : PMPattern)
    : Pattern by wf ϕ PMPattern_subterm :=
    pmp2ln_aux evm svm (pmpatt_evar x) :=
        match evm !! x with
        | Some n => patt_bound_evar n
        | None => patt_free_evar (string2evar x)
        end.


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
            mlc_expand
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


