From stdpp Require Import finite.

From Kore Require Export Semantics.
Export Signature.StringVariables.


Import Syntax.Notations
       Substitution.Notations.

Open Scope kore_scope.

Inductive nat_sorts := bool_s | nat_s.
Inductive nat_symbols := add | is0 | zero | succ | true | false.

#[global]
Instance sorts_eqdec : EqDecision nat_sorts.
Proof.
  solve_decision.
Defined.

#[global]
Program Instance sorts_finite : Finite nat_sorts := {
  enum := [bool_s; nat_s];
}.
Next Obligation.
  compute_done.
Defined.
Next Obligation.
  destruct x; set_solver.
Defined.

#[global]
Instance symbols_eqdec : EqDecision nat_symbols.
Proof.
  solve_decision.
Defined.

#[global]
Program Instance symbols_finite : Finite nat_symbols := {
  enum := [add; is0; zero; succ; true; false];
}.
Next Obligation.
  compute_done.
Defined.
Next Obligation.
  destruct x; set_solver.
Defined.
Inductive Nat_subsort : CRelationClasses.crelation nat_sorts :=.
(* Without "Program", the type-checking fails for some reason *)
Program Instance NatSig : Signature := {|
  sorts := {|
    sort := nat_sorts;
    subsort := Nat_subsort;
  |};
  variables := StringVariables;
  symbols := {|
    symbol := nat_symbols;
    arg_sorts :=
      fun x =>
        match x with
        | add => [nat_s; nat_s]
        | is0 => [nat_s]
        | zero => []
        | succ => [nat_s]
        | true => []
        | false => []
        end;
    ret_sort :=
      fun x =>
        match x with
        | add => nat_s
        | is0 => bool_s
        | zero => nat_s
        | succ => nat_s
        | true => bool_s
        | false => bool_s
        end;
  |};
|}.
Fail Next Obligation.

