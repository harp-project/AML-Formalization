Require Import locally_nameless.
Require Import ML.Signature.
Require Import Coq.Logic.Classical_Prop.
Import MLNotations.
Import ML.Signature.
Require Import Theories.Definedness.

Section sorts.

  Inductive Symbols := inhabitant.

  Context {sig : Signature}.

  Class Syntax :=
    { inj: Symbols -> (symbols sig);
      imported_definedness: @Definedness.Syntax sig;
    }.

  Context {self : Syntax}.

  Existing Instance imported_definedness.

  Let sym (s : Symbols) : @Pattern sig :=
    @patt_sym sig (inj s).
  
  Example test_pattern_1 := patt_equal (sym inhabitant) (sym inhabitant).
  Definition inhabitant_set(phi : Pattern) : Pattern := sym inhabitant $ phi.

  Definition patt_forall_of_sort (sort phi : Pattern) : Pattern :=
    patt_forall ((patt_in (patt_bound_evar 0) (inhabitant_set sort)) --> phi).

  Definition patt_exists_of_sort (sort phi : Pattern) : Pattern :=
    patt_exists ((patt_in (patt_bound_evar 0) (inhabitant_set sort)) and phi).

End sorts.
