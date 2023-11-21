From Coq Require Import ssreflect ssrfun ssrbool.

Require Import Setoid.
From Coq Require Import Unicode.Utf8.
From Coq.Logic Require Import Classical_Prop FunctionalExtensionality.
From Coq.Classes Require Import Morphisms_Prop.

From stdpp Require Import base sets.

From MatchingLogic Require Export Logic.
Import MatchingLogic.Logic.Notations.
Require Export MatchingLogic.Theories.Definedness_Syntax.

Import MatchingLogic.Theories.Definedness_Syntax.Notations.
Import BoundVarSugar.

Inductive Symbols := inhabitant.

Global Instance Symbols_eqdec : EqDecision Symbols.
Proof. unfold EqDecision. intros x y. unfold Decision. destruct x. decide equality. (*solve_decision.*) Defined.

Section sorts_syntax.
  Open Scope ml_scope.
  Context {Σ : Signature}.

  Class Syntax :=
    { inj : Symbols -> symbols;
      imported_definedness : Definedness_Syntax.Syntax;
    }.
  
  #[global] Existing Instance imported_definedness.

  Context {self : Syntax}.

  Local Definition sym (s : Symbols) : Pattern :=
    patt_sym (inj s).

  Example test_pattern_1 := patt_equal (sym inhabitant) (sym inhabitant).
  Definition patt_inhabitant_set(phi : Pattern) : Pattern := sym inhabitant $ phi.

  Definition patt_element_of (φ ψ : Pattern) := ⌈ φ and ψ ⌉.

End sorts_syntax.

Section sorts.
  Context {Σ : Signature}.
  Context {self : Syntax}.
  Open Scope ml_scope.
  Local Notation "〚 phi 〛" := (patt_inhabitant_set phi) (at level 0) : ml_scope.

  Obligation Tactic := idtac.

  #[global]
  Program Instance Unary_inhabitant_set : Unary patt_inhabitant_set := {}.
  Next Obligation.
    intros. repeat rewrite pm_correctness. reflexivity.
  Defined.
  Next Obligation.
    wf_auto2.
  Qed.
  Next Obligation.
    wf_auto2.
  Qed.
  Next Obligation.
    wf_auto2.
  Qed.

  Definition patt_sorted_neg (sort phi : Pattern) : Pattern :=
    〚sort〛 and ! phi.

  #[global]
  Program Instance Binary_sorted_neg : Binary patt_sorted_neg := {}.
  Next Obligation.
    intros. repeat rewrite pm_correctness. reflexivity.
  Defined.
  Next Obligation.
    intros. wf_auto2.
  Qed.
  Next Obligation.
    intros. wf_auto2.
  Qed.
  Next Obligation.
    intros. wf_auto2.
  Qed.

  Definition patt_exists_of_sort (sort phi : Pattern) : Pattern :=
    ex , ((b0 ∈ml 〚nest_ex sort〛) and phi).
  Local Notation "'ex' s ,  phi" := 
    (patt_exists_of_sort s phi) (at level 70) : ml_scope.

  #[global]
  Program Instance sorted_exists_binder : ESortedBinder patt_exists_of_sort nest_ex := {}.
  Next Obligation.
    intros.
    repeat rewrite pm_correctness.
    cbn.
    rewrite (@eswap _ _ _ nest_ex _ f_swap).
    replace (on_bevar pm_spec_data (increase_ex pm_spec_data a) 0) with b0. reflexivity.
    now rewrite pm_ezero_increase.
  Defined.

  Definition patt_forall_of_sort (sort phi : Pattern) : Pattern :=
    all , ((b0 ∈ml 〚nest_ex sort〛) ---> phi).

  Local Notation "'all' s ,  phi" := 
    (patt_forall_of_sort s phi) (at level 70) : ml_scope.

  #[global]
  Program Instance sorted_forall_binder : ESortedBinder patt_forall_of_sort nest_ex := {}.
  Next Obligation.
    intros.
    repeat rewrite pm_correctness.
    cbn.
    rewrite (@eswap _ _ _ nest_ex _ f_swap).
    replace (on_bevar pm_spec_data (increase_ex pm_spec_data a) 0) with b0. reflexivity.
    now rewrite pm_ezero_increase.
  Defined.

  (* TODO patt_forall_of_sort and patt_exists_of_sort are duals - a lemma *)

  (* TODO a lemma about patt_forall_of_sort *)

  Definition patt_total_function(phi from to : Pattern) : Pattern :=
    all from , (ex (nest_ex to) , ((nest_ex (nest_ex phi) $ b1) =ml b0)).

  Definition patt_partial_function(phi from to : Pattern) : Pattern :=
    all from , (ex (nest_ex to), ((nest_ex (nest_ex phi) $ b1) ⊆ml b0)).


  (* Assuming `f` is a total function, says it is injective on given domain. Does not quite work for partial functions. *)
  Definition patt_total_function_injective f from : Pattern :=
    all from , (all (nest_ex from) , 
                (((nest_ex (nest_ex f) $ b1) =ml (nest_ex (nest_ex f) $ b0)) ---> 
                  (b1 =ml b0))).

  (* Assuming `f` is a partial function, says it is injective on given domain. Works for total functions, too. *)
  Definition patt_partial_function_injective f from : Pattern :=
    all
      from ,
      (all
         (nest_ex from) ,
         (
            ! ((nest_ex (nest_ex f) $ b1) =ml ⊥ )
            --->
            ((nest_ex (nest_ex f) $ b1) =ml (nest_ex (nest_ex f) $ b0))
             ---> (b1 =ml b0))).

End sorts.

Section sorts.
  Context {Σ : Signature}.
  Context {self : Syntax}.
  Open Scope ml_scope.

  Definition patt_total_binary_function(phi from1 from2 to : Pattern)
  : Pattern :=
    patt_forall_of_sort from1 (
      patt_forall_of_sort (nest_ex from2) (
        patt_exists_of_sort (nest_ex (nest_ex to)) (
          (((nest_ex (nest_ex (nest_ex phi)) $ b2) $ b1) =ml b0)
        )
      )
    )
  .
End sorts.

Module Notations.
  Notation "〚 phi 〛" := (patt_inhabitant_set phi) (at level 0) : ml_scope.
  Notation "'all' s ,  phi" := (patt_forall_of_sort s phi) (at level 80) : ml_scope.
  Notation "'ex' s ,  phi" := (patt_exists_of_sort s phi) (at level 80) : ml_scope.
  Notation "phi :ml s1 × s2 -> s3" :=  (patt_total_binary_function phi s1 s2 s3) (at level 70) : ml_scope.
End Notations.

