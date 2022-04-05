From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Setoid.
From Coq Require Import Unicode.Utf8.
From Coq.Logic Require Import Classical_Prop FunctionalExtensionality.
From Coq.Classes Require Import Morphisms_Prop.

From stdpp Require Import base sets.

From MatchingLogic Require Import Syntax DerivedOperators Utils.extralibrary.
Require Import MatchingLogic.Theories.Definedness_Syntax.

Import MatchingLogic.Syntax.Notations.
Import MatchingLogic.Syntax.BoundVarSugar.
Import MatchingLogic.IndexManipulation.
Import MatchingLogic.DerivedOperators_Syntax.Notations.


Inductive Symbols := inhabitant.

Instance Symbols_eqdec : EqDecision Symbols.
Proof. unfold EqDecision. intros x y. unfold Decision. destruct x. decide equality. (*solve_decision.*) Defined.

Section sorts.

  Context {Σ : Signature}.

  Class Syntax :=
    { inj : Symbols -> symbols;
      imported_definedness :> Definedness_Syntax.Syntax;
    }.

  Context {self : Syntax}.

  Local Definition sym (s : Symbols) : Pattern :=
    patt_sym (inj s).
  
  Example test_pattern_1 := patt_equal (sym inhabitant) (sym inhabitant).
  Definition patt_inhabitant_set(phi : Pattern) : Pattern := sym inhabitant $ phi.


  Lemma bevar_subst_inhabitant_set ψ (wfcψ : well_formed_closed ψ) x ϕ :
    bevar_subst (patt_inhabitant_set ϕ) ψ x = patt_inhabitant_set (bevar_subst ϕ ψ x).
  Proof. unfold patt_inhabitant_set. simpl_bevar_subst. reflexivity. Qed.
  
  Lemma bsvar_subst_inhabitant_set ψ (wfcψ : well_formed_closed ψ) x ϕ :
    bsvar_subst (patt_inhabitant_set ϕ) ψ x = patt_inhabitant_set (bsvar_subst ϕ ψ x).
  Proof. unfold patt_inhabitant_set. simpl_bsvar_subst. reflexivity. Qed.
  
  #[global]
   Instance Unary_inhabitant_set : Unary patt_inhabitant_set :=
    {| unary_bevar_subst := bevar_subst_inhabitant_set ;
       unary_bsvar_subst := bsvar_subst_inhabitant_set ;
    |}.

  Definition patt_forall_of_sort (sort phi : Pattern) : Pattern :=
    patt_forall ((patt_in (patt_bound_evar 0) (patt_inhabitant_set (nest_ex sort))) ---> phi).

  Definition patt_exists_of_sort (sort phi : Pattern) : Pattern :=
    patt_exists ((patt_in (patt_bound_evar 0) (patt_inhabitant_set (nest_ex sort))) and phi).

  Lemma bevar_subst_forall_of_sort s ψ (wfcψ : well_formed_closed ψ) db ϕ :
    bevar_subst (patt_forall_of_sort s ϕ) ψ db = patt_forall_of_sort (bevar_subst s ψ db) (bevar_subst ϕ ψ (S db)).
  Proof.
    unfold patt_forall_of_sort.
    repeat (rewrite simpl_bevar_subst';[assumption|]).
    simpl. unfold nest_ex. replace (S db) with (db + 1) by lia. rewrite nest_ex_gt; auto. lia.
  Qed.

  Lemma bsvar_subst_forall_of_sort s ψ (wfcψ : well_formed_closed ψ) db ϕ :
    bsvar_subst (patt_forall_of_sort s ϕ) ψ db = patt_forall_of_sort (bsvar_subst s ψ db) (bsvar_subst ϕ ψ db).
  Proof.
    unfold patt_forall_of_sort.
    repeat (rewrite simpl_bsvar_subst';[assumption|]).
    simpl.
    rewrite bsvar_subst_nest_ex_aux_comm.
    { unfold well_formed_closed in wfcψ. destruct_and!. assumption. }
    reflexivity.
  Qed.

  Lemma bevar_subst_exists_of_sort s ψ (wfcψ : well_formed_closed ψ) db ϕ :
    bevar_subst (patt_exists_of_sort s ϕ) ψ db = patt_exists_of_sort (bevar_subst s ψ db) (bevar_subst ϕ ψ (db+1)).
  Proof.
    unfold patt_exists_of_sort.
    repeat (rewrite simpl_bevar_subst';[assumption|]).
    (* TODO rewrite all _+1 to 1+_ *)
    rewrite PeanoNat.Nat.add_comm. simpl.
    unfold nest_ex.
    simpl. unfold nest_ex. replace (S db) with (db + 1) by lia. rewrite nest_ex_gt; auto. lia.
  Qed.

  Lemma bsvar_subst_exists_of_sort s ψ (wfcψ : well_formed_closed ψ) db ϕ :
    bsvar_subst (patt_exists_of_sort s ϕ) ψ db = patt_exists_of_sort (bsvar_subst s ψ db) (bsvar_subst ϕ ψ db).
  Proof.
    unfold patt_exists_of_sort.
    repeat (rewrite simpl_bsvar_subst';[assumption|]).
    simpl.
    rewrite bsvar_subst_nest_ex_aux_comm.
    { unfold well_formed_closed in wfcψ. destruct_and!. assumption. }
    reflexivity.
  Qed.
    
  #[global]
   Instance EBinder_forall_of_sort s : EBinder (patt_forall_of_sort s) _ _:=
    {|
    ebinder_bevar_subst := bevar_subst_forall_of_sort s ;
    ebinder_bsvar_subst := bsvar_subst_forall_of_sort s ;
    |}.

  #[global]
   Instance EBinder_exists_of_sort s : EBinder (patt_exists_of_sort s) _ _:=
    {|
    ebinder_bevar_subst := bevar_subst_exists_of_sort s ;
    ebinder_bsvar_subst := bsvar_subst_exists_of_sort s ;
    |}.
  
  (* TODO patt_forall_of_sort and patt_exists_of_sorts are duals - a lemma *)

  (* TODO a lemma about patt_forall_of_sort *)
  
  Definition patt_total_function(phi from to : Pattern) : Pattern :=
    patt_forall_of_sort from (patt_exists_of_sort (nest_ex to) (patt_equal (patt_app (nest_ex (nest_ex phi)) b1) b0)).

  Definition patt_partial_function(phi from to : Pattern) : Pattern :=
    patt_forall_of_sort from (patt_exists_of_sort (nest_ex to) (patt_subseteq (patt_app (nest_ex (nest_ex phi)) b1) b0)).


  (* Assuming `f` is a total function, says it is injective on given domain. Does not quite work for partial functions. *)
  Definition patt_total_function_injective f from : Pattern :=
    patt_forall_of_sort from (patt_forall_of_sort (nest_ex from) (patt_imp (patt_equal (patt_app (nest_ex (nest_ex f)) b1) (patt_app (nest_ex (nest_ex f)) b0)) (patt_equal b1 b0))).

  (* Assuming `f` is a partial function, says it is injective on given domain. Works for total functions, too. *)
  Definition patt_partial_function_injective f from : Pattern :=
    patt_forall_of_sort
      from
      (patt_forall_of_sort
         (nest_ex from)
         (patt_imp
            (patt_not (patt_equal (patt_app (nest_ex (nest_ex f)) b1) patt_bott ))
            (patt_imp (patt_equal (patt_app (nest_ex (nest_ex f)) b1) (patt_app (nest_ex (nest_ex f)) b0)) (patt_equal b1 b0)))).
  
End sorts.