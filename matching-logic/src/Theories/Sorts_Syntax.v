From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Setoid.
From Coq Require Import Unicode.Utf8.
From Coq.Logic Require Import Classical_Prop FunctionalExtensionality.
From Coq.Classes Require Import Morphisms_Prop.

From stdpp Require Import base sets.

From MatchingLogic Require Import Syntax DerivedOperators_Syntax Utils.extralibrary wftactics.
Require Import MatchingLogic.Theories.Definedness_Syntax.

Import MatchingLogic.Syntax.Notations.
Import MatchingLogic.Substitution.Notations.
Import MatchingLogic.Syntax.BoundVarSugar.
Import MatchingLogic.IndexManipulation.
Import MatchingLogic.DerivedOperators_Syntax.Notations.
Import MatchingLogic.Theories.Definedness_Syntax.Notations.


Inductive Symbols := inhabitant.

Instance Symbols_eqdec : EqDecision Symbols.
Proof. unfold EqDecision. intros x y. unfold Decision. destruct x. decide equality. (*solve_decision.*) Defined.

Section sorts_syntax.

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

  Definition patt_element_of (φ ψ : Pattern) := ⌈ φ and ψ ⌉.

End sorts_syntax.

Section sorts.
  Context {Σ : Signature}.
  Context {self : Syntax}.
  Local Notation "〚 phi 〛" := (patt_inhabitant_set phi) (at level 0) : ml_scope.
  Lemma bevar_subst_inhabitant_set ψ (wfcψ : well_formed_closed ψ) x ϕ :
    〚ϕ〛.[evar: x ↦ ψ] = 〚ϕ.[evar: x ↦ ψ]〛.
  Proof. unfold patt_inhabitant_set. simpl_bevar_subst. reflexivity. Qed.

  Lemma bsvar_subst_inhabitant_set ψ (wfcψ : well_formed_closed ψ) X ϕ :
    〚ϕ〛.[svar: X ↦ ψ] = 〚ϕ.[svar: X ↦ ψ]〛.
  Proof. unfold patt_inhabitant_set. simpl_bsvar_subst. reflexivity. Qed.

  #[global]
   Instance Unary_inhabitant_set : Unary patt_inhabitant_set :=
    {| unary_bevar_subst := bevar_subst_inhabitant_set ;
       unary_bsvar_subst := bsvar_subst_inhabitant_set ;
       unary_wf := ltac:(wf_auto2) ;
       unary_free_evar_subst := ltac:(reflexivity) ;
       unary_free_svar_subst := ltac:(reflexivity) ;
       unary_evar_quantify := ltac:(reflexivity) ;
       unary_svar_quantify := ltac:(reflexivity) ;
    |}.

  Definition patt_sorted_neg (sort phi : Pattern) : Pattern :=
    〚sort〛 and ! phi.

  Lemma bevar_subst_sorted_neg ψ (wfcψ : well_formed_closed ψ) x s ϕ :
    bevar_subst (patt_sorted_neg s ϕ) ψ x = patt_sorted_neg (bevar_subst s ψ x) (bevar_subst ϕ ψ x).
  Proof. unfold patt_sorted_neg. simpl_bevar_subst. reflexivity. Qed.

  Lemma bsvar_subst_sorted_neg ψ (wfcψ : well_formed_closed ψ) x s ϕ :
    bsvar_subst (patt_sorted_neg s ϕ) ψ x = patt_sorted_neg (bsvar_subst s ψ x) (bsvar_subst ϕ ψ x).
  Proof. unfold patt_sorted_neg.
    simpl_bsvar_subst.
    reflexivity.
  Qed.

  #[global]
   Instance Binary_sorted_neg : Binary patt_sorted_neg :=
    {| binary_bevar_subst := bevar_subst_sorted_neg ;
       binary_bsvar_subst := bsvar_subst_sorted_neg ;
       binary_wf := ltac:(wf_auto2) ;
       binary_free_evar_subst := ltac:(reflexivity) ;
       binary_free_svar_subst := ltac:(reflexivity) ;
       binary_evar_quantify := ltac:(reflexivity) ;
       binary_svar_quantify := ltac:(reflexivity) ;
    |}.

  Definition patt_forall_of_sort (sort phi : Pattern) : Pattern :=
    all , ((b0 ∈ml 〚nest_ex sort〛) ---> phi).

  Local Notation "'all' s ,  phi" := 
    (patt_forall_of_sort s phi) (at level 70) : ml_scope.

  Definition patt_exists_of_sort (sort phi : Pattern) : Pattern :=
    ex , ((patt_bound_evar 0 ∈ml 〚nest_ex sort〛) and phi).
  Local Notation "'ex' s ,  phi" := 
    (patt_exists_of_sort s phi) (at level 70) : ml_scope.

  Lemma bevar_subst_forall_of_sort s ψ (wfcψ : well_formed_closed ψ) db ϕ :
    (all s , ϕ).[evar: db ↦ ψ] = all s.[evar: db ↦ ψ] , ϕ.[evar: S db ↦ ψ].
  Proof.
    unfold patt_forall_of_sort.
    repeat (rewrite simpl_bevar_subst';[assumption|]).
    simpl. unfold nest_ex. replace (S db) with (db + 1) by lia. rewrite nest_ex_gt; auto. lia.
  Qed.

  Lemma bsvar_subst_forall_of_sort s ψ (wfcψ : well_formed_closed ψ) db ϕ :
    (all s , ϕ).[svar: db ↦ ψ] = all s.[svar: db ↦ ψ] , ϕ.[svar: db ↦ ψ].
  Proof.
    unfold patt_forall_of_sort.
    repeat (rewrite simpl_bsvar_subst';[assumption|]).
    simpl.
    rewrite bsvar_subst_nest_ex_aux_comm.
    { unfold well_formed_closed in wfcψ. destruct_and!. assumption. }
    reflexivity.
  Qed.

  Lemma free_evar_subst_forall_of_sort s ψ x ϕ :
    well_formed_closed ψ ->
    free_evar_subst (all s , ϕ) ψ x = all (free_evar_subst s ψ x) , (free_evar_subst ϕ ψ x).
  Proof.
    intro Hwf.
    unfold patt_forall_of_sort.
    mlSimpl. rewrite nest_ex_free_evar_subst. wf_auto2. done.
  Qed.

  Lemma free_svar_subst_forall_of_sort s ψ x ϕ :
    well_formed_closed ψ ->
    free_svar_subst (all s , ϕ) ψ x = all (free_svar_subst s ψ x) , (free_svar_subst ϕ ψ x).
  Proof.
    intro Hwf.
    unfold patt_forall_of_sort.
    mlSimpl. rewrite nest_ex_free_svar_subst. wf_auto2. done.
  Qed.

  Lemma evar_quantify_forall_of_sort s db x ϕ :
    evar_quantify x db (all s , ϕ) = all (evar_quantify x db s) , (evar_quantify x (S db) ϕ).
  Proof.
    unfold patt_forall_of_sort.
    repeat (rewrite simpl_bevar_subst';[assumption|]).
    unfold nest_ex.
    simpl. unfold nest_ex. replace (S db) with (db + 1) by lia.
    rewrite nest_ex_gt_evar_quantify; auto. lia.
  Qed.

  Lemma svar_quantify_forall_of_sort s db X ϕ :
    svar_quantify X db (all s , ϕ) = all (svar_quantify X db s) , (svar_quantify X db ϕ).
  Proof.
    unfold patt_exists_of_sort.
    repeat (rewrite simpl_bevar_subst';[assumption|]).
    unfold nest_ex.
    simpl. unfold nest_ex. replace (S db) with (db + 1) by lia.
    rewrite nest_ex_svar_quantify; auto.
  Qed.

  #[global]
   Instance Binder_forall_of_sort s : Binder (patt_forall_of_sort s) _ _ _ _ _ _ :=
    {|
       binder_bevar_subst := bevar_subst_forall_of_sort s ;
       binder_bsvar_subst := bsvar_subst_forall_of_sort s ;
       binder_free_evar_subst := free_evar_subst_forall_of_sort s ;
       binder_free_svar_subst := free_svar_subst_forall_of_sort s ;
       binder_evar_quantify := evar_quantify_forall_of_sort s ;
       binder_svar_quantify := svar_quantify_forall_of_sort s ;
    |}.

  Lemma bevar_subst_exists_of_sort s ψ (wfcψ : well_formed_closed ψ) db ϕ :
    (ex s , ϕ).[evar: db ↦ ψ] = ex s.[evar: db ↦ ψ] , ϕ.[evar: S db ↦ ψ].
  Proof.
    unfold patt_exists_of_sort.
    repeat (rewrite simpl_bevar_subst';[assumption|]).
    unfold nest_ex.
    simpl. unfold nest_ex. replace (S db) with (db + 1) by lia.
    rewrite nest_ex_gt; auto. lia.
  Qed.

  Lemma bsvar_subst_exists_of_sort s ψ (wfcψ : well_formed_closed ψ) db ϕ :
    (ex s , ϕ).[svar: db ↦ ψ] = ex s.[svar: db ↦ ψ] , ϕ.[svar: db ↦ ψ].
  Proof.
    unfold patt_exists_of_sort.
    repeat (rewrite simpl_bsvar_subst';[assumption|]).
    simpl.
    rewrite bsvar_subst_nest_ex_aux_comm.
    { unfold well_formed_closed in wfcψ. destruct_and!. assumption. }
    reflexivity.
  Qed.

  Lemma free_evar_subst_exists_of_sort s ψ x ϕ :
    well_formed_closed ψ ->
    free_evar_subst (ex s , ϕ) ψ x = ex (free_evar_subst s ψ x) , (free_evar_subst ϕ ψ x).
  Proof.
    intro Hwf.
    unfold patt_exists_of_sort.
    mlSimpl. rewrite nest_ex_free_evar_subst. wf_auto2. done.
  Qed.

  Lemma free_svar_subst_exists_of_sort s ψ x ϕ :
    well_formed_closed ψ ->
    free_svar_subst (ex s , ϕ) ψ x = ex (free_svar_subst s ψ x) , (free_svar_subst ϕ ψ x).
  Proof.
    intro Hwf.
    unfold patt_exists_of_sort.
    mlSimpl. rewrite nest_ex_free_svar_subst. wf_auto2. done.
  Qed.

  Lemma evar_quantify_exists_of_sort s db x ϕ :
    evar_quantify x db (ex s , ϕ) = ex (evar_quantify x db s) , (evar_quantify x (S db) ϕ).
  Proof.
    unfold patt_exists_of_sort.
    repeat (rewrite simpl_bevar_subst';[assumption|]).
    unfold nest_ex.
    simpl. unfold nest_ex. replace (S db) with (db + 1) by lia.
    rewrite nest_ex_gt_evar_quantify; auto. lia.
  Qed.

  Lemma svar_quantify_exists_of_sort s db X ϕ :
    svar_quantify X db (ex s , ϕ) = ex (svar_quantify X db s) , (svar_quantify X db ϕ).
  Proof.
    unfold patt_exists_of_sort.
    repeat (rewrite simpl_bevar_subst';[assumption|]).
    unfold nest_ex.
    simpl. unfold nest_ex. replace (S db) with (db + 1) by lia.
    rewrite nest_ex_svar_quantify; auto.
  Qed.

  #[global]
   Instance Binder_exists_of_sort s : Binder (patt_exists_of_sort s) _ _ _ _ _ _ :=
    {|
       binder_bevar_subst := bevar_subst_exists_of_sort s ;
       binder_bsvar_subst := bsvar_subst_exists_of_sort s ;
       binder_free_evar_subst := free_evar_subst_exists_of_sort s ;
       binder_free_svar_subst := free_svar_subst_exists_of_sort s ;
       binder_evar_quantify := evar_quantify_exists_of_sort s ;
       binder_svar_quantify := svar_quantify_exists_of_sort s ;
    |}.
  
  (* TODO patt_forall_of_sort and patt_exists_of_sorts are duals - a lemma *)

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

Module Notations.
  Notation "〚 phi 〛" := (patt_inhabitant_set phi) (at level 0) : ml_scope.
  Notation "'all' s ,  phi" := (patt_forall_of_sort s phi) (at level 70) : ml_scope.
  Notation "'ex' s ,  phi" := (patt_exists_of_sort s phi) (at level 70) : ml_scope.
End Notations.