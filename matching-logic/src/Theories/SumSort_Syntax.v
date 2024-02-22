From Coq Require Import ssreflect ssrfun ssrbool.

From Coq Require Import Unicode.Utf8.
From stdpp Require Import base sets.

From MatchingLogic Require Import
    Logic
    Theories.Sorts_Syntax
.


Require Import Setoid.
From Coq.Logic Require Import Classical_Prop FunctionalExtensionality.
From Coq.Classes Require Import Morphisms_Prop.
Import BoundVarSugar.
Import Definedness_Syntax.Notations.
Import Sorts_Syntax.Notations.


Open Scope ml_scope.

Inductive Symbols {Σ : Signature} (s1 s2 : Pattern) :=
| ml_sum
| ml_injectL
| ml_injectR
| ml_ejectL
| ml_ejectR
.

#[global]
Instance Symbols_eqdec {Σ : Signature} s1 s2 : EqDecision (Symbols s1 s2).
Proof. solve_decision. Defined.

Class Syntax {Σ : Signature} (s1 s2 : Pattern) :=
{
    imported_sorts : Sorts_Syntax.Syntax;
    inj: Symbols s1 s2 -> symbols;
    inj_inj: Inj (=) (=) inj;
}.

#[global] Existing Instance imported_sorts.
#[global] Existing Instance inj_inj.

Module Notations.


    Notation "'mlSum' '(' s1 ',' s2 ')'"
        := (patt_sym (inj (ml_sum s1 s2)))
        : ml_scope
    .

    Notation "'mlInjectL' '(' s1 ',' s2 ')' '(' phi ')'" := 
        (patt_app (patt_sym (inj (ml_injectL s1 s2))) phi)
        : ml_scope
    .

    Notation "'mlInjectR' '(' s1 ',' s2 ')' '(' phi ')'" := 
        (patt_app (patt_sym (inj (ml_injectR s1 s2))) phi)
        : ml_scope
    .
    
    Notation "'mlEjectL' '(' s1 ',' s2 ')' '(' phi ')'" := 
        (patt_app (patt_sym (inj (ml_ejectL s1 s2))) phi)
        : ml_scope
    .

    Notation "'mlEjectR' '(' s1 ',' s2 ')' '(' phi ')'" := 
        (patt_app (patt_sym (inj (ml_ejectR s1 s2))) phi)
        : ml_scope
    .

End Notations.


Section axioms.
    Context
      {Σ : Signature}
      (s1 s2 : Pattern)
      (wfs1 : well_formed s1 = true)
      (wfs2 : well_formed s2 = true)
      {syntax : Syntax s1 s2}
    .
Import Notations.
Open Scope ml_scope.
 (* Open Scope ml_scope.
Delimit Scope ml_scope with ml. (* TODO move this somewhere else *) *)

    (* Local Notation "'(' phi1 ',ml' phi2 ')'" := 
        (patt_app (patt_app (patt_sym (inj (ml_pair s1 s2))) phi1) phi2)
        : ml_scope
    . *)

    Local Notation "'(' phi ').mlInjectL'" := 
        (patt_app (patt_sym (inj (ml_injectL s1 s2))) phi)
        : ml_scope
    .

    Local Notation "'(' phi ').mlInjectR'" := 
        (patt_app (patt_sym (inj (ml_injectR s1 s2))) phi)
        : ml_scope
    .
    
    Local Notation "'(' phi ').mlEjectL'" := 
        (patt_app (patt_sym (inj (ml_ejectL s1 s2))) phi)
        : ml_scope
    .
    
    Local Notation "'(' phi ').mlEjectR'" := 
        (patt_app (patt_sym (inj (ml_ejectR s1 s2))) phi)
        : ml_scope
    .



  Inductive AxiomName :=
    | AxInjectLeft
    | AxInjectRight
    
    | AxEjectLeft
    | AxEjectRight 
    
    | AxInverseInja1
    | AxInverseInja2
    
    | AxInverseInjb1
    | AxInverseInjb2
    
    | AxCoProduct
    .

    (* Arguments patt_forall_of_sort {Σ self} sort phi%ml_scope. *)

    Definition axiom (name : AxiomName) : Pattern :=
    match name with
    
    | AxInjectLeft =>
      all s1, ex mlSum (s1,s2) , (b1).mlInjectL =ml b0
      (* patt_forall_of_sort s1 (
        patt_exists_of_sort ( mlSum (s1,s2) ) (
        
          (b1).mlInjectL =ml b0
        
        )
      )  *)
        
    | AxInjectRight =>
      all s2, ex mlSum (s1,s2) , (b1).mlInjectR =ml b0 
      (* patt_forall_of_sort s2 (
        patt_exists_of_sort ( mlSum (s1,s2) ) (
        
          (b1).mlInjectR =ml b0
        )
      )  *)
    
    
    | AxEjectLeft =>
      all mlSum (s1,s2), ex s1 , (b1).mlEjectL ⊆ml b0
      (* patt_forall_of_sort ( mlSum (s1,s2) ) (
        patt_exists_of_sort s1 (
        
          (b1).mlEjectL ⊆ml b0
        
        )
      )  *)
        
    | AxEjectRight =>
      all mlSum (s1,s2), ex s2, (b1).mlEjectL ⊆ml b0
      (* patt_forall_of_sort ( mlSum (s1,s2) ) (
        patt_exists_of_sort s2 (
          
          (b1).mlEjectL ⊆ml b0
        
        )
      ) *)
        
        
    | AxInverseInja1 =>
       all s1, ( (b0).mlInjectL ).mlEjectL =ml b0
      (* patt_forall_of_sort s1 (
        ( (b0).mlInjectL ).mlEjectL =ml b0 ) 
       *)  
       
    | AxInverseInja2 =>
      all s2, ( (b0).mlInjectR ).mlEjectR =ml b0
      (* patt_forall_of_sort s2 ( 
        ( (b0).mlInjectR ).mlEjectR =ml b0 )
 *)    
    
    | AxInverseInjb1 =>
      all s2, ( (b0).mlInjectR ).mlEjectL =ml patt_bott 
      (* patt_forall_of_sort s2 (
        ( (b0).mlInjectR ).mlEjectL =ml patt_bott ) *)
        
    | AxInverseInjb2 =>
      all s1, ( (b0).mlInjectL ).mlEjectR =ml patt_bott 
      (* patt_forall_of_sort s1 (
        ( (b0).mlInjectL ).mlEjectR =ml patt_bott ) *)
    
    
    | AxCoProduct => 
       〚 mlSum (s1, s2) 〛  ⊆ml  patt_or ( (〚s1〛).mlInjectL )  ( (〚s2〛).mlInjectR ) 
      
(*       mlSum (s1, s2)   ⊆ml  patt_or ( (s1).mlInjectL )  ( (s2).mlInjectR )  *)
     
    end.

    Program Definition named_axioms : NamedAxioms :=
    {| NAName := AxiomName;
        NAAxiom := axiom;
    |}.
    Next Obligation.
    destruct name; simpl; wf_auto2.
    Qed.

    (* Definition Γprod := theory_of_NamedAxioms named_axioms. *)
    Definition theory := Definedness_Syntax.theory ∪
                       theory_of_NamedAxioms named_axioms.


End axioms.