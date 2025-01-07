From MatchingLogic Require Export Sorts_Syntax.
Import MatchingLogic.Logic.Notations
       MatchingLogic.Theories.Definedness_Syntax.Notations
       MatchingLogic.Theories.Sorts_Syntax.Notations.

Set Default Proof Mode "Classic".

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
    sym_inj: Symbols s1 s2 -> symbols;
    inj_inj: Inj (=) (=) sym_inj;
}.

#[global] Existing Instance imported_sorts.
#[global] Existing Instance inj_inj.

Module Notations.


    Notation "'mlSum' '(' s1 ',' s2 ')'" := 
        (patt_sym (sym_inj (ml_sum s1 s2)))
        : ml_scope
    .

    Notation "'(' phi ').mlInjectL(' s1 ',' s2 ')'" := 
        (patt_app (patt_sym (sym_inj (ml_injectL s1 s2))) phi)
        : ml_scope
    .

    Notation "'(' phi ').mlInjectR(' s1 ',' s2 ')'" := 
        (patt_app (patt_sym (sym_inj (ml_injectR s1 s2))) phi)
        : ml_scope
    .

    Notation "'(' phi ').mlEjectL(' s1 ',' s2 ')'" := 
        (patt_app (patt_sym (sym_inj (ml_ejectL s1 s2))) phi)
        : ml_scope
    .
    
    Notation "'(' phi ').mlEjectR(' s1 ',' s2 ')'" := 
        (patt_app (patt_sym (sym_inj (ml_ejectR s1 s2))) phi)
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


  Inductive AxiomName :=
    | AxSumSort
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

    Definition axiom (name : AxiomName) : Pattern :=
    match name with
    | AxSumSort =>
       s1 ∈ml Sorts ---> s2 ∈ml Sorts ---> mlSum (s1, s2) ∈ml Sorts
    | AxInjectLeft =>
        all s1, ex mlSum (s1,s2) , (b1).mlInjectL( s1 , s2 ) =ml b0
        
    | AxInjectRight =>
        all s2, ex mlSum (s1,s2) , (b1).mlInjectR( s1 , s2 ) =ml b0 
    
    | AxEjectLeft =>
        all mlSum (s1,s2), ex s1 , (b1).mlEjectL( s1 , s2 ) ⊆ml b0
        
    | AxEjectRight =>
        all mlSum (s1,s2), ex s2, (b1).mlEjectL( s1 , s2 ) ⊆ml b0
        
    | AxInverseInja1 =>
        all s1, ( (b0).mlInjectL( s1 , s2 ) ).mlEjectL( s1 , s2 ) =ml b0
        
    | AxInverseInja2 =>
        all s2, ( (b0).mlInjectR( s1 , s2 ) ).mlEjectR( s1 , s2 ) =ml b0
      
    | AxInverseInjb1 =>
        all s2, ( (b0).mlInjectR( s1 , s2 ) ).mlEjectL( s1 , s2 ) =ml patt_bott 
       
    | AxInverseInjb2 =>
        all s1, ( (b0).mlInjectL( s1 , s2 ) ).mlEjectR( s1 , s2 ) =ml patt_bott 
      
    | AxCoProduct => 
        〚 mlSum (s1, s2) 〛  ⊆ml  patt_or ( (〚s1〛).mlInjectL( s1 , s2 ) )  ( (〚s2〛).mlInjectR( s1 , s2 ) ) 
    end.

  Program Definition named_axioms : NamedAxioms :=
    {| 
      NAName := AxiomName;
      NAAxiom := axiom;
    |}.
  Next Obligation.
    destruct name; simpl; wf_auto2.
  Qed.

  Definition theory := Definedness_Syntax.theory ∪
                       theory_of_NamedAxioms named_axioms.

End axioms.