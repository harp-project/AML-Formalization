From MatchingLogic Require Export Sorts_Syntax.
Import MatchingLogic.Logic.Notations
       MatchingLogic.Theories.Definedness_Syntax.Notations
       MatchingLogic.Theories.Sorts_Syntax.Notations.

Set Default Proof Mode "Classic".

Inductive Symbols {Σ : Signature} (s1 s2 : Pattern) :=
| ml_prod
| ml_pair
| ml_projL
| ml_projR
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

    Notation "'mlProd' '(' s1 ',' s2 ')'"
        := (patt_sym (inj (ml_prod s1 s2)))
        : ml_scope
    .

     Notation "'mlPair' '{' s1 ',' s2 '}' '(' phi1 ',' phi2 ')'" := 
        (patt_app (patt_app (patt_sym (inj (ml_pair s1 s2))) phi1) phi2)
        : ml_scope
    .
        
    Notation "'(' phi1 '∷' s1 ',' phi2 '∷' s2 ')'" := 
        (patt_app (patt_app (patt_sym (inj (ml_pair s1 s2))) phi1) phi2)
        : ml_scope
    .
    
    Notation "'(' phi ').mlProjL(' s1 ',' s2 ')'" := 
        (patt_app (patt_sym (inj (ml_projL s1 s2))) phi)
        : ml_scope
    .
    
    Notation "'(' phi ').mlProjR(' s1 ',' s2 ')'" := 
        (patt_app (patt_sym (inj (ml_projR s1 s2))) phi)
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
    Delimit Scope ml_scope with ml. (* TODO move this somewhere else *) 



    Inductive AxiomName :=
    | AxPair
    | AxProjLeft
    | AxProjRight
    | AxInj
    | InversePairProja1
    | InversePairProja2
    | InversePairProjb
    .

    Arguments patt_forall_of_sort {Σ self} sort phi%_ml_scope.

    Definition axiom (name : AxiomName) : Pattern :=
    match name with
    
    | AxPair => 
         patt_total_binary_function
            (patt_sym (inj (ml_pair s1 s2)))
            s1
            s2
            (patt_sym (inj (ml_prod s1 s2))) 
          
    | AxProjLeft => 
        all mlProd(s1,s2), ex s1, (b1).mlProjL( s1 , s2 ) =ml b0 
            
    | AxProjRight =>
         all mlProd(s1,s2), ex s2, (b1).mlProjR( s1 , s2 ) =ml b0 
        
    | AxInj => 
        all s1, all s1, all s2, all s2, 
          patt_imp (
                    ( b3 ∷ s1 , b1 ∷ s2 ) =ml ( b2 ∷ s1 , b0 ∷ s2 )%ml
                        ) (
                            patt_and (
                                b3 =ml b2
                            ) (
                                b1 =ml b0
                            )
                        )
                        
    | InversePairProja1 => 
        all s1, all s2,  (( b1 ∷ s1 , b0 ∷ s2 )).mlProjL( s1 , s2 ) =ml b1 
        
    | InversePairProja2 =>
        all s1, all s2,  (( b1 ∷ s1 , b0 ∷ s2 )).mlProjL( s1 , s2 ) =ml b0 
        
    | InversePairProjb =>
        all mlProd(s1,s2), ( (b0).mlProjL( s1 , s2 ) ∷ s1 ,  (b0).mlProjR( s1 , s2 ) ∷ s2 )  =ml  b0
    end.

    Program Definition named_axioms : NamedAxioms :=
    {| NAName := AxiomName;
        NAAxiom := axiom;
    |}.
    Next Obligation.
    destruct name; simpl; wf_auto2.
    Qed.

    Definition theory := Definedness_Syntax.theory ∪
                       theory_of_NamedAxioms named_axioms.

End axioms.