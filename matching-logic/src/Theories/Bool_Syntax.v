From MatchingLogic Require Export Sorts_Syntax.
Import MatchingLogic.Logic.Notations
       MatchingLogic.Theories.Definedness_Syntax.Notations
       MatchingLogic.Theories.Sorts_Syntax.Notations.

Set Default Proof Mode "Classic".

Inductive Symbols : Set :=
| sBool
| sTrue
| sFalse
| sAnd
| sNeg
| sAndThen.

Global Instance Symbols_eqdec : EqDecision Symbols.
Proof. unfold EqDecision. intros x y. unfold Decision. destruct x; decide equality. (*solve_decision.*) Defined.

#[global]
Program Instance Symbols_finite : finite.Finite Symbols.
Next Obligation.
  exact [sBool; sTrue; sFalse; sAnd; sNeg; sAndThen].
Defined.
Next Obligation.
  unfold Symbols_finite_obligation_1.
  compute_done.
Defined.
Next Obligation.
  destruct x; compute_done.
Defined.

Global Instance Symbols_countable : countable.Countable Symbols.
Proof. apply finite.finite_countable. Defined.

Section bool_syntax.
  Context {Σ : Signature}.

  Class Syntax :=
    { sym_inj : Symbols -> symbols;
      imported_sorts : Sorts_Syntax.Syntax;
    }.

  #[global] Existing Instance imported_definedness.
  #[global] Existing Instance imported_sorts.

  Context {self : Syntax}.

  Definition mlBool     := patt_sym (sym_inj sBool).
  Definition mlTrue     := patt_sym (sym_inj sTrue).
  Definition mlFalse    := patt_sym (sym_inj sFalse).
  Definition mlsBAnd    := patt_sym (sym_inj sAnd).
  Definition mlsBNeg    := patt_sym (sym_inj sNeg).
  Definition mlsBAndThen := patt_sym (sym_inj sAndThen).

  Definition mlBAnd (φ1 φ2 : Pattern) : Pattern :=
    mlsBAnd ⋅ φ1 ⋅ φ2.
  Definition mlBNeg (φ : Pattern) : Pattern :=
    mlsBNeg ⋅ φ.
  Definition mlBAndThen ( φ1 φ2 : Pattern) : Pattern := 
    mlsBAndThen ⋅ φ1 ⋅ φ2.

End bool_syntax.

Section bools.
  Context {Σ : Signature}.
  Context {self : Syntax}.
  Open Scope ml_scope.

  Obligation Tactic := idtac.

  #[global]
  Program Instance Unary_inhabitant_set : Unary mlBNeg := {}.
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

  #[global]
  Program Instance Binary_sorted_neg : Binary mlBAnd := {}.
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
  
  #[global]
  Program Instance Binary_sorted_neg_1 : Binary mlBAndThen := {}.
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

End bools.

Module Notations.
  Notation "phi '&&ml' psi" := (mlBAnd phi psi) (at level 40, left associativity) : ml_scope.
  Notation "'!b' phi" := (mlBNeg phi) (at level 60) : ml_scope.
  Notation "phi 'andThen' psi" := (mlBAndThen phi psi) (at level 40, left associativity) : ml_scope.
End Notations.

Section axioms.
  Import Notations.
  Open Scope ml_scope.
  Context
    {Σ : Signature}
    {syntax : Syntax}.

  Inductive AxiomName := 
  | AxBoolSort
  | AxFunTrue
  | AxFunFalse
  | AxFunAnd
  | AxFunNeg
  | AxNoConfusion
  | AxInductiveDomain
  (* TODO: extend this with the DEFINITION axioms from "ML explained" *)
  | AxDefNegTrue
  | AxDefNegFalse
  | AxDefAndRightTrue
  | AxDefAndRightFalse
  | AxDefAndLeftTrue
  | AxDefAndLeftFalse
  (* extend to support andThen operator   *)
  | AxDefAndThenRightTrue
  | AxDefAndThenRightFalse
  | AxDefAndThenLeftTrue
  | AxDefAndThenLeftFalse
  . 

  Definition axiom (name : AxiomName) : Pattern :=
    match name with
    | AxBoolSort => mlBool ∈ml ⟦Sorts⟧
    | AxFunTrue => ex mlBool , mlTrue =ml b0
    | AxFunFalse => ex mlBool , mlFalse =ml b0
    | AxFunAnd =>
      all mlBool , all mlBool , ex mlBool , b1 &&ml b2 =ml b0
    | AxFunNeg => all mlBool , ex mlBool , !b b1 =ml b0
    | AxNoConfusion => !(mlTrue =ml mlFalse)
    | AxInductiveDomain => ⟦ mlBool ⟧ =ml (mlTrue or mlFalse)

    | AxDefNegTrue =>  !b mlTrue =ml mlFalse
    | AxDefNegFalse => !b mlFalse =ml mlTrue 
    | AxDefAndRightTrue =>  
      all mlBool, b0 &&ml mlTrue =ml b0 
    | AxDefAndRightFalse =>
      all mlBool, b0 &&ml mlFalse =ml mlFalse
    | AxDefAndLeftTrue =>
      all mlBool, mlTrue &&ml b0 =ml b0
    | AxDefAndLeftFalse =>
      all mlBool, mlFalse &&ml b0 =ml mlFalse 

    | AxDefAndThenRightTrue => 
      all mlBool, b0 andThen mlTrue =ml b0
    | AxDefAndThenRightFalse =>
      all, b0 andThen mlFalse =ml mlFalse
    | AxDefAndThenLeftTrue =>
      all mlBool, mlTrue andThen b0 =ml b0
    | AxDefAndThenLeftFalse => 
      all, mlFalse andThen b0 =ml mlFalse
      
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