From MatchingLogic Require Export Sorts_Syntax.
Import MatchingLogic.Logic.Notations
       MatchingLogic.Theories.Definedness_Syntax.Notations
       MatchingLogic.Theories.Sorts_Syntax.Notations.

Set Default Proof Mode "Classic".

Section nat_syntax.

  Context {Σ : Signature}.

  Inductive Symbols := sNat | sZero | sSucc | sAddNat.
  
  Global Instance Symbols_eqdec : EqDecision Symbols.
  Proof. unfold EqDecision. intros x y. unfold Decision. destruct x; decide equality. (*solve_decision.*)    
  Defined.

  Class Syntax :=
    { sym_inj : Symbols -> symbols;
      imported_sorts : Sorts_Syntax.Syntax;
    }.

  #[global] Existing Instance imported_sorts.

  Context {self : Syntax}.

  Definition Nat := patt_sym (sym_inj sNat).
  Definition Zero := patt_sym (sym_inj sZero).
  Definition Succ := patt_sym (sym_inj sSucc).
  Definition AddNat := patt_sym (sym_inj sAddNat).
  
  Definition mlAddNat (φ1 φ2 : Pattern) : Pattern :=
    AddNat ⋅ φ1 ⋅ φ2 .

End nat_syntax.

Section nat.
  Context {Σ : Signature}.
  Context {self : Syntax}.
  Open Scope ml_scope.

  Obligation Tactic := idtac.

  #[global]
  Program Instance Binary_sorted_add : Binary mlAddNat := {}.
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

End nat.

Module Notations.
  Notation "phi '+ml' psi" := (mlAddNat phi psi) (at level 40, left associativity) : ml_scope.
End Notations.

Section axioms.
  Import Notations.
  Context
    {Σ : Signature}
    {syntax : Syntax}
  .

  Inductive AxiomName := 
  | AxNatSort
  | AxFun1
  | AxFun2
  | AxNoConfusion1
  | AxNoConfusion2
  | AxInductiveDomain
  (* extend the axioms in spec for addition operator   *)
  | AxFunAdd
  | AxDefAddId
  | AxDefAdd.
  
  Definition axiom (name : AxiomName) : Pattern :=
    match name with
    | AxNatSort => Nat ∈ Sorts
    | AxFun1 => ex Nat , Zero =ml b0
    | AxFun2 => all Nat, ex Nat, Succ ⋅ b1 =ml b0
    | AxNoConfusion1 => all Nat, !(Zero =ml Succ ⋅ b0)
    | AxNoConfusion2 => all Nat, all Nat, (Succ ⋅ b1 =ml Succ ⋅ b0 ---> b1 =ml b0)
    | AxInductiveDomain => 〚 Nat 〛 =ml mu , Zero or Succ ⋅ B0
    (* extend to support addition operator*)
    | AxFunAdd =>
      all Nat, all Nat, ex Nat, b1 +ml b2 =ml b0
     
    | AxDefAddId =>
      all Nat, b0 +ml Zero =ml b0

    | AxDefAdd =>
      all Nat, all Nat, b0 +ml (Succ ⋅ b1)  =ml Succ ⋅ (b0 +ml b1)   
    end.

  Program Definition named_axioms : NamedAxioms :=
    {|
      NAName := AxiomName;
      NAAxiom := axiom;
    |}.
  Next Obligation.
    destruct name; simpl; wf_auto2.
  Qed.

  Definition theory := Definedness_Syntax.theory ∪ theory_of_NamedAxioms named_axioms.

End axioms.
