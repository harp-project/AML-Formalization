From MatchingLogic Require Export stdpp_ext.
From Kore Require Export Semantics.
Import Signature.StringVariables.
Import Kore.Syntax.Notations.
 
From Coq Require Import ZArith.
 
Open Scope kore_scope.
Open Scope string_scope.
Open Scope hlist_scope.
 
Module TheorySyntax.
 
  Inductive Ksorts :=
  | Kbool
  .
 
 
  Instance Ksorts_eq_dec : EqDecision Ksorts.
  Proof. solve_decision. Defined.
  Program Instance Ksorts_countable : finite.Finite Ksorts :=
  {
    enum := [Kbool]
  }.
  Next Obligation.
    compute_done.
  Defined.
  Final Obligation.
    intros. destruct x; set_solver.
  Defined.
 
 
  Inductive Ksyms :=
  | KandBool
  | Kfalse
  | KnotBool
  | Ktrue
  .
 
 
  Instance Ksyms_eq_dec : EqDecision Ksyms.
  Proof. solve_decision. Defined.
  Program Instance Ksyms_countable : finite.Finite Ksyms :=
  {
    enum := [KandBool; Kfalse; KnotBool; Ktrue]
  }.
  Next Obligation.
    compute_done.
  Defined.
  Final Obligation.
    intros. destruct x; set_solver.
  Defined.
 
 
  Program Instance TheorySignature : Signature := {|
    sorts := {|
      sort := Ksorts;
    |};
    variables := StringVariables;
    symbols := {|
      symbol := Ksyms;
      arg_sorts σ :=
        match σ with
        | KandBool => [Kbool;Kbool]
        | Kfalse => []
        | KnotBool => [Kbool]
        | Ktrue => []
        end;
      ret_sort σ :=
        match σ with
        | KandBool => Kbool
        | Kfalse => Kbool
        | KnotBool => Kbool
        | Ktrue => Kbool
        end;
    |};
  |}.
 
  Definition Theory_behavioural : @Theory TheorySignature :=
    PropSet (fun pat =>
 
      (* KandBool *)
      (exists R, pat = existT R (((Top{R}) and (((@kore_fevar _ _ _ Kbool "X0") ⊆k{R} ((Kfalse ⋅ ⟨⟩) and (@kore_fevar _ _ _ Kbool "Var'Unds'Gen1"))) and (((@kore_fevar _ _ _ Kbool "X1") ⊆k{R} (@kore_fevar _ _ _ Kbool "Var'Unds'Gen0")) and (Top{R})))) ---> ((KandBool ⋅ ⟨@kore_fevar _ _ _ Kbool "X0"; @kore_fevar _ _ _ Kbool "X1"⟩) =k{R} ((@kore_fevar _ _ _ Kbool "Var'Unds'Gen1") and (Top{Kbool}))) )) \/
 
      (* KandBool simplification *)
      (exists R, pat = existT R ((Top{R}) ---> ((KandBool ⋅ ⟨@kore_fevar _ _ _ Kbool "VarB"; Ktrue ⋅ ⟨⟩⟩) =k{R} ((@kore_fevar _ _ _ Kbool "VarB") and (Top{Kbool}))) )) \/
 
      (* KandBool simplification *)
      (exists R, pat = existT R ((Top{R}) ---> ((KandBool ⋅ ⟨@kore_fevar _ _ _ Kbool "Var'Unds'Gen0"; Kfalse ⋅ ⟨⟩⟩) =k{R} ((Kfalse ⋅ ⟨⟩) and (Top{Kbool}))) )) \/
 
      (* KandBool *)
      (exists R, pat = existT R (((Top{R}) and (((@kore_fevar _ _ _ Kbool "X0") ⊆k{R} (Ktrue ⋅ ⟨⟩)) and (((@kore_fevar _ _ _ Kbool "X1") ⊆k{R} (@kore_fevar _ _ _ Kbool "VarB")) and (Top{R})))) ---> ((KandBool ⋅ ⟨@kore_fevar _ _ _ Kbool "X0"; @kore_fevar _ _ _ Kbool "X1"⟩) =k{R} ((@kore_fevar _ _ _ Kbool "VarB") and (Top{Kbool}))) )) \/
 
      (* KnotBool *)
      (exists R, pat = existT R (((Top{R}) and (((@kore_fevar _ _ _ Kbool "X0") ⊆k{R} (Kfalse ⋅ ⟨⟩)) and (Top{R}))) ---> ((KnotBool ⋅ ⟨@kore_fevar _ _ _ Kbool "X0"⟩) =k{R} ((Ktrue ⋅ ⟨⟩) and (Top{Kbool}))) )) \/
 
      (* KnotBool *)
      (exists R, pat = existT R (((Top{R}) and (((@kore_fevar _ _ _ Kbool "X0") ⊆k{R} (Ktrue ⋅ ⟨⟩)) and (Top{R}))) ---> ((KnotBool ⋅ ⟨@kore_fevar _ _ _ Kbool "X0"⟩) =k{R} ((Kfalse ⋅ ⟨⟩) and (Top{Kbool}))) ))
    ).
 
  Definition Theory_functional : @Theory TheorySignature :=
    PropSet (fun pat =>
 
      (* KandBool is functional *)
      (exists R, pat = existT R (kore_exists Kbool ((kore_bevar (In_nil)) =k{R} (KandBool ⋅ ⟨@kore_fevar _ _ _ Kbool "K0"; @kore_fevar _ _ _ Kbool "K1"⟩)) )) \/
 
      (* KnotBool is functional *)
      (exists R, pat = existT R (kore_exists Kbool ((kore_bevar (In_nil)) =k{R} (KnotBool ⋅ ⟨@kore_fevar _ _ _ Kbool "K0"⟩)) ))
    ).
End TheorySyntax.
Module TheorySemantics.
  Import TheorySyntax.
  Inductive Kbool : Type :=
  | Kfalse : Kbool
  | Ktrue : Kbool.
  Definition KnotBool (x0 : Kbool) : Kbool := 
  match x0 with
    | Kfalse => Ktrue
    | Ktrue => Kfalse
  end.
  Definition KandBool (x0 : Kbool) (x1 : Kbool) : Kbool := 
  match x0,x1 with
    | Kfalse, _Gen0 => Kfalse
    | Ktrue, B => B
  end.
 
  Definition Model : @Model TheorySignature :=
    mkModel_singleton
      (Ksorts_rect _ boolTODO)
      (Ksyms_rect _ trueTODO
                    falseTODO
                    KnotBool
                    KandBool
      ).
End TheorySemantics.
