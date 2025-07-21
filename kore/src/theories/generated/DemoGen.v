
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

  Inductive Theory_subsorts : CRelationClasses.crelation Ksorts := .
  Program Instance TheorySignature : Signature := {|
    sorts := {|
      sort := Ksorts;
      subsort := Theory_subsorts;
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
      (exists R, pat = existT R (((Top{R}) and (((@kore_fevar _ _ _ Kbool "X0") ⊆k{R} ((Kfalse ⋅ ⟨⟩) and (@kore_fevar _ _ _ Kbool "Var'Unds'Gen1"))) and (((@kore_fevar _ _ _ Kbool "X1") ⊆k{R} (@kore_fevar _ _ _ Kbool "Var'Unds'Gen0")) and (Top{R})))) --->ₖ ((KandBool ⋅ ⟨@kore_fevar _ _ _ Kbool "X0"; @kore_fevar _ _ _ Kbool "X1"⟩) =k{R} ((@kore_fevar _ _ _ Kbool "Var'Unds'Gen1") and (Top{Kbool}))) )) \/

      (* KandBool simplification *)
      (exists R, pat = existT R ((Top{R}) --->ₖ ((KandBool ⋅ ⟨@kore_fevar _ _ _ Kbool "VarB"; Ktrue ⋅ ⟨⟩⟩) =k{R} ((@kore_fevar _ _ _ Kbool "VarB") and (Top{Kbool}))) )) \/

      (* KandBool simplification *)
      (exists R, pat = existT R ((Top{R}) --->ₖ ((KandBool ⋅ ⟨@kore_fevar _ _ _ Kbool "Var'Unds'Gen0"; Kfalse ⋅ ⟨⟩⟩) =k{R} ((Kfalse ⋅ ⟨⟩) and (Top{Kbool}))) )) \/

      (* KandBool *)
      (exists R, pat = existT R (((Top{R}) and (((@kore_fevar _ _ _ Kbool "X0") ⊆k{R} (Ktrue ⋅ ⟨⟩)) and (((@kore_fevar _ _ _ Kbool "X1") ⊆k{R} (@kore_fevar _ _ _ Kbool "VarB")) and (Top{R})))) --->ₖ ((KandBool ⋅ ⟨@kore_fevar _ _ _ Kbool "X0"; @kore_fevar _ _ _ Kbool "X1"⟩) =k{R} ((@kore_fevar _ _ _ Kbool "VarB") and (Top{Kbool}))) )) \/

      (* KnotBool *)
      (exists R, pat = existT R (((Top{R}) and (((@kore_fevar _ _ _ Kbool "X0") ⊆k{R} (Kfalse ⋅ ⟨⟩)) and (Top{R}))) --->ₖ ((KnotBool ⋅ ⟨@kore_fevar _ _ _ Kbool "X0"⟩) =k{R} ((Ktrue ⋅ ⟨⟩) and (Top{Kbool}))) )) \/

      (* KnotBool *)
      (exists R, pat = existT R (((Top{R}) and (((@kore_fevar _ _ _ Kbool "X0") ⊆k{R} (Ktrue ⋅ ⟨⟩)) and (Top{R}))) --->ₖ ((KnotBool ⋅ ⟨@kore_fevar _ _ _ Kbool "X0"⟩) =k{R} ((Kfalse ⋅ ⟨⟩) and (Top{Kbool}))) ))
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
  Definition KandBool (x0 : Kbool) (x1 : Kbool) : Kbool := 
  match x0,x1 with
    | Kfalse, _Gen0 => Kfalse
    | Ktrue, B => B
  end.
  Definition KnotBool (x0 : Kbool) : Kbool := 
  match x0 with
    | Kfalse => Ktrue
    | Ktrue => Kfalse
  end.

  Program Definition Model : @Model TheorySignature :=
    mkModel_singleton
      (Ksorts_rect _ Kbool)
      (Ksyms_rect _ KandBool Kfalse KnotBool Ktrue)
      ltac:(simpl; intros []; do 2 constructor)
      _
      (λ _ _, None).
  Next Obligation.
    intros ? ? H; simpl; inversion H.
  Defined.


Ltac autorewrite_set :=
  repeat (
    rewrite intersection_top_l_L +
    rewrite intersection_top_r_L +
    rewrite union_empty_l_L +
    rewrite union_empty_r_L +
    rewrite propset_difference_neg +
    rewrite propset_union_simpl +
    rewrite propset_intersection_simpl +
    rewrite singleton_subseteq_l +
    rewrite fmap_propset_singleton
  ).

Ltac basic_simplify_krule :=
  repeat eval_simplifier;
  simpl sort_inj;
  repeat (rewrite_app_ext; repeat rewrite fmap_propset_singleton);
  autorewrite_set.

Ltac simplify_krule :=
  basic_simplify_krule;
  apply propset_top_elem_of_2;
  intro;
  apply elem_of_PropSet;
  repeat rewrite elem_of_PropSet;
  repeat rewrite singleton_subseteq;
  repeat rewrite singleton_eq.

Ltac classicize :=
  apply Classical_Prop.imply_to_or.

Ltac simplify_equality :=
match goal with
      | [H : _ _ = _ _ |- _] => simplify_eq H; clear H; intro
      end.

Ltac abstract_var := 
  match goal with
    | [|- context [evar_valuation ?σ ?s]] =>
      let x := fresh "var" in
      let Hx := fresh "Hvar" in
        remember (evar_valuation σ s) as x eqn:Hx (*;
        clear Hx;
        revert x *)
    end.

  Goal satT Theory_behavioural Model.
  Proof.
    unfold satT, satM. intros.
    unfold Theory_behavioural in H.
    unfold_elem_of; destruct_or?; destruct_ex?; subst.
    all: simplify_krule; try reflexivity;
         try classicize;
         intros;
         repeat destruct_evar_val; subst;
         repeat simplify_equality; subst;
         try tauto;
         try congruence.
    (* simplification proofs: *)
    all: destruct_and!; subst; apply singleton_subseteq_l in H0;
         destruct H0;
         try rewrite singleton_subseteq in H0; set_solver.
  Defined.

End TheorySemantics.
