(* From Equations Require Import Equations. *)
From MatchingLogic Require Export stdpp_ext.
From Kore Require Export Semantics.
Import Signature.StringVariables.
Import Kore.Syntax.Notations.

Open Scope kore_scope.


Module BoolSyntax.

  Inductive Ksorts :=
  | Kbool.


  Instance Ksorts_eq_dec : EqDecision Ksorts.
  Proof. solve_decision. Defined.


  Program Instance Ksorts_finite : finite.Finite Ksorts := {
    enum := [Kbool];
  }.
  Next Obligation. compute_done. Defined.
  Final Obligation. destruct x; set_solver. Defined.

  Inductive Ksyms :=
  | Ktrue
  | Kfalse
  | KnotBool
  | KandBool
  | KandThenBool
  | KxorBool
  | KorBool
  | KorElseBool
  | KimpliesBool.

  Instance Ksyms_eq_dec : EqDecision Ksyms.
  Proof. solve_decision. Defined.

  Program Instance Ksyms_finite : finite.Finite Ksyms := {
    enum := [Ktrue; Kfalse; KnotBool; KandBool; KandThenBool;
             KxorBool; KorBool; KorElseBool; KimpliesBool];
  }.
  Next Obligation. compute_done. Defined.
  Final Obligation. destruct x; set_solver. Defined.


  Program Instance BoolSignature : Signature := {|
    sorts := {|
      sort := Ksorts;
    |};
    variables := StringVariables;
    symbols := {|
      symbol := Ksyms;
      arg_sorts σ :=
        match σ with
        | Ktrue => []
        | Kfalse => []
        | KnotBool => [Kbool]
        | KandBool => [Kbool; Kbool]
        | KandThenBool => [Kbool; Kbool]
        | KxorBool => [Kbool; Kbool]
        | KorBool => [Kbool; Kbool]
        | KorElseBool => [Kbool; Kbool]
        | KimpliesBool => [Kbool; Kbool]
        end;
      ret_sort σ := Kbool;
    |};
  |}.

  Open Scope hlist_scope.
  Open Scope string_scope.

(*
dv is only used with the following parameters:
\dv{SortBool{}}("true")
\dv{SortBool{}}("false")
\dv{SortInt{}}("n") (n is a number)
\dv{SortString{}}("s") (s is a string)
\dv{SortKConfigVar{}}("$PGM")

  axiom{R} \implies{R} (
    \and{R}(
      \top{R}(),
      \and{R} (
          \in{SortBool{}, R} (
            X0:SortBool{},
            \dv{SortBool{}}("false")
          ),
          \top{R} ()
        )),
    \equals{SortBool{},R} (
      LblnotBool'Unds'{}(X0:SortBool{}),
     \and{SortBool{}} (
       \dv{SortBool{}}("true"),
        \top{SortBool{}}())))

  axiom{R} \implies{R} (
    \and{R}(
      \top{R}(),
      \and{R} (
          \in{SortBool{}, R} (
            X0:SortBool{},
            \dv{SortBool{}}("true")
          ),
          \top{R} ()
        )),
    \equals{SortBool{},R} (
      LblnotBool'Unds'{}(X0:SortBool{}),
     \and{SortBool{}} (
       \dv{SortBool{}}("false"),
        \top{SortBool{}}())))

  axiom{R} \implies{R} (
    \and{R}(
      \top{R}(),
      \and{R} (
          \in{SortBool{}, R} (
            X0:SortBool{},
            \and{SortBool{}}(\dv{SortBool{}}("false"),Var'Unds'Gen1:SortBool{})
          ),\and{R} (
          \in{SortBool{}, R} (
            X1:SortBool{},
            Var'Unds'Gen0:SortBool{}
          ),
          \top{R} ()
        ))),
    \equals{SortBool{},R} (
      Lbl'Unds'andBool'Unds'{}(X0:SortBool{},X1:SortBool{}),
     \and{SortBool{}} (
       Var'Unds'Gen1:SortBool{},
        \top{SortBool{}}())))
 *)

  Program Definition Kbool_theory : @Theory BoolSignature :=
    PropSet (fun pat =>
      (exists R, pat =                              (* v-- this should be dv *)
        existT R ((Top{R} and kore_fevar "X" ⊆k{R} Kfalse ⋅ ⟨⟩)
          --->                               (* v-- this should be dv *)
         (KnotBool ⋅ ⟨kore_fevar "X"⟩ =k{R} (Ktrue ⋅ ⟨⟩ and Top{Kbool})))
      ) \/
      (exists R, pat =
        existT R ((Top{R} and kore_fevar "X" ⊆k{R} Ktrue ⋅ ⟨⟩)
          --->
        (KnotBool ⋅ ⟨kore_fevar "X"⟩ =k{R} (Kfalse ⋅ ⟨⟩ and Top{Kbool})))
      ) \/
      (exists R, pat =
        existT R ((Top{R} and
                   kore_fevar "X0" ⊆k{R} (Kfalse ⋅ ⟨⟩ and kore_fevar "_") and
                   @kore_fevar _ _ _ Kbool "X1" ⊆k{R} kore_fevar "_" and
                   Top{R})
          --->
        (KandBool ⋅ ⟨kore_fevar "X0"; kore_fevar "X1"⟩ =k{R} (kore_fevar "_" and Top{Kbool})))
      )
      (* \/ For testing:
      pat = existT Kbool Top{Kbool} *)
    )
    .
    (* Sometimes, implicit arguments are needed, e.g. if X ⊆ Y, and X and Y are both free variables. However, this might be resolved if X and Y would be bound *)

End BoolSyntax.

(* Tactic Notation "deconstruct_elem_of_Theory" :=
  repeat match goal with
  | [ H : _ ∈ ?Γ |- _ ] => destruct H
  end; (* clear; *) simpl. *)

Module BoolSemantics.

  Import BoolSyntax.

  Definition BoolModel : @Model BoolSignature :=
    mkModel_singleton
      (Ksorts_rect _ bool)
      (Ksyms_rect _ true
                    false
                    negb
                    andb
                    andb
                    xorb
                    orb
                    orb
                    implb)
      ltac:(intros []; auto with typeclass_instances).

  Ltac unfold_elem_of :=
  match goal with
  | [H : _ ∈ _ |- _]  => destruct H
  end.

(*   Lemma Propset_full_or_empty :
    forall (A : Type) (P : Prop),
      {[_ : A | P]} = ⊤ \/
      {[_ : A | P]} = ∅.
  Proof.
    intros.
    Require Import ClassicalPropType.
    pose proof ClassicalProp.classic.
  Admitted. *)

  Lemma propset_difference_neg :
    forall {A : Type} (P : A -> Prop),
      ⊤ ∖ {[x : A | P x]} = {[x : A | ~P x]}.
  Proof.
    intros.
    set_solver.
  Qed.

  Goal satT Kbool_theory BoolModel.
  Proof.
    (* unfold sat defs *)
    unfold satT, satM. intros.

    (* Generate a goal for each axiom: *)
    unfold Kbool_theory in H.
    unfold_elem_of; destruct_or?; destruct_ex?; subst.

    (* simplification *)
    * simpl.
      eval_helper.
      unshelve (repeat erewrite app_ext_singleton).
      1-3: simpl; try repeat econstructor. (* This seems to be fragile *)
      cbn.
      
      
      
      
      Search propset ⊤ ∅.
      
       set_solver.
    
    
    
    set_helper.
    rewrite_singleton_all. cbn. reflexivity.
  Qed.

End BoolSemantics.

