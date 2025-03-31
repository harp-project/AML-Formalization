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
  Definition Kbool_theory : @Theory BoolSignature :=
    PropSet (fun pat =>
      exists R, pat = existT R (KnotBool ⋅ ⟨Ktrue ⋅ ⟨⟩⟩ =k{R} Ktrue ⋅ ⟨⟩)
    ).

End BoolSyntax.

Module BoolSemantics.

  Import BoolSyntax.

  (* Definition bool_carrier (s : Ksorts) :=
    match s with 
    | Kbool => bool
    end.
  Check hlist.
  Program Definition bool_app
    (σ : Ksyms)
    (l : hlist bool_carrier (arg_sorts σ)) :
      propset (bool_carrier (ret_sort σ)) :=
  match σ with
  | Ktrue => {[true]}
  | Kfalse => {[false]}
  | KnotBool => _
  | KandBool => _
  | KandThenBool => _
  | KxorBool => _
  | KorBool => _
  | KorElseBool => _
  | KimpliesBool => _
  end. *)

  (* Program Definition BoolModel : @Model BoolSignature := {|
    carrier := bool_carrier;
    app := bool_app;
  |}. *)

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

  Goal satT Kbool_theory BoolModel.
  Proof.
    unfold satT. intros.
    
    cbn. unfold op_all, op_not. intros.
    deconstruct_elem_of_Theory; eval_helper; set_helper.
    now rewrite_singleton_all.

    repeat (unfold bevar_subst, Equality.block, solution_left, eq_rect_r; simpl).
    eval_helper. set_helper. now rewrite_singleton_all.
  Qed.

End BoolSemantics.

