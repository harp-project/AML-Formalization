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
grep -Eo "\\\\dv{[^}]*}[^\(]*\([^\)]*\)" /tmp/definition.kore > /tmp/matches

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
      (** negation: *)
      (* not false = true *)
      (exists R, pat =                              (* v-- this should be dv *)
        existT R ((Top{R} and kore_fevar "X" ⊆k{R} Kfalse ⋅ ⟨⟩)
          --->                               (* v-- this should be dv *)
         (KnotBool ⋅ ⟨kore_fevar "X"⟩ =k{R} (Ktrue ⋅ ⟨⟩ and Top{Kbool})))
      ) \/
      (* not true = false *)
      (exists R, pat =
        existT R ((Top{R} and kore_fevar "X" ⊆k{R} Ktrue ⋅ ⟨⟩)
          --->
        (KnotBool ⋅ ⟨kore_fevar "X"⟩ =k{R} (Kfalse ⋅ ⟨⟩ and Top{Kbool})))
      ) \/
      (** conjunction *)
      (* rule `_andBool_`(#token("false","Bool") #as _Gen1,_Gen0)=>_Gen1 *)
      (exists R, pat =
        existT R ((Top{R} and
                   kore_fevar "X0" ⊆k{R} (Kfalse ⋅ ⟨⟩ and kore_fevar "Gen1") and
                   @kore_fevar _ _ _ Kbool "X1" ⊆k{R} kore_fevar "Gen0" and
                   Top{R})
          --->
        (KandBool ⋅ ⟨kore_fevar "X0"; kore_fevar "X1"⟩ =k{R} (kore_fevar "Gen1" and Top{Kbool})))
      ) \/
      ((* rule `_andBool_`(B,#token("true","Bool"))=>B *)
        exists R, pat =
          existT R (
            Top{R} --->
            KandBool ⋅ ⟨kore_fevar "B"; Ktrue ⋅ ⟨⟩ ⟩ =k{R} (kore_fevar "B" and Top{Kbool})
          )
      ) \/
      ( (* rule `_andBool_`(_Gen0,#token("false","Bool"))=>#token("false","Bool") *)
        exists R, pat =
          existT R (
            Top{R} --->
            KandBool ⋅ ⟨kore_fevar "Gen0"; Kfalse ⋅ ⟨⟩ ⟩ =k{R} (Kfalse ⋅ ⟨ ⟩ and Top{Kbool})
        )
      ) \/
      ( (* rule `_andBool_`(#token("true","Bool"),B)=>B *)
        exists R, pat =
          existT R (
            Top{R} and kore_fevar "X0" ⊆k{R} Ktrue ⋅ ⟨⟩ and
            @kore_fevar _ _ _ Kbool "X1" ⊆k{R} kore_fevar "B" and Top{R}
            --->
            (KandBool ⋅ ⟨kore_fevar "X0"; kore_fevar "X1"⟩ =k{R} (kore_fevar "B" and Top{Kbool}))
          )
      ) \/
      (** andthen *)
      (*rule `_andThenBool_`(#token("false","Bool") #as _Gen1,_Gen0)=>_Gen1*)
      (
        exists R, pat =
          existT R (
            Top{R} and kore_fevar "X0" ⊆k{R} (Kfalse ⋅ ⟨⟩ and kore_fevar "Gen1") and
            @kore_fevar _ _ _ Kbool "X1" ⊆k{R} kore_fevar "Gen0" and Top{R}
            --->
            (KandThenBool ⋅ ⟨kore_fevar "X0"; kore_fevar "X1"⟩ =k{R} (kore_fevar "Gen1" and Top{Kbool}))
          )
      ) \/
      (*rule `_andThenBool_`(K,#token("true","Bool"))=>K*)
      (
        exists R, pat =
          existT R (
            Top{R} --->
            KandThenBool ⋅ ⟨kore_fevar "K"; Ktrue ⋅ ⟨⟩ ⟩ =k{R} (kore_fevar "K" and Top{Kbool})
          )
      ) \/
      (*rule `_andThenBool_`(_Gen0,#token("false","Bool"))=>#token("false","Bool")*)
      (
        exists R, pat =
          existT R (
            Top{R} --->
            KandThenBool ⋅ ⟨kore_fevar "Gen0"; Kfalse ⋅ ⟨⟩ ⟩ =k{R} (Kfalse ⋅ ⟨ ⟩ and Top{Kbool})
        )
      ) \/
      (*rule `_andThenBool_`(#token("true","Bool"),K)=>K*)
      (
        exists R, pat =
          existT R (
            Top{R} and kore_fevar "X0" ⊆k{R} Ktrue ⋅ ⟨⟩ and
            @kore_fevar _ _ _ Kbool "X1" ⊆k{R} kore_fevar "K" and Top{R}
            --->
            (KandThenBool ⋅ ⟨kore_fevar "X0"; kore_fevar "X1"⟩ =k{R} (kore_fevar "K" and Top{Kbool}))
          )
      ) \/
      (** xorBool *)
      (* rule `_xorBool_`(B,B)=>#token("false","Bool") *)
      (
        exists R, pat =
          existT R (
            Top{R} and @kore_fevar _ _ _ Kbool "X0" ⊆k{R} kore_fevar "B" and
            @kore_fevar _ _ _ Kbool "X1" ⊆k{R} kore_fevar "B" and Top{R}
            --->
            (KxorBool ⋅ ⟨kore_fevar "X0"; kore_fevar "X1"⟩ =k{R} (Kfalse ⋅ ⟨⟩ and Top{Kbool}))
          )
      ) \/
      (* rule `_xorBool_`(B,#token("false","Bool"))=>B *)
      (
        exists R, pat =
          existT R (
            Top{R}
            --->
            (KxorBool ⋅ ⟨kore_fevar "B"; Kfalse ⋅ ⟨⟩⟩ =k{R} (kore_fevar "B" and Top{Kbool}))
          )
      ) \/
      (* rule `_xorBool_`(#token("false","Bool"),B)=>B *)
      (
        exists R, pat =
          existT R (
            Top{R} and kore_fevar "X0" ⊆k{R} Kfalse ⋅ ⟨⟩ and
            @kore_fevar _ _ _ Kbool "X1" ⊆k{R} kore_fevar "B" and Top{R}
            --->
            (KxorBool ⋅ ⟨kore_fevar "X0"; kore_fevar "X1"⟩ =k{R} (kore_fevar "B" and Top{Kbool}))
          )
      ) \/
      (** orBool *)
      (* rule `_orBool_`(B,#token("false","Bool"))=>B *)
      (
        exists R, pat =
          existT R (
            Top{R}
            --->
            (KorBool ⋅ ⟨kore_fevar "B"; Kfalse ⋅ ⟨⟩⟩ =k{R} (kore_fevar "B" and Top{Kbool}))
          )
      ) \/
      (* rule `_orBool_`(_Gen0,#token("true","Bool"))=>#token("true","Bool") *)
      (
        exists R, pat =
          existT R (
            Top{R}
            --->
            (KorBool ⋅ ⟨kore_fevar "Gen0"; Ktrue ⋅ ⟨⟩⟩ =k{R} (Ktrue ⋅ ⟨⟩ and Top{Kbool}))
          )
      ) \/
      (* rule `_orBool_`(#token("false","Bool"),B)=>B *)
      (
        exists R, pat =
          existT R (
            Top{R} and kore_fevar "X0" ⊆k{R} Kfalse ⋅ ⟨⟩ and
            @kore_fevar _ _ _ Kbool "X1" ⊆k{R} kore_fevar "B" and Top{R}
            --->
            (KorBool ⋅ ⟨kore_fevar "X0"; kore_fevar "X1"⟩ =k{R} (kore_fevar "B" and Top{Kbool}))
          )
      ) \/
      (* rule `_orBool_`(#token("true","Bool"),_Gen0)=>#token("true","Bool") *)
      (
        exists R, pat =
          existT R (
            Top{R} and kore_fevar "X0" ⊆k{R} Ktrue ⋅ ⟨⟩ and
            @kore_fevar _ _ _ Kbool "X1" ⊆k{R} kore_fevar "Gen0" and Top{R}
            --->
            (KorBool ⋅ ⟨kore_fevar "X0"; kore_fevar "X1"⟩ =k{R} (Ktrue ⋅ ⟨⟩ and Top{Kbool}))
          )
      ) \/
      (** orElseBool *)
      (* rule `_orElseBool_`(K,#token("false","Bool"))=>K *)
      (
        exists R, pat =
          existT R (
            Top{R}
            --->
            (KorBool ⋅ ⟨kore_fevar "K"; Kfalse ⋅ ⟨⟩⟩ =k{R} (kore_fevar "K" and Top{Kbool}))
          )
      ) \/
      (* rule `_orElseBool_`(_Gen0,#token("true","Bool"))=>#token("true","Bool") *)
      (
        exists R, pat =
          existT R (
            Top{R}
            --->
            (KorBool ⋅ ⟨kore_fevar "Gen0"; Ktrue ⋅ ⟨⟩⟩ =k{R} (Ktrue ⋅ ⟨⟩ and Top{Kbool}))
          )
      ) \/
      (* rule `_orElseBool_`(#token("false","Bool"),K)=>K *)
      (
        exists R, pat =
          existT R (
            Top{R} and kore_fevar "X0" ⊆k{R} Kfalse ⋅ ⟨⟩ and
            @kore_fevar _ _ _ Kbool "X1" ⊆k{R} kore_fevar "K" and Top{R}
            --->
            (KorBool ⋅ ⟨kore_fevar "X0"; kore_fevar "X1"⟩ =k{R} (kore_fevar "K" and Top{Kbool}))
          )
      ) \/
      (* rule `_orElseBool_`(#token("true","Bool"),_Gen0)=>#token("true","Bool") *)
      (
        exists R, pat =
          existT R (
            Top{R} and kore_fevar "X0" ⊆k{R} Ktrue ⋅ ⟨⟩ and
            @kore_fevar _ _ _ Kbool "X1" ⊆k{R} kore_fevar "Gen0" and Top{R}
            --->
            (KorBool ⋅ ⟨kore_fevar "X0"; kore_fevar "X1"⟩ =k{R} (Ktrue ⋅ ⟨⟩ and Top{Kbool}))
          )
      ) \/
      (** impliesBool *)
      (* `_impliesBool_`(B,#token("false","Bool"))=>`notBool_`(B) *)
      (
        exists R, pat =
          existT R (
            Top{R}
            --->
            (KimpliesBool ⋅ ⟨kore_fevar "B"; Kfalse ⋅ ⟨⟩⟩ =k{R} (KnotBool ⋅ ⟨kore_fevar "B"⟩ and Top{Kbool}))
          )
      ) \/
      (* rule `_impliesBool_`(_Gen0,#token("true","Bool"))=>#token("true","Bool") *)
      (
        exists R, pat =
          existT R (
            Top{R}
            --->
            (KimpliesBool ⋅ ⟨kore_fevar "Gen0"; Ktrue ⋅ ⟨⟩⟩ =k{R} (Ktrue ⋅ ⟨⟩ and Top{Kbool}))
          )
      ) \/
      (* rule `_impliesBool_`(#token("false","Bool"),_Gen0)=>#token("true","Bool") *)
      (
        exists R, pat =
          existT R (
            Top{R} and kore_fevar "X0" ⊆k{R} Kfalse ⋅ ⟨⟩ and
            @kore_fevar _ _ _ Kbool "X1" ⊆k{R} kore_fevar "Gen0" and Top{R}
            --->
            (KimpliesBool ⋅ ⟨kore_fevar "X0"; kore_fevar "X1"⟩ =k{R} (Ktrue ⋅ ⟨⟩ and Top{Kbool}))
          )
      ) \/
      (* rule `_impliesBool_`(#token("true","Bool"),B)=>B *)
      (
        exists R, pat =
          existT R (
            Top{R} and kore_fevar "X0" ⊆k{R} Ktrue ⋅ ⟨⟩ and
            @kore_fevar _ _ _ Kbool "X1" ⊆k{R} kore_fevar "B" and Top{R}
            --->
            (KimpliesBool ⋅ ⟨kore_fevar "X0"; kore_fevar "X1"⟩ =k{R} (kore_fevar "B" and Top{Kbool}))
          )
      ) \/
    (** functional axioms *)
      (
      exists R, pat =
        existT R (
          kore_exists Kbool (KandBool ⋅ ⟨kore_fevar "K0"; kore_fevar "K1"⟩ =k{R} kore_bevar (In_nil)
        ))
      ) (* \/
      (
      exists R, pat =
        existT R (
          kore_exists Kbool (KandThenBool ⋅ ⟨kore_fevar "K0"; kore_fevar "K1"⟩ =k{R} kore_bevar (In_nil)
        ))
      ) \/
      (
      exists R, pat =
        existT R (
          kore_exists Kbool (KandBool ⋅ ⟨kore_fevar "K0"; kore_fevar "K1"⟩ =k{R} kore_bevar (In_nil)
        ))
      )*)
    )
    .
    (* Sometimes, implicit arguments are needed, e.g. if X ⊆ Y, and X and Y are both free variables. However, this might be resolved if X and Y would be bound *)

End BoolSyntax.

(* Tactic Notation "deconstruct_elem_of_Theory" :=
  repeat match goal with
  | [ H : _ ∈ ?Γ |- _ ] => destruct H
  end; (* clear; *) simpl. *)

(* Lemma propset_full_or_empty :
  forall (P : Prop),
    {[_ | P]} = ⊤ \/ {[_ | P]} = ⊥. *)

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

  Ltac destruct_evar_val :=
  match goal with
  | [ |- context [evar_valuation ?ρ ?x] ] =>
    let H := fresh "Val" in
      destruct (evar_valuation ρ x) eqn:H
  end.

  Ltac solve_dep_prods :=
    match goal with
    | [ |- ()] => exact tt
    | [ |- prod (sigT _) _] =>
      apply pair; [
        eapply existT; reflexivity
      |
        solve_dep_prods
      ]
    end.

  Ltac solve_all_singleton :=
  match goal with
  | [ |- all_singleton _] => cbn; solve_dep_prods
  end.

  (* For some reason, this tac does not work outside this file *)
  Ltac autorewrite_set :=
    repeat (
      rewrite intersection_top_l_L +
      rewrite intersection_top_r_L +
      rewrite union_empty_l_L +
      rewrite union_empty_r_L +
      rewrite propset_difference_neg
    ).

  (* This would be much more simple, if rewrite_stat innermost worked... *)
  Ltac rewrite_app_ext_innnermost G :=
  match G with
  | context [app_ext ?σ ?args] =>
    rewrite_app_ext_innnermost args (* This step is just to reach
                                        the innermost app_ext *)
    (* idtac "match" σ args *)
  | context [app_ext ?σ ?args] => (* This branch fails, if there is no
                                     more app_exts, therefore
                                     it succeeds for the last (innermost)
                                     app_ext *)
    (* idtac "last1" σ args; *)
    (* let H := fresh "H" in
    (* we explicitly rewrite: *)
    unshelve (epose proof (@app_ext_singleton _ BoolModel σ args ltac:(solve_all_singleton)) as H);
    (* idtac "last2" σ args; *)
    rewrite H; (* erewrite does not work here, for some reason *)
    clear H *)
    rewrite (@app_ext_singleton _ BoolModel σ args ltac:(solve_all_singleton))
  end.

  Ltac rewrite_app_ext :=
  match goal with
  | |- ?G => rewrite_app_ext_innnermost G; cbn
  end.

  Goal satT Kbool_theory BoolModel.
  Proof.
    (* unfold sat defs *)
    unfold satT, satM. intros.

    (* Generate a goal for each axiom: *)
    unfold Kbool_theory in H.
    unfold_elem_of; destruct_or?; destruct_ex?; subst.

    1-25:
      simpl;
      eval_helper;
      autorewrite_set;
      repeat rewrite_app_ext;
      repeat destruct_evar_val;
      set_solver.
    
    simpl.
    eval_helper.
    cbn.
    apply propset_fa_union_full.
    intros.
    (* eexists. *)
    (* eval_helper. *)
    Import Equations.
    simp eval.
    
    cbn.
    

(*     (* simplification *)
    * simpl.
      eval_helper.
      autorewrite_set.
      unshelve (repeat erewrite app_ext_singleton).
      1-3: simpl; try repeat econstructor. (* This seems to be fragile *)
      cbn.
      destruct_evar_val; set_solver.
    * simpl.
      eval_helper.
      autorewrite_set.
      unshelve (repeat erewrite app_ext_singleton).
      1-3: simpl; try repeat econstructor. (* This seems to be fragile *)
      cbn.
      destruct_evar_val; set_solver.
    * simpl.
      eval_helper.
      autorewrite_set.
      unshelve (repeat erewrite app_ext_singleton).
      1-3: simpl; try repeat econstructor. (* This seems to be fragile *)
      cbn.
      do 2 destruct_evar_val; set_solver. *)
  Qed.

End BoolSemantics.

