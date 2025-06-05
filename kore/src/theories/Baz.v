From MatchingLogic Require Export stdpp_ext.
From Kore Require Export Semantics.
Import Signature.StringVariables.
Import Kore.Syntax.Notations.

From Coq Require Import ZArith.

Open Scope kore_scope.
Open Scope hlist_scope.
Open Scope string_scope.

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
  eval_helper2;
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


Ltac abstract_var := 
  match goal with
    | [|- context [evar_valuation ?σ ?s]] =>
      let x := fresh "var" in
      let Hx := fresh "Hvar" in
        remember (evar_valuation σ s) as x eqn:Hx (*;
        clear Hx;
        revert x *)
    end.

Module T.

  (* We have two sorts: natural numbers and bools *)
  Inductive DemoSorts :=
  | SortBaz
  | SortBar
  | SortFoo
  | SortBax
  (* | SortInt *)
(*   | SortGeneratedCounterCell
  | SortGeneratedTopCell *)
  (* | SortList *)
  | SortK
  | SortKItem.

  (* We prove decidable equality and finiteness of the type above. *)
  Instance DemoSorts_eq_dec : EqDecision DemoSorts.
  Proof. solve_decision. Defined.
  Program Instance DemoSorts_finite : finite.Finite DemoSorts := {
    enum := [SortBaz; SortBar; SortFoo; SortBax; (* SortInt; *)
             (* SortGeneratedCounterCell; SortGeneratedTopCell; *)
             (* SortList; *) SortK; SortKItem];
  }.
  Next Obligation. compute_done. Defined.
  Final Obligation. destruct x; set_solver. Defined.


  Inductive DemoSyms :=
  | SymBar
  | SymBaz1
  | SymBaz2
  | SymBax
  | SymF
  | SymKseq
  | SymDotk.

  (* We prove decidable equality and finiteness of the type above. *)
  Instance DemoSyms_eq_dec : EqDecision DemoSyms.
  Proof. solve_decision. Defined.
  Program Instance DemoSyms_finite : finite.Finite DemoSyms := {
    enum := [SymBar; SymBaz1; SymBaz2; SymBax; SymF; SymKseq; SymDotk];
  }.
  Next Obligation. compute_done. Defined.
  Final Obligation. destruct x; set_solver. Defined.

  (* TODO generator: This should be generated based on
     the subsorting relation/klean typeclass instances.
     Each constructor is an Inj instance in KLean *)
  Inductive Demo_subsort : CRelationClasses.crelation DemoSorts :=
  | inj_bax_kitem : Demo_subsort SortBax SortKItem
  | inj_foo_kitem : Demo_subsort SortFoo SortKItem
  | inj_baz_kitem : Demo_subsort SortBaz SortKItem
  | inj_bar_kitem : Demo_subsort SortBar SortKItem
  | inj_bax_foo : Demo_subsort SortBax SortFoo
  | inj_baz_foo : Demo_subsort SortBaz SortFoo
  | inj_bar_foo : Demo_subsort SortBar SortFoo
  | inj_baz_bar : Demo_subsort SortBaz SortBar
  | inj_baz_bax : Demo_subsort SortBaz SortBax.

  (* TODO generator: These two goals can be generated as
     they appear here *)
  Goal
    forall s1 s2 s3, Demo_subsort s1 s2 -> Demo_subsort s2 s3 ->
      Demo_subsort s1 s3.
  Proof.
    intros ??? H1 H2; inversion H1; inversion H2; try constructor; subst; try discriminate.
  Defined.
  Goal
    forall s1 s2, Demo_subsort s1 s2 -> Demo_subsort s2 s1 -> s1 = s2.
  Proof.
    intros ?? H H0; inversion H; subst; inversion H0; subst.
  Defined.

  (* In the signature, we need to define the sorts, the variable types,
     and the typing/sorting rules for symbols: *)
  Program Instance DemoSignature : Signature := {|
    sorts := {|
      sort := DemoSorts;
      subsort := Demo_subsort
    |};
    variables := StringVariables;
    symbols := {|
      symbol := DemoSyms;
      arg_sorts :=
        fun σ => match σ with
                  | SymBar => []
                  | SymBaz1 => []
                  | SymBaz2 => []
                  | SymBax => []
                  | SymF => [SortFoo]
                  | SymKseq => [SortKItem; SortK]
                  | SymDotk => []
                 end;
      ret_sort := fun σ => match σ with
                            | SymBar => SortBar
                            | SymBaz1 => SortBaz
                            | SymBaz2 => SortBaz
                            | SymBax => SortBax
                            | SymF => SortBaz
                            | SymKseq => SortK
                            | SymDotk => SortK
                           end;
    |};
  |}.

  (* TODO generator: a huge mutually inductive type should
     be generated. Alternatively, the KLean's approach
     could also work (by not making all of these mutual).
     In the KLean project, KCell, GeneratedTop, GeneratedCounter
     appear here too.
     *)
  Inductive baz_carrier : Set :=
  | c_baz1
  | c_baz2
  with bar_carrier : Set :=
  | c_bar
  | c_inj_baz_bar (b : baz_carrier)
  with bax_carrier : Set :=
  | c_bax
  | c_inj_baz_bax (b : baz_carrier)
  with foo_carrier : Set :=
  | c_inj_bar_foo (b : bar_carrier)
  | c_inj_bax_foo (b : bax_carrier)
  | c_inj_baz_foo (b : baz_carrier)
  with k_carrier : Set  :=
  | c_dotk
  | c_kseq (k : kitem_carrier) (l : k_carrier)
  with kitem_carrier : Set :=
  | c_inj_bar_kitem (b : bar_carrier)
  | c_inj_bax_kitem (b : bax_carrier)
  | c_inj_baz_kitem (b : baz_carrier)
  | c_inj_foo_kitem (b : foo_carrier).

  (* TODO generator: This function assigns the inductive
     types above to their sorts. I don't think, KLean
     uses this concept. In our case, this will be the
     sort-indexed carrier. *)
  Definition carrier (s : DemoSorts) : Set :=
  match s with
  | SortBaz => baz_carrier
  | SortBar => bar_carrier
  | SortFoo => foo_carrier
  | SortBax => bax_carrier
  | SortK => k_carrier
  | SortKItem => kitem_carrier
  end.

  (* TODO generator: here retr of KLean should be
     included in the function generation to handle
     injections. Retr is expressed here with 
     pattern matching. *)
  Definition f (x : foo_carrier) : baz_carrier :=
  match x with (* This pattern matching is retr of klean! *)
  | c_inj_bar_foo _ => c_baz1
  | c_inj_baz_foo _ => c_baz1
  | _ => c_baz2
  end.

  Program Definition DemoModel : @Model DemoSignature := mkModel_singleton
    carrier
    (fun σ =>
        match σ with
        | SymBar => c_bar
        | SymBaz1 => c_baz1
        | SymBaz2 => c_baz2
        | SymBax => c_bax
        | SymF => f
        | SymKseq => c_kseq
        | SymDotk => c_dotk
        end
      )
    _
    _.
  Next Obligation.
    destruct s; repeat constructor.
  Defined.
  (* TODO generator: these should be generated based on the injs
     of KLean. *)
  Final Obligation.
    intros s1 s2 H x; inversion H; subst.
    * exact (c_inj_bax_kitem x).
    * exact (c_inj_foo_kitem x).
    * exact (c_inj_baz_kitem x).
    * exact (c_inj_bar_kitem x).
    * exact (c_inj_bax_foo x).
    * exact (c_inj_baz_foo x).
    * exact (c_inj_bar_foo x).
    * exact (c_inj_baz_bar x).
    * exact (c_inj_baz_bax x).
  Defined.

  (* TODO generator: these are pre-defined tests *)
  Goal
    forall ρ, @eval DemoSignature DemoModel [] [] _ ρ
      (SymF ⋅ ⟨kore_inj _ inj_bar_foo (SymBar ⋅ ⟨⟩) ⟩) = {[c_baz1]}.
  Proof.
    intros.
    by basic_simplify_krule.
(*     rewrite eval_app_simpl. simpl.
    rewrite eval_equation_21. simpl.
    rewrite (@eval_app_simpl DemoSignature _ _ _ SymBar).
    simpl hmap.
    rewrite_app_ext.
    rewrite fmap_propset_singleton.
    rewrite_app_ext.
    reflexivity. *)
  Qed.

  Goal
    forall ρ, @eval DemoSignature DemoModel [] [] _ ρ
      (SymF ⋅ ⟨kore_inj _ inj_baz_foo (SymBaz2 ⋅ ⟨⟩) ⟩) = {[c_baz1]}.
  Proof.
    intros.
    by basic_simplify_krule.
(*     rewrite eval_app_simpl. simpl.
    rewrite eval_equation_21. simpl.
    rewrite (@eval_app_simpl DemoSignature _ _ _ SymBaz2).
    simpl hmap.
    rewrite_app_ext.
    rewrite fmap_propset_singleton.
    rewrite_app_ext.
    reflexivity. *)
  Qed.

  Goal
    forall ρ, @eval DemoSignature DemoModel [] [] _ ρ
      (SymF ⋅ ⟨kore_inj _ inj_bar_foo (kore_inj _ inj_baz_bar (SymBaz2 ⋅ ⟨⟩)) ⟩) = {[c_baz1]}.
  Proof.
    intros.
    by basic_simplify_krule.
(*     rewrite eval_app_simpl. simpl.
    rewrite eval_equation_21. simpl.
    rewrite eval_equation_21. simpl.
    rewrite (@eval_app_simpl DemoSignature _ _ _ SymBaz2).
    simpl hmap.
    rewrite_app_ext.
    rewrite fmap_propset_singleton.
    rewrite fmap_propset_singleton.
    rewrite_app_ext.
    reflexivity. *)
  Qed.

  Goal
    forall ρ, @eval DemoSignature DemoModel [] [] _ ρ
      (SymF ⋅ ⟨kore_inj _ inj_bax_foo (kore_inj _ inj_baz_bax (SymBaz2 ⋅ ⟨⟩)) ⟩) = {[c_baz1]}.
  Proof.
    intros.
    basic_simplify_krule. (* 
    rewrite eval_app_simpl. simpl.
    rewrite eval_equation_21. simpl.
    rewrite eval_equation_21. simpl.
    rewrite (@eval_app_simpl DemoSignature _ _ _ SymBaz2).
    simpl hmap.
    rewrite_app_ext.
    rewrite fmap_propset_singleton.
    rewrite fmap_propset_singleton.
    rewrite_app_ext. *)
    Fail reflexivity.
  Abort.

End T.
