From MatchingLogic Require Export Definedness_Syntax.
Import MatchingLogic.Logic.Notations
       MatchingLogic.Theories.Definedness_Syntax.Notations.

Set Default Proof Mode "Classic".


Inductive Symbols := sym_inh | sym_sorts.

Global Instance Symbols_eqdec : EqDecision Symbols.
Proof. unfold EqDecision. intros x y. unfold Decision; destruct x; decide equality. (*solve_decision.*) Defined.

#[global]
Program Instance Symbols_finite : finite.Finite Symbols.
Next Obligation.
  exact [sym_inh; sym_sorts].
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

Section sorts_syntax.
  Context {Σ : Signature}.

  Class Syntax :=
    { sym_inj : Symbols -> symbols;
      imported_definedness : Definedness_Syntax.Syntax;
    }.
  #[global] Existing Instance imported_definedness.

  Context {self : Syntax}.

  Local Definition sym (s : Symbols) : Pattern :=
    patt_sym (sym_inj s).

  Definition inhabitant := sym sym_inh.
  Definition Sorts := sym sym_sorts.

  Example test_pattern_1 := patt_equal (inhabitant) (inhabitant).
  Definition patt_inhabitant_set(phi : Pattern) : Pattern := inhabitant ⋅ phi.

  Definition patt_element_of (φ ψ : Pattern) := ⌈ φ and ψ ⌉.

End sorts_syntax.

Section sorts.
  Context {Σ : Signature}.
  Context {self : Syntax}.
  Open Scope ml_scope.
  Local Notation "〚 phi 〛" := (patt_inhabitant_set phi) (at level 0) : ml_scope.

  Obligation Tactic := idtac.

  Class ESortedBinder (binder : Pattern -> Pattern -> Pattern) := {
      esorted_binder_morphism :
        forall {A : Type} (f : A -> Pattern -> Pattern)
           (f_morph : PatternMorphism f)
           (f_swap : SwappableEx f nest_ex f_morph)
           (s phi : Pattern) a,
        f a (binder s phi) = binder (f a s) (f (increase_ex pm_spec_data a) phi) ;
  }.

  #[global]
  Program Instance Unary_inhabitant_set : Unary patt_inhabitant_set := {}.
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

  Definition patt_sorted_neg (sort phi : Pattern) : Pattern :=
    〚sort〛 and ! phi.

  #[global]
  Program Instance Binary_sorted_neg : Binary patt_sorted_neg := {}.
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

  Definition patt_exists_of_sort (sort phi : Pattern) : Pattern :=
    ex , ((b0 ∈ml 〚nest_ex sort〛) and phi).
  Local Notation "'ex' s ,  phi" := 
    (patt_exists_of_sort s phi) (at level 70) : ml_scope.

  #[global]
  Program Instance sorted_exists_binder : ESortedBinder patt_exists_of_sort := {}.
  Next Obligation.
    intros.
    repeat rewrite pm_correctness.
    unfold patt_exists_of_sort.
    repeat rewrite <- pm_correctness.
    mlSimpl.
    rewrite pm_correctness. cbn.
    replace (on_bevar pm_spec_data (increase_ex pm_spec_data a) 0) with b0.
    2: {
      now rewrite pm_ezero_increase.
    }
    rewrite pm_correctness. cbn.
    rewrite eswap.
    repeat rewrite pm_correctness.
    reflexivity.
  Defined.

  Definition patt_forall_of_sort (sort phi : Pattern) : Pattern :=
    all , ((b0 ∈ml 〚nest_ex sort〛) ---> phi).

  Local Notation "'all' s ,  phi" := 
    (patt_forall_of_sort s phi) (at level 70) : ml_scope.

  #[global]
  Program Instance sorted_forall_binder : ESortedBinder patt_forall_of_sort := {}.
  Next Obligation.
    intros.
    repeat rewrite pm_correctness.
    unfold patt_exists_of_sort.
    repeat rewrite <- pm_correctness.
    mlSimpl.
    rewrite pm_correctness. cbn.
    replace (on_bevar pm_spec_data (increase_ex pm_spec_data a) 0) with b0.
    2: {
      now rewrite pm_ezero_increase.
    }
    rewrite pm_correctness. cbn.
    rewrite eswap.
    repeat rewrite pm_correctness.
    reflexivity.
  Defined.

  (* TODO patt_forall_of_sort and patt_exists_of_sort are duals - a lemma *)

  (* TODO a lemma about patt_forall_of_sort *)

  Definition patt_total_function(phi from to : Pattern) : Pattern :=
    all from , (ex (nest_ex to) , ((nest_ex (nest_ex phi) ⋅ b1) =ml b0)).

  Definition patt_partial_function(phi from to : Pattern) : Pattern :=
    all from , (ex (nest_ex to), ((nest_ex (nest_ex phi) ⋅ b1) ⊆ml b0)).


  (* Assuming `f` is a total function, says it is injective on given domain. Does not quite work for partial functions. *)
  Definition patt_total_function_injective f from : Pattern :=
    all from , (all (nest_ex from) , 
                (((nest_ex (nest_ex f) ⋅ b1) =ml (nest_ex (nest_ex f) ⋅ b0)) ---> 
                  (b1 =ml b0))).

  (* Assuming `f` is a partial function, says it is injective on given domain. Works for total functions, too. *)
  Definition patt_partial_function_injective f from : Pattern :=
    all
      from ,
      (all
         (nest_ex from) ,
         (
            ! ((nest_ex (nest_ex f) ⋅ b1) =ml ⊥ )
            --->
            ((nest_ex (nest_ex f) ⋅ b1) =ml (nest_ex (nest_ex f) ⋅ b0))
             ---> (b1 =ml b0))).

  Definition patt_total_binary_function(phi from1 from2 to : Pattern)
  : Pattern :=
    patt_forall_of_sort from1 (
      patt_forall_of_sort (nest_ex from2) (
        patt_exists_of_sort (nest_ex (nest_ex to)) (
          (((nest_ex (nest_ex (nest_ex phi)) ⋅ b2) ⋅ b1) =ml b0)
        )
      )
    )
  .

  ______ TODO: nonempty Sorts!


End sorts.

Module Notations.
  Notation "〚 phi 〛" := (patt_inhabitant_set phi) (at level 0) : ml_scope.
  Notation "'all' s ,  phi" := (patt_forall_of_sort s phi) (at level 80) : ml_scope.
  Notation "'ex' s ,  phi" := (patt_exists_of_sort s phi) (at level 80) : ml_scope.
  Notation "phi :ml s1 × s2 -> s3" :=  (patt_total_binary_function phi s1 s2 s3) (at level 70) : ml_scope.
End Notations.

Ltac mlESortedSimpl_single :=
match goal with
| |- context G [?f ?arg _ (?binder _ _)] =>
  let Hyp := fresh "H" in
  let Hyp2 := fresh "H" in
    (* We check whether we have a sorted binder *)
    assert (Hyp: ESortedBinder binder) by (typeclasses eauto + eauto);
    (* We check wether we found a swappable substitution *)
    assert (Hyp2: SwappableEx (f arg) nest_ex _) by (typeclasses eauto + eauto);
    (* The previous checks are needed to correctly identify the position for
       simplification, since using only rewrite fails on finding the right
       instances *)
    erewrite (@esorted_binder_morphism _ _ Hyp _ _ _ Hyp2);
    clear Hyp Hyp2;
    try rewrite [increase_ex _ _]/=
end.

Ltac mlESortedSimpl_single_hyp H :=
match type of H with
| context G [?f ?arg _ (?binder _ _)] =>
  let Hyp := fresh "H" in
  let Hyp2 := fresh "H" in
    (* We check whether we have a sorted binder *)
    assert (Hyp: ESortedBinder binder) by (typeclasses eauto + eauto);
    (* We check wether we found a swappable substitution *)
    assert (Hyp2: SwappableEx (f arg) nest_ex _) by (typeclasses eauto + eauto);
    (* The previous checks are needed to correctly identify the position for
       simplification, since using only rewrite fails on finding the right
       instances *)
    erewrite (@esorted_binder_morphism _ _ Hyp _ _ _ Hyp2) in H;
    clear Hyp Hyp2;
    try rewrite [increase_ex _ _]/= in H
end.

(* TODO: extend with mu *)
Tactic Notation "mlSortedSimpl" := repeat mlESortedSimpl_single.
Tactic Notation "mlSortedSimpl" "in" hyp(H) := repeat mlESortedSimpl_single_hyp H.

Tactic Notation "mlSimpl" := repeat (mlUnsortedSimpl; mlSortedSimpl); cbn.
Tactic Notation "mlSimpl" "in" hyp(H) := repeat (mlUnsortedSimpl in H; mlSortedSimpl in H); cbn.

Section simplTest.
  (* NOTE: these tactics are not exported!!!!! *)
  Import Substitution.Notations.
  Import Notations.
  Open Scope ml_scope.
  Context {Σ : Signature} {S : Syntax}.

  Goal forall s p x,
    (all s , p)^{evar:0 ↦ x} = (all s^{evar:0 ↦ x}, p^{evar:1 ↦ x}) ->
    (all s , p)^{evar:0 ↦ x} = (all s^{evar:0 ↦ x}, p^{evar:1 ↦ x}).
  Proof.
    intros.
    mlSortedSimpl.
    mlSortedSimpl in H.
    reflexivity.
  Qed.

  Goal forall s p1 p2 p3 x,
    (p1 ---> all s , p2 ---> p3)^{evar:0 ↦ x} =
    (p1^{evar:0 ↦ x} ---> all s^{evar:0 ↦ x}, p2^{evar:1 ↦ x} ---> p3^{evar:1 ↦ x}).
  Proof.
    intros. mlSimpl.
    mlSortedSimpl.
    mlSimpl.
    reflexivity.
  Qed.

  Goal forall s ψ x X, well_formed_closed ψ ->
  (patt_forall_of_sort s ψ)^[[evar: x ↦ ψ]] = patt_bott ->
  (patt_forall_of_sort s ψ)^{evar: 0 ↦ x} = patt_bott ->
  (patt_forall_of_sort s ψ)^{{evar: x ↦ 0}} = patt_bott ->
  (patt_forall_of_sort s ψ)^[[svar: X ↦ ψ]] = patt_bott ->
  (patt_forall_of_sort s ψ)^{svar: 0 ↦ X} = patt_bott ->
  (patt_forall_of_sort s ψ)^{{svar: X ↦ 0}} = patt_bott ->
  (patt_forall_of_sort s ψ)^[[svar: X ↦ ψ]] = patt_bott /\
  (patt_forall_of_sort s ψ)^{svar: 0 ↦ X} = patt_bott /\
  (patt_forall_of_sort s ψ)^{{svar: X ↦ 0}} = patt_bott /\
  (patt_forall_of_sort s ψ)^[[evar: x ↦ ψ]] = patt_bott /\ 
  (patt_forall_of_sort s ψ)^{evar: 0 ↦ x} = patt_bott /\
  (patt_forall_of_sort s ψ)^{{evar: x ↦ 0}} = patt_bott
  .
  Proof.
    intros.
    repeat mlSortedSimpl.
    mlSortedSimpl in H0.
    mlSortedSimpl in H1.
    mlSortedSimpl in H2.
    mlSortedSimpl in H3.
    mlSortedSimpl in H4.
    mlSortedSimpl in H5.
    intuition.
  Qed.

  Goal forall s ψ x, (* well_formed_closed ψ -> *)
  (patt_forall_of_sort (patt_imp s s) ψ)^[[evar: x ↦ ψ]] = patt_bott
  .
  Proof.
    intros.
    Fail progress mlSortedSimpl.
  Abort.

  Local Definition ml_plus := patt_app.
  Local Definition ml_in := patt_app.
  Local Definition ml_eq := patt_app.


  Import Substitution.Notations.
  Import Pattern.Notations.
  Import DerivedOperators_Syntax.Notations.
  Import Pattern.BoundVarSugar.

  Local Notation "a +ml b" := (ml_plus a b) (at level 67).
  Local Notation "a =ml b" := (ml_eq a b) (at level 67).
  Local Notation "a ∈ml b" := (ml_in a b) (at level 67).
  Local Notation "'ex' , phi" := (patt_exists phi) (at level 80) : ml_scope.
  Local Notation "'mu' , phi" := (patt_mu phi) (at level 80) : ml_scope.
  Local Notation "〚 phi 〛" := (patt_inhabitant_set phi) (at level 0) : ml_scope.

  Open Scope ml_scope.

  Local Definition Nat := patt_bott.
  Local Definition Zero := patt_bott.
  Local Definition Succ := patt_bott.

  Goal forall X,
    (( patt_free_svar X ⊆ml 〚 Nat 〛 --->
         Zero ∈ml patt_free_svar X --->
         (all Nat, (b0 ∈ml patt_free_svar X ---> 
         Succ ⋅ b0 ∈ml patt_free_svar X)) --->
         (all Nat, b0 ∈ml patt_free_svar X ) ) ^[[svar:X↦ex Nat, b0 and Zero +ml b0 =ml b0]] ) = 
        ( (ex Nat, b0 and Zero +ml b0 =ml b0) ⊆ml 〚 Nat 〛 --->
         Zero ∈ml (ex Nat, b0 and Zero +ml b0 =ml b0) --->
         (all Nat, (b0 ∈ml (ex Nat, b0 and Zero +ml b0 =ml b0) ---> 
         Succ ⋅ b0 ∈ml (ex Nat, b0 and Zero +ml b0 =ml b0))) --->
         (all Nat, b0 ∈ml (ex Nat, b0 and Zero +ml b0 =ml b0) ) ).
  Proof.
    intros. mlSimpl.
    case_match.
    - reflexivity.
    - try congruence.
  Qed.

End simplTest.
