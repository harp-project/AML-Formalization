(**
  * Definedness

   In this module we define the definedness symbol and use it to build derived notions
   like totality and equality.
 *)

From MatchingLogic Require Export Logic.
Import MatchingLogic.Logic.Notations.

Set Default Proof Mode "Classic".

(* We have only one symbol *)
Inductive Symbols := def_sym.

Global Instance Symbols_eqdec : EqDecision Symbols.
Proof.
  solve_decision.
Defined.

#[global]
Program Instance Symbols_finite : finite.Finite Symbols.
Next Obligation.
  exact [def_sym].
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

  Class Syntax {Σ : Signature} :=
  {
    (* 'Symbols' are a 'subset' of all the symbols from the signature *)
    sym_inj: Symbols -> symbols;
    (* TODO make it injective? *)
    (* for convenience *)
  }.

Section definedness.

  Open Scope ml_scope.

  Context {Σ : Signature}.

  Context {syntax : Syntax}.

  Definition definedness : Pattern :=
    patt_sym (sym_inj def_sym).

  Definition patt_defined (phi : Pattern) : Pattern :=
    definedness ⋅ phi.

  Definition patt_total (phi: Pattern) : Pattern :=
    patt_not (patt_defined (patt_not phi)).

  Definition patt_subseteq (phi1 phi2 : Pattern) : Pattern :=
    patt_total (phi1 ---> phi2).

  Definition patt_equal (phi1 phi2 : Pattern) : Pattern :=
    patt_total (phi1 <---> phi2).

  Definition patt_in (phi1 phi2 : Pattern) : Pattern :=
    patt_defined (patt_and phi1 phi2).

  Definition AC_patt_defined : Application_context :=
    @ctx_app_r _ definedness box ltac:(auto).

  Definition is_predicate_pattern ψ : Pattern :=
    (patt_equal ψ patt_top) or (patt_equal ψ patt_bott).
End definedness.

Module Notations.
  Import Syntax.

  Notation "⌈ p ⌉" := (patt_defined p) : ml_scope.
  Notation "⌊ p ⌋" := (patt_total p) : ml_scope.
  Notation "p =ml q" := (patt_equal p q) (at level 68, left associativity) : ml_scope.
  Notation "p ⊆ml q" := (patt_subseteq p q) (at level 68, left associativity) : ml_scope.
  Notation "p ∈ml q" := (patt_in p q) (at level 68, left associativity) : ml_scope.
  
  Notation "'⌈_⌉'" := definedness : ml_scope.
End Notations.

Section definedness.
  Context
    {Σ : Signature}
    {syntax : Syntax}
  .
  Import Notations.
  Open Scope ml_scope.

  Lemma well_formed_defined ϕ:
    well_formed ϕ = true ->
    well_formed ⌈ ϕ ⌉ = true.
  Proof.
    intros Hwfϕ.
    unfold patt_defined.
    auto.
  Qed.

  (*
  #[local]
   Hint Resolve well_formed_defined : core.
   *)

  Lemma well_formed_total ϕ:
    well_formed ϕ = true ->
    well_formed ⌊ ϕ ⌋ = true.
  Proof.
    intros Hwfϕ.
    unfold patt_total.
    wf_auto2.
  Qed.
(*
  #[local]
   Hint Resolve well_formed_total : core.
*)
  Lemma well_formed_equal (phi1 phi2 : Pattern) :
    well_formed phi1 = true ->
    well_formed phi2 = true ->
    well_formed (phi1 =ml phi2) = true.
  Proof.
    intros wfphi1 wfphi2. unfold "=ml". wf_auto2.
  Qed.
(*
  #[local]
   Hint Resolve well_formed_equal : core.
*)
  Lemma well_formed_subseteq (phi1 phi2 : Pattern) :
    well_formed phi1 = true ->
    well_formed phi2 = true ->
    well_formed (phi1 ⊆ml phi2) = true.
  Proof.
    intros wfphi1 wfphi2. unfold "⊆ml". wf_auto2.
  Qed.

  (*
  #[local]
   Hint Resolve well_formed_subseteq : core.
*)

  Lemma well_formed_in (phi1 phi2 : Pattern) :
    well_formed phi1 = true ->
    well_formed phi2 = true ->
    well_formed (phi1 ∈ml phi2) = true.
  Proof.
    intros wfphi1 wfphi2. unfold "∈ml". wf_auto2.
  Qed.

  (*
  #[local]
   Hint Resolve well_formed_in : core.
*)

  Definition ev_x := (evar_fresh []).
  Definition p_x := patt_free_evar ev_x.

  Inductive AxiomName := AxDefinedness.

  Definition axiom (name : AxiomName) : Pattern :=
    match name with
    | AxDefinedness => patt_defined p_x
    end.

  Program Definition named_axioms : NamedAxioms :=
    {| NAName := AxiomName;
      NAAxiom := axiom;
    |}.
  Next Obligation.
    destruct name; simpl; wf_auto2.
  Qed.

  Definition theory := theory_of_NamedAxioms named_axioms.

  Obligation Tactic := idtac.

  (** Substitution classes: *)
  #[global]
  Program Instance Unary_defined : Unary patt_defined := {}.
  Next Obligation.
    intros. unfold patt_defined. repeat rewrite pm_correctness.
    simpl. reflexivity.
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
  Program Instance Unary_total : Unary patt_total := {}.
  Next Obligation.
    intros. unfold patt_total. repeat rewrite pm_correctness.
    simpl. reflexivity.
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
  Program Instance Binary_equal : Binary patt_equal := {}.
  Next Obligation.
    intros. unfold patt_equal. repeat rewrite pm_correctness.
    simpl. reflexivity.
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
  Program Instance Binary_subseteq : Binary patt_subseteq := {}.
  Next Obligation.
    intros. unfold patt_subseteq. repeat rewrite pm_correctness.
    simpl. reflexivity.
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
  Program Instance Binary_in : Binary patt_in := {}.
  Next Obligation.
    intros. unfold patt_in. repeat rewrite pm_correctness.
    simpl. reflexivity.
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

  (* Defines ϕ₁ to be an inversion of ϕ₂ *)
  (* ∀ x. ϕ₁ x = ∃ y. y ∧ (x ∈ ϕ₂ y)
     This assumes, that bound element variables x and y do not occur in ϕ₁ and ϕ₂ *)
     Definition patt_eq_inversion_of ϕ₁ ϕ₂
     := patt_forall
          (patt_equal
             (patt_app (nest_ex ϕ₁) (patt_bound_evar 0))
             (patt_exists (patt_and (patt_bound_evar 0)
                                    (patt_in (patt_bound_evar 1)
                                             (patt_app (nest_ex (nest_ex ϕ₂)) (patt_bound_evar 0)))))).


End definedness.