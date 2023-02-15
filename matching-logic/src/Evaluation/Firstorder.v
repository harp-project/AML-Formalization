From Coq Require Import String.

From MatchingLogic Require Import
    Logic
    DerivedOperators_Syntax
    ProofSystem
    ProofMode
.

Import
  MatchingLogic.Logic.Notations
  MatchingLogic.DerivedOperators_Syntax.Notations
.

Open Scope string_scope.
Open Scope list_scope.
Open Scope ml_scope.

(** Low-level proof, using only the proof system *)
Lemma ex3_low : forall {Σ : Signature} (Γ : Theory) (A B : Pattern) x,
  well_formed A = true ->
  well_formed B = true ->
  x ∉ free_evars A ->
  x ∉ free_evars B ->
  Γ ⊢ (ex, A^{{evar:x ↦ 0}} and B^{{evar:x↦0}}) ---> ex, A^{{evar:x↦0}}.
Proof.
  intros Σ Γ A B x WFA WFB Hx1 Hx2.
  (* inline proof of ex_quan_monotone *)
  assert (forall A B, well_formed A -> well_formed B -> x ∉ free_evars A -> x ∉ free_evars B ->
    Γ ⊢ A ---> B -> Γ ⊢ (ex, A^{{evar:x↦0}}) ---> ex, B^{{evar:x↦0}}) as H. {
    intros. apply Ex_gen. 1-2: shelve.
    eapply syllogism_meta. 1-3: shelve. exact H3.
    rewrite <- (evar_open_evar_quantify x 0 B0) at 1. 2: shelve.
    unfold evar_open. fold (instantiate (ex, B0^{{evar:x↦0}}) (patt_free_evar x)).
    epose proof (Ex_quan Γ (B0^{{evar:x↦0}}) x _) as H4.
    eapply useGenericReasoning in H4. exact H4. shelve.
  }
  apply (H (A and B)). 1-4: shelve.
  epose proof (pf_conj_elim_l Γ A B _ _).
  eapply useGenericReasoning in H0. exact H0. shelve.
  Unshelve.
  (* 9 well_formed goals *)
  3-7,9-10,13-14: try wf_auto2.
  (* 3 variable membership goals *)
  4,5: cbn; solve_free_evars 1. 2: { apply evar_quantify_no_occurrence. }
  (* 3 ProofInfoLe goals *)
  1-3: try_solve_pile.
Defined.

From Coq Require Import ssreflect ssrfun ssrbool.

Open Scope string_scope.
Open Scope list_scope.
Open Scope ml_scope.

(** Proof using only FOL proof mode *)
Lemma ex3_fol_pm : forall {Σ : Signature} (Γ : Theory) (A B : Pattern) x,
  well_formed A = true ->
  well_formed B = true ->
  x ∉ free_evars A ->
  x ∉ free_evars B ->
  Γ ⊢ (ex, A^{{evar:x ↦ 0}} and B^{{evar:x↦0}}) ---> ex, A^{{evar:x↦0}}.
Proof.
  intros Σ Γ A B x WFA WFB Hx1 Hx2.
  mlIntro "H". mlDestructEx "H" as x. 1-2: shelve.
  mlSimpl. mlExists x. fromMLGoal.
  epose proof (pf_conj_elim_l Γ A _ _ _) as H0.
  eapply useGenericReasoning in H0. exact H0. shelve.
  Unshelve.  
  (* 2 variable inclusion *)
  1-2: cbn; repeat rewrite free_evars_evar_quantify; set_solver.
  (* 2 well_formedness *)
  1-2: wf_auto2.
  (* 1 ProofInfoLe *)
  try_solve_pile.
Defined.

(** Proof using proof mode *)
Lemma ex3_pm : forall {Σ : Signature} (Γ : Theory) (A B : Pattern) x,
  well_formed A = true ->
  well_formed B = true ->
  x ∉ free_evars A ->
  x ∉ free_evars B ->
  Γ ⊢ (ex, A^{{evar:x ↦ 0}} and B^{{evar:x↦0}}) ---> ex, A^{{evar:x↦0}}.
Proof.
  intros Σ Γ A B x WFA WFB Hx1 Hx2.
  mlIntro "H". mlDestructEx "H" as x. 1-2: shelve.
  mlSimpl. mlDestructAnd "H" as "H0" "H1".
  mlExists x. mlAssumption.
  Unshelve.  
  1-2: cbn; repeat rewrite free_evars_evar_quantify; set_solver.
Defined.

Section compute.
  From MatchingLogic.Theories Require Import Definedness_Syntax
                                             Definedness_Semantics
                                             Sorts_Syntax
                                             Sorts_Semantics
                                             Definedness_ProofSystem.
  From stdpp Require Import base fin_sets sets propset finite.

  Inductive Symbols :=
    | sym_import_definedness (d : Definedness_Syntax.Symbols)
    | Zero | Succ (* constructors for Nats *)
    | TT | FF
    | even
  .

  Instance Symbols_eqdec : EqDecision Symbols.
  Proof. solve_decision. Defined.

  #[local]
  Program Instance Symbols_fin : Finite Symbols :=
  {|
    enum := [Zero; Succ; TT ; FF; even;
      sym_import_definedness Definedness_Syntax.definedness] ;
  |}.
  Next Obligation.
    repeat constructor; set_solver.
  Qed.
  Next Obligation.
    destruct x; try set_solver.
    destruct d; set_solver.
  Qed.

  Instance signature : Signature :=
    {| variables := StringMLVariables ;
       ml_symbols := {|
          symbols := Symbols ;
        |}
    |}.

  Instance definedness_syntax : Definedness_Syntax.Syntax :=
    {|
       Definedness_Syntax.inj := sym_import_definedness;
    |}.

  Open Scope string_scope.
  Let X0 := patt_free_evar "X0".
  Let X := patt_free_evar "X".
  Let sym_even := patt_sym even.
  Let sym_succ := patt_sym Succ.
  Let sym_zero := patt_sym Zero.
  Let sym_tt := patt_sym TT.
  Let sym_ff := patt_sym FF.
  (* axioms *)
  Definition defined : Pattern := Definedness_Syntax.axiom AxDefinedness.

  Definition A : Pattern :=
    sym_zero.
  Definition B : Pattern :=
    patt_app sym_succ sym_zero.
  
  Definition proof3_low := ex3_low ∅ A B "X" ltac:(wf_auto2) ltac:(wf_auto2) ltac:(set_solver) ltac:(set_solver).
  Definition proof3_fol_pm := ex3_fol_pm ∅ A B "X" ltac:(wf_auto2) ltac:(wf_auto2) ltac:(set_solver) ltac:(set_solver).
  Definition proof3_pm := ex3_pm ∅ A B "X" ltac:(wf_auto2) ltac:(wf_auto2) ltac:(set_solver) ltac:(set_solver).

End compute.
