From Coq Require Import String.

From Coq Require Import ssreflect ssrfun ssrbool. (* <- needed for mlAssert *)
From stdpp Require Import list. (* <- needed for mlRevertLast *)
From MatchingLogic Require Import
    Logic
    DerivedOperators_Syntax
    ProofSystem
    ProofMode.MLPM
.

Import
  MatchingLogic.Logic.Notations
  MatchingLogic.DerivedOperators_Syntax.Notations
.

Open Scope string_scope.
Open Scope list_scope.
Open Scope ml_scope.

From Coq Require Import ssreflect ssrfun ssrbool.

Open Scope string_scope.
Open Scope list_scope.
Open Scope ml_scope.

Local Lemma Private_revert_forall_iter {Σ : Signature} (Γ : Theory) :
  forall (l : list Pattern) (ϕ : Pattern) x,
  Pattern.wf l ->
  well_formed ϕ ->
  Γ ⊢i foldr patt_imp (all , ϕ^{{evar: x ↦ 0}}) l ---> foldr patt_imp ϕ l
    using BasicReasoning.
Proof.
  intros l ϕ x Wfl Wfϕ. apply prf_weaken_conclusion_iter_meta. 1-3: wf_auto2.
  mlIntro "H".
  mlSpecialize "H" with x.
  rewrite evar_open_evar_quantify. wf_auto2.
  mlAssumption.
Qed.

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

Definition private_test_revert_1 :=
  (Private_revert_forall_iter ∅ [] patt_bott (fresh_evar patt_bott)
    ltac:(wf_auto2) ltac:(wf_auto2)).
Definition private_test_revert_2 :=
  (revert_forall_iter ∅ [] patt_bott (fresh_evar patt_bott)
    ltac:(wf_auto2) ltac:(wf_auto2)).
Definition private_test_revert_3 :=
  (Private_revert_forall_iter ∅ [A;B;A;B;A;B] patt_bott (fresh_evar patt_bott)
    ltac:(wf_auto2) ltac:(wf_auto2)).
Definition private_test_revert_4 :=
  (revert_forall_iter ∅ [A;B;A;B;A;B] patt_bott (fresh_evar patt_bott)
    ltac:(wf_auto2) ltac:(wf_auto2)).

    (*
  Compute proof_size_info (ex1_low ∅ A B ltac:(wf_auto2) ltac:(wf_auto2)).
  Compute proof_size_info (ex1_pm ∅ A B ltac:(wf_auto2) ltac:(wf_auto2)). *)

End compute.

