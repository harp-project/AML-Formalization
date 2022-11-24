From MatchingLogic Require Export
  Logic
  ProofMode_base
  ProofInfo
  ProofMode_propositional
  ProofMode_firstorder
  ProofMode_fixpoint
  ProofMode_reshaper
  ProofMode_misc
.

(** Importing this file opens the necessary scope for the proof mode to work
    properly! *)
Open Scope ml_scope.
Open Scope string_scope.
Open Scope list_scope.

From Coq Require Import String.

Import
  MatchingLogic.Logic.Notations
  MatchingLogic.DerivedOperators_Syntax.Notations
.

Fixpoint proof_size {Σ : Signature} {φ : Pattern} {Γ}
   (pf : ML_proof_system Γ φ) : nat :=
match pf with
 | Modus_ponens _ phi1 phi2 x x0 => 1 + proof_size x + proof_size x0
 | ProofSystem.Ex_gen _ phi1 phi2 x x0 x1 x2 x3 => 1 + proof_size x2
 | ProofSystem.Framing_left _ phi1 phi2 psi x x0 => 1 + proof_size x0
 | ProofSystem.Framing_right _ phi1 phi2 psi x x0 => 1 + proof_size x0
 | ProofSystem.Svar_subst _ phi psi X x x0 x1 => 1 + proof_size x1
 | ProofSystem.Knaster_tarski _ phi psi x x0 => 1 + proof_size x0
 | ProofSystem.Existence _ => 1
 | _ => 1
end.

Definition proof_size_info {Σ : Signature} {φ Γ i} (pf : derives_using Γ φ i) : nat :=
match pf with
 | exist _ x x0 => proof_size x
end.

Lemma ex1_coq :
  forall (A B : Prop), A -> B -> A /\ B.
Proof.
  intros. split. assumption. assumption.
Qed.

(** Low-level proof, using only the proof system *)
Lemma ex1_low : forall {Σ : Signature} (Γ : Theory) (A B : Pattern),
  well_formed A = true ->
  well_formed B = true ->
  Γ ⊢i (A ---> B ---> (A and B))
  using BasicReasoning.
Proof.
  intros Σ Γ A B WFA WFB.
  epose proof (tB := (A_impl_A Γ B _)).
  epose proof (t1 := MP (P2 Γ (!(!A) ---> !B) A Bot _ _ _) (P1 _ _ B _ _)).
  epose proof (t2 := MP (reorder_meta _ _ _ (P4 Γ (!A) B _ _)) (P1 _ _ B _ _)).
  epose proof (t3'' := MP (P1 Γ A (!(!A) ---> !B) _ _) (P1 _ _ B _ _)).
  epose proof (t4 := MP tB (MP t2 (P2 Γ B B _ _ _ _))).
  epose proof (t5'' := 
          MP t4
                       (MP t1
                                     (P2 Γ B ((!(!A) ---> !B) ---> !A)
                                         (((!(!A) ---> !B) ---> A) ---> !(!(!A) ---> !B)) _ _ _))).
  epose proof (tA := (P1 Γ A B) _ _).
  epose proof (tB' := MP tB (P1 _ (B ---> B) A _ _)).
  epose proof (t3' := MP t3'' (P2 _ B A ((!(!A) ---> !B) ---> A) _ _ _)).
  epose proof (t3 := MP t3' (P1 _ ((B ---> A) ---> B ---> (! (! A) ---> ! B) ---> A) A _ _)).
  epose proof (t5' := MP t5''
                            (P2 _ B ((!(!A) ---> !B) ---> A) (!(!(!A) ---> !B)) _ _ _)).
  epose proof (t5 := MP t5' 
                           (P1 _ ((B ---> (! (! A) ---> ! B) ---> A) ---> B ---> ! (! (! A) ---> ! B))
                               A _ _)).
  epose proof (t6 := MP tA
                           (MP t3
                                         (P2 _ A (B ---> A) (B ---> (!(!A) ---> !B) ---> A) _ _ _))).
  epose proof (t7 := MP t6 
                           (MP t5 
                                         (P2 _ A (B ---> (!(!A) ---> !B) ---> A) (B ---> !(!(!A) ---> !B)) _ _ _))).
  apply t7.
  Unshelve.
    (* 43 well-formedness goals *)
    all: wf_auto2.
Defined.

From Coq Require Import ssreflect ssrfun ssrbool.

Open Scope string_scope.
Open Scope list_scope.
Open Scope ml_scope.

Lemma ex1_pm2 : forall {Σ : Signature} (Γ : Theory) (A B : Pattern),
  well_formed A = true ->
  well_formed B = true ->
  Γ ⊢i (A ---> B ---> (A and B))
  using BasicReasoning.
Proof.
  intros Σ Γ A B WFA WFB.
  do 2 mlIntro; mlSplitAnd; mlAssumption.
Defined.

(** Proof using proof mode *)
Lemma ex1_pm : forall {Σ : Signature} (Γ : Theory) (A B : Pattern),
  well_formed A = true ->
  well_formed B = true ->
  Γ ⊢i (A ---> B ---> (A and B))
  using BasicReasoning.
Proof.
  intros Σ Γ A B WFA WFB.
  unfold patt_and, patt_or, patt_not.
  mlIntro "Ha". mlIntro "Hb". mlIntro "H".
  mlAssert ("H0" : B). { wf_auto2. } { mlAssumption. }
  mlRevertLast.
  mlApply "H".
  mlIntro "H0". mlApply "H0". mlAssumption.
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
       symbols := Symbols ;
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

  Definition proof1_low : nat := proof_size_info (ex1_low ∅ A B ltac:(wf_auto2) ltac:(wf_auto2)).
  Definition proof1_pm : nat := proof_size_info (ex1_pm ∅ A B ltac:(wf_auto2) ltac:(wf_auto2)).
  Definition proof1_pm2 : nat := proof_size_info (ex1_pm2 ∅ A B ltac:(wf_auto2) ltac:(wf_auto2)).
(*
  Compute proof_size_info (ex1_low ∅ A B ltac:(wf_auto2) ltac:(wf_auto2)).
  Compute proof_size_info (ex1_pm ∅ A B ltac:(wf_auto2) ltac:(wf_auto2)). *)

End compute.
