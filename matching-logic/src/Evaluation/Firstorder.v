From MatchingLogic Require Import Theories.Definedness_Syntax
                                  ProofMode.MLPM.

Import MatchingLogic.Logic.Notations.

Set Default Proof Mode "Classic".

Definition Example3 : Type := 
  forall (Σ : Signature) (Γ : Theory) (A B : Pattern),
  well_formed (ex, A) = true ->
  well_formed (ex, B) = true ->
  Γ ⊢ (ex, A and B) ---> ex, A
.

Lemma ex3_low : Example3.
Proof.
  unfold Example3.
  intros Σ Γ A B WFA WFB.
  (* inline proof of ex_quan_monotone *)
  assert (forall A B x, well_formed (ex, A) -> well_formed (ex, B) -> x ∉ free_evars A -> x ∉ free_evars B ->
    Γ ⊢ (evar_open x 0 A) ---> (evar_open x 0 B) -> Γ ⊢ (ex, A) ---> ex, B) as H. {
    intros.
    apply strip_exists_quantify_l with (x := x).
    { exact H1. }
    { shelve. }
    apply Ex_gen. 1-2: shelve.
    eapply syllogism_meta. 1-3: shelve. exact H3.
    epose proof (Htmp := Ex_quan Γ B0 x _).
    cbn in Htmp.
    eapply useGenericReasoning in Htmp.
    apply Htmp.
    shelve.
  }
  mlFreshEvar as x.
  apply (H (A and B) A x).
  1-4: shelve.
  mlSimpl.
  epose proof (pf_conj_elim_l Γ (A^{evar:0↦x}) (B^{evar:0↦x}) _ _) as H0.
  eapply useGenericReasoning in H0. exact H0. shelve.
  Unshelve.
  (* 9 well_formed goals *)
  1,4-7,9-10,13-14: solve [wf_auto2].
  (* 3 variable membership goals *)
  2: cbn; solve_free_evars 1. 4: fm_solve. 3: fm_solve.
  (* 3 ProofInfoLe goals *)
  1-3: try_solve_pile.
Defined.


(** Proof using only FOL proof mode *)
Lemma ex3_fol_pm : Example3.
Proof.
  unfold Example3.
  intros Σ Γ A B WFA WFB.
  mlIntro "H".
  mlDestructEx "H" as x.
  mlSimpl.
  mlExists x.
  fromMLGoal.
  epose proof (pf_conj_elim_l Γ (A^{evar:0↦x}) _ _ _) as H0.
  eapply useGenericReasoning in H0.
  { exact H0. }
  { shelve. }
  Unshelve.
  (* 2 well_formedness *)
  1-2: wf_auto2.
  (* 1 ProofInfoLe *)
  try_solve_pile.  
Defined.

(** Proof using proof mode *)
Lemma ex3_pm : Example3.
Proof.
  unfold Example3.
  intros Σ Γ A B wfA wfB.
  mlIntro "H".
  mlDestructEx "H" as x.
  mlSimpl.
  mlDestructAnd "H" as "H0" "H1".
  mlExists x.
  mlAssumption.
Defined.

Lemma ex3_coq {T : Type} A B:
  (exists (x : T), A x /\ B x) -> exists x, A x.
Proof.
  intros H.
  destruct H as [x H].
  destruct H as [H0 H1].
  exists x.
  assumption.
Qed.

Section compute.

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
      sym_import_definedness Definedness_Syntax.def_sym] ;
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
       Definedness_Syntax.sym_inj := sym_import_definedness;
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
  
  Definition proof3_low    := ex3_low    signature ∅ A B ltac:(reflexivity) ltac:(reflexivity).
  Definition proof3_fol_pm := ex3_fol_pm signature ∅ A B ltac:(reflexivity) ltac:(reflexivity).
  Definition proof3_pm     := ex3_pm     signature ∅ A B ltac:(reflexivity) ltac:(reflexivity).

End compute.
