From Coq Require Import String.

From stdpp Require Import base pmap gmap fin_maps finite.

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

(** Low-level proof, using only the proof system *)
Lemma ex2_low {Σ : Signature} (A B C D : Pattern) (Γ : Theory) :
  well_formed (A ---> B ---> C ---> D) = true ->
  Γ ⊢ ((B $ C) <---> D) ->
  Γ ⊢ ((A $ (B $ C)) ---> (A $ D)).
Proof.
  intros Hwf H.
  apply pf_iff_proj1 in H.
  eapply Framing_right with (ψ := A) in H.
  exact H.
  Unshelve.
  (* 3 well-formedness goal *)
  1,3,4: wf_auto2.
  (* 1 proof info goal *)
  try_solve_pile.
Defined.

(** Low-level proof, using the congruence lemma *)
Lemma ex2_low2 {Σ : Signature} (A B C D : Pattern) (Γ : Theory) :
  well_formed (A ---> B ---> C ---> D) = true ->
  Γ ⊢ ((B $ C) <---> D) ->
  Γ ⊢ ((A $ (B $ C)) ---> (A $ D)).
Proof.
  intros Hwf H.
  remember (fresh_evar (A $ B $ C)) as x.
  epose proof (prf_equiv_congruence _ _ _
                   {| pcPattern := A $ patt_free_evar x; pcEvar := x |}
                    _ _ _ _ _ H).
  cbn in H0. destruct decide. 2: congruence.
  rewrite free_evar_subst_no_occurrence in H0. shelve.
  rewrite free_evar_subst_no_occurrence in H0. shelve.
  apply pf_iff_proj1 in H0. exact H0.
  Unshelve.
  (* 5 well-formedness goal *)
  1-5: cbn; wf_auto2.
  (* 1 proof info goal *)
  apply pile_any.
  (* 2 free variable constraints *)
  1-2: subst x; solve_fresh.
Defined.

(** Low-level proof, using the iterated congruence lemma + explosion
    in proof size because of MP and the bigger context for
    the congruence lemma *)
Lemma ex2_low3 {Σ : Signature} (A B C D : Pattern) (Γ : Theory) :
  well_formed (A ---> B ---> C ---> D) = true ->
  Γ ⊢ ((B $ C) <---> D) ->
  Γ ⊢ ((A $ (B $ C)) ---> (A $ D)).
Proof.
  intros Hwf H.
  remember (fresh_evar (A $ B $ C $ D)) as x.
  epose proof (prf_equiv_congruence_iter _ _ _
                   {| pcPattern := A $ patt_free_evar x ---> A $ D; pcEvar := x |}
                    [] _ _ _ _ _ _ H).
  cbn in H0. destruct decide. 2: congruence.
  repeat rewrite free_evar_subst_no_occurrence in H0. 1-4: shelve.
  apply pf_iff_proj2 in H0. eapply MP. 2: exact H0.
  gapply A_impl_A.
  Unshelve.
  1,8: try_solve_pile.
  1-7: wf_auto2.
  all: subst x; try solve_fresh.
Defined.

Lemma ex2_low4 {Σ : Signature} (A B C D : Pattern) (Γ : Theory) :
  well_formed (A ---> B ---> C ---> D) = true ->
  Γ ⊢ ((B $ C) <---> D) ->
  Γ ⊢ ((A $ (B $ C)) ---> (A $ D)).
Proof.
  intros Hwf H.
  remember (fresh_evar (A $ B $ C $ D)) as x.
  toMLGoal. wf_auto2.
  epose proof (MLGoal_rewriteIff _ _ _
                   {| pcPattern := A $ patt_free_evar x ---> A $ D; pcEvar := x |}
                    [] _ _ H) as H0.
  cbn in H0. destruct decide. 2: congruence.
  repeat rewrite free_evar_subst_no_occurrence in H0. 1-4: shelve.
  apply H0.
  mlIntro. mlAssumption.
  Unshelve.
  try_solve_pile.
  wf_auto2.
  all: subst x; try solve_fresh.
Defined.

From Coq Require Import ssreflect ssrfun ssrbool.

Open Scope string_scope.
Open Scope list_scope.
Open Scope ml_scope.

(** Proof using proof mode *)
Lemma ex2_pm {Σ : Signature} (A B C D : Pattern) (Γ : Theory) :
  well_formed (A ---> B ---> C ---> D) = true ->
  Γ ⊢ ((B $ C) <---> D) ->
  Γ ⊢ ((A $ (B $ C)) ---> (A $ D))
.
Proof.
  intros Hwf H.
  mlRewrite H at 1.
  mlIntro "H1". mlExact "H1".
Defined.

Lemma ex2_pm2 {Σ : Signature} (A B C D : Pattern) (Γ : Theory) :
  well_formed (A ---> B ---> C ---> D) = true ->
  Γ ⊢ ((B $ C) <---> D) ->
  Γ ⊢ ((A $ (B $ C)) ---> (A $ D))
.
Proof.
  intros Hwf H.
  mlRewrite <- H at 1.
  mlIntro "H1". mlExact "H1".
Defined.

Section compute.
  From MatchingLogic.Theories Require Import Definedness_Syntax
                                             Definedness_Semantics
                                             Sorts_Syntax
                                             Sorts_Semantics
                                             Definedness_ProofSystem.
  Import Definedness_Syntax.Notations.
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
  Open Scope ml_scope.
  Let Z := patt_free_evar "Z".
  Let X := patt_free_evar "X".
  Let Y := patt_free_evar "Y".
  Let sym_even := patt_sym even.
  Let sym_succ := patt_sym Succ.
  Let sym_zero := patt_sym Zero.
  Let sym_tt := patt_sym TT.
  Let sym_ff := patt_sym FF.
  (* axioms *)
  Definition defined : Pattern := Definedness_Syntax.axiom AxDefinedness.

(*   Lemma functional_syms :
    theory ⊢ patt_exists (patt_app sym_succ sym_zero =ml b0).
  Proof.
    subst sym_succ sym_zero.
    unfold patt_equal, patt_total, patt_iff, patt_and.
    Search derives_using patt_exists  patt_defined.
    Search patt_defined patt_total.
    Search patt_imp patt_and. (* 
    pose proof (nimpl_eq_and theory (patt_sym Succ $ patt_sym Zero) b0).
     at 1.
    Search derives_using patt_exists. *)
    eapply MP. instantiate (1 := (ex , patt_sym Succ $ patt_sym Zero =ml b0) ^ [X]).
    2: gapply Ex_quan.
    2-3: shelve.
    unfold instantiate. mlSimpl. simpl.
    
    Search patt_equal derives_using.
    Search patt_free_evar derives_using.
    unfold patt_equal, patt_total, patt_iff, patt_and.
    Search patt_defined patt_or.
    remember (@patt_sym signature Succ $ @patt_sym signature Zero) as A.
    epose proof (nimpl_eq_and theory A X _ _).
    apply useAnyReasoning in H.
    epose proof (not_not_eq theory (! (A ---> X) or ! (X ---> A)) _).
    apply useAnyReasoning in H0.
    mlRewrite H0 at 1. clear H0.
    mlRewrite H at 1.
  Defined. *)

(*   Definition proof2_low : nat := proof_size_info (ex2_low sym_succ sym_succ sym_zero X ∅ ltac:(wf_auto2)).
  Definition proof2_pm : nat := proof_size_info (ex2_low2 ∅ A B ltac:(wf_auto2) ltac:(wf_auto2)).
  Definition proof2_pm2 : nat := proof_size_info (ex2_pm ∅ A B ltac:(wf_auto2) ltac:(wf_auto2)). *)

  Lemma premise :
    ∅ ⊢ Y $ Z <---> Y $ Z.
  Proof.
    gapply pf_iff_equiv_refl.
    apply pile_any.
    wf_auto2.
  Defined.


  Definition proof2_low := ex2_low X Y Z (Y $ Z) ∅ ltac:(wf_auto2) premise.
  Definition proof2_pm := ex2_low2 X Y Z (Y $ Z) ∅ ltac:(wf_auto2) premise.
  Definition proof2_pm2 := ex2_pm X Y Z (Y $ Z) ∅ ltac:(wf_auto2) premise.
  Definition proof2_pm3 := ex2_pm2 X Y Z (Y $ Z) ∅ ltac:(wf_auto2) premise.

  Definition proof2_low3 := ex2_low3 X Y Z (Y $ Z) ∅ ltac:(wf_auto2) premise.
  Definition proof2_low4 := ex2_low4 X Y Z (Y $ Z) ∅ ltac:(wf_auto2) premise.

(* 
  Compute proof_size_info (ex2_low ∅ A B ltac:(wf_auto2) ltac:(wf_auto2)).
  Compute proof_size_info (ex2_pm ∅ A B ltac:(wf_auto2) ltac:(wf_auto2)). *)

End compute.
