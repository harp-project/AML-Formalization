From MatchingLogic Require Import Logic ProofMode.

From Coq Require Import String.

(** Importing this file opens the necessary scope for the proof mode to work
    properly! *)
Open Scope ml_scope.
Open Scope string_scope.
Open Scope list_scope.

Import
  MatchingLogic.Logic.Notations
  MatchingLogic.DerivedOperators_Syntax.Notations
.

Set Default Proof Mode "Classic".

Lemma reorder_head_to_last {Σ : Signature} (Γ : Theory) :
  ∀ (l : list Pattern) (g x : Pattern) ,
    wf l → well_formed g → well_formed x →
    Γ ⊢i foldr patt_imp g (l ++ [x]) --->  foldr patt_imp g (x :: l)
      using BasicReasoning.
Proof.
  induction l; intros g x Wfl Wfg Wfx.
  - mlIntro "H". mlAssumption.
  - simpl. mlIntro "H". mlIntro "H0". mlIntro "H1".
    mlAssert ("H2" : (foldr patt_imp g (x::l))). wf_auto2.
    {
      mlApplyMeta IHl. mlApply "H". mlAssumption.
    }
    mlApply "H2".  mlAssumption.
Qed.

Lemma reorder_head_to_last_meta {Σ : Signature} (Γ : Theory) :
  forall (l : list Pattern) (g x : Pattern) i,
  wf l → well_formed g → well_formed x
  → Γ ⊢i foldr patt_imp g (l ++ [x]) using i
  → Γ ⊢i foldr patt_imp g (x :: l) using i.
Proof.
  intros l g x i Wfl Wfg Wfx H. eapply MP.
  2: {
    pose proof (reorder_head_to_last Γ l g x) as H0.
    feed specialize H0. 1-3: wf_auto2.
    use i in H0. exact H0. 
  }
  exact H.
Qed.

Lemma propagate_forall {Σ : Signature} (Γ : Theory):
  forall ϕ₁ ϕ₂ x,
  well_formed ϕ₁ ->
  well_formed ϕ₂ ->
  x ∉ free_evars ϕ₁ ->
  Γ ⊢i ((all, (ϕ₁ ---> ϕ₂^{{evar:x↦0}})) ---> (ϕ₁ ---> all, ϕ₂^{{evar:x↦0}}))
    using (ExGen := {[x]}, SVSubst := ∅, KT := false).
Proof.
  intros ϕ₁ ϕ₂ x Wf1 Wf2 Hx. mlIntro "H". mlIntro "H0".
  mlAssert ("H1" : ((all, ϕ₁ ---> ϕ₂^{{evar:x↦0}}) and ϕ₁)). wf_auto2.
  { mlSplitAnd; mlAssumption. }
  mlClear "H". mlClear "H0".
  fromMLGoal.
  apply forall_gen.
  unfold evar_is_fresh_in. cbn.
  pose proof (evar_quantify_no_occurrence ϕ₂ x 0) as H. set_solver.
  try_solve_pile.
  mlIntro "H".
  mlDestructAnd "H".
  pose proof (forall_variable_substitution Γ (ϕ₁ ---> ϕ₂) x ltac:(wf_auto2)) as H0.
  simpl in H0.
  rewrite (evar_quantify_fresh _ _ ϕ₁) in H0.
  2: by unfold evar_is_fresh_in.
  mlRevertLast.
  mlApplyMeta H0. mlAssumption.
Qed.

Lemma universal_generalization_iter {Σ : Signature} (Γ : Theory):
  forall (l : list Pattern) (ϕ : Pattern) x i,
  wf l ->
  well_formed ϕ ->
  x ∉ free_evars (foldr patt_imp patt_bott l) ->
  ProofInfoLe (ExGen := {[x]}, SVSubst := ∅, KT := false) i ->
  Γ ⊢i foldr patt_imp ϕ l using i ->
  Γ ⊢i foldr patt_imp (all , ϕ^{{evar: x ↦ 0}}) l using i.
Proof.
  induction l; intros ϕ x i Wfl Wfϕ Hx Hle H.
  - by apply universal_generalization.
  - apply reorder_last_to_head_meta in H. 2-4: wf_auto2.
    rewrite foldr_snoc in H. apply (IHl _ x) in H. 2-3: wf_auto2.
    2: { simpl in Hx. set_solver. }
    simpl in H. rewrite evar_quantify_fresh in H.
    2: { unfold evar_is_fresh_in. set_solver. }
    eapply prf_weaken_conclusion_iter_meta_meta in H.
    5: gapply propagate_forall.
    5,9: try_solve_pile.
    2-7: try by wf_auto2.
    2: simpl in Hx; set_solver.
    apply reorder_head_to_last_meta. 1-3: wf_auto2.
    by rewrite foldr_snoc.
Qed.

Lemma MLGoal_forallIntro {Σ:Signature} Γ l g (x : evar) i :
  x ∉ free_evars (foldr patt_imp patt_bott (patterns_of l)) ->
  x ∉ free_evars g ->
  ProofInfoLe (ExGen := {[x]}, SVSubst := ∅, KT := false) i ->
  mkMLGoal _ Γ l (g^{evar: 0 ↦ x}) i ->
  mkMLGoal _ Γ l (all, g) i.
Proof.
  unfold of_MLGoal in *. simpl in *. intros Hx1 Hx2 Hi H Hwf1 Hwfl.
  rewrite <- (evar_quantify_evar_open x 0 g). 3: wf_auto2. 2: assumption.
  apply universal_generalization_iter. 1-2: wf_auto2.
  assumption. try_solve_pile.
  apply H; wf_auto2. 
Qed.

Tactic Notation "mlIntroAll" constr(x) :=
_ensureProofMode;
apply (MLGoal_forallIntro _ _ _ x);
[   try subst x; try solve_fresh
  | try subst x; try solve_fresh
  | try subst x; try_solve_pile
  | unfold evar_open; mlSimpl; repeat rewrite bevar_subst_not_occur by wf_auto2
].


Local Example Forall_test {Σ : Signature} Γ ϕ:
  well_formed ϕ ->
  Γ ⊢ all , (ϕ ---> ϕ and ϕ).
Proof.
  intro.
  toMLGoal. wf_auto2.
  mlIntroAll (fresh_evar ϕ).
  mlIntro "A". mlSplitAnd; mlAssumption.
Qed.

Lemma revert_forall_iter {Σ : Signature} (Γ : Theory) :
  forall (l : list Pattern) (ϕ : Pattern) x,
  wf l ->
  well_formed ϕ ->
  Γ ⊢i foldr patt_imp (all , ϕ^{{evar: x ↦ 0}}) l ---> foldr patt_imp ϕ l
    using (ExGen := {[x]}, SVSubst := ∅, KT := false).
Proof.
  intros l ϕ x Wfl Wfϕ. apply prf_weaken_conclusion_iter_meta. 1-3: wf_auto2.
  apply forall_variable_substitution. wf_auto2.
Qed.

Lemma revert_forall_iter_meta {Σ : Signature} (Γ : Theory) :
  forall (l : list Pattern) (ϕ : Pattern) x i,
  wf l ->
  well_formed ϕ ->
  ProofInfoLe (ExGen := {[x]}, SVSubst := ∅, KT := false) i ->
  Γ ⊢i foldr patt_imp (all , ϕ^{{evar: x ↦ 0}}) l using i ->
  Γ ⊢i foldr patt_imp ϕ l using i.
Proof.
  intros l ϕ x i Wfl Wfϕ Hi H.
  eapply MP. 2: gapply revert_forall_iter. 3-4: wf_auto2. 2: try_solve_pile.
  exact H.
Qed.

Lemma MLGoal_revertAll {Σ:Signature} Γ l g (x : evar) i :
  ProofInfoLe (ExGen := {[x]}, SVSubst := ∅, KT := false) i ->
  mkMLGoal _ Γ l (all, g^{{evar:x ↦ 0}}) i ->
  mkMLGoal _ Γ l g i.
Proof.
  unfold of_MLGoal in *. simpl in *. intros Hi H Hwf1 Hwfl.
  apply (revert_forall_iter_meta Γ _ _ x). 1-2: wf_auto2. try_solve_pile.
  apply H; wf_auto2.
Qed.

Tactic Notation "mlRevertAll" constr(x) :=
  _ensureProofMode;
  apply (MLGoal_revertAll _ _ _ x);[try_solve_pile|].

Local Example forall_revert_1 {Σ : Signature} Γ ϕ ψ x:
  well_formed ϕ -> well_formed (ex, ψ) ->
  x ∉ free_evars ϕ ->
  x ∉ free_evars ψ ->
  Γ ⊢ (ϕ ---> all, ψ) ->
  Γ ⊢ ϕ ---> ψ^{evar:0 ↦ x}.
Proof.
  intros.
  toMLGoal. wf_auto2.
  mlIntro. mlRevertAll x.
  rewrite evar_quantify_evar_open. 3: wf_auto2. 2: assumption.
  by fromMLGoal.
Qed.

Local Example forall_revert_2 {Σ : Signature} Γ ϕ ψ:
  well_formed ϕ -> well_formed (ex, ψ) ->
  Γ ⊢ (ϕ ---> all, ψ) ->
  Γ ⊢ all, ϕ ---> ψ.
Proof.
  intros.
  remember (fresh_evar (ψ $ ϕ)) as x.
  toMLGoal. wf_auto2.
  mlIntroAll x.
  mlIntro. mlRevertAll x.
  fold (evar_open x 0 ψ).
  rewrite evar_quantify_evar_open. 2: subst x; solve_fresh.
  2: wf_auto2.
  by fromMLGoal.
Qed.


(* Iterated congruence lemma proved without induction *)
Lemma prf_equiv_congruence_iter_no_ind {Σ : Signature} (Γ : Theory) (p q : Pattern) (C : PatternCtx) l
  (wfp : well_formed p)
  (wfq : well_formed q)
  (wfC : PC_wf C)
  (VarsC : pcEvar C ∉ free_evars_of_list l)
  (gpi : ProofInfo)
  (pile : ProofInfoLe
    (ExGen := list_to_set (evar_fresh_seq (free_evars (foldr patt_imp (pcPattern C) l) ∪ free_evars p ∪ free_evars q ∪ {[pcEvar C]}) (maximal_exists_depth_to 0 (pcEvar C) (pcPattern C))),
     SVSubst := list_to_set (svar_fresh_seq (free_svars (foldr patt_imp (pcPattern C) l) ∪
                free_svars p ∪ free_svars q) (maximal_mu_depth_to 0 (pcEvar C) (pcPattern C))),
     KT := mu_in_evar_path (pcEvar C) (pcPattern C) 0
    )
    gpi
  ):
  Pattern.wf l ->
  Γ ⊢i p <---> q using ( gpi) ->
  Γ ⊢i (foldr patt_imp (emplace C p) l) <---> (foldr patt_imp (emplace C q) l) using  gpi.
Proof.
  intros wfl Himp.
  rewrite -> fresh_foldr_is_context. 2: assumption.
  rewrite -> fresh_foldr_is_context. 2: assumption.
  
  eapply eq_prf_equiv_congruence with
    (edepth := 0) (sdepth := 0)
    (el := evar_fresh_seq
    (free_evars (foldr patt_imp (pcPattern C) l)
     ∪
     free_evars p ∪ free_evars q ∪ {[pcEvar C]})
    (maximal_exists_depth_to 0 (pcEvar C) (foldr patt_imp (pcPattern C) l)))
    (sl := svar_fresh_seq (free_svars (foldr patt_imp (pcPattern C) l) ∪
    free_svars p ∪ free_svars q) (maximal_mu_depth_to 0 (pcEvar C) (foldr patt_imp (pcPattern C) l)))
    (evs := list_to_set (evar_fresh_seq
    (free_evars (foldr patt_imp (pcPattern C) l)
     ∪ free_evars p ∪ free_evars q ∪ {[pcEvar C]})
    (maximal_exists_depth_to 0 (pcEvar C) (foldr patt_imp (pcPattern C) l))))
    (svs := list_to_set (svar_fresh_seq (free_svars (foldr patt_imp (pcPattern C) l) ∪
    free_svars p ∪ free_svars q) (maximal_mu_depth_to 0 (pcEvar C) (foldr patt_imp (pcPattern C) l))));
  auto; simpl.
  wf_auto2. 1-3: unfold PC_wf in wfC; wf_auto2.
  {
    apply evar_fresh_seq_correct.
  }
  {
    rewrite evar_fresh_seq_length. lia.
  }
  {
    intros. set_solver.
  }
  {
    apply svar_fresh_seq_correct.
  }
  { 
    rewrite svar_fresh_seq_length. lia.
  }
  {
    intros. set_solver.
  }
  { 
    destruct pile as [HEV [HSV HKT] ].
    constructor; simpl in *. 2: constructor; simpl in *.
    {
      clear -HEV VarsC.
      rewrite (maximal_exists_depth_foldr_notin); assumption.
    }
    {
      clear -HSV VarsC.
      rewrite (maximal_mu_depth_foldr_notin); assumption.
      
    }
    {
      clear -HKT VarsC.
      unfold mu_in_evar_path.
      rewrite (maximal_mu_depth_foldr_notin); assumption.
    }
  }
Defined.

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
       symbols := Symbols ;
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

(* rewrite example *)
Lemma ex2_pm1 {Σ : Signature} (A B C D : Pattern) (Γ : Theory) :
  well_formed (A ---> B ---> C ---> D) = true ->
  Γ ⊢ ((B $ C) <---> D) ->
  Γ ⊢ A ---> ((A $ (B $ C)) ---> (A $ D))
.
Proof.
  intros Hwf H.
  mlIntro "H".
  mlRewrite H at 1.
  mlIntro "H1". mlExact "H1".
Defined.

(* example with the induction-based iterated congruence lemma for a smaller context *)
Lemma ex2_pm2 {Σ : Signature} (A B C D : Pattern) (Γ : Theory) :
  well_formed (A ---> B ---> C ---> D) = true ->
  Γ ⊢ ((B $ C) <---> D) ->
  Γ ⊢ A ---> ((A $ (B $ C)) ---> (A $ D))
.
Proof.
  intros Hwf H.
  remember (patt_free_evar (fresh_evar (A $ B $ C $ D))) as x.
  pose proof (prf_equiv_congruence_iter Γ (B $ C) D {|pcPattern := A $ x; pcEvar := (fresh_evar (A $ B $ C $ D))|} [A] ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2) AnyReasoning ltac:(try_solve_pile) ltac:(wf_auto2) H).
  subst x.
  cbn in H0. destruct decide. 2: congruence.
  do 2 rewrite free_evar_subst_no_occurrence in H0. 2-4: solve_fresh.
  apply pf_iff_proj1 in H0. 2-3: wf_auto2.
  do 2 mlIntro. mlApplyMeta H0. mlSplitAnd.
  - mlIntro. mlAssumption.
  - mlAssumption.
Defined.

(* example with the complex context-based iterated congruence lemma for a smaller context *)
Lemma ex2_pm3 {Σ : Signature} (A B C D : Pattern) (Γ : Theory) :
  well_formed (A ---> B ---> C ---> D) = true ->
  Γ ⊢ ((B $ C) <---> D) ->
  Γ ⊢ A ---> ((A $ (B $ C)) ---> (A $ D))
.
Proof.
  intros Hwf H.
  remember (patt_free_evar (fresh_evar (A $ B $ C $ D))) as x.
  pose proof (prf_equiv_congruence_iter_no_ind Γ (B $ C) D {|pcPattern := A $ x; pcEvar := (fresh_evar (A $ B $ C $ D))|} [A] ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2) ltac:(solve_fresh) AnyReasoning ltac:(try_solve_pile) ltac:(wf_auto2) H).
  subst x.
  cbn in H0. destruct decide. 2: congruence.
  do 2 rewrite free_evar_subst_no_occurrence in H0. 2-4: solve_fresh.
  apply pf_iff_proj1 in H0. 2-3: wf_auto2.
  do 2 mlIntro. mlApplyMeta H0. mlSplitAnd.
  - mlIntro. mlAssumption.
  - mlAssumption.
Defined.

(* example with the congruence lemma for a smaller context *)
Lemma ex2_pm4 {Σ : Signature} (A B C D : Pattern) (Γ : Theory) :
  well_formed (A ---> B ---> C ---> D) = true ->
  Γ ⊢ ((B $ C) <---> D) ->
  Γ ⊢ A ---> ((A $ (B $ C)) ---> (A $ D))
.
Proof.
  intros Hwf H.
  remember (patt_free_evar (fresh_evar (A $ B $ C $ D))) as x.
  pose proof (prf_equiv_congruence Γ (B $ C) D {|pcPattern := A ---> A $ x; pcEvar := (fresh_evar (A $ B $ C $ D))|} AnyReasoning ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2)
  ltac:(try_solve_pile) H).
  subst x.
  cbn in H0. destruct decide. 2: congruence.
  do 2 rewrite free_evar_subst_no_occurrence in H0. 2-4: solve_fresh.
  apply pf_iff_proj1 in H0. 2-3: wf_auto2.
  do 2 mlIntro. mlApplyMeta H0. mlSplitAnd.
  - mlIntro. mlAssumption.
  - mlAssumption.
Defined.










(* These should reflect the idea of mlRewrite: *)
(* Numbers should be similar as for mlRewrite *)
(* example with the induction-based iterated congruence lemma for a bigger context *)
Lemma ex3_pm2 {Σ : Signature} (A B C D : Pattern) (Γ : Theory) :
  well_formed (A ---> B ---> C ---> D) = true ->
  Γ ⊢ ((B $ C) <---> D) ->
  Γ ⊢ A ---> ((A $ (B $ C)) ---> (A $ D))
.
Proof.
  intros Hwf H.
  remember (patt_free_evar (fresh_evar (A $ B $ C $ D))) as x.
  pose proof (prf_equiv_congruence_iter Γ (B $ C) D {|pcPattern := A $ x ---> A $ D; pcEvar := (fresh_evar (A $ B $ C $ D))|} [A] ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2) AnyReasoning ltac:(try_solve_pile) ltac:(wf_auto2) H).
  subst x.
  cbn in H0. destruct decide. 2: congruence.
  do 4 rewrite free_evar_subst_no_occurrence in H0. 2-16: solve_fresh.
  apply pf_iff_proj2 in H0. 2-3: wf_auto2.
  remember (A ---> A $ B $ C ---> A $ D) as AA.
  remember (A ---> A $ D ---> A $ D ) as BB.
  mlApplyMeta H0. subst BB.
  do 2 mlIntro. mlExact "1".
Defined.

(* example with the complex context-based iterated congruence lemma for a bigger context *)
Lemma ex3_pm3 {Σ : Signature} (A B C D : Pattern) (Γ : Theory) :
  well_formed (A ---> B ---> C ---> D) = true ->
  Γ ⊢ ((B $ C) <---> D) ->
  Γ ⊢ A ---> ((A $ (B $ C)) ---> (A $ D))
.
Proof.
  intros Hwf H.
  remember (patt_free_evar (fresh_evar (A $ B $ C $ D))) as x.
  pose proof (prf_equiv_congruence_iter_no_ind Γ (B $ C) D {|pcPattern := A $ x ---> A $ D; pcEvar := (fresh_evar (A $ B $ C $ D))|} [A] ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2) ltac:(solve_fresh) AnyReasoning ltac:(try_solve_pile) ltac:(wf_auto2) H).
  subst x.
  cbn in H0. destruct decide. 2: congruence.
  do 4 rewrite free_evar_subst_no_occurrence in H0. 2-16: solve_fresh.
  apply pf_iff_proj2 in H0. 2-3: wf_auto2.
  remember (A ---> A $ B $ C ---> A $ D) as AA.
  remember (A ---> A $ D ---> A $ D ) as BB.
  mlApplyMeta H0. subst BB.
  do 2 mlIntro. mlExact "1".
Defined.

(* Numbers should be similar as for mlRewrite *)
(* example with the congruence lemma for a big context *)
Lemma ex3_pm4 {Σ : Signature} (A B C D : Pattern) (Γ : Theory) :
  well_formed (A ---> B ---> C ---> D) = true ->
  Γ ⊢ ((B $ C) <---> D) ->
  Γ ⊢ A ---> ((A $ (B $ C)) ---> (A $ D))
.
Proof.
  intros Hwf H.
  remember (patt_free_evar (fresh_evar (A $ B $ C $ D))) as x.
  pose proof (prf_equiv_congruence Γ (B $ C) D {|pcPattern := A ---> A $ x ---> A $ D; pcEvar := (fresh_evar (A $ B $ C $ D))|} AnyReasoning ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2)
  ltac:(try_solve_pile) H).
  subst x.
  cbn in H0. destruct decide. 2: congruence.
  do 4 rewrite free_evar_subst_no_occurrence in H0. 2-16: solve_fresh.
  apply pf_iff_proj2 in H0. 2-3: wf_auto2.
  remember (A ---> A $ B $ C ---> A $ D) as AA.
  remember (A ---> A $ D ---> A $ D ) as BB.
  mlApplyMeta H0. subst BB.
  do 2 mlIntro. mlExact "1".
Defined.


Lemma premise :
∅ ⊢ Y $ Z <---> Y $ Z.
Proof.
gapply pf_iff_equiv_refl.
apply pile_any.
wf_auto2.
Defined.

Definition proof_pm1 : nat := proof_size_info (ex2_pm1 X Y Z (Y $ Z) ∅ ltac:(wf_auto2) premise).
Definition proof_pm2 : nat := proof_size_info (ex2_pm2 X Y Z (Y $ Z) ∅ ltac:(wf_auto2) premise).
Definition proof_pm3 : nat := proof_size_info (ex2_pm3 X Y Z (Y $ Z) ∅ ltac:(wf_auto2) premise).
Definition proof_pm4 : nat := proof_size_info (ex2_pm4 X Y Z (Y $ Z) ∅ ltac:(wf_auto2) premise).

Definition proof2_pm2 : nat := proof_size_info (ex3_pm2 X Y Z (Y $ Z) ∅ ltac:(wf_auto2) premise).
Definition proof2_pm3 : nat := proof_size_info (ex3_pm3 X Y Z (Y $ Z) ∅ ltac:(wf_auto2) premise).
Definition proof2_pm4 : nat := proof_size_info (ex3_pm4 X Y Z (Y $ Z) ∅ ltac:(wf_auto2) premise).

End compute.
(*
Extraction Language Haskell.

From Coq Require Extraction.
Require Import ExtrHaskellBasic.
Require Import ExtrHaskellString.
Extraction "Test.hs" proof_pm1 proof_pm3  proof_pm2  proof_pm4
                               proof2_pm3 proof2_pm2 proof2_pm4.
*)