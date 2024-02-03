From Coq Require Import ssreflect ssrfun ssrbool.

From Ltac2 Require Import Ltac2.

From Coq Require Import String Ensembles Setoid.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.Classical_Prop.
From Coq.Logic Require Import FunctionalExtensionality Eqdep_dec.
From Coq.Classes Require Import Morphisms_Prop.
From Coq.Unicode Require Import Utf8.
From Coq.micromega Require Import Lia.

From MatchingLogic Require Export Logic ProofMode.MLPM.
From MatchingLogic.Theories Require Export Definedness_Syntax Definedness_ProofSystem.
From MatchingLogic.Utils Require Export stdpp_ext.

Require Export MatchingLogic.wftactics.

From stdpp Require Import base fin_sets sets propset proof_irrel option list.

Import extralibrary.

Import MatchingLogic.Logic.Notations.
Import MatchingLogic.Theories.Definedness_Syntax.Notations.

Set Default Proof Mode "Classic".

Require Import MatchingLogic.Theories.DeductionTheorem.

Require MatchingLogic.Theories.Sorts_Syntax.
Export MatchingLogic.Theories.Sorts_Syntax.Notations.

From Coq Require Import ssreflect ssrfun ssrbool.

Require Import Setoid.
From Coq Require Import Unicode.Utf8.
From Coq.Logic Require Import Classical_Prop FunctionalExtensionality.
From Coq.Classes Require Import Morphisms_Prop.

From stdpp Require Import base sets.

From MatchingLogic Require Import Logic MLPM.
From MatchingLogic.Theories Require Import Definedness_ProofSystem Sorts_ProofSystem FOEquality_ProofSystem.
Import MatchingLogic.Logic.Notations.
Require Import MatchingLogic.Theories.Nat_Syntax.

Import MatchingLogic.Theories.Definedness_Syntax.Notations.
Import MatchingLogic.Theories.Nat_Syntax.Notations.

Set Default Proof Mode "Classic".

From MatchingLogic Require Import
  Theories.DeductionTheorem
  Theories.Sorts_Syntax
  FOEquality_ProofSystem
  Sorts_ProofSystem
  Nat_Syntax.

Import MatchingLogic.Theories.Sorts_Syntax.Notations.

Open Scope ml_scope.
Open Scope string_scope.
Open Scope list_scope.

  
Section nat.
  Context
    {Σ : Signature}
    {syntax : Nat_Syntax.Syntax}
  .
  
  Theorem forall_functional_subst_meta: 
    ∀ (φ φ' : Pattern) (Γ : Theory),
      Definedness_Syntax.theory ⊆ Γ
        → mu_free φ
          → well_formed φ'
            → well_formed_closed_ex_aux φ 1
              → well_formed_closed_mu_aux φ 0
                -> Γ ⊢ is_functional φ' 
                  → Γ ⊢ (all , φ) -> Γ ⊢i φ^[evar:0↦φ'] using AnyReasoning.
   Proof.
    intros.
    toMLGoal.
    wf_auto2.
    now apply mu_free_wfp.
    mlApplyMeta forall_functional_subst.
    2-5:assumption.
    mlSplitAnd.
    * mlExactMeta H5.
    * unfold is_functional in H4. mlExactMeta H4.
  Defined.
  
  Theorem exists_functional_subst_meta: 
    ∀ (φ φ' : Pattern) (Γ : Theory),
      Definedness_Syntax.theory ⊆ Γ
        → mu_free φ
          → well_formed φ'
            → well_formed_closed_ex_aux φ 1
              → well_formed_closed_mu_aux φ 0
                → Γ  ⊢ (ex , φ) ^ [φ'] 
                  -> Γ ⊢ is_functional φ' 
                    -> Γ ⊢i (ex , φ) using AnyReasoning.
   Proof.
    intros.
    toMLGoal.
    wf_auto2.
    now apply mu_free_wfp. 
    mlApplyMeta exists_functional_subst.
    2-3:assumption.
    2:eauto.
    2-3:assumption.
    mlSplitAnd.
    * mlExactMeta H4.
    * mlExactMeta H5.
  Defined.
  
  Theorem membership_monotone_functional:
    ∀ (Γ : Theory) (φ₁ φ₂  t : Pattern)  (i : ProofInfo),
      Definedness_Syntax.theory ⊆ Γ
        → well_formed φ₁
          → well_formed φ₂
            → well_formed t
              → Γ ⊢i is_functional t using i
                → Γ ⊢i φ₁ ---> φ₂ using i
                  → Γ ⊢i  t ∈ml φ₁ ---> t ∈ml φ₂ using i .
   Proof.
    intros.
    unfold patt_in.
    apply ceil_monotonic.
    1: set_solver.
    1-2: wf_auto2.
    toMLGoal.
    wf_auto2.
    mlIntro "H".
    mlDestructAnd "H" as "H1" "H2".
    mlSplitAnd.
    * mlAssumption.
    * mlApplyMeta H4.
      mlAssumption.
   Defined.
   
  Theorem membership_or_2_functional: 
    ∀ (Γ : Theory) (φ₁ φ₂ t : Pattern),
      well_formed φ₁
        → well_formed φ₂
          → well_formed t
            → Definedness_Syntax.theory ⊆ Γ 
              → Γ ⊢i is_functional t 
                ---> t ∈ml φ₁ or t ∈ml φ₂ 
                  ---> t ∈ml (φ₁ or φ₂) using AnyReasoning.
  Proof.
    intros.
    toMLGoal.
    1: wf_auto2.
    mlIntro "H".
    unfold patt_in.
    epose proof (H3 := prf_prop_or_iff Γ AC_patt_defined ( t and φ₁) (t and φ₂) _ _ ).
    apply pf_iff_proj2 in H3.
    2-3: wf_auto2.
    mlClear "H".
    fromMLGoal.
    eapply syllogism_meta.
    4: gapply H3; try_solve_pile.
    1-3: wf_auto2.
    simpl.
    unshelve (eapply Framing_right).
    { wf_auto2. }
    { unfold BasicReasoning. try_solve_pile. }
    toMLGoal.
    1: wf_auto2.
    mlIntro. mlDestructOr "0".
    - mlDestructAnd "1". unfold patt_and. mlIntro. mlDestructOr "1".
      + mlApply "3". mlExactn 0.
      + mlApply "4". mlLeft. mlExactn 1.
    - mlDestructAnd "2". unfold patt_and. mlIntro. mlDestructOr "2".
      + mlApply "3". mlExactn 0.
      + mlApply "4". mlRight. mlExactn 1.
    Unshelve.
    1-2:wf_auto2.
   Defined.
  
  Theorem membership_or_2_functional_meta: 
    ∀ (Γ : Theory) (φ₁ φ₂ t : Pattern),
      well_formed φ₁
        → well_formed φ₂
          → well_formed t
            → Definedness_Syntax.theory ⊆ Γ
              → Γ ⊢i is_functional t using AnyReasoning 
                → Γ ⊢i t ∈ml φ₁ or t ∈ml φ₂ 
                  ---> t ∈ml (φ₁ or φ₂) using AnyReasoning.
  Proof.
    intros.
    toMLGoal.
    1:wf_auto2.
    mlIntro "H".
    pose proof membership_or_2_functional Γ (φ₁) (φ₂) t .
    ospecialize* H4.
    1-3: wf_auto2.
    set_solver.
    mlAdd H4.
    mlApply "0".
    simpl.
    mlSplitAnd.
    1: mlExactMeta H3.
    mlExact "H".
  Defined.
    
  Theorem unnamed: 
    ∀ {Σ : Signature} (p : Pattern) (x : evar) (n : db_index),
      mu_free p = mu_free (p^{{evar:x↦n}}).
  Proof.
    induction p;
    intros.
    * simpl. case_match. all:reflexivity.
    * simpl. reflexivity.
    * simpl. reflexivity.
    * simpl. reflexivity.
    * simpl. reflexivity.
    * simpl. rewrite <- IHp1. rewrite <- IHp2. reflexivity. 
    * simpl. reflexivity.
    * simpl. rewrite <- IHp1. rewrite <- IHp2. reflexivity.
    * simpl.  rewrite <- IHp.  reflexivity.
    * simpl. reflexivity.
  Defined.
    
  Theorem membership_and_2_functional: 
    ∀ (Γ : Theory)  (φ₁ φ₂ t : Pattern),
      well_formed φ₁
        → well_formed φ₂
          → mu_free φ₁
            → mu_free φ₂
              → well_formed t
                → Definedness_Syntax.theory ⊆ Γ
                  → Γ ⊢i is_functional t ---> t ∈ml φ₁ and  t ∈ml φ₂ 
                    ---> t ∈ml (φ₁ and φ₂) using AnyReasoning.
  Proof.
    intros.
    toMLGoal.
    1: wf_auto2.
    mlIntro "H".
    mlIntro "H1".
    
    remember ( fresh_evar( φ₁ ---> φ₂)  ) as x.
    
    pose proof membership_and_2 Γ x φ₁ φ₂ ltac:(wf_auto2)ltac:(wf_auto2) ltac:(set_solver). 
    
    apply universal_generalization with (x := x) in H5.
    2: try_solve_pile.
    2: wf_auto2. 
    use AnyReasoning in H5.
    mlAdd H5.
    
    mlConj "0" "H" as "H2". mlClear "0".
    mlApplyMeta forall_functional_subst in "H2".
    2:{ simpl. case_match.
        2:congruence. wf_auto2. 
      }
    2:{ simpl. case_match.
        2:congruence. wf_auto2. 
      }
    2:{ simpl. case_match.
        2:congruence. rewrite evar_quantify_fresh.
        1:{ subst x.  unfold evar_is_fresh_in. solve_fresh. }
        rewrite evar_quantify_fresh.
        1:{ subst x.  unfold evar_is_fresh_in. solve_fresh. }
        wf_auto2.
      }
    2:assumption.
    
    mlSimpl. simpl. case_match. 2:congruence.
    mlSimpl. simpl.
    
    rewrite evar_quantify_fresh.
    1:{ subst x.  unfold evar_is_fresh_in. solve_fresh. }
    
    rewrite evar_quantify_fresh.
    1:{ subst x.  unfold evar_is_fresh_in. solve_fresh. }
    
    rewrite bevar_subst_not_occur.
    1:wf_auto2.
    
    rewrite bevar_subst_not_occur.
    1:wf_auto2.
    
    mlApply "H2".
    mlAssumption.
  Defined.
  
  Theorem membership_and_2_functional_meta: 
    ∀ (Γ : Theory)  (φ₁ φ₂ t : Pattern),
      well_formed φ₁
        → well_formed φ₂
          → mu_free φ₁
            → mu_free φ₂
              → well_formed t
                → Definedness_Syntax.theory ⊆ Γ
                  → Γ ⊢ is_functional t 
                    → Γ ⊢i t ∈ml φ₁ and  t ∈ml φ₂ 
                      ---> t ∈ml (φ₁ and φ₂) using AnyReasoning.
  Proof.
    intros.
    toMLGoal.
    1:wf_auto2.
    mlIntro "H".
    epose proof membership_and_2_functional Γ (φ₁) (φ₂) t _ _ _ _ _ _.
    mlAdd H6.
    mlApply "0". simpl.
    mlSplitAnd.
    1:mlExactMeta H5.
    mlAssumption.
    Unshelve.
    1-5: wf_auto2.
    set_solver.
  Defined.
  
  Theorem  membership_symbol_ceil_aux_0_functional:
    ∀ (Γ : Theory) (φ t1 t2 : Pattern),
      Definedness_Syntax.theory ⊆ Γ
        → well_formed φ
          → mu_free φ
            → well_formed t1
              → well_formed t2
                → mu_free t2
                  → Γ ⊢i is_functional t1 ---> is_functional t2 
                    ---> ⌈ t1 and φ ⌉ 
                      ---> ⌈ t2 and ⌈ t1 and φ ⌉ ⌉ using AnyReasoning.
  Proof.
    intros.
    toMLGoal.
    wf_auto2.
    mlIntro. 
    mlIntro.
    mlIntro.
    
    remember (fresh_evar(φ)  ) as x.
    
    remember ( fresh_evar( φ ---> patt_free_evar x ) ) as y.
    
    epose proof membership_symbol_ceil_aux_0 Γ (x) (y) (φ) _ _.
    
    apply universal_generalization with (x := x) in H5.
    2: try_solve_pile.
    2: wf_auto2.
    
    apply universal_generalization with (x := y) in H5.
    2: try_solve_pile.
    2:{ mlSimpl.
        1:{ case_match. all:reflexivity. }
        1:{ case_match. case_match. 1-2:reflexivity.
            case_match. all:reflexivity. }
        1:{ case_match. all:reflexivity. }
        1:{ case_match. all:reflexivity. }
        1:{ case_match. case_match. 1-2:reflexivity.
            case_match. all:reflexivity. }
        1:{ case_match. all:reflexivity. }
        1:{ case_match. all:reflexivity. }
        1:{ case_match. case_match. 1-2:reflexivity.
            case_match. all:reflexivity. }
        1:{ case_match. all:reflexivity. }
      }
    
    mlSimpl in H5. simpl in H5. case_match. 2:congruence.
    case_match.
    * exfalso. apply x_eq_fresh_impl_x_notin_free_evars in Heqy. simpl in *. set_solver.
    * mlSimpl in H5. simpl in H5. case_match. 2:congruence.
      use AnyReasoning in H5.
      mlAdd H5.
    
      mlConj "3" "1" as "f".
      mlApplyMeta forall_functional_subst in "f".
      2-3: wf_auto2.
      2:{ simpl. rewrite evar_quantify_fresh.
          1:{ rewrite evar_quantify_fresh. subst x. unfold evar_is_fresh_in. solve_fresh. 
              subst y. unfold evar_is_fresh_in. solve_fresh. 
            }
          rewrite evar_quantify_fresh. 
          subst x. unfold evar_is_fresh_in. solve_fresh.
          wf_auto2.
        }
      2: set_solver.
      mlSimpl. simpl.
      
      mlConj "f" "0" as "g".
      mlApplyMeta forall_functional_subst in "g".
      2-3: wf_auto2.
      2:{ simpl. rewrite evar_quantify_fresh.
          1:{ rewrite evar_quantify_fresh. 
              subst x. unfold evar_is_fresh_in. solve_fresh. 
              subst y. unfold evar_is_fresh_in. solve_fresh. 
            }
          rewrite evar_quantify_fresh. 
          subst x. unfold evar_is_fresh_in. solve_fresh.
          rewrite bevar_subst_not_occur.
          1: wf_auto2.
          wf_auto2.
        }
      2: set_solver.
      
      mlClear "f";mlClear "3";clear H5.
      mlSimpl. simpl.
   
      rewrite evar_quantify_fresh.
      1:{ rewrite evar_quantify_fresh.
          1:{ subst x.  unfold evar_is_fresh_in. solve_fresh. }  
          1:{ subst y. unfold evar_is_fresh_in. solve_fresh. }
        }
        
      rewrite evar_quantify_fresh.
      1:{ subst x. unfold evar_is_fresh_in. solve_fresh. }
   
      rewrite bevar_subst_not_occur.
      1:{ rewrite bevar_subst_not_occur. all:wf_auto2. }
    
      rewrite bevar_subst_not_occur.
      1: wf_auto2.
      
      rewrite bevar_subst_not_occur.
      1: wf_auto2.
      
      mlApply "g".
      mlAssumption.
      Unshelve. 
      set_solver.
      wf_auto2.
  Defined.
  
  Theorem  provable_iff_top:
    ∀ {Σ : Signature} (Γ : Theory) (φ : Pattern)   (i : ProofInfo),
      well_formed φ
        → Γ ⊢i φ using i
          → Γ ⊢i φ <--->  patt_top using i .
  Proof.
    intros.
    mlSplitAnd.
    2:{ mlIntro. mlExactMeta H0. }
    mlIntro.
    pose proof top_holds Γ.
    use i in H1.
    mlExactMeta H1.
  Defined.
    
  Theorem  patt_and_id_r:
    ∀ {Σ : Signature} (Γ : Theory) (φ : Pattern),
      well_formed φ
        → Γ ⊢i φ and patt_top <--->  φ using BasicReasoning .
  Proof.
    intros.
    mlSplitAnd.
    * mlIntro.
      mlDestructAnd "0".
      mlAssumption.
    * mlIntro.
      mlSplitAnd.
      1: mlAssumption.
      mlIntro.
      mlAssumption.
  Defined.
  
  Theorem  something:
    ∀ {Σ : Signature} {syntax : Definedness_Syntax.Syntax} 
     (Γ : Theory) (φ₁ φ₂ : Pattern)   (i : ProofInfo),
      Definedness_Syntax.theory ⊆ Γ
        → well_formed φ₁
          → well_formed φ₂
            → Γ ⊢i is_functional φ₂ using AnyReasoning
              → Γ ⊢i φ₁ using i
                → Γ ⊢i  φ₂ ∈ml φ₁  using AnyReasoning .
  Proof.
    intros.
    (* toMLGoal.
    wf_auto2. *)
    unfold patt_in.
    apply provable_iff_top in H3.
    2: wf_auto2.
    use AnyReasoning in H3.
    mlRewrite H3 at 1.
    pose proof patt_and_id_r Γ φ₂ ltac:(wf_auto2).
    use AnyReasoning in H4.
    mlRewrite H4 at 1.
    mlAdd H2. mlRevert "0". unfold is_functional.
    mlIntro.
    mlDestructEx "0" as x.
(*     1:admit. *)
    mlSimpl. cbn.
    rewrite evar_open_not_occur.
    1: wf_auto2.
    mlRewriteBy "0" at 1. 
    pose proof defined_evar Γ x H.
    use AnyReasoning in H5.
    mlExactMeta H5.
  Defined.
    
  Theorem  something_v2:
    ∀ {Σ : Signature} {syntax : Definedness_Syntax.Syntax} (Γ : Theory) (φ₁ φ₂ : Pattern),
      Definedness_Syntax.theory ⊆ Γ
        → well_formed φ₁
          → well_formed φ₂
            → Γ ⊢i φ₁ using AnyReasoning
              → Γ ⊢i is_functional φ₂ --->  φ₂ ∈ml φ₁  using AnyReasoning .
  Proof.
    intros.
    unfold patt_in.
    apply provable_iff_top in H2.
    2:wf_auto2.
    mlRewrite H2 at 1.
    pose proof patt_and_id_r Γ φ₂ ltac:(wf_auto2).
    use AnyReasoning in H3.
    mlRewrite H3 at 1.
    unfold is_functional.
    mlIntro.
    mlDestructEx "0" as x.
    mlSimpl. cbn.
    rewrite evar_open_not_occur.
    wf_auto2.
    mlRewriteBy "0" at 1.
    pose proof defined_evar Γ x H.
    use AnyReasoning in H4.
    mlExactMeta H4.
  Defined.
    
  Theorem  something_v3:
    ∀ {Σ : Signature} {syntax : Definedness_Syntax.Syntax} (Γ : Theory) (φ₁ φ₂ : Pattern),
      Definedness_Syntax.theory ⊆ Γ
        → well_formed φ₁
          → well_formed φ₂
            → Γ ⊢i is_functional φ₂ ---> φ₁ using AnyReasoning
              → Γ ⊢i is_functional φ₂ --->  φ₂ ∈ml φ₁  using AnyReasoning .
  Proof.
  Abort.


(* suppose \phi is_functional 
 *)
  Theorem t1:
    ∀ (Γ : Theory) (φ φ' : Pattern) (i : ProofInfo) ,
      Definedness_Syntax.theory ⊆ Γ 
        → well_formed φ
          → well_formed (ex , φ')
            →  Γ ⊢i φ ∈ml (ex, φ')
              --->   φ'^[evar:0↦φ]  using i.
  Proof.
    (* intros.
    mlIntro "H".
    unfold patt_in. *)
(*     ceil_propagation_exists_1:
  ∀ {Σ : Signature} {syntax : Definedness_Syntax.Syntax} (Γ : Theory) (φ : Pattern),
    Definedness_Syntax.theory ⊆ Γ
    → well_formed (ex , φ) → Γ ⊢i ⌈ ex , φ ⌉ ---> (ex , ⌈ φ ⌉) using BasicReasoning
     *)
    (* mlApplyMeta patt_defined_and in "H".
    2-3:admit.
    mlDestructAnd "H".
    mlApplyMeta ceil_propagation_exists_1 in "1".
    2:set_solver. *)
(*     rewrite bevar_subst_positive.
    1:admit.
    Search patt_exists derives_using.
    mlDestructEx "1" as x.
    1:admit.
    Search patt_defined.
    rewrite evar_quantify_fresh. *)
    
(*     Definedness_ProofSystem.test_spec:
  ∀ {Σ : Signature} {syntax : Definedness_Syntax.Syntax} (Γ : Theory) (φ ψ : Pattern),
    Definedness_Syntax.theory ⊆ Γ
    → well_formed (ex , φ)
      → well_formed ψ
        → mu_free φ
          → Γ ⊢i all , φ using AnyReasoning
            → Γ ⊢i ex , ψ =ml b0 using AnyReasoning → Γ ⊢i φ^[evar:0↦ψ] using AnyReasoning
     *)
(*      Unnamed_thm:
  ∀ (Σ : Signature) (syntax : Definedness_Syntax.Syntax) (Γ : Theory) (φ t : Pattern),
    Definedness_Syntax.theory ⊆ Γ
    → mu_free φ
      → well_formed t
        → well_formed (ex , φ)
          → Γ ⊢i (all , φ) ---> (ex , t =ml b0) ---> φ^[evar:0↦t] using AnyReasoning
      *)
(*     mlApplyMeta forall_functional_subst.
    2-6:admit.
    mlSplitAnd.
    * mlIntroAll x.
      1:admit.
      admit.  *)
(*     Search patt_in patt_exists derives_using. *)
  Admitted.

  Lemma use_nat_axiom ax Γ :
    Nat_Syntax.theory ⊆ Γ ->
      Γ ⊢ axiom ax.
  Proof.
    intro HΓ.
    apply useBasicReasoning.
    apply BasicProofSystemLemmas.hypothesis.
    { destruct ax; wf_auto2. }
    {
      apply elem_of_weaken with (X := theory_of_NamedAxioms named_axioms).
      {
        unfold theory_of_NamedAxioms, named_axioms, axiom; simpl.
        apply elem_of_PropSet.
        exists ax.
        reflexivity.
      }
      {
        unfold theory in HΓ.
        set_solver.
      }
    }
  Defined.

  Lemma nat_subset_imp_in X :
    theory ⊢ (〚 Nat 〛 ⊆ml patt_free_svar X) ---> (all Nat, b0 ∈ml patt_free_svar X).
  Proof.
    unfold patt_forall_of_sort.
    unfold patt_in.
    unfold nest_ex; simpl; fold Nat.
    unfold patt_subseteq.
    apply deduction_theorem with (gpi := (ExGen := {[fresh_evar ⊥]}, SVSubst := ∅, KT := false, AKT := false)).
    rewrite <- evar_quantify_evar_open with (n := 0) (phi := (⌈ b0 and 〚 Nat 〛 ⌉ ---> ⌈ b0 and patt_free_svar X ⌉)) (x := fresh_evar ⊥).
    apply universal_generalization.
    { try_solve_pile. }
    { wf_auto2. }
    {
      unfold evar_open.
      mlSimpl.
      simpl.
      apply ceil_monotonic.
      { unfold theory. set_solver. }
      { wf_auto2. }
      { wf_auto2. }
      apply and_weaken.
      { wf_auto2. }
      { wf_auto2. }
      { wf_auto2. }
      apply useBasicReasoning.
      apply BasicProofSystemLemmas.hypothesis.
      { wf_auto2. }
      { clear. set_solver. }
    }
    { clear. set_solver. }
    { wf_auto2. }
    { wf_auto2. }
    { wf_auto2. }
    { unfold theory. set_solver. }
    { set_solver. }
    { set_solver. }
    { set_solver. }
  Defined.
  
  Lemma Svar_subst (Γ : Theory) (ϕ ψ : Pattern) (X : svar)  (i : ProofInfo)
    {pile : ProofInfoLe (
          {| pi_generalized_evars := ∅;
             pi_substituted_svars := {[X]};
             pi_uses_kt := false ;
             pi_uses_advanced_kt := false ;
          |}) i} :
    well_formed ψ 
      -> Γ ⊢i ϕ using i 
        -> Γ ⊢i (ϕ^[[svar: X ↦ ψ]]) using i.
  Proof.
    intros wfψ [pf Hpf].
    unshelve (eexists).
    {
      apply ProofSystem.Svar_subst.
      { pose proof (Hwf := proved_impl_wf _ _ pf). exact Hwf. }
      { exact wfψ. }
      { exact pf. }
    }
    {
      simpl.
      constructor; simpl.
      {
        destruct Hpf as [Hpf2 Hpf3 Hpf4].
        apply Hpf2.
      }
      {
        destruct Hpf as [Hpf2 Hpf3 Hpf4].
        pose proof (Hpile := pile_impl_allows_svsubst_X _ _ _ _ pile).
        clear -Hpile Hpf3.
        set_solver.
      }
      {
        destruct Hpf as [Hpf2 Hpf3 Hpf4].
        exact Hpf4.
      }
      {
        destruct Hpf as [Hpf2 Hpf3 Hpf4 Hpf5].
        exact Hpf5.
      }
    }
  Defined.

  Theorem peano_induction X :
    theory ⊢ patt_free_svar X ⊆ml 〚 Nat 〛 
      ---> Zero ∈ml patt_free_svar X 
        ---> ( all Nat, (b0 ∈ml patt_free_svar X ---> Succ $ b0 ∈ml patt_free_svar X) )
          ---> all Nat, b0 ∈ml patt_free_svar X.
  Proof.
(*     toMLGoal.
    { wf_auto2. }
    
    mlIntro "H".
    mlIntro "H1".
    mlIntro "H2".

    mlApplyMeta nat_subset_imp_in.
    Search patt_mu derives_using.
    Search patt_defined patt_total derives_using.
    
    
    remember (evar_fresh [] ) as x.
    
    
    pose proof membership_symbol_ceil_aux_aux_0 theory x ( patt_free_svar X) 
                                         ltac:( unfold theory;set_solver) ltac:(wf_auto2).
   Check universal_generalization.
   apply universal_generalization with (x:=x) in H.
   2: try_solve_pile.
   2: wf_auto2.
   mlSimpl in H. simpl in H.
   case_match.
   2: congruence.
   Check forall_functional_subst.
   assert ( theory ⊢ (ex , Zero =ml b0) ).
   1:admit.
   Search patt_and derives_using.
   use AnyReasoning in H.
(*    epose proof conj_intro_meta _ _ _ _ _ _ H H1.
   Unshelve.
   2-3: wf_auto2. *)
     mlSpecMeta H with Zero.
     2:unfold theory;set_solver.
     2:simpl;reflexivity.
     mlSimpl in H.
     simpl in H.
     mlApplyMeta H in "H1".
     Search patt_and patt_total.
     unfold patt_forall_of_sort.
     Search patt_exists patt_total derives_using. *)
     
    (* rephrase "H2" into a totality statement and use propagation of totality through conjuction  *)
                                   
  Admitted.  
  
  Theorem peano_induction_1 X :
    theory ⊢ patt_free_svar X ⊆ml 〚 Nat 〛 
    -> theory ⊢ Zero ∈ml patt_free_svar X 
      -> theory ⊢ all Nat, ( b0 ∈ml patt_free_svar X ---> Succ $ b0 ∈ml patt_free_svar X ) 
        -> theory ⊢ all Nat, b0 ∈ml patt_free_svar X.
  Proof.
    intros XN Z S.

    toMLGoal.
    { wf_auto2. }

    mlApplyMeta nat_subset_imp_in.

    mlAdd (use_nat_axiom AxInductiveDomain theory ltac:(reflexivity)) as "ind". unfold axiom.
    mlRewriteBy "ind" at 1.
    { unfold theory. set_solver. }

    mlClear "ind".
    unfold "⊆ml".
    fromMLGoal.

    Check phi_impl_total_phi_meta.
    apply phi_impl_total_phi_meta.
    { wf_auto2. }
    { apply pile_any. }

    apply Knaster_tarski.
    { apply pile_any. }
    { wf_auto2. }
    unfold instantiate. mlSimpl. simpl.
 
    toMLGoal.
    { wf_auto2. }
    mlIntro "H".
    mlDestructOr "H" as "Z0" "S0".
    { (* Base case *)
      mlRevertLast.
      mlApplyMeta total_phi_impl_phi.
      2: instantiate (1 := fresh_evar ⊥); solve_fresh.
      2: { unfold theory. set_solver. }

      fromMLGoal.

      apply membership_impl_subseteq.
      { unfold theory. set_solver. }
      { reflexivity. }
      { reflexivity. }
      { wf_auto2. }
      { wf_auto2. }
      {
        toMLGoal.
        { wf_auto2. }
        mlApplyMeta ex_sort_impl_ex.
        2: { unfold theory. set_solver. }
        mlAdd (use_nat_axiom AxFun1 theory ltac:(reflexivity)) as "f"; unfold axiom.
        mlExact "f".
      }
      assumption.
    }
    { (* Inductive case *)
      fromMLGoal.
      apply membership_elimination with (x := ev_x).
      { solve_free_evars 1. }
      { apply pile_any. }
      { wf_auto2. }
      { unfold theory. set_solver. }

      remember (fresh_evar (b0 ∈ml (Succ $ patt_free_svar X ---> patt_free_svar X))) as x.

      rewrite <- evar_quantify_evar_open with (phi := b0 ∈ml (Succ $ patt_free_svar X ---> patt_free_svar X)) (n := 0) (x := x).
      2:{
          subst x.
          eapply evar_is_fresh_in_richer'.
          2: { apply set_evar_fresh_is_fresh'. }
          clear. set_solver.
        }
      2: { cbn. reflexivity. }
      apply universal_generalization;[apply pile_any|wf_auto2|].
      mlSimpl. unfold evar_open. simpl.

      pose proof (Htmp := membership_imp theory x (Succ $ patt_free_svar X) (patt_free_svar X)).
      ospecialize* Htmp.
      { unfold theory. set_solver. }
      { wf_auto2. }
      { wf_auto2. }
      use AnyReasoning in Htmp.

      toMLGoal.
      { wf_auto2. }

      mlRewrite Htmp at 1. clear Htmp. fold AnyReasoning.

      unfold patt_forall_of_sort, nest_ex in S; simpl in S; fold Nat in S.

      pose proof (Htmp := membership_symbol_right theory (patt_free_svar X) Succ x).
      ospecialize* Htmp.
      { unfold theory. set_solver. }
      { wf_auto2. }
      { wf_auto2. }
      { reflexivity. }
      { reflexivity. }
      mlIntro "H".
      mlApplyMeta Htmp in "H". clear Htmp.

      fromMLGoal.

      remember (fresh_evar (b0 ∈ml patt_free_svar X and patt_free_evar x ∈ml Succ $ b0)) as y.
      rewrite <- evar_quantify_evar_open with (n := 0) (x := y) (phi := b0 ∈ml patt_free_svar X and patt_free_evar x ∈ml Succ $ b0).
      2:{
          subst y. eapply evar_is_fresh_in_richer'.
          2: { apply set_evar_fresh_is_fresh'. }
          clear. set_solver.
        }
      2: wf_auto2.

      gapply BasicProofSystemLemmas.Ex_gen.
      { apply pile_any. }
      { apply pile_any. }
      {
        subst y. eapply evar_is_fresh_in_richer'.
        2: { apply set_evar_fresh_is_fresh'. }
        clear. set_solver.
      }

      mlSimpl. unfold evar_open. simpl. fold AnyReasoning.

      toMLGoal.
      { wf_auto2. }
      mlIntro "H".
      mlDestructAnd "H" as "ys" "H0".

      pose proof (M := membership_imp_equal theory (patt_free_evar x) (Succ $ patt_free_evar y)).
      ospecialize* M.
      { unfold theory. set_solver. }
      { reflexivity. }
      { wf_auto2. }
      { wf_auto2. }

      apply total_phi_impl_phi_meta with (x := fresh_evar ⊥) in XN;
      [|unfold theory; set_solver|set_solver|wf_auto2|apply pile_any].

      mlAdd M as "M". clear M.
      mlApplyMeta and_impl' in "M".
      mlApplyMeta and_impl' in "M".
      mlAssert ("M0" : (patt_free_evar x =ml Succ $ patt_free_evar y)).
      { wf_auto2. }
      {
        mlApply "M". mlClear "M".
        mlSplitAnd. mlSplitAnd.
        + mlClear "ys". mlClear "H0".
          mlApplyMeta BasicProofSystemLemmas.Ex_quan.
          unfold instantiate. mlSimpl. simpl.
          fromMLGoal.
          aapply patt_equal_refl.
          { wf_auto2. }
        + mlApplyMeta ex_sort_impl_ex;[|unfold theory; set_solver].
          mlAdd (use_nat_axiom AxFun2 theory ltac:(set_solver)) as "H". unfold axiom.
          unfold "all _ , _", nest_ex. simpl. fold Nat.
          rewrite <- evar_quantify_evar_open with (x := y) (n := 0) (phi := b0 ∈ml 〚 Nat 〛 ---> (ex Nat , Succ $ b1 =ml b0)).
          2: {
               subst y. eapply evar_is_fresh_in_richer'.
               2: apply set_evar_fresh_is_fresh'.
               clear. set_solver.
             }
          2: wf_auto2.
          mlApplyMeta forall_variable_substitution in "H".
          2-10: case_match;[wf_auto2|congruence].
          unfold evar_open. mlSimpl. simpl.
          case_match. 2: congruence.
          mlApply "H". mlClear "H". mlClear "H0".
          unfold patt_in.
          fromMLGoal.
          aapply ceil_monotonic;[unfold theory; set_solver|wf_auto2|wf_auto2|].
          toMLGoal. wf_auto2.
          mlIntro "yX".
          mlDestructAnd "yX" as "y" "X".
          mlSplitAnd.
          * mlExact "y".
          * mlAdd XN as "H". mlApply "H". mlExact "X". 
        + mlExact "H0".
      }
      mlClear "M".

      mlRewriteBy "M0" at 1;[unfold theory; set_solver|].

      mlClear "M0".

      apply forall_elim with (x := y) in S.
      2: { wf_auto2. }
      unfold evar_open in S. mlSimpl in S. simpl in S.
      mlAdd S as "S". clear S.
      mlApplyMeta and_impl' in "S".
      mlApply "S". mlClear "S".
      mlSplitAnd.
      + mlClear "H0".
        fromMLGoal.
        aapply ceil_monotonic;[unfold theory; set_solver|wf_auto2|wf_auto2|].
        toMLGoal. wf_auto2.
        mlAdd XN as "H".
        mlIntro "yX".
        mlDestructAnd "yX" as "y" "X".
        mlSplitAnd.
        * mlExact "y".
        * mlApply "H". mlExact "X". 
      + mlExact "ys".
    }
  Defined.
  
  Theorem add_zero_r: 
    forall Γ , theory ⊆ Γ 
                -> Γ ⊢ all Nat, b0 +ml Zero =ml b0.
  Proof.
    intros.
    toMLGoal.
    wf_auto2.
    mlIntroAll x.
    unfold nest_ex. mlSimpl. cbn. fold Nat.
    pose proof use_nat_axiom AxDefAddId Γ H.
    simpl in H0. mlAdd H0 as "AddId".
    mlSpecialize "AddId" with x. mlSimpl. cbn.
    mlAssumption.
  Defined.
  
  Theorem add_zero_l: 
    forall Γ , theory ⊆ Γ 
                ->  Γ ⊢ all Nat, Zero +ml b0 =ml b0.
  Proof.
    intros.
    toMLGoal.
    wf_auto2.
    unfold theory in H.
    
    remember (svar_fresh []) as X.
    pose proof peano_induction X.
  
    (*   Ψ ≡ ∃z:Nat.z ∧ ϕ(z)  *)
  
    apply Svar_subst with (X:= X) (ψ:= ex Nat, b0 and Zero +ml b0 =ml b0 )  in H0.
    2:try_solve_pile.
    2:wf_auto2.
    
    apply extend_theory with (Γ':= Γ) in H0.
    2: assumption.
    
    mlAdd H0.
    clear H0.
  
    replace ((_--->_) ^[[svar:X↦ex Nat, b0 and Zero +ml b0 =ml b0]] ) with
    
      ( 
       ( ex Nat, b0 and Zero +ml b0 =ml b0 ) ⊆ml 〚 Nat 〛 ---> Zero ∈ml ( ex Nat, b0 and Zero +ml b0 =ml b0 ) 
        --->
        
       ( all Nat, b0 ∈ml (ex Nat, b0 and Zero +ml b0 =ml b0) 
         ---> Succ $ b0 ∈ml (ex Nat, b0 and Zero +ml b0 =ml b0) 
       ) 
        --->
         
       ( all Nat, b0 ∈ml (ex Nat, b0 and Zero +ml b0 =ml b0) ) 
      ).
       
    2:{ 
        cbn.
        case_match.
        2: congruence.
        reflexivity.
      }
      
    mlAssert ( "H": ( (ex Nat, b0 and Zero +ml b0 =ml b0 ) ⊆ml 〚 Nat 〛 ) ).
    1:wf_auto2.
    1:{ 
        unfold "⊆ml".
        mlClear "0".
        fromMLGoal.
        apply phi_impl_total_phi_meta.
        1:wf_auto2.
        1:apply pile_any.
        
        mlIntro "H".
        mlDestructEx "H" as x. unfold nest_ex. simpl. fold Nat.  mlSimpl. simpl. cbn.
        mlDestructAnd "H".
        
        mlRevert "0".
        
        pose proof use_nat_axiom AxInductiveDomain Γ H. 
        simpl in H0.
        mlAdd H0 as "ind".
        mlRewriteBy "ind" at 1.
      
        mlIntro "H".
      
        mlApplyMeta membership_implies_implication in "H".
        mlRewriteBy "ind" at 1.
        mlApply "H".
        mlDestructAnd "1".
        mlAssumption.
      }
   
    mlAssert ( "H0": ( Zero ∈ml (ex Nat, b0 and Zero +ml b0 =ml b0) )  ).
    1:wf_auto2.
    1:{
        pose proof use_nat_axiom AxInductiveDomain Γ H. 
        simpl in H0.
        mlAdd H0 as "ind".
        mlRevert "H".
        mlRewriteBy "ind" at 1.
        
        mlIntro "H".
        mlClear "0".
        
        unfold patt_exists_of_sort.
        remember (evar_fresh [] ) as x.
        
        epose proof membership_exists_2 Γ (x) (b0 ∈ml 〚 nest_ex Nat 〛 and (b0 and Zero +ml b0 =ml b0))
         ltac:(set_solver) ltac:(wf_auto2).
        unfold nest_ex in *. simpl in *. fold Nat in *.
        
        apply universal_generalization with (x := x ) in H1 .
        2:try_solve_pile.
        2:wf_auto2.
        
        use AnyReasoning in H1.
        apply forall_functional_subst_meta with ( φ' := Zero ) in H1.
        2: set_solver. 
        2:{ 
            simpl. case_match.
            2: congruence.
            reflexivity.
          } 
        2: wf_auto2.
        2:{
            simpl. case_match.
            2: congruence.
            reflexivity.
          }
        2:{
            simpl. case_match.
            2: congruence.
            reflexivity.
          }
        2:{
            mlApplyMeta ex_sort_impl_ex.
            2: set_solver.
            pose proof use_nat_axiom AxFun1 Γ H;simpl in H2;mlAdd H2 as "f";mlExact "f".
          }
          
        mlAdd H1. clear H1.
        mlSimpl. simpl. case_match. 2: congruence.
        
        simpl.
        mlApply "0".
          
        pose proof exists_functional_subst 
         (Zero ∈ml (b0 ∈ml 〚 Nat 〛 and (b0 and Zero +ml b0 =ml b0)))
         (Zero) Γ.
          
        mlApplyMeta H2.
        2-4: wf_auto2.
        2: set_solver.
          
          (* prove separatly is_functional zero  *)
        mlAssert( "P": (is_functional Zero)).
        1: wf_auto2.
        1:{ 
            mlApplyMeta ex_sort_impl_ex.
            2: set_solver.
            pose proof use_nat_axiom AxFun1 Γ H;simpl in H3;mlAdd H3 as "f";mlExact "f".
          }
           
        mlSplitAnd.
        * unfold instantiate. mlSimpl. simpl.
          clear H2.
          mlClear "0";mlClear "ind";mlClear "H".
          
          mlApplyMeta membership_and_2_functional_meta.
          2:{ 
              mlApplyMeta ex_sort_impl_ex.
              2: set_solver.
              pose proof use_nat_axiom AxFun1 Γ H; simpl in H2; mlAdd H2 as "f";mlExact "f".
            }
          2: set_solver.
          2-3: wf_auto2.
 
          mlSplitAnd.
          + assert ( P1: (  Γ ⊢ Zero ∈ml 〚 Nat 〛) ).
            1:{ 
                toMLGoal.
                wf_auto2.
                mlAdd H0 as "ind".
                mlRewriteBy "ind" at 1.
                    
                epose proof membership_monotone_functional Γ 
                 ( (mu , Zero or Succ $ B0) ^ [mu , Zero or Succ $ B0] ) 
                 (mu , Zero or Succ $ B0) (Zero) (AnyReasoning) ltac:(set_solver) ltac:(wf_auto2) 
                  ltac:(wf_auto2) ltac:(wf_auto2) _ .
                    
                pose proof Pre_fixp Γ (Zero or Succ $ B0) ltac:(wf_auto2).
                    
                use AnyReasoning in H3.
                specialize (H2 H3).
                unfold instantiate in H2. mlSimpl in H2. simpl in H2.
                
                mlApplyMeta H2.
                mlApplyMeta membership_or_2_functional_meta.
                2:{ 
                    mlApplyMeta ex_sort_impl_ex.
                    2: set_solver.
                    pose proof use_nat_axiom AxFun1 Γ H; simpl in H4; mlAdd H4 as "f";mlExact "f".
                  }
                2: set_solver.
                 
                mlLeft.
                mlApplyMeta membership_refl.
                2: set_solver.
                mlApplyMeta ex_sort_impl_ex.
                2: set_solver.
                pose proof use_nat_axiom AxFun1 Γ H; simpl in H4; mlAdd H4 as "f";mlExact "f".
              }
              
              epose proof membership_symbol_ceil_aux_0_functional Γ (〚 Nat 〛 ) (Zero) (Zero) ltac:(wf_auto2)
               ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2).
               
              mlApplyMeta H2.
              
              mlSplitAnd.
              1: mlAssumption.
              mlSplitAnd.
              1: mlAssumption.
              mlExactMeta P1.
             
          (* 
            epose proof something Γ ( Zero ∈ml 〚 Nat 〛) Zero (AnyReasoning) ltac:(set_solver) ltac:(wf_auto2) 
             ltac:(wf_auto2) _ P1.
            mlExactMeta H2. *)
          
          + mlApplyMeta membership_and_2_functional_meta.
            2:{ 
                mlApplyMeta ex_sort_impl_ex.
                2: set_solver.
                pose proof use_nat_axiom AxFun1 Γ H; simpl in H2; mlAdd H2 as "f";mlExact "f".
              }
            2: set_solver.
            2-3: wf_auto2.
            
            mlSplitAnd.
            - mlApplyMeta membership_refl.
              2: set_solver.
              mlAssumption.
              
            - assert ( P1: ( Γ ⊢ Zero +ml Zero =ml Zero) ).
              1: { 
                   toMLGoal.
                   wf_auto2.
                   pose proof use_nat_axiom AxDefAddId Γ H. simpl in H2.
                   apply forall_functional_subst_meta with (φ' := Zero) in H2.
                   2: set_solver.
                   2: reflexivity.
                   2-4: wf_auto2.
                   2:{ 
                       mlApplyMeta ex_sort_impl_ex.
                       2: set_solver.
                       pose proof use_nat_axiom AxFun1 Γ H; simpl in H3; mlAdd H3 as "f";mlExact "f".
                     }
                         
                   mlAdd H2.
                   mlSimpl. cbn. 
                   mlApply "0". fold Nat.
                   pose proof use_nat_axiom AxInductiveDomain Γ H.
                   simpl in H3. mlAdd H3 as "ind".
                   mlRewriteBy "ind" at 1.
                    
                   epose proof membership_monotone_functional Γ 
                    ( (mu , Zero or Succ $ B0) ^ [mu , Zero or Succ $ B0] ) 
                    (mu , Zero or Succ $ B0) (Zero) (AnyReasoning) ltac:(set_solver) ltac:(wf_auto2) 
                    ltac:(wf_auto2) ltac:(wf_auto2) _ .
                    
                   pose proof Pre_fixp Γ (Zero or Succ $ B0) ltac:(wf_auto2).
                    
                   use AnyReasoning in H5.
                   specialize (H4 H5).
                   unfold instantiate in H4. mlSimpl in H4. simpl in H4.
                   
                   mlApplyMeta H4.
                   mlApplyMeta membership_or_2_functional_meta.
                   2:{ 
                       mlApplyMeta ex_sort_impl_ex.
                       2: set_solver.
                       pose proof use_nat_axiom AxFun1 Γ H; simpl in H6; mlAdd H6 as "f";mlExact "f".
                     }
                   2: set_solver.
                   
                   mlLeft.
                   mlApplyMeta membership_refl.
                   2: set_solver.
                   mlApplyMeta ex_sort_impl_ex.
                   2: set_solver.
                   pose proof use_nat_axiom AxFun1 Γ H; simpl in H6; mlAdd H6 as "f";mlExact "f".
                 }
                 
              epose proof something Γ (Zero +ml Zero =ml Zero) Zero (AnyReasoning) ltac:(set_solver) 
               ltac:(wf_auto2) ltac:(wf_auto2) _ P1.
              mlExactMeta H2.
      
        * mlAssumption.
      }
(*           
 pose membership_and_2 and universal generalisation into 2, use forall functional substitution
 
    prove that Zero ∈ml [[Nat]] --> this is total ---> it is equivalent to top -> ... ∈ml top (is true)   
    
    from the left side of the current goal
    
*)


(*  for the right hand side ---> use membership_and_2 
- ref in Zero in Zero 
- zero in zero +ml zero =ml zero 

same chain of thoughts as 1st one for totality.

*)

      
    mlAssert ( "H1": (  all Nat, b0 ∈ml (ex Nat, b0 and Zero +ml b0 =ml b0) 
                          ---> Succ $ b0 ∈ml (ex Nat, b0 and Zero +ml b0 =ml b0) 
                     ) ).
    1:wf_auto2.
    1:{ 
        unfold patt_exists_of_sort. 
        mlIntroAll x. simpl. unfold nest_ex. simpl. fold Nat.
        mlIntro "H1".
        mlIntro "H2".
        mlClear "0";mlClear "H";mlClear "H0".
       
        epose proof membership_exists_2 Γ (x) (b0 ∈ml 〚 nest_ex Nat 〛 and (b0 and Zero +ml b0 =ml b0))
         ltac:(set_solver) ltac:(wf_auto2).
       
        apply universal_generalization with (x := x ) in H0 .
        2:try_solve_pile.
        2:wf_auto2.
      
        use AnyReasoning in H0.
        mlSimpl in H0. simpl in H0. case_match. 2: congruence.
      
        mlAssert ( "P" : ( is_functional ( Succ $ patt_free_evar x))).
        1: wf_auto2.
        1:{ 
            unfold is_functional.
            pose proof use_nat_axiom AxFun2 Γ H. simpl in H2.
            mlAdd H2. 
            mlSpecialize "0" with x. mlSimpl. mlSortedSimpl. mlSimpl. cbn.
            mlApplyMeta ex_sort_impl_ex.
            2: set_solver.
            mlApply "0". 
            mlExact "H1". 
          }
        
         mlAdd H0 as "f". clear H0. 
         mlConj "f" "P" as "H3". mlClear "f".
      
        mlApplyMeta forall_functional_subst in "H3".
        2-3: wf_auto2.
        2: reflexivity.
        2: set_solver.
      
        mlSimpl. simpl.
        mlApply "H3". mlClear "H3".
       
        pose proof exists_functional_subst 
         ( (Succ $ patt_free_evar x) ∈ml (b0 ∈ml 〚 Nat 〛 and (b0 and Zero +ml b0 =ml b0)))
         (Succ $ patt_free_evar x) Γ.
       
        mlApplyMeta H0.
        2-3: wf_auto2.
        2: reflexivity.
        2: set_solver.
      
       unfold instantiate. mlSimpl. simpl.
      
       mlSplitAnd.
       * clear H0.
         pose proof t1 Γ (patt_free_evar x ) (b0 ∈ml 〚 Nat 〛 and (b0 and Zero +ml b0 =ml b0)) 
          (AnyReasoning) ltac:(set_solver) ltac:(wf_auto2) ltac:(wf_auto2).
         mlApplyMeta H0 in "H2".
         clear H0.
         mlSimpl. simpl.
         mlDestructAnd "H2".
         mlDestructAnd "1".
         mlClear "0". 
      
         pose proof membership_and_2_functional Γ 
          (Succ $ patt_free_evar x ∈ml 〚 Nat 〛)
          (Succ $ patt_free_evar x and Zero +ml (Succ $ patt_free_evar x) =ml Succ $ patt_free_evar x)
          (Succ $ patt_free_evar x)
          ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2)  ltac:(set_solver).
         
         mlApplyMeta H0. clear H0.
        
          mlSplitAnd.
          1: mlAssumption.
         
          mlSplitAnd.
          - assert ( P2: ( Γ ⊢ patt_free_evar x ∈ml 〚 Nat 〛 ---> Succ $ patt_free_evar x  ∈ml 〚 Nat 〛) ).
                1:{ 
                    mlIntro "H".
                    pose proof use_nat_axiom AxFun2 Γ H. simpl in H0.
                    mlAdd H0. mlSpecialize "0" with x. mlSimpl. mlSortedSimpl. mlSimpl. cbn.
                    mlApply "0" in "H".
                    remember (evar_fresh[x]) as y.
                    mlDestructEx "H" as y.
                    1-3: cbn;pose proof set_evar_fresh_is_fresh'' [x] as S; clear -S; set_solver.
                    mlSimpl. cbn.
                    mlDestructAnd "H". 
                    mlRewriteBy "2" at 1.
                    mlAssumption.
                  }
                  
            mlAssert ( "P1" : (  (Succ $ patt_free_evar x)  ∈ml 〚 Nat 〛 ) ).
            1:{ wf_auto2. }
            1:{      
                mlApplyMeta P2.
                mlAssumption.
              }
            epose proof membership_symbol_ceil_aux_0_functional Γ 
             (〚 Nat 〛) (Succ $ patt_free_evar x) (Succ $ patt_free_evar x) ltac:(wf_auto2)
              ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2) .
            
            mlApplyMeta H0.
            mlSplitAnd.
            1: mlAssumption.
            mlSplitAnd.
            1-2: mlAssumption.
            
          - pose proof membership_and_2_functional Γ 
             (Succ $ patt_free_evar x )
             (Zero +ml (Succ $ patt_free_evar x) =ml Succ $ patt_free_evar x)
             (Succ $ patt_free_evar x)
             ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2) ltac:(set_solver) .
            
            mlApplyMeta H0. clear H0.
            
            mlSplitAnd.
            1: mlAssumption.
           
            mlSplitAnd.
            1:{ 
                mlApplyMeta membership_refl. 
                mlExact "P". 
                set_solver. 
              }
              
            mlAssert ( "P1" : ( (* Γ ⊢ *) Zero +ml (Succ $ patt_free_evar x) =ml Succ $ patt_free_evar x )).
            1: wf_auto2.
               1:{
                   pose proof use_nat_axiom AxDefAdd Γ H.
                   simpl in H0.
                   mlAdd H0. clear H0.
                   mlSpecialize "0" with x.
                   mlSimpl. mlSortedSimpl. mlSimpl.
                   simpl. cbn. 
                   mlApply "H1" in "0". mlClear "0".
                  
                   mlAssert( "P2": (is_functional Zero)).
                   1: wf_auto2.
                   1:{ 
                       mlApplyMeta ex_sort_impl_ex.
                       2: set_solver.
                       pose proof use_nat_axiom AxFun1 Γ H;simpl in H0;mlAdd H0 as "f";mlExact "f".
                     }
                  
                   mlConj "H1" "P2" as "H2".
                   mlClear "H1".
                  
                   mlApplyMeta forall_functional_subst in "H2".
                   2-3: wf_auto2.
                   2: reflexivity.
                   2: set_solver.
                  
                   mlSimpl. simpl.
                   
                   mlRevert "H2".
                   mlRewriteBy "3" at 1.
                   
                   mlIntro "H".
                   mlApply "H". unfold nest_ex. simpl. fold Nat.
                   
                   pose proof use_nat_axiom AxInductiveDomain Γ H. 
                   simpl in H0. mlAdd H0 as "ind". clear H0.
                   mlRewriteBy "ind" at 1.
                   
                   epose proof membership_monotone_functional Γ 
                    ( (mu , Zero or Succ $ B0) ^ [mu , Zero or Succ $ B0] ) 
                    (mu , Zero or Succ $ B0) (Zero) (AnyReasoning) ltac:(set_solver) ltac:(wf_auto2) 
                    ltac:(wf_auto2) ltac:(wf_auto2) _ .
                    
                   pose proof Pre_fixp Γ (Zero or Succ $ B0) ltac:(wf_auto2).
                    
                   use AnyReasoning in H2.
                   specialize (H0 H2).
                   unfold instantiate in H0. mlSimpl in H0. simpl in H0.
                   
                   mlApplyMeta H0.
                   mlApplyMeta membership_or_2_functional_meta.
                   2: { 
                        mlApplyMeta ex_sort_impl_ex.
                        2: set_solver.
                        pose proof use_nat_axiom AxFun1 Γ H; simpl in H3; mlAdd H3 as "f";mlExact "f".
                      }
                   2: set_solver.
                    
                   mlLeft.
                   mlApplyMeta membership_refl.
                   2: set_solver.
                   mlExact "P2". 
                 }
                 
            mlRewriteBy "P1" at 1.
            epose proof something_v2 Γ
             (Succ $ patt_free_evar x =ml Succ $ patt_free_evar x)
             ( Succ $ patt_free_evar x ) ltac:(set_solver) ltac:(wf_auto2) ltac:(wf_auto2). 
            mlApplyMeta H0.
             
            mlAssumption.
            mlReflexivity. 
           
       * mlAssumption.
       Unshelve.
       2,5: set_solver.
       
       1:{ 
           mlApplyMeta ex_sort_impl_ex.
           2: set_solver.
           pose proof use_nat_axiom AxFun1 Γ H;simpl in H2;mlAdd H2 as "f";mlExact "f".
         }
       1:{ 
           mlApplyMeta ex_sort_impl_ex.
           2: set_solver.
           pose proof use_nat_axiom AxFun1 Γ H;simpl in H4;mlAdd H4 as "f";mlExact "f".
         }
       1:{ 
           mlApplyMeta ex_sort_impl_ex.
           2: set_solver.
           pose proof use_nat_axiom AxFun1 Γ H;simpl in H2;mlAdd H2 as "f";mlExact "f".
         }
       1:{ 
           mlApplyMeta ex_sort_impl_ex.
           2: set_solver.
           pose proof use_nat_axiom AxFun1 Γ H;simpl in H0;mlAdd H0 as "f";mlExact "f".
         }
      }
   
    mlApply "0" in "H".
    mlApply "H" in "H0".
    mlApply "H0" in "H1".
    mlClear "0".
    mlClear "H".
    mlClear "H0".
    mlIntroAll x.
 
    mlSpecialize "H1" with x.
    mlSimpl. simpl.
   
    mlSortedSimpl. mlSimpl. cbn. fold Nat.
   
    mlIntro "H".
   
    mlAssert ( "f" : ( patt_free_evar x ∈ml 〚 Nat 〛 )  ).
    1: wf_auto2.
    1: mlExact "H".
     
    mlApply "H1" in "H".
    mlClear "H1".
    unfold patt_exists_of_sort.
    
    pose proof t1 Γ (patt_free_evar x ) (b0 ∈ml 〚 nest_ex Nat 〛 and (b0 and Zero +ml b0 =ml b0))
     (AnyReasoning) ltac:(set_solver) ltac:(wf_auto2) ltac:(wf_auto2).
    mlApplyMeta H0 in "H".
    clear H0.
    
    mlSimpl. simpl.
    mlDestructAnd "H".
    mlDestructAnd "1".
    mlAssumption.
  Defined.
             

End nat.

Close Scope ml_scope.
Close Scope string_scope.
Close Scope list_scope.