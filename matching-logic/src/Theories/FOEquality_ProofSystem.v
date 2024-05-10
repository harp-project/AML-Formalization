From Coq Require Import ssreflect ssrfun ssrbool.

From Ltac2 Require Import Ltac2.

From Coq Require Import String Ensembles Setoid.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.Classical_Prop.
From Coq.Logic Require Import FunctionalExtensionality Eqdep_dec.
From Coq.Classes Require Import Morphisms_Prop.
From Coq.Unicode Require Import Utf8.
From Coq.micromega Require Import Lia.

From MatchingLogic Require Import Logic ProofMode.MLPM.
From MatchingLogic.Theories Require Import Definedness_Syntax Definedness_ProofSystem.
From MatchingLogic.Utils Require Import stdpp_ext.

Require Import MatchingLogic.wftactics.

From stdpp Require Import base fin_sets sets propset proof_irrel option list.

Import extralibrary.

Import MatchingLogic.Logic.Notations.
Import MatchingLogic.Theories.Definedness_Syntax.Notations.

Require Import MatchingLogic.Theories.DeductionTheorem.

Require MatchingLogic.Theories.Sorts_Syntax.
Import MatchingLogic.Theories.Sorts_Syntax.Notations.

Set Default Proof Mode "Classic".

Open Scope ml_scope.
Open Scope string_scope.
Open Scope list_scope.

Lemma membership_imp_equal {Σ : Signature} {syntax : Syntax} Γ φ φ' :
  theory ⊆ Γ -> mu_free φ' ->
  well_formed φ -> well_formed φ' ->
  Γ ⊢ (ex , (φ =ml b0)) --->
      (ex , (φ' =ml b0)) --->
      (φ ∈ml φ') ---> (φ =ml φ').
Proof.
  intros HΓ Mufree Wf1 Wf2.
  toMLGoal. wf_auto2.

  mlIntro "fun0". mlIntro "fun1".
  epose proof (@forall_functional_subst _ _ (⌈ b0 and φ' ⌉ ---> ⌊ b0 <---> φ' ⌋) φ 
                  Γ HΓ ltac:(wf_auto2) ltac:(wf_auto2) _ ltac:(wf_auto2)) as H.
  Unshelve.
  2: wf_auto2.
  mlSimpl in H. simpl in H.
  repeat rewrite bevar_subst_not_occur in H. wf_auto2.
  mlApplyMeta H. clear H.
  mlSplitAnd.
  2: mlExact "fun0".

  (* TODO: proposal: functional_reasoning tactic, which replaces a pattern with a 
                     free variable *)
  epose proof (forall_functional_subst (all, (⌈ b0 and b1 ⌉ ---> ⌊ b0 <---> b1 ⌋)) φ'
                  Γ HΓ ltac:(wf_auto2) ltac:(wf_auto2) _ ltac:(wf_auto2)) as H.
  Unshelve.
  2: wf_auto2.
  mlApplyMeta H. clear H.

  mlSplitAnd.
  2: mlExact "fun1".
  remember (fresh_evar patt_bott) as xx.
  remember (fresh_evar (patt_free_evar xx)) as yy.
  assert (xx <> yy) as XY.
  { solve_fresh_neq. }
  mlClear "fun0". mlClear "fun1".
  fromMLGoal.

  (* TODO: mlIntro for supporting 'all' *)

  pose proof (universal_generalization Γ (all , (⌈ b0 and patt_free_evar xx ⌉ ---> ⌊ b0 <---> patt_free_evar xx ⌋)) xx AnyReasoning (pile_any _)) as H1.
  simpl in H1.
  rewrite decide_eq_same in H1.
  apply H1.
  { wf_auto2. }
  clear H1.
  pose proof (@universal_generalization _ Γ (⌈ (patt_free_evar yy) and (patt_free_evar xx) ⌉ ---> ⌊ (patt_free_evar yy) <---> (patt_free_evar xx) ⌋) yy AnyReasoning (pile_any _)) as H1.
  simpl in H1.
  rewrite decide_eq_same in H1.
  destruct (decide (yy = xx)) eqn:Heqyx;[congruence|].
  apply H1.
  { wf_auto2. }
  clear H1.
  now apply overlapping_variables_equal.
Defined.

Lemma membership_imp_equal_meta {Σ : Signature} {syntax : Syntax} Γ φ φ' :
    theory ⊆ Γ -> mu_free φ' ->
    well_formed φ -> well_formed φ' ->
    Γ ⊢ (ex , (φ =ml b0)) ->
    Γ ⊢ (ex , (φ' =ml b0)) ->
    Γ ⊢ (φ ∈ml φ') ---> (φ =ml φ') .
Proof.
  intros HΓ Mufree Wf1 Wf2 H0 H1.
  toMLGoal.
  { wf_auto2. }
  mlAdd H1 as "H1".
  mlAdd H0 as "H0".
  fromMLGoal.
  apply membership_imp_equal; assumption.
Defined.

Lemma membership_impl_subseteq {Σ : Signature} {syntax : Syntax} Γ g ψ :
  theory ⊆ Γ -> mu_free ψ -> mu_free g ->
  well_formed g -> well_formed ψ ->
  Γ ⊢ (ex , (g =ml b0)) ->
  Γ ⊢ (g ∈ml ψ) ->
  Γ ⊢ (g ⊆ml ψ).
Proof.
  intros HΓ Hmfψ Hmfg wfg wfψ Hfung H.

  apply phi_impl_total_phi_meta.
  { wf_auto2. }
  { apply pile_any. }

  apply membership_elimination with (x := (fresh_evar (g ---> ψ))).
  { solve_fresh. }
  { apply pile_any. }
  { wf_auto2. }
  { set_solver. }

  remember (fresh_evar (b0 ∈ml (g ---> ψ))) as x.

  rewrite <- evar_quantify_evar_open with (phi := b0 ∈ml (g ---> ψ)) (n := 0) (x := x).
  2: {
    subst x.
    eapply evar_is_fresh_in_richer'.
    2: { apply set_evar_fresh_is_fresh'. }
    clear. set_solver.
  }
  2: { cbn. split_and!; try reflexivity; fold well_formed_closed_ex_aux; wf_auto2. }
  apply universal_generalization;[apply pile_any|wf_auto2|].
  mlSimpl. unfold evar_open. simpl.

  rewrite bevar_subst_not_occur.
  { wf_auto2. }
  rewrite bevar_subst_not_occur.
  { wf_auto2. }

  pose proof (Htmp := membership_imp Γ x g ψ).
  ospecialize* Htmp.
  { set_solver. }
  { wf_auto2. }
  { wf_auto2. }
  use AnyReasoning in Htmp.

  toMLGoal.
  { wf_auto2. }
  mlRewrite Htmp at 1. clear Htmp. fold AnyReasoning.

  mlIntro "H".

  pose proof (Htmp := membership_imp_equal_meta Γ (patt_free_evar x) g).
  ospecialize* Htmp.
  { assumption. }
  { assumption. }
  { wf_auto2. }
  { wf_auto2. }
  {
    pose proof (Hex := Ex_quan Γ (patt_free_evar x =ml b0) x).
    ospecialize* Hex.
    { wf_auto2. }
    use AnyReasoning in Hex.
    toMLGoal.
    { wf_auto2. }
    mlApplyMeta Hex. unfold instantiate. mlSimpl. simpl.
    fromMLGoal.
    aapply patt_equal_refl.
    { wf_auto2. }
  }
  { assumption. }

  mlApplyMeta Htmp in "H". clear Htmp.
  mlRevertLast.
  mlRewrite (patt_equal_comm (patt_free_evar x) g Γ HΓ ltac:(wf_auto2) ltac:(wf_auto2)) at 1. fold AnyReasoning.
  mlIntro "H".
  mlApplyMeta (equality_elimination_proj Γ g (patt_free_evar x) (b0 ∈ml ψ)) in "H". mlSimpl. simpl.
  rewrite bevar_subst_not_occur.
  { wf_auto2. }
  rewrite bevar_subst_not_occur.
  { wf_auto2. }
  mlApply "H".
  mlClear "H".
  fromMLGoal.
  assumption.
  { wf_auto2. }
  { wf_auto2. }
  { cbn. split_and!;[assumption|reflexivity|reflexivity]. }
  { assumption. }
Defined.

Theorem exists_functional_subst_meta: ∀ {Σ : Signature} {syntax : Syntax} (Γ : Theory) (φ φ' : Pattern) ,
  Definedness_Syntax.theory ⊆ Γ ->
  mu_free φ ->
  well_formed φ' ->
  well_formed_closed_ex_aux φ 1 ->
  well_formed_closed_mu_aux φ 0 ->
  Γ ⊢ (ex , φ) ^ [φ'] ->
  Γ ⊢ is_functional φ' -> 
  Γ ⊢i (ex , φ) using AnyReasoning.
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

Theorem membership_monotone_functional: ∀ {Σ : Signature} {syntax : Syntax} (Γ : Theory) (φ₁ φ₂  t : Pattern)  (i : ProofInfo),
  Definedness_Syntax.theory ⊆ Γ ->
  well_formed φ₁ ->
  well_formed φ₂ ->
  well_formed t ->
  Γ ⊢i is_functional t using i ->
  Γ ⊢i φ₁ ---> φ₂ using i ->
  Γ ⊢i  t ∈ml φ₁ ---> t ∈ml φ₂ using i .
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
   
 Theorem membership_or_2_functional: ∀ {Σ : Signature} {syntax : Syntax} (Γ : Theory) (φ₁ φ₂ t : Pattern),
  well_formed φ₁ ->
  well_formed φ₂ ->
  well_formed t ->
  Definedness_Syntax.theory ⊆ Γ ->
  Γ ⊢i is_functional t ---> 
  t ∈ml φ₁ or t ∈ml φ₂ --->
  t ∈ml (φ₁ or φ₂) using AnyReasoning.
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
  
Theorem membership_or_2_functional_meta: ∀ {Σ : Signature} {syntax : Syntax} (Γ : Theory) (φ₁ φ₂ t : Pattern),
  well_formed φ₁ ->
  well_formed φ₂ ->
  well_formed t ->
  Definedness_Syntax.theory ⊆ Γ ->
  Γ ⊢i is_functional t using AnyReasoning -> 
  Γ ⊢i t ∈ml φ₁ or t ∈ml φ₂ --->  
  t ∈ml (φ₁ or φ₂) using AnyReasoning.
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
    
Theorem membership_and_2_functional: ∀ {Σ : Signature} {syntax : Syntax} (Γ : Theory)  (φ₁ φ₂ t : Pattern),
  well_formed φ₁ ->
  well_formed φ₂ ->
  mu_free φ₁ ->
  mu_free φ₂ ->
  well_formed t ->
  Definedness_Syntax.theory ⊆ Γ ->
  Γ ⊢i is_functional t ---> 
  t ∈ml φ₁ and  t ∈ml φ₂ --->  
  t ∈ml (φ₁ and φ₂) using AnyReasoning.
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
  
Theorem membership_and_2_functional_meta: ∀ {Σ : Signature} {syntax : Syntax} (Γ : Theory)  (φ₁ φ₂ t : Pattern),
  well_formed φ₁ -> 
  well_formed φ₂ ->
  mu_free φ₁ ->
  mu_free φ₂ ->
  well_formed t ->
  Definedness_Syntax.theory ⊆ Γ ->
  Γ ⊢ is_functional t -> 
  Γ ⊢i t ∈ml φ₁ and  t ∈ml φ₂ ---> 
  t ∈ml (φ₁ and φ₂) using AnyReasoning.
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
  
Theorem  membership_symbol_ceil_aux_0_functional:∀ {Σ : Signature} {syntax : Syntax} (Γ : Theory) (φ t1 t2 : Pattern),
  Definedness_Syntax.theory ⊆ Γ ->
  well_formed φ ->
  mu_free φ ->
  well_formed t1 ->
  well_formed t2 ->
  mu_free t2 ->
  Γ ⊢i is_functional t1 ---> 
  is_functional t2 --->
  ⌈ t1 and φ ⌉ ---> 
  ⌈ t2 and ⌈ t1 and φ ⌉ ⌉ using AnyReasoning.
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
      all: try(case_match; reflexivity).
      all: try(case_match; case_match; reflexivity; case_match; reflexivity) .
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

Theorem proved_membership_functional:
  ∀ {Σ : Signature} {syntax : Definedness_Syntax.Syntax} 
   (Γ : Theory) (φ₁ φ₂ : Pattern),
    Definedness_Syntax.theory ⊆ Γ ->
    well_formed φ₁ ->
    well_formed φ₂ ->
    Γ ⊢i φ₁ using AnyReasoning ->
    Γ ⊢i is_functional φ₂ --->  φ₂ ∈ml φ₁  using AnyReasoning .
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
  remember (fresh_evar(φ₂)) as x.
  mlDestructEx "0" as x.
  mlSimpl. cbn.
  rewrite evar_open_not_occur.
  wf_auto2.
  mlRewriteBy "0" at 1.
  pose proof defined_evar Γ x H.
  use AnyReasoning in H4.
  mlExactMeta H4.
Defined.

Theorem proved_membership_functional_meta:
  ∀ {Σ : Signature} {syntax : Definedness_Syntax.Syntax} 
   (Γ : Theory) (φ₁ φ₂ : Pattern),
    Definedness_Syntax.theory ⊆ Γ ->
    well_formed φ₁ ->
    well_formed φ₂ ->
    Γ ⊢i is_functional φ₂ using AnyReasoning ->
    Γ ⊢i φ₁ using AnyReasoning ->
    Γ ⊢i  φ₂ ∈ml φ₁  using AnyReasoning .
Proof.
  intros.
  mlApplyMeta proved_membership_functional.
  mlExactMeta H2.
  mlExactMeta H3.
  set_solver.
Defined.

Close Scope ml_scope.
Close Scope string_scope.
Close Scope list_scope.