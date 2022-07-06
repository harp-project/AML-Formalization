From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Ltac2 Require Import Ltac2.

Require Import Equations.Prop.Equations.

From Coq Require Import String Ensembles Setoid.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.Classical_Prop.
From Coq.Logic Require Import FunctionalExtensionality Eqdep_dec.
From Coq.Classes Require Import Morphisms_Prop.
From Coq.Unicode Require Import Utf8.
From Coq.micromega Require Import Lia.

From MatchingLogic Require Import Syntax NamedAxioms DerivedOperators_Syntax ProofSystem ProofMode IndexManipulation Substitution.
From MatchingLogic.Theories Require Import Definedness_Syntax Definedness_ProofSystem.
From MatchingLogic.Utils Require Import stdpp_ext.

Require Import MatchingLogic.wftactics.

From stdpp Require Import base fin_sets sets propset proof_irrel option list.

Import extralibrary.

Import MatchingLogic.Syntax.Notations.
Import MatchingLogic.DerivedOperators_Syntax.Notations.
Import MatchingLogic.Syntax.BoundVarSugar.
Import MatchingLogic.ProofSystem.Notations.

Set Default Proof Mode "Classic".

Close Scope equations_scope. (* Because of [!] *)

Import Notations.
Open Scope ml_scope.

Section ProofSystemTheorems.
  Context
    {Σ : Signature}
    {syntax : Syntax}.

  Lemma Prop₃_left: forall Γ φ φ',
      theory ⊆ Γ -> mu_free φ ->
      well_formed φ -> well_formed φ' ->
      Γ ⊢ (φ and (φ' =ml φ)) ---> (φ and φ')
      using AnyReasoning.
  Proof.
    intros Γ φ φ' SubTheory Mufree Wf1 Wf2.
    toMyGoal. wf_auto2.
    mgIntro. mgDestructAnd 0.
    mgRewriteBy 1 at 1. auto. wf_auto.
    mgSplitAnd; mgExactn 0.
  Defined.

  Lemma membership_imp_equal :
    forall Γ φ φ',
      theory ⊆ Γ -> mu_free φ' ->
      well_formed φ -> well_formed φ' ->
      Γ ⊢ (ex , (φ =ml b0)) using AnyReasoning ->
      Γ ⊢ (ex , (φ' =ml b0)) using AnyReasoning ->
      Γ ⊢ (φ ∈ml φ') ---> (φ =ml φ') using AnyReasoning .
  Proof.
    intros Γ φ φ' HΓ Mufree Wf1 Wf2 Funφ Funφ'.
    unfold patt_in, patt_equal.
    toMyGoal. wf_auto2.

    (* TODO: proposal: functional_reasoning tactic, which replaces a pattern with a 
                       free variable *)
    epose proof (@forall_functional_subst _ _ (⌈ b0 and φ' ⌉ ---> ⌊ b0 <---> φ' ⌋) φ 
                    Γ HΓ ltac:(wf_auto2) ltac:(wf_auto2) _ ltac:(wf_auto2)) as H.
    Unshelve. 2: { cbn. case_match; auto. apply andb_true_iff in Wf2 as [_ Wf2].
                   apply andb_true_iff in Wf2 as [_ Wf2].
                   (* NOTE: using eapply breaks the proof *)
                   apply well_formed_closed_ex_aux_ind with (ind_evar2 := 1)in Wf2.
                   rewrite Wf2. auto. lia. } (* TODO: this should be auto... *)
    simpl in H.
    repeat rewrite bevar_subst_not_occur in H. wf_auto2. (* TODO: cast_proof? *)
    mgApplyMeta H. clear H.
    mgSplitAnd. 2: fromMyGoal; wf_auto2.
    epose proof (@forall_functional_subst _ _ (all, (⌈ b0 and b1 ⌉ ---> ⌊ b0 <---> b1 ⌋)) φ'
                    Γ HΓ ltac:(wf_auto2) ltac:(wf_auto2) _ ltac:(wf_auto2)) as H.
    Unshelve. 2: { cbn. do 2 case_match; auto; lia. }
    mgApplyMeta H. clear H.

    mgSplitAnd. 2: fromMyGoal; wf_auto2.
    remember (fresh_evar patt_bott) as x.
    remember (fresh_evar (patt_free_evar x)) as y.
    assert (x <> y) as XY.
    { intro. apply x_eq_fresh_impl_x_notin_free_evars in Heqy.
      subst. set_solver. } (* TODO: this should be auto... *)
    fromMyGoal. wf_auto2.


   (* TODO: mgIntro for supporting 'all' *)

    pose proof (@universal_generalization _ Γ (all , (⌈ b0 and patt_free_evar x ⌉ ---> ⌊ b0 <---> patt_free_evar x ⌋)) x AnyReasoning (pile_any _)) as H1.
    simpl in H1.
    case_match; try congruence.
    apply H1.
    { wf_auto2. }
    clear H1.
    pose proof (@universal_generalization _ Γ (⌈ (patt_free_evar y) and (patt_free_evar x) ⌉ ---> ⌊ (patt_free_evar y) <---> (patt_free_evar x) ⌋) y AnyReasoning (pile_any _)) as H1.
    simpl in H1. clear Heqs. do 2 case_match; auto; try congruence.
    2: { clear Heqs Heqs0. congruence.  }
    apply H1.
    { wf_auto2. }
    clear H1.
    now apply defined_variables_equal.
  Defined.

  Lemma functional_pattern_defined :
    forall Γ φ, theory ⊆ Γ -> well_formed φ ->
       Γ ⊢ (ex , (φ =ml b0)) ---> ⌈ φ ⌉
       using AnyReasoning.
  Proof.
    intros Γ φ HΓ Wf.
    toMyGoal. wf_auto2.
    mgIntro.
    mgApplyMeta (@forall_functional_subst _ _ ⌈ b0 ⌉ φ _ HΓ ltac:(wf_auto2)
                 ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2)).
    mgSplitAnd.
    * mgClear 0. fromMyGoal. wf_auto2.
      remember (fresh_evar patt_bott) as x.
      pose proof (@universal_generalization _ Γ ⌈patt_free_evar x⌉ x AnyReasoning (pile_any _)) 
        as H1.
      cbn in H1. case_match. 2: congruence. apply H1. reflexivity.
      gapply defined_evar.
      { apply pile_any. }
      { exact HΓ. }
    * mgExactn 0.
  Defined.

  Lemma equal_imp_membership :
    forall Γ φ φ',
      theory ⊆ Γ -> mu_free φ' ->
      well_formed φ -> well_formed φ' ->
      Γ ⊢ ⌈ φ' ⌉ using AnyReasoning ->
      Γ ⊢ (φ =ml φ') ---> (φ ∈ml φ') using AnyReasoning.
  Proof.
    intros Γ φ φ' HΓ MF WF1 WF2 Def.
    toMyGoal. wf_auto2.
    mgIntro.
    mgRewriteBy 0 at 1; cbn; wf_auto2.
      mgClear 0. unfold patt_in.
      assert (Γ ⊢ ( φ' and φ' <---> φ') using AnyReasoning) as H1.
      {
        toMyGoal. wf_auto2.
        mgSplitAnd; mgIntro.
        - mgDestructAnd 0. mgExactn 0.
        - mgSplitAnd; mgExactn 0.
      }
      now mgRewrite H1 at 1.
  Defined.

  Lemma membership_equal_equal :
    forall Γ φ φ',
      theory ⊆ Γ -> mu_free φ' ->
      well_formed φ -> well_formed φ' ->
      Γ ⊢ (ex , (φ =ml b0)) using AnyReasoning ->
      Γ ⊢ (ex , (φ' =ml b0)) using AnyReasoning ->
      Γ ⊢ (φ ∈ml φ') =ml (φ =ml φ') using AnyReasoning.
  Proof.
    intros Γ φ φ' HΓ Mufree Wf1 Wf2 Func1 Func2.
    unfold patt_equal at 1.

    toMyGoal. wf_auto2.
    mgIntro.
    mgApplyMeta (useAnyReasoning (@bott_not_defined _ _ Γ)).
    fromMyGoal. wf_auto2.
    
    apply ceil_monotonic; auto.
    { apply pile_any. }
    { wf_auto2. }

    toMyGoal. wf_auto2.
    mgApplyMeta (useAnyReasoning (@not_not_intro _ Γ ((φ ∈ml φ' <---> φ =ml φ' ))
                    ltac:(wf_auto2))).
    mgSplitAnd; mgIntro.
    * mgApplyMeta (membership_imp_equal HΓ Mufree Wf1 Wf2 Func1 Func2). mgExactn 0.
    * mgApplyMeta (equal_imp_membership HΓ Mufree Wf1 Wf2 _). mgExactn 0.
      Unshelve.
      toMyGoal. wf_auto2.
      now mgApplyMeta (functional_pattern_defined HΓ Wf2).
  Defined.

  Lemma Prop₃_right : forall Γ φ φ',
      theory ⊆ Γ ->
      well_formed φ -> well_formed φ' -> mu_free φ' ->
      Γ ⊢ (ex , (φ =ml b0)) using AnyReasoning ->
      Γ ⊢ (ex , (φ' =ml b0)) using AnyReasoning ->
      Γ ⊢ (φ and φ') ---> (φ and (φ =ml φ')) using AnyReasoning.
  Proof.
    intros Γ φ φ' HΓ Wf1 Wf2 MF Func1 Func2.
    toMyGoal. wf_auto2.
    mgIntro.
    mgAssert (⌈ φ and φ' ⌉). wf_auto2.
    (* Why can we only mgApplyMeta here, and not after mgRevert? *)
    mgApplyMeta (useAnyReasoning (@phi_impl_defined_phi Σ syntax Γ (φ and φ') HΓ ltac:(wf_auto2))).
    mgExactn 0.
    replace (⌈ φ and φ' ⌉) with (φ ∈ml φ') by auto.
    mgDestructAnd 0. mgSplitAnd.
    * mgExactn 0.
    * mgApplyMeta (membership_imp_equal HΓ MF Wf1 Wf2 Func1 Func2).
      mgExactn 2.
  Defined.

  Corollary delete : forall φ φ' Γ,
    well_formed φ -> well_formed φ'
  ->
    Γ ⊢ φ and φ' =ml φ' ---> φ
    using AnyReasoning.
  Proof.
    intros φ φ' Γ WF1 WF2.
    toMyGoal. wf_auto2.
    mgIntro. mgDestructAnd 0. mgExactn 0.
  Defined.

  Lemma free_evar_subst_id :
    forall φ x, φ.[[evar: x ↦ patt_free_evar x]] = φ.
  Proof.
    induction φ; intros x'; simpl; auto.
    * case_match; subst; auto.
    * rewrite IHφ1. now rewrite IHφ2.
    * rewrite IHφ1. now rewrite IHφ2.
    * now rewrite IHφ.
    * now rewrite IHφ.
  Qed.

  Theorem elimination : forall φ φ' x Γ, x ∉ free_evars φ ->
    theory ⊆ Γ -> mu_free φ ->
    well_formed_closed_ex_aux φ 1 ->
    well_formed_closed_mu_aux φ 0 ->
    well_formed φ' ->
    Γ ⊢ φ.[evar: 0 ↦ patt_free_evar x] and φ' =ml patt_free_evar x ---> 
        φ.[evar: 0 ↦ φ'] and φ' =ml patt_free_evar x
    using AnyReasoning.
  Proof.
    intros φ φ' x Γ NotIn HΓ MF WFp1 WFp2 WF2.
    assert (well_formed (φ.[evar:0↦φ'])) as WFF.
    { wf_auto2. apply bevar_subst_positive; auto.
        now apply mu_free_wfp. }
    assert (well_formed (φ.[evar:0↦patt_free_evar x])) as WFFF. {
      wf_auto2. apply bevar_subst_positive; auto.
        now apply mu_free_wfp. }
    toMyGoal. wf_auto2.
    mgIntro. mgDestructAnd 0. mgSplitAnd. 2: mgExactn 1.
    epose proof (@equality_elimination_basic _ _ Γ φ' (patt_free_evar x)
            {|pcEvar := x; pcPattern := φ.[evar: 0 ↦ patt_free_evar x]|} 
            HΓ WF2 ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2)).
    cbn in H.
    assert (Hwfeaψ': well_formed_closed_ex_aux φ' 0 = true).
    {
      (* TODO this clear should not be necessary *)
      clear - WF2.
      wf_auto2.
    }
    pose proof (@bound_to_free_variable_subst Σ φ x 1 0 φ' ltac:(lia) ltac:(wf_auto2) WFp1 NotIn) as H0.
    unfold evar_open in H0. rewrite <- H0 in H. (* TODO: cast_proof? *)
    rewrite free_evar_subst_id in H.
    assert (Γ ⊢ φ.[evar:0↦φ'] <---> φ.[evar:0↦patt_free_evar x] --->
                φ.[evar:0↦patt_free_evar x] ---> φ.[evar:0↦φ'] using AnyReasoning) as Hiff. {
      toMyGoal; wf_auto2.
      mgIntro. unfold patt_iff. mgDestructAnd 0. mgExactn 1.
    }
    
    apply useAnyReasoning in H.
    epose proof (@syllogism_meta Σ Γ _ _ _ AnyReasoning _ _ _ H Hiff).
    (* TODO: mgApplyMeta buggy?
             Tries to match the longest conclusion, not the shortest *)
    apply reorder_meta in H1.
    mgRevert. mgApplyMeta H1. mgExactn 0.
    Unshelve. all: wf_auto2.
    cbn. rewrite mu_free_bevar_subst; wf_auto2.
  Defined.

  Theorem elimination_reverse : forall φ φ' x Γ, x ∉ free_evars φ ->
    theory ⊆ Γ -> mu_free φ ->
    well_formed_closed_ex_aux φ 1 ->
    well_formed_closed_mu_aux φ 0 ->
    well_formed φ' ->
    Γ ⊢ φ.[evar: 0 ↦ φ'] and φ' =ml patt_free_evar x --->
        φ.[evar: 0 ↦ patt_free_evar x] and φ' =ml patt_free_evar x
    using AnyReasoning.
  Proof.
    intros φ φ' x Γ NotIn HΓ MF WFp1 WFp2 WF2.
    assert (well_formed (φ.[evar:0↦φ'])) as WFF.
    { wf_auto2. apply bevar_subst_positive; auto.
        now apply mu_free_wfp. }
    assert (well_formed (φ.[evar:0↦patt_free_evar x])) as WFFF. {
      wf_auto2. apply bevar_subst_positive; auto.
        now apply mu_free_wfp. }
    toMyGoal. wf_auto2.
    mgIntro. mgDestructAnd 0. mgSplitAnd. 2: mgAssumption.
    epose proof (@equality_elimination_basic _ _ Γ φ' (patt_free_evar x)
            {|pcEvar := x; pcPattern := φ.[evar: 0 ↦ patt_free_evar x]|} 
            HΓ WF2 ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2)).
    cbn in H.
    pose proof (@bound_to_free_variable_subst _ φ x 1 0 φ' ltac:(lia) ltac:(clear -WF2; wf_auto2) WFp1 NotIn) as H0.
    unfold evar_open in H0. rewrite <- H0 in H. (* TODO: cast_proof? *)
    rewrite free_evar_subst_id in H.
    assert (Γ ⊢ φ.[evar:0↦φ'] <---> φ.[evar:0↦patt_free_evar x] --->
                φ.[evar:0↦φ'] ---> φ.[evar:0↦patt_free_evar x] using AnyReasoning) as Hiff. {
      toMyGoal; wf_auto2.
      mgIntro. unfold patt_iff. mgDestructAnd 0. mgExactn 0.
    }
    apply useAnyReasoning in H.
    epose proof (@syllogism_meta _ Γ _ _ _ AnyReasoning _ _ _ H Hiff).
    (* TODO: mgApplyMeta buggy?
             Tries to match the longest conclusion, not the shortest *)
    apply reorder_meta in H1.
    mgRevert. mgApplyMeta H1. mgExactn 0.
    Unshelve. all: wf_auto2.
    cbn. rewrite mu_free_bevar_subst; wf_auto2.
  Defined.




  (**
     Should be a consequence of the injectivity axiom:

      f(x₁,...,xₙ) = f(x₁',...,xₙ') → x₁ = x₁' ∧ ... ∧ xₙ = xₙ'

     The question is, why can we assume this axiom?
  *)
  Definition application_chain (φ : Pattern) (φs : list Pattern) : Pattern :=
    fold_left (fun Acc φ => patt_app Acc φ) φs φ.

  Theorem application_equal : forall φs ψ φ's Γ,
    length φs = length φ's ->
    well_formed ψ -> (* Forall well_formed φs -> Forall well_formed φ's *)
    (forall i, i < length φs -> well_formed (nth i φs ⊥)) ->
    (forall i, i < length φ's -> well_formed (nth i φ's ⊥))
  ->
    Γ ⊢ application_chain ψ φs =ml application_chain ψ φ's --->
         fold_right (fun '(x, y) Acc => Acc and x =ml y) Top (zip φs φ's)
    using AnyReasoning.
  Proof.
    induction φs;
    intros ψ φ's Γ Len WF WFs1 WFs2.
    * apply eq_sym, length_zero_iff_nil in Len. subst. cbn.
      toMyGoal. wf_auto2. mgIntro. mgClear 0. (* TODO: mgExact for meta theorems *)
      fromMyGoal. wf_auto2.
      useBasicReasoning.
      apply (top_holds Γ).
    * destruct φ's. simpl in Len. congruence.
      simpl in Len. inversion Len. clear Len.
      cbn.
      admit.
  Abort.

End ProofSystemTheorems.

Section UnificationProcedure.
  Context {Σ : Signature} {ΣS : Syntax}.

  (* Fixpoint apps_r (C : Application_context) : bool :=
  match C with
   | box => true
   | ctx_app_l cc p => apps_r cc
   | ctx_app_r p cc => false
  end. *)

  (** Based on https://www.cs.bu.edu/fac/snyder/publications/UnifChapter.pdf *)
  Definition Unification_problem : Set := list (Pattern * Pattern) * 
                                          list (evar * Pattern).

  Fixpoint get_apps (p : Pattern) : option (symbols * list Pattern) :=
  match p with
  | patt_app p1 p2 =>
    match get_apps p1 with
    | Some (s, ps) => Some (s, ps ++ [p2])
    | None => None
    end
  | patt_sym s => Some (s, [])
  | _ => None
  end.

  Definition u_remove := remove (prod_eqdec Pattern_eqdec Pattern_eqdec).

  Definition subst_ziplist (x : evar) (p : Pattern) 
    : list (Pattern * Pattern) -> list (Pattern * Pattern) :=
    map (fun '(p1, p2) => ( p1.[[evar: x ↦ p]] , p2.[[evar: x ↦ p]] )).
  Definition subst_list (x : evar) (p : Pattern) 
    : list (evar * Pattern) -> list (evar * Pattern) :=
    map (fun '(y, p2) => ( y , p2.[[evar: x ↦ p]] )).

  Reserved Notation "u ===> u'" (at level 80).
  Inductive unify_step : Unification_problem -> option Unification_problem -> Set :=
  (* trivial/delete *)
  | u_trivial t U S U' :
    (U ++ (t, t)::U', S) ===> Some (U ++ U', S)
  (* decomposition *)
  | u_decompose U U' S t1 t2 f ps ps' :
    get_apps t1 = Some (f, ps) -> get_apps t2 = Some (f, ps') ->
    length ps = length ps'
   ->
    (U ++ (t1, t2)::U', S) ===> Some (zip ps ps' ++ U ++ U', S)
  (* symbol_clash *)
  | u_clash U U' S t1 t2 f g ps ps' :
    get_apps t1 = Some (f, ps) -> get_apps t2 = Some (g, ps') ->
    f <> g
   ->
    (U ++ (t1, t2)::U', S) ===> None
  (* orient *)
  | u_orient U U' S t x:
    (U ++ (t, patt_free_evar x)::U', S) ===> Some (U ++ (patt_free_evar x, t)::U', S)
  (* occurs check *)
  | u_check U U' S x t:
    x ∈ free_evars t ->
    patt_free_evar x <> t
   ->
    (U ++ (t, patt_free_evar x)::U', S) ===> None
  (* elimination *)
  | u_elim U U' S x t:
    x ∉ free_evars t
   ->
    (U ++ (patt_free_evar x, t)::U', S) ===> Some (subst_ziplist x t (U ++ U'), 
                                                   (x, t) :: subst_list x t S)
  where "u ===> u'" := (unify_step u u').

  Definition eq_pats := (fun '(p1, p2) => p1 =ml p2).
  Definition eq_vars := (fun '(x, p2) => patt_free_evar x =ml p2).

  Definition unification_to_pattern (u : Unification_problem) : Pattern :=
    match u with
    | (Us, Ss) => 
        foldr patt_and Top (map eq_pats Us)
        and
        foldr patt_and Top (map eq_vars Ss)
    end.
  Print Unification_problem.
  Definition wf_unification (u : Unification_problem) :=
    wf (map fst u.1) && wf (map snd u.1) && wf (map snd u.2).

(*   Theorem foldr_equiv :
    forall l p l' p0, well_formed p -> well_formed (foldr patt_and p0 l) -> well_formed (foldr patt_and p0 l') ->
    forall Γ, Γ ⊢ foldr patt_and p0 (l ++ p::l') <---> foldr patt_and p0 (p::l ++ l').
  Proof.
    intros l. induction l; intros p l' p0 WFp WFl WFl' Γ.
    * simpl. apply pf_iff_equiv_refl. wf_auto2.
    * simpl.
  Admitted. *)

  Theorem wf_unify_step :
    forall u u' : Unification_problem,
    u ===> Some u' ->
    wf_unification u ->
    wf_unification u'.
  Proof.
    intros u u' D. dependent induction D; intros WF.
    * 
  Admitted.

  Theorem wf_unify_pattern :
    forall u, wf_unification u -> well_formed (unification_to_pattern u).
  Proof.
  Admitted.

  Theorem foldr_last_element :
    forall Γ xs x y,
    well_formed x -> well_formed y -> wf xs ->
    Γ ⊢ foldr patt_and (x and y) xs <--->
    ((foldr patt_and y xs) and x) using AnyReasoning.
  Proof.
    induction xs; intros x y Wf1 Wf2 Wf3; simpl.
    * gapply patt_and_comm; auto. apply pile_any.
    * apply wf_tail' in Wf3 as Wf4.
      specialize (IHxs x y Wf1 Wf2 Wf4).
      unshelve(toMyGoal).
      {
        assert (well_formed a) by now apply andb_true_iff in Wf3.
        apply well_formed_and; apply well_formed_imp;
        repeat apply well_formed_and; auto;
        apply well_formed_foldr_and; wf_auto2.
      }
      mgSplitAnd; mgIntro; mgDestructAnd 0.
      - mgRevert. mgRewrite IHxs at 1. mgIntro. mgDestructAnd 1.
        mgSplitAnd; [mgSplitAnd;mgAssumption|mgAssumption].
      - mgRewrite IHxs at 1. mgDestructAnd 0.
        mgSplitAnd; [mgAssumption|mgSplitAnd;mgAssumption].
    Unshelve.
    
  Admitted.

  Theorem unification_soundness :
    forall u u' : Unification_problem,
    u ===> Some u' ->
    wf_unification u ->
    forall Γ, theory ⊆ Γ -> Γ ⊢ unification_to_pattern u ---> unification_to_pattern u' using AnyReasoning.
  Proof.
    intros u u' D WF.
    assert (wf_unification u') as H.
    { eapply wf_unify_step; eassumption. }
    inversion D; intros Γ HΓ.
    * subst.
      (* TODO: why does toMyGoal simplify??? *)
      (* Opaque unification_to_pattern. *)
      with_strategy opaque [unification_to_pattern] toMyGoal.
      { apply well_formed_imp; apply wf_unify_pattern; auto. }
      (* Transparent unification_to_pattern. *)
      cbn.
      rewrite map_app. simpl map.

      mgIntro. mgDestructAnd 0. mgSplitAnd. 2: mgExactn 1.
      mgClear 1.
      replace (fix app (l m : list Pattern) {struct l} : list Pattern :=
         match l with
         | [] => m
         | a :: l1 => a :: app l1 m
         end) with (@app Pattern) by reflexivity.
      mgRevert.
      rewrite map_app.
      do 2 rewrite foldr_app. Check consume.
      simpl.
      apply wf_unify_pattern in WF. cbn in WF.
      rewrite map_app in WF. rewrite foldr_app in WF.
      simpl in WF.
      remember (foldr patt_and Top (map eq_pats U')) as L1.
      remember (map eq_pats U) as L2.
      epose proof (@foldr_last_element Γ L2 (t =ml t) L1 _ _ _).
      mgRewrite H0 at 1.
      mgIntro. mgDestructAnd 0. mgExactn 0.
    * subst. admit.
    * subst; simpl.
      with_strategy opaque [unification_to_pattern] toMyGoal.
      { apply well_formed_imp. admit. }
      do 2 rewrite map_app. simpl map.
      do 2 rewrite foldr_app. simpl.
      remember (foldr patt_and Top (map eq_pats U')) as L1.
      remember (map eq_pats U) as L2.
      epose proof (@foldr_last_element Γ L2 (t =ml patt_free_evar x) L1 _ _ _).
      mgRewrite H0 at 1.
      epose proof (@foldr_last_element Γ L2 (patt_free_evar x =ml t) L1 _ _ _).
      mgRewrite H1 at 1.
      mgIntro. mgDestructAnd 0. mgDestructAnd 0.
      mgSplitAnd. mgSplitAnd. 1, 3: mgAssumption.
      mgClear 0. mgClear 1.
      mgApplyMeta (@patt_eq_sym _ _ Γ t (patt_free_evar x) _ ltac:(wf_auto2) ltac:(wf_auto2)). mgExactn 0.
    * subst; simpl.
      with_strategy opaque [unification_to_pattern] toMyGoal.
      { apply well_formed_imp. admit. }
      rewrite map_app. simpl map.
      rewrite foldr_app. simpl.
    Unshelve. all: admit.
  Abort.
























(* (*   Axiom f : symbols.
  Compute (get_apps (patt_sym f $ ⊥ $ ⊤ $ ⊥)). *)
  Fixpoint unify_step1 (u : Unification_problem) : option Unification_problem :=
  match u with
  | []           => Some []
  | (t1, t2)::xs =>
    match unify_step1 xs with
    | None => None
    | Some xs' =>
      match decide (t1 = t2) with
      | left _ => Some xs' (* delete *)
      | right _ =>
        match get_apps t1, get_apps t2 with
        | Some (s, ps), Some (s', ps') =>
          match decide (s = s') with
          | left _ => Some (xs' ++ zip ps ps') (* decomposition *)
          | right _ => None (* symbol clash *)
          end
        | _, _ => Some xs'
        end
      end
    end
  end. *)

  Definition is_free_evar (p : Pattern) : bool :=
  match p with
  | patt_free_evar _ => true
  | _ => false
  end.

  Definition swap_if {A : Type} (P : A -> bool) (p : A * A): A * A :=
  match p with
  | (p1, p2) =>
    match P p1, P p2 with
    | true, _ => (p1, p2)
    | _, true => (p2, p1)
    | _, _    => (p1, p2)
    end
  end.

  (* (* orient *)
  Definition unify_step2 (u : Unification_problem) : Unification_problem :=
     map (swap_if is_free_evar) u.

  (* occurs_check *)
  Fixpoint unify_step3 (u : Unification_problem) : option Unification_problem :=
  match u with
  | [] => Some []
  | (p1, p2)::xs =>
    match unify_step3 xs with
    | Some xs' =>
      match p1 with
      | patt_free_evar x =>
        match decide (x ∈ free_evars p2) with
        | left _ => None
        | right _ => Some ((p1, p2)::xs')
        end
      | _ => Some ((p1, p2)::xs')
      end
    | None => None
    end
  end.

  (* 1x elimination *)
  Fixpoint unify_step3 (u : Unification_problem) : Unification_problem :=
  match u with
  | [] => []
  | (patt_free_evar x, p2)::xs => 
  | (p1, p2)::xs => unify_step3 xs
  end. *)

End UnificationProcedure.