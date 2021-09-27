From Coq Require Import ssreflect ssrfun ssrbool.

From Coq Require Import Ensembles Bool.
From MatchingLogic Require Import Syntax Semantics DerivedOperators ProofSystem Helpers.FOL_helpers.

From stdpp Require Import list tactics fin_sets.

From MatchingLogic.Utils Require Import stdpp_ext.

Import extralibrary.

Import
  MatchingLogic.Syntax.Notations
  MatchingLogic.DerivedOperators.Notations
  MatchingLogic.ProofSystem.Notations
.

Open Scope ml_scope.

Ltac reduce_free_evar_subst_step star :=
      match goal with
      | [ |- context ctx [free_evar_subst' ?more ?p ?q star]]
        =>
          rewrite -> (@free_evar_subst_no_occurrence _ more star p q) by (
            apply count_evar_occurrences_0;
            subst star;
            eapply evar_is_fresh_in_richer';
            [|apply set_evar_fresh_is_fresh'];
            simpl; clear; set_solver
          )
      end.

Ltac reduce_free_evar_subst star :=
  unfold free_evar_subst;
  repeat (reduce_free_evar_subst_step star).

Ltac solve_fresh_contradictions star :=
  unfold fresh_evar; simpl;
  match goal with
  | h: star = ?x |- _
    => let hcontra := fresh "Hcontra" in
       assert (hcontra: x <> star) by (unfold fresh_evar; simpl; solve_fresh_neq);
       rewrite -> h in hcontra;
       contradiction
  end.

Ltac clear_obvious_equalities :=
  repeat (
      match goal with
      | [ h: ?x = ?x |- _ ] => clear h
      end
    ).

Ltac simplify_emplace star :=
  unfold emplace;
  simpl;
  unfold free_evar_subst;
  simpl;
  repeat break_match_goal;
  clear_obvious_equalities; try contradiction;
  try (solve_fresh_contradictions star);
  repeat (rewrite nest_ex_aux_0);
  reduce_free_evar_subst star.

Ltac pf_rewrite h :=
  unshelve(
  match type of h with
  | @ML_proof_system ?sigma ?gamma (?l <---> ?r)
    =>
    match goal with
    | [ |- @ML_proof_system ?sigma ?gamma ?pat]
      => idtac "pat: " pat;
      match pat with
      | context ctx [l] =>
          let l' := context ctx [l] in
          idtac "have" l';
          let star := fresh "star" in
          remember (@fresh_evar sigma pat) as star;
            (* Replace the original pattern with its emplace-ed version *)
            let ctxpat := context ctx [(@patt_free_evar sigma star)] in
            let alternative := (eval red in (@emplace sigma (@Build_PatternCtx sigma star ctxpat) l)) in
            replace pat with alternative by (simplify_emplace star; try reflexivity; shelve);

            (* Use the congruence lemma and h *)
            eapply Modus_ponens;
            [(shelve)|(shelve)|idtac|
              (apply pf_iff_proj1;
               [shelve|shelve|
                 (apply prf_equiv_congruence;
                  [shelve|shelve|shelve|
                    (apply pf_iff_equiv_sym;
                     [shelve|shelve|
                       apply h])
            ])])];
            match goal with
            | [ |- @ML_proof_system _ _ ?curpat]
              => let new_pat := context ctx [r] in
                 idtac "new: " new_pat;
                 replace curpat with new_pat by (simplify_emplace star; try reflexivity; shelve)
            end;
            subst star
      (* (*;
        (* replace the emplaced version with the original pattern but with the new value *)
            let alternative' := (eval red in (@emplace sigma (@Build_PatternCtx sigma star ctxpat) r)) in
            let current := context ctx [r] in
            replace alternative' with current;
            [|( simplify_emplace; try reflexivity; shelve)]*) *)
      end
    end
  end).


(* break_match_goal is slow here *)

Local Example ex_prf_rewrite {Σ : Signature} Γ a a' b x:
  well_formed a ->
  well_formed a' ->
  well_formed b ->
  Γ ⊢ a <---> a' ->
  Γ ⊢ (a $ b ---> (patt_free_evar x)) <---> (a' $ b ---> (patt_free_evar x)).
Proof.
  intros wfa wfa' wfb Himp.
  pf_rewrite Himp; auto.  
Abort.

