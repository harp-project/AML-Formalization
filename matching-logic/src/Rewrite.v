From Coq Require Import ssreflect ssrfun ssrbool.

From Ltac2 Require Import Ltac2.
From Coq Require Import Ensembles Bool.
From MatchingLogic Require Import Syntax Semantics DerivedOperators ProofSystem Helpers.FOL_helpers.

From stdpp Require Import list tactics fin_sets.

From MatchingLogic.Utils Require Import stdpp_ext.

Import extralibrary.

From Ltac2 Require Import Message Control.
Ltac2 msg x := print (of_string x).

Import
  MatchingLogic.Syntax.Notations
  MatchingLogic.DerivedOperators.Notations
  MatchingLogic.ProofSystem.Notations
.

Open Scope ml_scope.

Ltac2 pf_rewrite (h : constr) :=
  try(
  match! (Constr.type h) with
  | @ML_proof_system ?sigma ?gamma (?l <---> ?r)
    =>
    msg "got something";
    match! goal with
    | [ |- @ML_proof_system ?sigma ?gamma ?pat]
      => print (of_constr l);
      match! pat with
      | context ctx [?l'] =>
        if (Bool.neg (Constr.equal l l')) then fail else msg "eq";
           msg "matched";
    (*            let my_ctx := (Pattern.instantiate ctx (constr:(patt_bott))) in*)
(*              let my_ctx := (Pattern.instantiate ctx (constr:($r))) in*)
(*       let my_ctx := (Pattern.instantiate
                        ctx
                        (constr:(@patt_free_evar $sigma (@fresh_evar $sigma $pat)))) in *)
        let star := (constr:(@fresh_evar $sigma $pat)) in
        print (of_constr star);
        let ctxpat := (Pattern.instantiate ctx (constr:(@patt_free_evar $sigma $star))) in
        print (of_constr ctxpat);
        let alternative := (constr:(@emplace $sigma (@Build_PatternCtx $sigma $star $ctxpat) $l)) in
        print (of_constr alternative);
        ltac1:(sigma gamma pat new_pat |- replace pat with new_pat)
               (Ltac1.of_constr sigma)
               (Ltac1.of_constr gamma)
               (Ltac1.of_constr pat)
               (Ltac1.of_constr alternative);
        msg "after ltac1"
      end
    end
  end).

Search free_evar_subst'.
Check @well_formed_free_evar_subst.
Check @free_evar_subst_no_occurrence.


Ltac2 reduce_free_evar_subst_step () :=
      match! goal with
      | [ |- context ctx [free_evar_subst' ?more ?p ?q ?x]]
        =>  rewrite (@free_evar_subst_no_occurrence _ $more $x $p $q) >
           [|(rewrite count_evar_occurrences_0 >
              [reflexivity|(
                 eapply evar_is_fresh_in_richer' >
                 [|apply set_evar_fresh_is_fresh'];
               simpl; clear; ltac1:(set_solver)
           )])]
      end.

Ltac2 reduce_free_evar_subst () :=
  unfold free_evar_subst;
  repeat (reduce_free_evar_subst_step ()).


Set Default Proof Mode "Classic".
Local Example ex_prf_rewrite {Σ : Signature} Γ a a' b x:
  well_formed a ->
  well_formed a' ->
  well_formed b ->
  Γ ⊢ a <---> a' ->
  Γ ⊢ (a $ b ---> (patt_free_evar x)) <---> (a' $ b ---> (patt_free_evar x)).
Proof.
  intros wfa wfa' wfb Himp.
  ltac2:(pf_rewrite constr:(Himp)).
  
  2: {
    unfold emplace. simpl.
    unfold free_evar_subst. simpl.
    repeat case_match; try congruence. 2: 
    rewrite ?nest_ex_aux_0. cbn.
    ltac2:(reduce_free_evar_subst ()). reflexivity.
  }
Abort.

