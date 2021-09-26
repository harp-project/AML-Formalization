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


(*
Ltac2 pf_rewrite (h : constr) :=
  try(
  match! goal with
    | [ |- @ML_proof_system ?sigma ?gamma ?pat]
    =>
    match! (Constr.type h), pat with
    | ((@ML_proof_system ?sigma ?gamma (?l <---> ?r)), (context ctx [?l]))
        =>
        msg "got something"
  end
end).
      => print (of_constr l);
      match! pat with
      | context ctx [?my] =>
        msg "matched"; print (of_constr r);
        ltac1:(pat |- replace pat with patt_bott) (Ltac1.of_constr (goal ()));
        msg "after ltac1"
      end
    end
  end).
*)

Check emplace. Print PatternCtx.
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
        ltac1:(sigma gamma pat new_pat |- cut (@ML_proof_system sigma gamma new_pat))
               (Ltac1.of_constr sigma)
               (Ltac1.of_constr gamma)
               (Ltac1.of_constr pat)
               (Ltac1.of_constr alternative);
        msg "after ltac1"
      end
    end
  end).


Set Default Proof Mode "Classic".
Local Example ex_prf_rewrite {Σ : Signature} Γ a a' b c:
  Γ ⊢ a <---> a' ->
  Γ ⊢ (a $ b ---> c) <---> (a' $ b ---> c).
Proof.
  intros Himp.
  ltac2:(pf_rewrite constr:(Himp)).
  
  2: {
    
  }
Abort.

