From Coq Require Import ssreflect ssrfun ssrbool.

From Ltac2 Require Import Ltac2.
From Coq Require Import Ensembles Bool.
From MatchingLogic Require Import Syntax Semantics DerivedOperators ProofSystem Helpers.FOL_helpers.

From stdpp Require Import list tactics fin_sets.

From MatchingLogic.Utils Require Import stdpp_ext.

Import extralibrary.

From Ltac2 Require Import Message Control Fresh Option.
Ltac2 msg x := print (of_string x).

Import
  MatchingLogic.Syntax.Notations
  MatchingLogic.DerivedOperators.Notations
  MatchingLogic.ProofSystem.Notations
.

Open Scope ml_scope.

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

(*
Ltac2 solve_fresh_contradictions () :=
  unfold fresh_evar; simpl;
  repeat (
  match! goal with
  | [ h: ?y = ?y |- _ ] => Std.clear [h]
  end);
  match! goal with
  | [ h: fresh_evar ?p = ?x |- _ ]
    => let h := Control.hyp h in
       let hcontra := in_goal ident:(hcontra25) in
       print (of_constr h);
       msg "have x"; print (of_constr x); print (of_constr p);
       assert ($hcontra: $x <> fresh_evar $p) by ltac1:(unfold fresh_evar; simpl; solve_fresh_neq);
       print (of_constr h);
       msg "Just before rewrite";
       ltac1:(h hcontra |- rewrite -> h in hcontra)
             (Ltac1.of_constr h)
             (Ltac1.of_ident hcontra); (* This does not work in old Coq (v8.13) *)
       (*rewrite -> $h in $hcontra;*)
       ltac1:(contradiction)
  end.
 *)
Ltac solve_fresh_contradictions :=
  unfold fresh_evar; simpl;
  repeat (
  match goal with
  | h: ?y = ?y |- _ => clear h
  end);
  match goal with
  | h: fresh_evar ?p = ?x |- _
    => let hcontra := fresh "Hcontra" in
       assert (hcontra: x <> fresh_evar p) by (unfold fresh_evar; simpl; solve_fresh_neq);
       rewrite -> h in hcontra;
       contradiction
  end.

Ltac2 simplify_emplace () := unfold emplace; simpl;
           unfold free_evar_subst; simpl;
           repeat ltac1:(case_match);
           try ltac1:(congruence);
           try (ltac1:(solve_fresh_contradictions));
           repeat (rewrite nest_ex_aux_0);
           reduce_free_evar_subst ().

Ltac2 pf_rewrite_shelved (h : constr) :=
  match! (Constr.type h) with
  | @ML_proof_system ?sigma ?gamma (?l <---> ?r)
    =>
    match! goal with
    | [ |- @ML_proof_system ?sigma ?gamma ?pat]
      => print (of_constr l);
      match! pat with
      | context ctx [?l'] =>
        if (Bool.neg (Constr.equal l l')) then fail else ();
        let star := (constr:(@fresh_evar $sigma $pat)) in
        (*print (of_constr star);*)
        (* Replace the original pattern with its emplace-ed version *)
        let ctxpat := (Pattern.instantiate ctx (constr:(@patt_free_evar $sigma $star))) in
        let alternative := (constr:(@emplace $sigma (@Build_PatternCtx $sigma $star $ctxpat) $l)) in
        ltac1:(sigma gamma pat new_pat |- replace pat with new_pat)
               (Ltac1.of_constr sigma)
               (Ltac1.of_constr gamma)
               (Ltac1.of_constr pat)
               (Ltac1.of_constr alternative) >
        [|( simplify_emplace (); try reflexivity; shelve ()
        )];
        (* Use the congruence lemma and $h *)
        eapply Modus_ponens >
        [(shelve ())|(shelve ())|()|
          (apply pf_iff_proj1 >
           [shelve () |shelve ()|
             (apply prf_equiv_congruence >
              [shelve ()|shelve ()|shelve ()|
                (apply pf_iff_equiv_sym >
                 [shelve ()|shelve ()|
                   apply $h])
        ])])];
        (* replace the emplaced version with the original pattern but with the new value *)
        let alternative' := (constr:(@emplace $sigma (@Build_PatternCtx $sigma $star $ctxpat) $r)) in
        print (of_constr alternative');
        ltac1:(sigma gamma pat new_pat |- replace pat with new_pat)
               (Ltac1.of_constr sigma)
               (Ltac1.of_constr gamma)
               (Ltac1.of_constr alternative')
               (Ltac1.of_constr (Pattern.instantiate ctx r)) >
        [|( simplify_emplace (); try reflexivity; shelve ()
        )]
      end
    end
  end.
Set Default Proof Mode "Classic".

Ltac2 unshelve_wrapper tac := (ltac1:(unshelve ltac2:(Ltac1.lambda tac) )).

(* TODO: how to pass the parameter? *)
(*Ltac pf_rewrite_unshelved x := unshelve (ltac2:(x |- pf_rewrite_shelved (Option.get (Ltac1.to_constr x)))).*)

(*Ltac2 pf_rewrite_unshelved x := ltac1:(unshelve (ltac2:(x |- pf_rewrite_shelved (Option.get (Ltac1.to_constr x))))).*)
    


Local Example ex_prf_rewrite {Σ : Signature} Γ a a' b x:
  well_formed a ->
  well_formed a' ->
  well_formed b ->
  Γ ⊢ a <---> a' ->
  Γ ⊢ (a $ b ---> (patt_free_evar x)) <---> (a' $ b ---> (patt_free_evar x)).
Proof.
  intros wfa wfa' wfb Himp.
  (*pf_rewrite_unshelved Himp.*)
  ltac2:(pf_rewrite_shelved constr:(Himp)).
  
Abort.

