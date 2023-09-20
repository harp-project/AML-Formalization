(** * Module [extralibrary]: library functions, theorems, and tactics *)
From Coq Require Import ssreflect ssrfun ssrbool.
From Coq Require Import Bool.Bool.
From stdpp Require Import base tactics.
Require Import Arith.
Require Import ZArith.
Require Import List.
Require Import Coq.micromega.Lia.

(* alternative to destruct: when hypotheses/goals contain match expressions *)
Ltac break_match_hyp :=
match goal with
| [ H : context [ match ?X with _=>_ end ] |- _] =>
     match type of X with
     | sumbool _ _=>destruct X
     | _=>destruct X eqn:? 
     end 
end.

Ltac break_match_goal :=
match goal with
| [ |- context [ match ?X with _=>_ end ] ] => 
    match type of X with
    | sumbool _ _ => destruct X
    | _ => destruct X eqn:?
    end
end.

(** Usage: 
   Works similarly for `match` expressions too
*)
Goal forall x, x && true = x.
Proof.
  intro x. unfold andb. break_match_goal; reflexivity.
Qed.

(** ** Arithmetic *)

Inductive comparison_nat (x y: nat) : Set :=
  | Nat_less:    x < y -> comparison_nat x y
  | Nat_equal:   x = y -> comparison_nat x y
  | Nat_greater: x > y -> comparison_nat x y.

Lemma compare_nat: forall x y, comparison_nat x y.
Proof.
  intros. case (lt_eq_lt_dec x y); intro.
  destruct s. apply Nat_less; auto. apply Nat_equal; auto.
  apply Nat_greater; auto.
Defined.

(** ** Peano induction. *)

(** This is a variant of the induction principle over natural
  numbers.  It will be used later to do induction over
  the size of a type. *)

Lemma Peano_induction:
  forall (P: nat -> Prop),
  (forall x, (forall y, y < x -> P y) -> P x) ->
  forall x, P x.
Proof.
  intros P H.
  assert (forall x, forall y, y < x -> P y).
  {
    induction x; intros.
    {
      lia.
    }
    {
      apply H. intros. apply IHx. lia.
    }
  }
  {
    intro. apply H0 with (S x). lia.
  }
Qed.

(* taken from https://softwarefoundations.cis.upenn.edu/vfa-current/Perm.html *)
Lemma eqb_reflect : forall x y, reflect (x = y) (x =? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.eqb_eq.
Qed.

(* Taken from
   https://gitlab.mpi-sws.org/iris/stdpp/-/blob/c5ee00e4ba9e0122ddfbd0de97847d8e96154595/theories/tactics.v
   and modified so that it works with [= true] instead of `is_True`
 *)

Tactic Notation "naive_bsolver" tactic(tac) :=
  unfold iff, not in *;
  repeat match goal with
  | H : context [∀ _, _ ∧ _ ] |- _ =>
    repeat setoid_rewrite forall_and_distr in H; revert H
  end;
  let rec go n :=
  repeat match goal with
  (**i solve the goal *)
  | |- _ => fast_done
  (**i intros *)
  | |- ∀ _, _ => intro
  (**i simplification of assumptions *)
  | H : False |- _ => destruct H
  | H : _ ∧ _ |- _ =>
     (* Work around bug https://coq.inria.fr/bugs/show_bug.cgi?id=2901 *)
     let H1 := fresh in let H2 := fresh in
     destruct H as [H1 H2]; try clear H
  | H : ∃ _, _  |- _ =>
     let x := fresh in let Hx := fresh in
     destruct H as [x Hx]; try clear H
  | H : ?P → ?Q, H2 : ?P |- _ => specialize (H H2)
  | H : is_true (bool_decide _) |- _ => apply bool_decide_eq_true in H
  | H : (bool_decide _) = true |- _ => apply bool_decide_eq_true in H
  | H : is_true (_ && _) |- _ => apply andb_true_iff in H; destruct H
  | H : (_ && _) = true |- _ => apply andb_true_iff in H; destruct H
  (**i simplify and solve equalities *)
  | |- _ => progress simplify_eq/=
  (**i operations that generate more subgoals *)
  | |- _ ∧ _ => split
  | |- is_true (bool_decide _) => apply bool_decide_eq_true
  | |- (bool_decide _) = true => apply bool_decide_eq_true
  | |- is_true (_ && _) => apply andb_true_iff; split
  | |- (_ && _) = true => apply andb_true_iff; split
  | H : _ ∨ _ |- _ =>
     let H1 := fresh in destruct H as [H1|H1]; try clear H
  | H : is_true (_ || _) |- _ =>
    apply orb_true_iff in H; let H1 := fresh in destruct H as [H1|H1]; try clear H
  | H : (_ || _) = true |- _ =>
     apply orb_true_iff in H; let H1 := fresh in destruct H as [H1|H1]; try clear H
  (**i solve the goal using the user supplied tactic *)
  | |- _ => solve [tac]
  end;
  (**i use recursion to enable backtracking on the following clauses. *)
  match goal with
  (**i instantiation of the conclusion *)
  | |- ∃ x, _ => no_new_unsolved_evars ltac:(eexists; go n)
  | |- _ ∨ _ => first [left; go n | right; go n]
  | |- is_true (_ || _) => apply orb_true_iff; first [left; go n | right; go n]
  | |- (_ || _) = true => apply orb_true_iff; first [left; go n | right; go n]
  | _ =>
    (**i instantiations of assumptions. *)
    lazymatch n with
    | S ?n' =>
      (**i we give priority to assumptions that fit on the conclusion. *)
      match goal with
      | H : _ → _ |- _ =>
        is_non_dependent H;
        no_new_unsolved_evars
          ltac:(first [eapply H | efeed pose proof H]; clear H; go n')
      end
    end
  end
  in iter (fun n' => go n') (eval compute in (seq 1 6)).
Tactic Notation "naive_bsolver" := naive_bsolver eauto.

Tactic Notation "split_and" :=
  match goal with
  | |- _ /\ _ => split
  | |- Is_true (_ && _) => apply andb_True; split
  | |- is_true (_ && _) => apply andb_true_iff; split
  | |- (_ && _) = true => apply andb_true_iff; split                                                  
  end.
Tactic Notation "split_and" "?" := repeat split_and.
Tactic Notation "split_and" "!" := hnf; split_and; split_and?.

Ltac destruct_and_go H :=
  try lazymatch type of H with
  | True => clear H
  | _ ∧ _ =>
    let H1 := fresh in
    let H2 := fresh in
    destruct H as [ H1 H2 ];
    destruct_and_go H1; destruct_and_go H2
  | Is_true (bool_decide _) =>
    apply (bool_decide_unpack _) in H;
    destruct_and_go H
  | Is_true (_ && _) =>
    apply andb_True in H;
    destruct_and_go H
  | is_true (_ && _) =>
    apply andb_true_iff in H;
    destruct_and_go H
  | (_ && _) = true =>
    apply andb_true_iff in H;
    destruct_and_go H
  end.

Tactic Notation "destruct_and" "?" ident(H) :=
  destruct_and_go H.
Tactic Notation "destruct_and" "!" ident(H) :=
  hnf in H; progress (destruct_and? H).
Tactic Notation "destruct_and" "?" :=
  repeat match goal with H : _ |- _ => progress (destruct_and? H) end.
Tactic Notation "destruct_and" "!" :=
  progress destruct_and?.

Ltac destruct_ex_go H :=
  try lazymatch type of H with
  | True => clear H
  | (ex _) => let x := fresh "x" in let H' := fresh "H" in destruct H as [ x H ]
  end.
Tactic Notation "destruct_ex" "?" ident(H) :=
  destruct_ex_go H.
Tactic Notation "destruct_ex" "!" ident(H) :=
  hnf in H; progress (destruct_ex? H).

Tactic Notation "destruct_ex" "?" :=
  repeat match goal with H : _ |- _ => progress (destruct_ex? H) end.
Tactic Notation "destruct_ex" "!" :=
  progress destruct_ex?.

Tactic Notation "destruct_and_ex" "?" :=
  repeat (destruct_and? || destruct_ex?).
Tactic Notation "destruct_and_ex" "!" :=
  progress destruct_and_ex?.


Tactic Notation "destruct_or" "?" ident(H) :=
  repeat
    (match type of H with
     | is_true false => inversion H
     | False => destruct H
     | _ ∨ _ => destruct H as [H|H]
     | Is_true (bool_decide _) => apply (bool_decide_unpack _) in H
     | Is_true (_ || _) => apply orb_True in H; destruct H as [H|H]
     | is_true (_ || _) => apply orb_true_iff in H; destruct H as [H|H]
     | (_ || _) = true => apply orb_true_iff in H; destruct H as [H|H]
     end).

Tactic Notation "destruct_or" "!" ident(H) := hnf in H; progress (destruct_or? H).

Tactic Notation "destruct_or" "?" :=
  repeat match goal with H : _ |- _ => progress (destruct_or? H) end.
Tactic Notation "destruct_or" "!" :=
  progress destruct_or?.

  Tactic Notation "is_really_non_dependent" constr(H) :=
  match goal with
  | _ : context [ H ] |- _ => fail 1
  | _ := context [ H ]  |- _ => fail 1
  | |- context [ H ] => fail 1
  | _ => idtac
  end.
 

Ltac destruct_and_deduplicate' H cont :=
  lazymatch type of H with
  | ?P /\ ?P =>
    lazymatch goal with
    | [H1 : P |- _] => clear H
    | _ => 
      let H2 := fresh "H" in
      pose proof (H2 := proj1 H);
      clear H;
      cont H2
    end
  | ?P /\ ?Q =>
    lazymatch goal with
    | [H1 : P, H2 : Q |- _]
      => clear H
    | [H1 : P |- _]
      =>
        let H2 := fresh "H" in
        pose proof (H2 := proj2 H);
        clear H;
        cont H2
    | [H1 : Q |- _]
      =>
        let H2 := fresh "H" in
        pose proof (H2 := proj1 H);
        clear H;
        cont H2
    | _
      =>
      let H1 := fresh in
      let H2 := fresh in
      destruct H as [ H1 H2 ];
      cont H1; cont H2
    end
  end
.

Tactic Notation
  "destruct_and_deduplicate" ident(H) tactic(cont)
  := destruct_and_deduplicate' H cont
.

Example ex_destruct_and_deduplicate P Q R:
  P /\ Q -> P /\ R -> Q /\ R -> R /\ R -> R.
Proof.
  intros H1 H2 H3 H4.
  destruct_and_deduplicate H1 (fun h => idtac h).
  destruct_and_deduplicate H2 (fun h => idtac h).
  destruct_and_deduplicate H3 (fun h => idtac h).
  destruct_and_deduplicate H4 (fun h => idtac h).
  assumption.
Qed.

(* A lightweight version of destruct_and *)
  Ltac destruct_andb_go H :=
    try lazymatch type of H with
    | true => clear H
    | (_ && _) = true =>
      apply andb_true_iff in H;
      destruct_and_deduplicate H destruct_andb_go
    end.
  
  (* We first use the associativity so that every destruct
     yields at least one 'atomic' hypothesis
     (not containing [andb]), which may already exist
     among the other hypotheses.
   *)
  Ltac destruct_andb_go_wrapper H :=
    (*repeat rewrite -> andb_assoc in H;*)
    destruct_andb_go H
  .
  
  Tactic Notation "destruct_andb" "?" ident(H) :=
    destruct_andb_go_wrapper H.
  Tactic Notation "destruct_andb" "!" ident(H) :=
    hnf in H; progress (destruct_andb? H).
  Tactic Notation "destruct_andb" "?" :=
    repeat match goal with H : _ |- _ => progress (destruct_andb? H) end.
  Tactic Notation "destruct_andb" "!" :=
    progress destruct_andb?.