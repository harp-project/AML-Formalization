From Coq Require Import Strings.Ascii.
From Coq Require Import Strings.String.
Require Import Coq.Strings.Byte.

Check string.

Check "065"%char.

Compute ascii_of_nat 65.

Import ZArith.BinInt.
From Coq Require Import Reals.
Import Lists.List.
Import ListNotations.
Import Arith.PeanoNat.
Require Coq.Program.Wf.
Require Import Omega.


Definition string_less (s1 s2 : string) : Prop :=
String.length s1 < String.length s2
.

Definition partial_max (s1 s2 : string) : string :=
(* match s1, s2 with
| EmptyString, s => s
| s, EmptyString => s
| String a s, String a' s' => let x := partial_max s s' in
                                if String.eqb x s then String a s else String a' s'
end *)
if String.length s1 <? String.length s2 then s2 else s1
.

Compute partial_max "foo" "".
Compute partial_max "bar" "foo".
Compute partial_max "foo" "foo1".
Compute partial_max "foo" "fo".
Compute partial_max "true" "atrue".


(** Just append an 's' to the front *)
Definition string_succ (s : string) : string := String "s"%char s.

(** Maximum element of a list, with the custom max *)
Definition list_max (l : list string) := fold_right partial_max EmptyString l.


(** New fresh variable, based on a list of variables *)
Definition new_fresh (l : list string) : string :=
  string_succ (list_max l).

Compute new_fresh [].

Open Scope string_scope.
Compute new_fresh ["asd"; "asdasd"; "asdase"].

Inductive term :=
| Nil
| Var (s : string)
| App (a1 a2 : term)
| Ex (x : string) (a : term).

Fixpoint size (a : term) : nat :=
match a with
 | Nil => 1
 | Var s => 1
 | App a1 a2 => 1 + size a1 + size a2
 | Ex x a => 1 + size a
end.

Fixpoint variables (a : term) : list string :=
match a with
 | Nil => []
 | Var s => [s]
 | App a1 a2 => variables a1 ++ variables a2
 | Ex x a => x::(variables a)
end.

Fixpoint replace_var (x x': string) (a : term) : term :=
match a with
| Nil => Nil
| Var s => if String.eqb s x then Var x' else a
| App a1 a2 => App (replace_var x x' a1) (replace_var x x' a2)
| Ex y a => if String.eqb y x then Ex x' (replace_var x x' a)
                              else Ex y  (replace_var x x' a)
end.

Lemma size_unmod x x' a: 
  size a = size (replace_var x x' a).
Proof.
  induction a; try(simpl; omega).
  * simpl. destruct (s =? x); simpl; omega.
  * simpl. destruct (x0 =? x); simpl; omega.
Qed.

Program Fixpoint subst_var (x : string) (x' a: term) {measure (size a)} : term :=
match a with
| Nil => Nil
| Var s => if String.eqb s x then x' else a
| App a1 a2 => App (subst_var x x' a1) (subst_var x x' a2)
| Ex y a => let z := new_fresh (variables a) in
              Ex z (subst_var x x' (replace_var y z a))
end.

Next Obligation.
simpl. omega.
Qed.

Next Obligation.
simpl. omega.
Qed.

Next Obligation.
simpl. rewrite <- size_unmod. omega.
Qed.

Compute subst_var "y"%string (Var "x"%string) (Ex "x"%string (App (Var "x"%string) (Var "y"%string))).

Require Import Coq.Program.Equality.
Import Coq.Logic.Classical_Prop.

Lemma partial_max_split : forall a b,
  partial_max a b = a \/ partial_max a b = b.
Proof.
  induction a; intros; destruct b; auto.
  * simpl. pose (IHa b). destruct o.
    - left. unfold partial_max in *.
      simpl in *. case_eq (String.length a0 <? String.length b); intros.
      + rewrite H0 in H. subst. apply Nat.ltb_lt in H0. omega.
      + rewrite H0 in H. subst. replace (S (String.length a0) <? S (String.length b)) with false. auto.
    - unfold partial_max in *. simpl in *. case_eq (S (String.length a0) <? S (String.length b)); intros.
      + auto.
      + auto.
Qed.

Compute string_less "true" "strue".

Lemma string_succ_length s :
  String.length (string_succ s) = S (String.length s).
Proof.
  simpl. auto.
Qed.

Import Coq.Arith.PeanoNat.

Lemma string_succ_gt s :
  string_less s (string_succ s).
Proof.
  unfold string_succ, string_less.
  destruct s.
  * simpl. auto.
  * simpl. auto.
Qed.

Lemma string_length_neq a b:
  String.length a <> String.length b -> a <> b.
Proof.
  intros. unfold not in *. intros. apply H. subst. auto.
Qed.

Import Bool.Bool. 

Lemma string_less_neq a b :
  string_less a b -> a <> b.
Proof.
  intros. unfold string_less in H. apply Nat.lt_neq in H. apply string_length_neq. auto.
Qed.

Lemma partial_max_leq a b :
  String.length a <= String.length (partial_max a b) /\ 
  String.length b <= String.length (partial_max a b).
Proof.
  split.
  * unfold partial_max. case_eq (String.length a <? String.length b); intros. 
    - apply Nat.ltb_lt in H. omega.
    - auto.
  * unfold partial_max. case_eq (String.length a <? String.length b); intros. 
    - apply Nat.ltb_lt in H. omega.
    - apply negb_true_iff in H. rewrite <- Nat.leb_antisym in H.
      apply Nat.leb_le. auto.
Qed.

Lemma partial_max_less a b s:
  string_less (partial_max a b) s -> string_less a s /\ string_less b s.
Proof.
  intros. pose (partial_max_leq a b).
  inversion a0.
  pose (partial_max_split a b). destruct o.
  * rewrite H2 in *. split; auto. unfold string_less in *.
    omega.
  * rewrite H2 in *. split; auto. unfold string_less in *.
    omega.
Qed.

(* Lemma lt_all_less l s :
  string_less (list_max l) s ->
(forall s', In s' l -> string_less s' s).
Proof.
  unfold string_less in *.
  induction l; intros.
  * contradiction.
  * simpl in *. apply IHl.
Qed. *)


(** 
  The general thought is:
  - If a string is bigger, than the list maximum, then it is not in the list
  - The new fresh variable is bigger, than the list maximum, the generation was based on
  => The new fresh variable is not in the list

*)
Lemma lt_max_not_in l s:
  string_less (list_max l) s -> ~In s l.
Proof.
  unfold string_less.
  intros.
  induction l.
  * unfold not. intros. contradiction.
  * pose (Nat.lt_neq _ _ H). apply string_length_neq in n.
    unfold not. intros. apply IHl. simpl in *.
    simpl in n, H. case_eq (partial_max_split a (list_max l)); intros; subst.
    - rewrite e in *. unfold not. intros.
      destruct H1. contradiction.
      apply IHl. 2: auto. admit.
    - unfold not. intros. case_eq (partial_max_split a (list_max l)); intros; subst.
      + rewrite e0 in *. admit.
      + 
Qed.

Lemma new_fresh_correct l :
  ~In (new_fresh l) l.
Proof.
  induction l.
  * unfold not; intros. inversion H.
  * unfold new_fresh. simpl. apply and_not_or. split.
    - simpl. destruct (max_split a (list_max l)).
      + rewrite H. apply not_eq_succ.
      + rewrite H.
