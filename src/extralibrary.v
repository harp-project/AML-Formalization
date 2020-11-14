(** * Module [extralibrary]: library functions, theorems, and tactics *)

Require Import Arith.
Require Import ZArith.
Require Import List.

(** ** Tactics *)

Ltac decEq :=
  match goal with
  | [ |- (_, _) = (_, _) ] =>
      apply injective_projections; unfold fst,snd; try reflexivity
  | [ |- (@Some ?T _ = @Some ?T _) ] =>
      apply (f_equal (@Some T)); try reflexivity
  | [ |- (@cons ?T _ _ = @cons ?T _ _) ] =>
      apply (f_equal2 (@cons T)); try reflexivity
  | [ |- (?X _ _ _ _ _ = ?X _ _ _ _ _) ] =>
      apply (f_equal5 X); try reflexivity
  | [ |- (?X _ _ _ _ = ?X _ _ _ _) ] =>
      apply (f_equal4 X); try reflexivity
  | [ |- (?X _ _ _ = ?X _ _ _) ] =>
      apply (f_equal3 X); try reflexivity
  | [ |- (?X _ _ = ?X _ _) ] =>
      apply (f_equal2 X); try reflexivity
  | [ |- (?X _ = ?X _) ] =>
      apply (f_equal X); try reflexivity
  | [ |- (?X ?A <> ?X ?B) ] =>
      cut (A <> B); [intro; congruence | try discriminate]
  end.

Ltac omegaContradiction :=
  cut False; [contradiction|omega].

Ltac caseEq name :=
  generalize (refl_equal name); pattern name at -1 in |- *; case name.

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

(** ** Lists *)

Lemma notin_cons_l:
  forall (A: Set) (u: A) (x: A) (l: list A),
  ~In u (x :: l) -> u <> x.
Proof.
  simpl; intros. apply sym_not_equal. tauto.
Qed.

Lemma notin_cons_r:
  forall (A: Set) (u: A) (x: A) (l: list A),
  ~In u (x :: l) -> ~In u l.
Proof.
  simpl; intros. tauto.
Qed.

Lemma notin_app_l:
  forall (A: Set) (u: A) (l1 l2: list A),
  ~In u (l1 ++ l2) -> ~In u l1.
Proof.
  intros. generalize (in_or_app l1 l2 u). tauto.
Qed.
Lemma notin_app_r:
  forall (A: Set) (u: A) (l1 l2: list A),
  ~In u (l1 ++ l2) -> ~In u l2.
Proof.
  intros. generalize (in_or_app l1 l2 u). tauto.
Qed.

Hint Resolve sym_not_equal notin_cons_l notin_cons_r notin_app_l notin_app_r.

Lemma in_app_equiv:
  forall (A: Set) (x y: A) (l1 l2 l3 l4: list A),
  (In x l1 <-> In y l3) -> (In x l2 <-> In y l4) -> (In x (l1 ++ l2) <-> In y (l3 ++ l4)).
Proof.
  intros. generalize (in_or_app l1 l2 x). generalize (in_or_app l3 l4 y).
  generalize (in_app_or l1 l2 x). generalize (in_app_or l3 l4 y). tauto.
Qed.
Hint Resolve in_app_equiv.

Lemma in_app_l:
  forall (A: Set) (x: A) (l1 l2: list A), In x l1 -> In x (l1 ++ l2).
Proof.
  intros. apply in_or_app. tauto.
Qed.
Lemma in_app_r:
  forall (A: Set) (x: A) (l1 l2: list A), In x l2 -> In x (l1 ++ l2).
Proof.
  intros. apply in_or_app. tauto.
Qed.
Hint Resolve in_app_l in_app_r.

Lemma in_cons_other:
  forall (A: Set) (x y: A) (l: list A),
  In x (y :: l) -> x <> y -> In x l.
Proof.
  intros. elim H; intros. congruence. auto.
Qed.
Hint Resolve in_cons_other.


Lemma map_append:
  forall (A B: Set) (f: A -> B) (l1 l2: list A),
  map f (l1 ++ l2) = (map f l1) ++ (map f l2).
Proof.
  induction l1; simpl; intros. auto. decEq; auto. 
Qed.

Lemma incl_cons2:
  forall (A: Set) (x: A) (l1 l2: list A),
  incl l1 l2 -> incl (x::l1) (x::l2).
Proof.
  intros; red; simpl; intros. generalize (H a). tauto.
Qed.
Hint Resolve in_app_or in_or_app incl_refl incl_tl incl_cons incl_cons2 incl_app.


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
  induction x; intros.
  omegaContradiction.
  apply H. intros. apply IHx. omega.
  intro. apply H0 with (S x). omega.
Qed.

