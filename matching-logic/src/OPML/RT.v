From stdpp Require Import base tactics.
From Coq Require Import Lists.List.
Import ListNotations.

Inductive hlist {A : Type} (F : A -> Type) : list A -> Type :=
  | hnil : hlist F []
  | hcons {x} {xs} : F x -> hlist F xs -> hlist F (x :: xs)
.

Arguments hlist {_} _ & _.
Arguments hnil {_} {_}.
Arguments hcons {_} {_} {_} {_} & _ _.

Declare Scope hlist_scope.
Delimit Scope hlist_scope with hlist.
Bind Scope hlist_scope with hlist.

Infix "::" := hcons (at level 60, right associativity) : hlist_scope.
Notation "[ ]" := hnil (format "[ ]") : hlist_scope.
Notation "[ x ]" := (hcons x hnil) : hlist_scope.
Notation "[ x ; y ; .. ; z ]" := (hcons x (hcons y .. (hcons z hnil) ..)) (format "[ '[' x ; '/' y ; '/' .. ; '/' z ']' ]") : hlist_scope.

Check [1; 2; true; 3; false]%hlist : hlist (bool_rect _ nat bool) [true; true; false; true; false].

Class Sort : Type := {
  carrier : Type;
  sort_ed : EqDecision carrier;
  }.

Instance asd : Sort := {| carrier := bool; sort_ed := _ |}.

Inductive RT {A : Sort} (B : carrier) : Type :=
  | Leaf : RT B
  | Node {xs} : hlist RT xs -> RT B
.

Arguments Leaf {_} {_}.
Arguments Node {_} {_} {_} & _.

Check Node [Leaf; Node [Leaf; Leaf]; Leaf] : @RT asd true.

Fixpoint depth {A} (x : RT A) : nat :=
  match x with
  | Leaf => 1
  | Node l => hlist_rect _ _ _ 0 (fun _ _ y _ IHys => Nat.max IHys (depth y)) _ l
  end.

Arguments depth {_} !_.

Definition hlistIn {A} {ED : EqDecision A} {F : A -> Type} {x : A} {xs : list A} (y : F x) (ys : hlist F xs) : Prop :=
  match ys with
  | hnil => False
  | @hcons _ _ x' _ y' ys' => match (decide (x = x')) with
                              | left e => (eq_rect _ _ y _ e = y')
                              | _ => False
                              end
  end.

Arguments hlistIn {_} {_} {_} {_} {_} & _ !_.

Definition SubTree {A : Sort} {B : carrier} (x y : RT B) : Prop :=
  match y with
  | Leaf => False
  | Node l => @hlistIn _ (sort_ed) _ _ _ x l
  end.

Arguments SubTree {_} {_} _ !_.

Goal forall {A : Sort} {B : carrier}, well_founded (@SubTree A B).
Proof.
  intros.
  unfold well_founded.
  fix thisworks 1.
  intros [].
  split. intros. destruct H.
  split. intros. simpl in H. destruct h.
  destruct H.
  simpl in H.
  case_match.
  2: destruct H.
  apply rew_swap in H. rewrite H.
  apply thisworks.
Qed.

