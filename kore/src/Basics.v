From stdpp Require Import list propset.
Import ListNotations.

Definition is_leftb {A B : Set} (x : A + B) : bool :=
match x with
| inl _ => true
| _ => false
end.

Definition is_rightb {A B : Set} (x : A + B) : bool :=
match x with
| inl _ => false
| _ => true
end.

Definition andb_split_1 (b1 b2 : bool) : andb b1 b2 = true -> b1 = true.
Proof.
  destruct b1, b2; simpl; try reflexivity.
  all: intros; congruence.
Defined.

Definition andb_split_2 (b1 b2 : bool) : andb b1 b2 = true -> b2 = true.
Proof.
  destruct b1, b2; simpl; try reflexivity.
  all: intros; congruence.
Defined.

Inductive hlist {A : Type} {F : A -> Type} : list A -> Type :=
| hnil : hlist []
| hcons {x : A} {xs : list A} : F x -> hlist xs -> hlist (x :: xs).

Arguments hlist {_} _ & _.
Arguments hnil {_} {_}.
Arguments hcons {_} {_} {_} {_} & _ _.
Arguments hlist_rect {_} {_} {_} & _ _ {_} _ /.

Declare Scope hlist_scope.
Delimit Scope hlist_scope with hlist.
Notation "[ ]" := hnil (format "[ ]") : hlist_scope.
Notation "[ x ]" := (hcons _ x hnil)  : hlist_scope.
Notation "[ x ; y ; .. ; z ]" := (hcons x (hcons y .. (hcons z hnil) ..))  : hlist_scope.

Fixpoint pointwise_elem_of {A : Type} {T : A -> Type}
  ss {struct ss} :
  (* (l : @hlist A T ss)
  (lps : @hlist A (fun s => propset (T s)) ss) *)
  @hlist A T ss ->
  @hlist A (fun s => propset (T s)) ss ->
  Prop. (* := *)
Proof.
  refine (match ss with
    | []    => fun _ _ => True
    | s::ss => fun l l' =>
      (match l in (@hlist _ _ l1)
        return (l1 = s::ss -> Prop) with
      | hnil =>
        fun (H : [] = s :: ss) => False_rect Prop ltac:(discriminate H)
      | @hcons _ _ a l0 x xs =>
        fun (H : a :: l0 = s::ss) =>
          (match l' in (@hlist _ _ l1')
             return l1' = s::ss -> Prop with
           | hnil => fun (H0 : [] = s :: ss) => False_rect Prop ltac:(discriminate H0)
           | @hcons _ _ a' l0' y ys =>
             fun (H0 : a' :: l0' = s :: ss) =>
               x ∈ y /\ pointwise_elem_of _ _ ss _ _
           end
          ) eq_refl
      end) eq_refl
    end).
  * injection H. injection H0. intros. rewrite H4. rewrite H2.
    typeclasses eauto.
  * injection H. intros. rewrite H1 in xs. exact xs.
  * injection H0. intros. rewrite H1 in ys. exact ys.
Defined.

Definition test1 : hlist (bool_rect _ nat bool) [true; false] := [1; true]%hlist.
Definition test2 : hlist (propset ∘ bool_rect _ nat bool) [true; false] := [{[1]}; {[true]}]%hlist.
Goal pointwise_elem_of _ test1 test2.
Proof.
  simpl. set_solver.
Qed.