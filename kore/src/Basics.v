From stdpp Require Export list propset.
From Coq Require Export Program.Equality.

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
Notation "⟨ ⟩" := hnil (format "⟨  ⟩") : hlist_scope.
Notation "⟨ x ⟩" := (hcons x hnil)  : hlist_scope.
Notation "⟨ x ; y ; .. ; z ⟩" := (hcons x (hcons y .. (hcons z hnil) ..))  : hlist_scope.

Check ⟨⟩%hlist.
Check ⟨_⟩%hlist.
Check ⟨_;_;_⟩%hlist.

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

Definition test1 : hlist (bool_rect _ nat bool) [true; false] := ⟨1; true⟩%hlist.
Definition test2 : hlist (propset ∘ bool_rect _ nat bool) [true; false] := ⟨{[1]}; {[true]}⟩%hlist.
Goal pointwise_elem_of _ test1 test2.
Proof.
  simpl. set_solver.
Qed.
Print Forall.


Inductive InTy {A : Type} : A -> list A -> Type :=
  | In_nil {x} {xs} : InTy x (x :: xs)
  | In_cons {x y} {xs} : InTy y xs -> InTy y (x :: xs)
.

Definition cons_eq_inv {A : Type} {x y : A} {xs ys : list A}
  (H : x :: xs = y :: ys) : x = y /\ xs = ys :=
    conj (f_equal (list_rect _ x (λ a _ _, a)) H)
         (f_equal (list_rect _ xs (λ _ a _, a)) H).

Fixpoint InTy_app {A : Type} {s : A} {ex ex' ex'' : list A} 
  (pf : InTy s (ex ++ ex'')) : InTy s (ex ++ ex' ++ ex'').
Proof.
  dependent destruction pf.
  - destruct ex; simpl in *.
    + induction ex'; simpl.
      * rewrite <- x. left.
      * right. exact IHex'.
    + apply cons_eq_inv in x as [-> ->].
      left.
  - destruct ex; simpl in *.
    + induction ex'; simpl.
      * rewrite <- x.
        right. exact pf.
      * right. exact IHex'.
    + apply cons_eq_inv in x as [-> ->].
      right. apply InTy_app. exact pf.
Defined.

Arguments InTy_app {_} {_} {_} {_} {_} !_.

Definition app_comm_cons_defined
 : ∀ (A : Type) (x y : list A) (a : A),
     a :: x ++ y = (a :: x) ++ y.
Proof.
  intros. simpl.
  reflexivity.
Defined.

Require Import PropExtensionality.
Require Import FunctionalExtensionality.

#[export]
Instance propset_leibniz_equiv A : LeibnizEquiv (propset A).
Proof.
  intros x y H. unfold equiv in H. unfold set_equiv_instance in H.
  destruct x,y.
  apply f_equal. apply functional_extensionality.
  intros x. apply propositional_extensionality.
  specialize (H x). destruct H as [H1 H2].
  split; auto.
Qed.

Definition hcons_inv {A} {F : A -> Type} {x} {xs} P (X : forall (y : F x) (ys : hlist F xs), P) (ys : hlist F (x :: xs)) : P :=
    match ys in (hlist _ l) return (l = x :: xs -> P) with
    | hnil => λ H, False_rect _ (eq_ind nil (list_rect _ True (λ _ _ _, False)) I _ H)
    | @hcons _ _ a l y ys => λ H, X (eq_rect a F y x (f_equal (list_rect _ x (λ a _ _, a)) H)) (eq_rect l (hlist F) ys xs (f_equal (list_rect _ xs (λ _ a _, a)) H))
    end eq_refl.

Lemma destruct_hcons {A} {F : A -> Type} {x} {xs} (l : hlist F (x :: xs)) : sigT (λ '(y, ys), l = hcons y ys).
Proof.
  dependent destruction l.
  exists (f, l). reflexivity.
Defined.

Lemma destruct_hnil {A} {F : A -> Type} (l : hlist F []) : l = hnil.
Proof.
  dependent destruction l.
  reflexivity.
Defined.

Fixpoint all_singleton {A : Type} {M : A -> Type} {xs}
  (ys : @hlist A (propset ∘ M) xs) : Type :=
    match ys with
    | hnil => unit 
    | hcons y ys => prod (sigT (eq y ∘ singleton)) (all_singleton ys)
    end.

Fixpoint all_singleton_extract
  {A : Type}
  {M : A -> Type}
  {xs : list A}
  {ys : hlist (propset ∘ M) xs}
  (H : all_singleton ys) {struct ys}
  : hlist M xs.
Proof.
  destruct ys. left.
  simpl in H. destruct H as [[] ?].
  right. assumption.
  eapply all_singleton_extract. eassumption.
Defined.

Tactic Notation "set_helper" :=
  repeat match goal with
         | [ |- PropSet ?P ≡ ⊤ ] => enough (forall x, P x) by set_solver; intros
         | [ |- context[?x ∪ ∅] ] => rewrite union_empty_r
         (* put these into separate lemmas? *)
         | [ |- ⊤ ∖ ?X ≡ ⊤ ] => enough (X ≡ ∅) by set_solver
         | [ |- ⊤ ∖ ?X ≡ ∅ ] => enough (X ≡ ⊤) by set_solver
         | [ |- ⊤ ≫= ?f ≡ ∅ ] => enough (forall x, f x ≡ ∅) by set_solver; intros
         end.


Lemma propset_difference_neg :
  forall {A : Type} (P : A -> Prop),
    ⊤ ∖ {[x : A | P x]} = {[x : A | ~P x]}.
Proof.
  intros.
  set_solver.
Qed.

Lemma intersection_top_l_L {A C : Type}
    {H : ElemOf A C}
    {H0 : Top C}
    {H1 : Empty C}
    {H2 : Singleton A C}
    {H3 : Intersection C}
    {H4 : Union C}
    {H5 : Difference C} :
    Set_ A C → LeibnizEquiv C →
    TopSet A C ->
    LeftId eq (@top _ H0) intersection.
Proof.
  intros.
  unfold LeftId. set_solver.
Qed.

Lemma intersection_top_r_L {A C : Type}
    {H : ElemOf A C}
    {H0 : Top C}
    {H1 : Empty C}
    {H2 : Singleton A C}
    {H3 : Intersection C}
    {H4 : Union C}
    {H5 : Difference C} :
    Set_ A C → LeibnizEquiv C →
    TopSet A C ->
    RightId eq (@top _ H0) intersection.
Proof.
  intros.
  unfold RightId. set_solver.
Qed.

Lemma propset_top_elem_of_2 :
  forall {A : Type} (S : propset A),
    (forall (t : A), t ∈ S) -> S = ⊤.
Proof.
  intros. set_solver.
Qed.

(* Ltac autorewrite_set :=
  repeat (
    rewrite intersection_top_l_L +
    rewrite intersection_top_r_L +
    rewrite union_empty_l_L +
    rewrite union_empty_r_L +
    rewrite propset_difference_neg
  ).

Ltac solve_set_instances :=
  match goal with
  | [|- Set_ _ _ ] => typeclasses eauto
  | [|- LeibnizEquiv _ ] => typeclasses eauto
  | [|- TopSet _ _ ] => typeclasses eauto
  end. *)

Fixpoint hmap {J} {A B : J -> Type}
  (f : ∀ j, A j -> B j)
  {js : list J} (v : @hlist J A js) {struct v} : @hlist J B js :=
match v with
| hnil => hnil
| hcons x xs => hcons (f _ x) (hmap f xs)
end.

Fixpoint uncurry_n {S R : Type}
  {l : list S}
  {T : S -> Type}
  (f : foldr (λ c a, T c -> a) R l)
    (hl : hlist T l) : R.
Proof.
  induction hl.
  * simpl in f. exact f.
  * simpl in f.
    specialize (f f0).
    specialize (IHhl f). exact IHhl.
Defined.

Lemma propset_union_simpl :
  forall T (P Q : T -> Prop),
    {[ x | P x ]} ∪ {[ x | Q x]} = {[ x | P x \/ Q x ]}.
Proof.
  set_solver.
Qed.

Lemma propset_intersection_simpl :
  forall T (P Q : T -> Prop),
    {[ x | P x ]} ∩ {[ x | Q x]} = {[ x | P x /\ Q x ]}.
Proof.
  set_solver.
Qed.

  Check @singleton_subseteq.
  Lemma singleton_eq :
    forall (A C : Type) (H : ElemOf A C) (H0 : Empty C)
         (H1 : Singleton A C) (H2 : Union C) (H3 : LeibnizEquiv C), SemiSet A C ->
      forall (x y : A), @singleton A C H1 x = {[y]} <-> x = y.
  Proof.
    intros. set_solver.
  Qed.
