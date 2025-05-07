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
Bind Scope hlist_scope with hlist.
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

Ltac invt H := inversion H; subst; clear H.

Lemma JMeq_eq_rect {U : Type} {P : U → Type} {p q : U} {x : P p} {y : P q} (H : p = q) : JMeq x y -> eq_rect p P x q H = y.
Proof.
  intros.
  apply JMeq_eq_dep, eq_dep_eq_sigT, eq_sigT_sig_eq in H0 as [].
  rewrite (Eqdep.EqdepTheory.UIP _ _ _ H x0).
  all: assumption.
Defined.


Create HintDb kore.
Hint Unfold AntiSymm : kore.
Hint Constructors PartialOrder : kore.
Hint Extern 5 (EqDecision _) => unfold EqDecision, Decision; decide equality : kore.
Hint Unfold eq_rect_r : kore.
Hint Rewrite -> Eqdep.EqdepTheory.eq_rect_eq : kore.
Hint Rewrite <- Eqdep.EqdepTheory.eq_rect_eq : kore.
Hint Unfold Equality.block solution_left : kore.
Hint Extern 5 (?x ∈ ⊤) => simple apply elem_of_top' : kore.
Hint Unfold Equality.block solution_left : kore.
