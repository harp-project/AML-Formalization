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

Lemma singleton_eq :
  forall (A C : Type) (H : ElemOf A C) (H0 : Empty C)
       (H1 : Singleton A C) (H2 : Union C) (H3 : LeibnizEquiv C), SemiSet A C ->
    forall (x y : A), @singleton A C H1 x = {[y]} <-> x = y.
Proof.
  intros. set_solver.
Qed.


  (*   Fixpoint HForall {J} {A : J -> Type}
      (P : ∀ j, A j -> Prop)
      {js : list J} (v : @hlist J A js) {struct v} : Prop :=
      match v with
      | hnil => True
      | hcons x xs => P _ x ∧ HForall P xs
      end.

    Fixpoint HBiForall {J1 J2} {A1 : J1 -> Type} {A2 : J2 -> Type}
      (P : ∀ j1 j2, A1 j1 -> A2 j2 -> Prop)
      {js1 : list J1}
      {js2 : list J2}
      (v1 : @hlist J1 A1 js1) (v2 : @hlist J2 A2 js2)
        {struct v1} : Prop :=
      match v1, v2 with
      | hnil, hnil => True
      | hcons x xs, hcons y ys => P _ _ x y ∧ HBiForall P xs ys
      | _, _ => False
      end.*)

Ltac invt H := inversion H; subst; clear H.

Lemma JMeq_eq_rect {U : Type} {P : U → Type} {p q : U} {x : P p} {y : P q} (H : p = q) : JMeq x y -> eq_rect p P x q H = y.
Proof.
  intros.
  apply JMeq_eq_dep, eq_dep_eq_sigT, eq_sigT_sig_eq in H0 as [].
  rewrite (Eqdep.EqdepTheory.UIP _ _ _ H x0).
  all: assumption.
Defined.

Lemma fmap_propset_singleton :
  forall {A B : Type}
    (f : A -> B) (x : A),
    f <$> ({[x]} : propset A) = ({[f x]} : propset B).
Proof.
  set_solver.
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

Definition orElse {A} (x y : option A) : option A :=
match x with
| Some a => Some a
| None   => y
end.
Notation "f <|> g" := (orElse f g) (at level 56, left associativity).

Lemma propset_top_eq {A : Type} (P Q : Prop) :
  P <-> Q ->
  ({[ _ | P]} : propset A) = ({[_ | Q]} : propset A).
Proof.
  set_solver.
Qed.

Require Import Classical_Pred_Type.

Lemma DM_exists :
      ∀ (U : Type) (P : U → Prop),
         ¬ (∃ n : U, P n) <-> (∀ n : U, ¬ P n).
Proof.
  intros.
  split; intros.
  - by apply not_ex_all_not with (n := n) in H.
  - by apply all_not_not_ex.
Qed.
Lemma DM_and :
      ∀ (A B : Prop),
         ¬ (A /\ B) <-> (¬A \/ ¬B).
Proof.
  split.
  - by apply Classical_Prop.not_and_or.
  - by apply Classical_Prop.or_not_and.
Qed.

Definition hlist_app {T P}
  {lty rty : list T}
  (l : hlist P lty)
  (r : hlist P rty) : hlist P (lty ++ rty).
Proof.
  induction l; simpl.
  - exact r.
  - exact (hcons f (IHl)).
Defined.

Lemma Z_gtb_le x y:
  ((x >? y) = false <-> x <= y)%Z.
Proof.
  lia.
Qed.
Lemma Z_geb_lt x y:
  ((x >=? y) = false <-> x < y)%Z.
Proof.
  lia.
Qed.



Ltac all_to_prop :=
  repeat
  match goal with
  (* ==== nat versions ==== *)
  | [ H: Nat.eqb ?a ?b = true |- _ ] => apply Nat.eqb_eq in H
  | [ H: Nat.eqb ?a ?b = false |- _ ] => apply Nat.eqb_neq in H
  | [ H: ?a <=? ?b = true |- _ ] => apply Nat.leb_le in H
  | [ H: ?a <=? ?b = false |- _ ] => apply Nat.leb_gt in H
  | [ H: ?a <? ?b = true |- _ ] => apply Nat.ltb_lt in H
  | [ H: ?a <? ?b = false |- _ ] => apply Nat.ltb_ge in H

  (* ==== Z versions ==== *)
  | [ H: Z.eqb ?a ?b = true |- _ ] => apply Z.eqb_eq in H
  | [ H: Z.eqb ?a ?b = false |- _ ] => apply Z.eqb_neq in H
  | [ H: Z.leb ?a ?b = true |- _ ] => apply Z.leb_le in H
  | [ H: Z.leb ?a ?b = false |- _ ] => apply Z.leb_gt in H
  | [ H: Z.ltb ?a ?b = true |- _ ] => apply Z.ltb_lt in H
  | [ H: Z.ltb ?a ?b = false |- _ ] => apply Z.ltb_ge in H
  | [ H: Z.geb ?a ?b = true |- _ ] => apply Z.geb_ge in H
  | [ H: Z.geb ?a ?b = false |- _ ] => apply Z_geb_lt in H
  | [ H: Z.gtb ?a ?b = true |- _ ] => apply Z.gtb_gt in H
  | [ H: Z.gtb ?a ?b = false |- _ ] => apply Z_gtb_le in H

  (* ==== Plain bools ==== *)
  | [ H: true = true |- _ ] => clear H
  | [ H: false = false |- _ ] => clear H
  | [ H: true = false |- _ ] => discriminate H
  | [ H: false = true |- _ ] => discriminate H
  | [ H: negb ?b = true |- _ ] => apply Bool.negb_true_iff in H
  | [ H: negb ?b = false |- _ ] => apply Bool.negb_false_iff in H
  | [ H: andb _ _ = true |- _ ] => apply Bool.andb_true_iff in H as []
  | [ H: orb _ _ = false |- _ ] => apply Bool.orb_false_iff in H as []
  end.

Open Scope Z_scope.
Goal
  forall x y : Z,
    x >? y = true ->
    x >=? y = true ->
    x <? y = true ->
    x <=? y = true ->
    x >? y = false ->
    x >=? y = false ->
    x <? y = false ->
    x <=? y = false ->
    True.
Proof.
  intros.
  all_to_prop.
Abort.
Close Scope Z_scope.

Ltac bool_to_prop :=
  repeat match goal with
  (* ==== Plain bools ==== *)
  | [ H: true = true |- _ ] => clear H
  | [ H: false = false |- _ ] => clear H
  | [ H: true = false |- _ ] => discriminate H
  | [ H: false = true |- _ ] => discriminate H
  | [ H: negb ?b = true |- _ ] => apply Bool.negb_true_iff in H
  | [ H: negb ?b = false |- _ ] => apply Bool.negb_false_iff in H
  | [ H: andb _ _ = true |- _ ] => apply Bool.andb_true_iff in H as []
  | [ H: orb _ _ = false |- _ ] => apply Bool.orb_false_iff in H as []
  end.

Lemma simpl_none_bind : ∀ {A B : Type} (mx : option A),
      (mx ≫= λ x : A, None : option B) = None.
Proof.
  unfold mbind, option_bind.
  intros. by case_match.
Qed.

Lemma simpl_none_orelse :
    forall T (X : option T), X <|> None = X.
Proof.
  unfold orElse. by destruct X.
Qed.
