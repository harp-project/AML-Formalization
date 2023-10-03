From Coq Require Import ssreflect ssrfun ssrbool.

Require Import Coq.Setoids.Setoid Coq.Classes.Morphisms Coq.Relations.Relations.
Require Import Logic.IndefiniteDescription Coq.Logic.FunctionalExtensionality.

From stdpp
Require Import
    base
    decidable
    propset
    sets
.


Class Surj' {A B} (R : relation B) (f : A -> B) : Type := {
    surj'_inv : B -> A ;
    surj'_pf: ∀ (b : B), R (f (surj'_inv b)) b
}.

#[export]
Instance surj_surj' {A B} (R : relation B) (f : A -> B) {_ : @Surj' A B R f} : Surj R f.
Proof.
    unfold Surj.
    intros y.
    exists (surj'_inv y).
    apply surj'_pf.
Defined.

#[export]
Instance surj'_id {A} : @Surj' A A (=) Datatypes.id.
Proof.
    exists Datatypes.id.
    intros b. reflexivity.
Defined.

#[export]
    Instance compose_surj' {A B C} R (f : A → B) (g : B → C) :
    Surj' (=) f -> Surj' R g -> Surj' R (g ∘ f).
Proof.
    intros [sf Hsf] [sg Hsg].
    exists (sf ∘ sg).
    intros x. unfold compose.
    rewrite Hsf.
    apply Hsg.
Qed.
