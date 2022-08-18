From Coq Require Import ssreflect ssrfun ssrbool.
From Coq Require Import Ensembles Logic.Classical_Prop.
From Coq Require Import Arith.Wf_nat Relations.Relation_Operators Wellfounded.Wellfounded.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq.micromega Require Import Lia.

From Equations Require Import Equations.

From stdpp Require Import base option.

From MatchingLogic Require Import
     Utils.wflexprod
     Syntax
     Semantics
     DerivedOperators_Syntax
     ProofSystem
     ProofMode
     Utils.extralibrary
.


Import MatchingLogic.Syntax.Notations MatchingLogic.DerivedOperators_Syntax.Notations.


Global Set Transparent Obligations.
Derive NoConfusion for Pattern.
Derive Subterm for Pattern.


Open Scope ml_scope.

Equations match_not {Σ : Signature} (p : Pattern)
  : ({ p' : Pattern & p = patt_not p'}) + (forall p', p <> patt_not p')
  :=
  match_not (p' ---> ⊥) := inl _ ;
  match_not _ := inr _ .
Solve Obligations with Tactics.program_simplify; CoreTactics.equations_simpl.
Next Obligation.
  intros. eapply existT. reflexivity.
Defined.

Lemma match_not_patt_not  {Σ : Signature} p: is_inl (match_not (patt_not p)).
Proof.
  funelim (match_not _). simpl. reflexivity.
Qed.

Equations match_or {Σ : Signature} (p : Pattern)
  : ({ p1 : Pattern & {p2 : Pattern & p = patt_or p1 p2}}) + (forall p1 p2, p <> patt_or p1 p2)
  :=
  match_or (p1 ---> p2) with match_not p1 => {
    | inl (existT p1' e) => inl _
    | inr _ => inr _
    } ;      
  match_or _ := inr _.
Solve Obligations with Tactics.program_simplify; CoreTactics.equations_simpl.
Next Obligation.
  intros. inversion e. subst. eapply existT. eapply existT. reflexivity.
Defined.
Next Obligation.
  intros.
  unfold patt_or.
  assert (p1 <> patt_not p0). auto.
  congruence.
Defined.

Lemma match_or_patt_or  {Σ : Signature} p1 p2: is_inl (match_or (patt_or p1 p2)).
Proof. reflexivity. Qed.

Equations?  match_and {Σ : Signature} (p : Pattern)
  : ({ p1 : Pattern & {p2 : Pattern & p = patt_and p1 p2}}) + (forall p1 p2, p <> patt_and p1 p2)
  :=
  match_and p with match_not p => {
    | inr _ := inr _ ;
    | inl (existT p' e') with match_or p' => {
      | inr _ := inr _ ;
      | inl (existT p1 (existT p2 e12)) with match_not p1 => {
        | inr _ := inr _ ;
        | inl (existT np1 enp1) with match_not p2 => {
          | inr _ := inr _ ;
          | inl (existT np2 enp2) := inl _
          }
        }
      }
    }.
Proof.
  - subst. eapply existT. eapply existT. reflexivity.
  - subst. intros. unfold not. intros Hcontra. inversion Hcontra.
    subst. specialize (n p0). contradiction.
  - subst. intros. unfold not. intros Hcontra. inversion Hcontra.
    subst. specialize (n p0). contradiction.
  - subst. intros. unfold not. intros Hcontra. inversion Hcontra.
    subst. specialize (n (patt_not p1) (patt_not p2)). contradiction.
  - intros. unfold not. intros Hcontra. subst.
    specialize (n ((patt_or (patt_not p1) (patt_not p2)))). contradiction.
Defined.

Lemma match_and_patt_and  {Σ : Signature} p1 p2: is_inl (match_and (patt_and p1 p2)).
Proof. reflexivity. Qed.

Lemma match_and_patt_or  {Σ : Signature} p1 p2: is_inl (match_and (patt_or p1 p2)) = false.
Proof.
  funelim (match_and _); rewrite -Heqcall; simpl; try reflexivity.
  subst. try inversion e'.
Qed.

Equations match_imp {Σ : Signature} (p : Pattern)
  : ({ p1 : Pattern & {p2 : Pattern & p = patt_imp p1 p2}}) + (forall p1 p2, p <> patt_imp p1 p2)
  :=
  match_imp (p1 ---> p2) := inl _ ;
  match_imp _ := inr _.
Solve Obligations with Tactics.program_simplify; CoreTactics.equations_simpl.
Next Obligation.
  intros. eapply existT. eapply existT. reflexivity.
Defined.

Lemma match_imp_patt_imp {Σ : Signature} p1 p2: is_inl (match_imp (patt_imp p1 p2)).
Proof. reflexivity. Qed.

Equations match_bott {Σ : Signature} (p : Pattern)
  : (p = patt_bott) + (p <> patt_bott)
  :=
  match_bott patt_bott := inl _ ;
  match_bott _ := inr _.
Solve Obligations with Tactics.program_simplify; CoreTactics.equations_simpl.
Next Obligation. reflexivity. Defined.


Equations match_a_impl_b_impl_c {Σ : Signature} (p : Pattern) :
  ({a : Pattern & {b : Pattern & {c : Pattern & p = patt_imp a (patt_imp b c)}}})
  + (forall (a b c : Pattern), p <> patt_imp a (patt_imp b c)) :=
  match_a_impl_b_impl_c (p1 ---> (p2 ---> p3)) := inl _ ;
  match_a_impl_b_impl_c _ := inr _ .
Solve Obligations with Tactics.program_simplify; CoreTactics.equations_simpl.
Next Obligation.
  intros Σ p1 p2 p3.
  do 3 eapply existT.
  reflexivity.
Defined.

