From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From stdpp Require Import propset.

From MatchingLogic Require Import Syntax.

(* TODO: set? *)
(* TODO: well-formedness *)
Record NamedAxioms {Σ : Signature} :=
{
  NAName : Type;
  NAAxiom : NAName -> Pattern ;
  NAwf : forall (name : NAName), well_formed (NAAxiom name) ;
}.


Definition theory_of_NamedAxioms {Σ : Signature} (NAs : NamedAxioms) : Theory :=
  PropSet (fun p => exists (n : NAName NAs), p = NAAxiom n).

  
(* TODO: do we want to make this a type class? *)
Record NamedAxiomsIncluded {Σ : Signature}  (NA₁ NA₂ : NamedAxioms) :=
  { NAIinj : NAName NA₁ -> NAName NA₂;
    NAIax : forall (n : NAName NA₁), NAAxiom n = NAAxiom (NAIinj n);
  }.

Lemma NamedAxiomsIncluded_impl_TheoryIncluded {Σ : Signature} NA₁ NA₂:
  NamedAxiomsIncluded NA₁ NA₂ ->
  (theory_of_NamedAxioms NA₁) ⊆ (theory_of_NamedAxioms NA₂).
Proof.
  intros [inj ax].
  unfold theory_of_NamedAxioms.
  rewrite -> elem_of_subseteq.
  intros ϕ H.
  rewrite -> elem_of_PropSet. rewrite -> elem_of_PropSet in H.
  destruct H as [n Hn]. subst ϕ.
  eexists. auto.
Qed.

Program Definition NamedAxiomsIncluded_refl {Σ : Signature} NA : NamedAxiomsIncluded NA NA :=
  {| NAIinj := λ n, n; |}.
Next Obligation. auto. Qed.
(* TODO make it a stdpp preorder  *)

Program Definition NamedAxiomsIncluded_compose {Σ : Signature} NA₁ NA₂ NA₃ :
  NamedAxiomsIncluded NA₁ NA₂ ->
  NamedAxiomsIncluded NA₂ NA₃ ->
  NamedAxiomsIncluded NA₁ NA₃ :=
  λ HI₁ HI₂, {| NAIinj := λ n, NAIinj HI₂ (NAIinj HI₁ n);  |}.
Next Obligation.
  intros Σ NA₁ NA₂ NA₃ [inj₁ ax₁] [inj₂ ax₂] n.
  simpl.
  rewrite -ax₂.
  rewrite -ax₁.
  auto.
Qed.
