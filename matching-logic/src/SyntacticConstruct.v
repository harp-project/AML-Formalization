From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From stdpp Require Import base.

From MatchingLogic.Utils
Require Import
    extralibrary
    stdpp_ext
.

From MatchingLogic
Require Import
    Pattern
    Substitution
.

Import MatchingLogic.Substitution.Notations.

Section with_signature.
    Context {Σ : Signature}.


(* Every syntactic construct has a category (unary operator, binder etc),
   and has to have certain properties about well-formedness
   and substitution.
*)
Class (* E *) Binder (ebinder : Pattern -> Pattern)
    (bevo: db_index -> Pattern -> Pattern -> Pattern)
    (bsvo: db_index -> Pattern -> Pattern -> Pattern)
    (fevo: evar -> Pattern -> Pattern -> Pattern)
    (fsvo: svar -> Pattern -> Pattern -> Pattern)
    (feq: evar -> db_index -> Pattern -> Pattern)
    (fsq: svar -> db_index -> Pattern -> Pattern)
    :=
{
binder_bevar_subst :
  forall ψ,
    well_formed_closed ψ ->
    forall n ϕ,
      bevar_subst (ebinder ϕ) ψ n = bevo n ψ ϕ ;
binder_bsvar_subst :
  forall ψ,
    well_formed_closed ψ ->
    forall n ϕ,
      bsvar_subst (ebinder ϕ) ψ n = bsvo n ψ ϕ ;
binder_free_evar_subst :
  forall ψ x φ, well_formed_closed ψ ->
    (ebinder φ).[[evar: x ↦ ψ]] = fevo x ψ φ;
binder_free_svar_subst :
  forall ψ x φ, well_formed_closed ψ ->
    (ebinder φ).[[svar: x ↦ ψ]] = fsvo x ψ φ;
binder_evar_quantify :
  forall n x φ,
    evar_quantify x n (ebinder φ) = feq x n φ;
binder_svar_quantify :
  forall n x φ,
    svar_quantify x n (ebinder φ) = fsq x n φ;
}.

(* Class SBinder (sbinder : Pattern -> Pattern)
    (bevo: db_index -> Pattern -> Pattern -> Pattern)
    (bsvo: db_index -> Pattern -> Pattern -> Pattern)
    (fevo: evar -> Pattern -> Pattern -> Pattern)
    (fsvo: svar -> Pattern -> Pattern -> Pattern)
    (feq: evar -> db_index -> Pattern -> Pattern)
    (fsq: svar -> db_index -> Pattern -> Pattern)
:=
{
sbinder_bevar_subst :
  forall ψ,
    well_formed_closed ψ ->
    forall n φ,
      bevar_subst (sbinder φ) ψ n = bevo n ψ φ ;
sbinder_bsvar_subst :
  forall ψ,
    well_formed_closed ψ ->
    forall n φ,
      bsvar_subst (sbinder φ) ψ n = bsvo n ψ φ ;
sbinder_free_evar_subst :
  forall ψ x φ,
    (sbinder φ).[[evar: x ↦ ψ]] = fevo x ψ φ;
sbinder_free_svar_subst :
  forall ψ x φ,
    (sbinder φ).[[svar: x ↦ ψ]] = fsvo x ψ φ;
sbinder_evar_quantify :
  forall n x φ,
    evar_quantify x n (sbinder φ) = feq x n φ;
sbinder_svar_quantify :
  forall n x φ,
    svar_quantify x n (sbinder φ) = fsq x n φ;
}. *)

(* Non-variable nullary operation *)
Class NVNullary (nvnullary : Pattern) :=
{
nvnullary_bevar_subst :
  forall ψ,
    well_formed_closed ψ ->
    forall n,
      bevar_subst nvnullary ψ n = nvnullary ;
nvnullary_bsvar_subst :
  forall ψ,
    well_formed_closed ψ ->
    forall n,
      bevar_subst nvnullary ψ n = nvnullary ;
nvnullary_free_evar_subst :
  forall ψ x,
    nvnullary.[[evar: x ↦ ψ]] = nvnullary;
nvnullary_free_svar_subst :
  forall ψ x,
    nvnullary.[[svar: x ↦ ψ]] = nvnullary;
nvnullary_evar_quantify :
  forall n x,
    evar_quantify x n nvnullary = nvnullary;
nvnullary_svar_quantify :
  forall n x,
    svar_quantify x n nvnullary = nvnullary;

nvnullary_wf : well_formed nvnullary = true ;
}.

Class Unary (patt : Pattern -> Pattern) :=
{
unary_bevar_subst :
  forall ψ,
    well_formed_closed ψ ->
    forall n ϕ,
      bevar_subst (patt ϕ) ψ n = patt (bevar_subst ϕ ψ n) ;
unary_bsvar_subst :
  forall ψ,
    well_formed_closed ψ ->
    forall n ϕ,
      bsvar_subst (patt ϕ) ψ n = patt (bsvar_subst ϕ ψ n) ;
unary_free_evar_subst :
  forall ψ x φ,
    (patt φ).[[evar: x ↦ ψ]] = patt φ.[[evar: x ↦ ψ]];
unary_free_svar_subst :
  forall ψ x φ,
    (patt φ).[[svar: x ↦ ψ]] = patt φ.[[svar: x ↦ ψ]];
unary_evar_quantify :
  forall n x φ,
    evar_quantify x n (patt φ) = patt (evar_quantify x n φ);
unary_svar_quantify :
  forall n x φ,
    svar_quantify x n (patt φ) = patt (svar_quantify x n φ);

unary_wf : forall ψ, well_formed ψ -> well_formed (patt ψ) ;
}.

Class Binary (binary : Pattern -> Pattern -> Pattern) :=
{
binary_bevar_subst :
  forall ψ,
    well_formed_closed ψ ->
    forall n ϕ₁ ϕ₂,
      bevar_subst (binary ϕ₁ ϕ₂) ψ n = binary (bevar_subst ϕ₁ ψ n) (bevar_subst ϕ₂ ψ n) ;
binary_bsvar_subst :
  forall ψ,
    well_formed_closed ψ ->
    forall n ϕ₁ ϕ₂,
      bsvar_subst (binary ϕ₁ ϕ₂) ψ n = binary (bsvar_subst ϕ₁ ψ n) (bsvar_subst ϕ₂ ψ n) ;
binary_free_evar_subst :
  forall ψ x φ₁ φ₂,
    (binary φ₁ φ₂).[[evar: x ↦ ψ]] = binary (φ₁.[[evar: x ↦ ψ]]) (φ₂.[[evar: x ↦ ψ]]);
binary_free_svar_subst :
  forall ψ x φ₁ φ₂,
    (binary φ₁ φ₂).[[svar: x ↦ ψ]] = binary (φ₁.[[svar: x ↦ ψ]]) (φ₂.[[svar: x ↦ ψ]]);
binary_evar_quantify :
  forall n x φ₁ φ₂,
    evar_quantify x n (binary φ₁ φ₂) = binary (evar_quantify x n φ₁) (evar_quantify x n φ₂);
binary_svar_quantify :
  forall n x φ₁ φ₂,
    svar_quantify x n (binary φ₁ φ₂) = binary (svar_quantify x n φ₁) (svar_quantify x n φ₂);

binary_wf : forall ψ1 ψ2, well_formed ψ1 -> well_formed ψ2 -> well_formed (binary ψ1 ψ2) ;
}.

Definition simpl_bevar_subst' :=
(@binder_bevar_subst,
 (* @sbinder_bevar_subst, *)
 @nvnullary_bevar_subst,
 @unary_bevar_subst,
 @binary_bevar_subst
).

Definition simpl_bsvar_subst' :=
(@binder_bsvar_subst,
 (* @sbinder_bsvar_subst, *)
 @nvnullary_bsvar_subst,
 @unary_bsvar_subst,
 @binary_bsvar_subst
).

Definition simpl_free_evar_subst' :=
(@binder_free_evar_subst,
(*  @sbinder_free_evar_subst, *)
 @nvnullary_free_evar_subst,
 @unary_free_evar_subst,
 @binary_free_evar_subst
).

Definition simpl_free_svar_subst' :=
(@binder_free_svar_subst,
(*  @sbinder_free_svar_subst, *)
 @nvnullary_free_svar_subst,
 @unary_free_svar_subst,
 @binary_free_svar_subst
).

Definition simpl_evar_quantify' :=
(@binder_evar_quantify,
(*  @sbinder_evar_quantify, *)
 @nvnullary_evar_quantify,
 @unary_evar_quantify,
 @binary_evar_quantify
).

Definition simpl_svar_quantify' :=
(@binder_svar_quantify,
(*  @sbinder_svar_quantify, *)
 @nvnullary_svar_quantify,
 @unary_svar_quantify,
 @binary_svar_quantify
).

#[global]
Instance Binder_exists : Binder patt_exists _ _ _ _ _ _ :=
{|
binder_bevar_subst := bevar_subst_exists ;
binder_bsvar_subst := bsvar_subst_exists ;
binder_free_evar_subst := λ ψ x φ _, free_evar_subst_exists ψ x φ;
binder_free_svar_subst := λ ψ x φ _, free_svar_subst_exists ψ x φ;
binder_evar_quantify := evar_quantify_exists;
binder_svar_quantify := svar_quantify_exists;
|}.

#[global]
Instance Binder_mu : Binder patt_mu _ _ _ _ _ _ :=
{|
binder_bevar_subst := bevar_subst_mu ;
binder_bsvar_subst := bsvar_subst_mu ;
binder_free_evar_subst := λ ψ x φ _, free_evar_subst_mu ψ x φ;
binder_free_svar_subst := λ ψ x φ _, free_svar_subst_mu ψ x φ;
binder_evar_quantify := evar_quantify_mu;
binder_svar_quantify := svar_quantify_mu;
|}.


#[global]
Instance NVNullary_bott : NVNullary patt_bott :=
{|
nvnullary_bevar_subst := bevar_subst_bott ;
nvnullary_bsvar_subst := bsvar_subst_bott ;
nvnullary_free_evar_subst := ltac:(reflexivity);
nvnullary_free_svar_subst := ltac:(reflexivity);
nvnullary_evar_quantify := ltac:(reflexivity);
nvnullary_svar_quantify := ltac:(reflexivity);
nvnullary_wf := well_formed_bott ;
|}.

#[global]
Instance NVNullary_sym s : NVNullary (patt_sym s) :=
{|
nvnullary_bevar_subst := λ ψ (wfcψ : well_formed_closed ψ) n, @bevar_subst_sym Σ ψ wfcψ n s ;
nvnullary_bsvar_subst := λ ψ (wfcψ : well_formed_closed ψ) n, @bsvar_subst_sym Σ ψ wfcψ n s;
nvnullary_free_evar_subst := ltac:(reflexivity);
nvnullary_free_svar_subst := ltac:(reflexivity);
nvnullary_evar_quantify := ltac:(reflexivity);
nvnullary_svar_quantify := ltac:(reflexivity);
nvnullary_wf := (well_formed_sym s) ;
|}.

#[global]
Instance Binary_app : Binary patt_app :=
{|
binary_bevar_subst := bevar_subst_app ;
binary_bsvar_subst := bsvar_subst_app ;
binary_free_evar_subst := ltac:(reflexivity);
binary_free_svar_subst := ltac:(reflexivity);
binary_evar_quantify := ltac:(reflexivity);
binary_svar_quantify := ltac:(reflexivity);
binary_wf := well_formed_app ;
|}.

#[global]
Instance Binary_imp : Binary patt_imp :=
{|
binary_bevar_subst := bevar_subst_imp ;
binary_bsvar_subst := bsvar_subst_imp ;
binary_free_evar_subst := ltac:(reflexivity);
binary_free_svar_subst := ltac:(reflexivity);
binary_evar_quantify := ltac:(reflexivity);
binary_svar_quantify := ltac:(reflexivity);
binary_wf := well_formed_imp ;
|}.

End with_signature.