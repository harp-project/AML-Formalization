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
Print evar_quantify.
Print free_evar_subst.
Check bevar_subst_exists.
Search free_evar_subst patt_exists.
Class EBinder (ebinder : Pattern -> Pattern)
    (fevo: db_index -> Pattern -> Pattern -> Pattern )
    (fsvo: db_index -> Pattern -> Pattern -> Pattern )
    :=
{
ebinder_bevar_subst :
  forall ψ,
    well_formed_closed ψ ->
    forall n ϕ,
      bevar_subst (ebinder ϕ) ψ n = fevo n ψ ϕ ;
ebinder_bsvar_subst :
  forall ψ,
    well_formed_closed ψ ->
    forall n ϕ,
      bsvar_subst (ebinder ϕ) ψ n = fsvo n ψ ϕ ;
ebinder_free_evar_subst :
  forall ψ φ x,
    (ebinder φ).[[evar: x ↦ ψ]] = ebinder (φ.[[evar: x ↦ ψ]])
}.

Class SBinder (sbinder : Pattern -> Pattern) :=
{
sbinder_bevar_subst :
  forall ψ,
    well_formed_closed ψ ->
    forall n ϕ,
      bevar_subst (sbinder ϕ) ψ n = sbinder (bevar_subst ϕ ψ n) ;
sbinder_bsvar_subst :
  forall ψ,
    well_formed_closed ψ ->
    forall n ϕ,
      bsvar_subst (sbinder ϕ) ψ n = sbinder (bsvar_subst ϕ ψ (S n)) ;
}.

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

binary_wf : forall ψ1 ψ2, well_formed ψ1 -> well_formed ψ2 -> well_formed (binary ψ1 ψ2) ;
}.

Definition simpl_bevar_subst' :=
(@ebinder_bevar_subst,
 @sbinder_bevar_subst,
 @nvnullary_bevar_subst,
 @unary_bevar_subst,
 @binary_bevar_subst
).

Definition simpl_bsvar_subst' :=
(@ebinder_bsvar_subst,
 @sbinder_bsvar_subst,
 @nvnullary_bsvar_subst,
 @unary_bsvar_subst,
 @binary_bsvar_subst
).

#[global]
Instance EBinder_exists : EBinder patt_exists _ _ :=
{|
ebinder_bevar_subst := bevar_subst_exists ;
ebinder_bsvar_subst := bsvar_subst_exists ;
|}.

#[global]
Instance SBinder_mu : SBinder patt_mu :=
{|
sbinder_bevar_subst := bevar_subst_mu ;
sbinder_bsvar_subst := bsvar_subst_mu ;
|}.


#[global]
Program Instance NVNullary_bott : NVNullary patt_bott :=
{|
nvnullary_bevar_subst := bevar_subst_bott ;
nvnullary_bsvar_subst := bsvar_subst_bott ;
nvnullary_wf := well_formed_bott ;
|}.

#[global]
Instance NVNullary_sym s : NVNullary (patt_sym s) :=
{|
nvnullary_bevar_subst := λ ψ (wfcψ : well_formed_closed ψ) n, @bevar_subst_sym Σ ψ wfcψ n s ;
nvnullary_bsvar_subst := λ ψ (wfcψ : well_formed_closed ψ) n, @bsvar_subst_sym Σ ψ wfcψ n s;
nvnullary_wf := (well_formed_sym s) ;
|}.

#[global]
Instance Binary_app : Binary patt_app :=
{|
binary_bevar_subst := bevar_subst_app ;
binary_bsvar_subst := bsvar_subst_app ;
binary_wf := well_formed_app ;
|}.

#[global]
Instance Binary_imp : Binary patt_imp :=
{|
binary_bevar_subst := bevar_subst_imp ;
binary_bsvar_subst := bsvar_subst_imp ;
binary_wf := well_formed_imp ;
|}.

End with_signature.