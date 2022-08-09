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

From stdpp Require Import fin_sets.

From MatchingLogic
Require Import
    Pattern
    Substitution
.

Import MatchingLogic.Substitution.Notations.

Section with_signature.
  Context {Σ : Signature}.

(**
  * General substitutions


  First, we extract the information that identify the different substiutions:
  - How to "step" or "increase" (mostly de Bruijn indices) some properties
    in the recursive calls for binders
  - How the substitutions work for variables (both set and element, bound and free)
*)

  Record SpecificSubst (A : Type) : Type := {
      increase_ex : A -> A;
      increase_mu : A -> A;
      on_fevar : A -> evar -> Pattern;
      on_fsvar : A -> svar -> Pattern;
      on_bevar : A -> db_index -> Pattern;
      on_bsvar : A -> db_index -> Pattern;
  }.

  (**
    We define the general structure of substitutions, and use the specific
    information for the binders and the variables defined in `SpeificSubst`.
   *)

  Fixpoint apply_subst {A : Type} (s : SpecificSubst A) (st : A) (phi : Pattern) :=
    match phi with
    | patt_free_evar x => on_fevar s st x
    | patt_free_svar X => on_fsvar s st X
    | patt_bound_evar n => on_bevar s st n
    | patt_bound_svar N => on_bsvar s st N
    | patt_sym sm => patt_sym sm
    | patt_app phi1 phi2 => patt_app (apply_subst s st phi1) (apply_subst s st phi2)
    | patt_bott => patt_bott
    | patt_imp phi1 phi2 => patt_imp (apply_subst s st phi1) (apply_subst s st phi2)
    | patt_exists phi' => patt_exists (apply_subst s (increase_ex s st) phi')
    | patt_mu phi' => patt_mu (apply_subst s (increase_mu s st) phi')
    end.

  (** For substitutions that can be described with the previous definition,
      we can instantiate the following type class: *)

  Class PatternMorphism (f : Pattern -> Pattern) := {
      base_type : Type ;
      init : base_type ;
      spec_data : SpecificSubst base_type ;
      correctness : forall phi, f phi = apply_subst spec_data init phi
  }.

  (** Variable quantifications are such morphisms: *)

  #[global]
  Program Instance Evar_quantify_morphism (x' : evar) (db : db_index) :
     PatternMorphism (evar_quantify x' db) := {
    base_type := db_index ;
    init := db ;
    spec_data := {|
      increase_ex := fun x => S x ;
      increase_mu := id ;
      on_fevar := fun level x => if decide (x' = x)
                                 then patt_bound_evar level
                                 else patt_free_evar x;
      on_fsvar := fun _ X => patt_free_svar X;
      on_bevar := fun _ n => patt_bound_evar n;
      on_bsvar := fun _ N => patt_bound_svar N;
    |}
  }.
  Next Obligation.
    intros x' db φ. revert x' db. induction φ; intros x' db; simpl; auto.
    * case_match; simpl; auto.
    * now rewrite -> IHφ1, IHφ2.
    * now rewrite -> IHφ1, IHφ2.
    * now rewrite IHφ.
    * now rewrite IHφ.
  Defined.


  #[global]
  Program Instance Svar_quantify_morphism (x' : svar) (db : db_index) :
     PatternMorphism (svar_quantify x' db) := {
    base_type := db_index ;
    init := db ;
    spec_data := {|
      increase_ex := id;
      increase_mu := fun x => S x ;
      on_fevar := fun _ X => patt_free_evar X;
      on_fsvar := fun level x => if decide (x' = x)
                                 then patt_bound_svar level
                                 else patt_free_svar x;
      on_bevar := fun _ n => patt_bound_evar n;
      on_bsvar := fun _ N => patt_bound_svar N;
    |}
  }.
  Next Obligation.
    intros x' db φ. revert x' db. induction φ; intros x' db; simpl; auto.
    * case_match; simpl; auto.
    * now rewrite -> IHφ1, IHφ2.
    * now rewrite -> IHφ1, IHφ2.
    * now rewrite IHφ.
    * now rewrite IHφ.
  Defined.

  #[global]
  Program Instance Bevar_subst_morphism (db : db_index) (ψ : Pattern) :
     PatternMorphism (bevar_subst db ψ) := {
    base_type := db_index ;
    init := db ;
    spec_data := {|
      increase_ex := fun x => S x ;
      increase_mu := id ;
      on_fevar := fun _ x => patt_free_evar x;
      on_fsvar := fun _ X => patt_free_svar X;
      on_bevar := fun x n =>
        match compare_nat n x with
        | Nat_less _ _ _ => patt_bound_evar n
        | Nat_equal _ _ _ => ψ
        | Nat_greater _ _ _ => patt_bound_evar (Nat.pred n)
        end;
      on_bsvar := fun _ N => patt_bound_svar N;
    |}
  }.
  Next Obligation.
    intros x' db φ. revert x' db. induction φ; intros x' db; simpl; auto.
    * case_match; simpl; auto.
    * now rewrite -> IHφ1, IHφ2.
    * now rewrite -> IHφ1, IHφ2.
    * now rewrite IHφ.
    * now rewrite IHφ.
  Defined.

  #[global]
  Program Instance Bsvar_subst_morphism (Db : db_index) (ψ : Pattern) :
     PatternMorphism (bsvar_subst Db ψ) := {
    base_type := db_index ;
    init := Db ;
    spec_data := {|
      increase_ex := id ;
      increase_mu := fun x => S x ;
      on_fevar := fun _ x => patt_free_evar x;
      on_fsvar := fun _ X => patt_free_svar X;
      on_bevar := fun _ n => patt_bound_evar n;
      on_bsvar := fun X N =>
        match compare_nat N X with
        | Nat_less _ _ _ => patt_bound_svar N
        | Nat_equal _ _ _ => ψ
        | Nat_greater _ _ _ => patt_bound_svar (Nat.pred N)
        end;
    |}
  }.
  Next Obligation.
    intros x' db φ. revert x' db. induction φ; intros x' db; simpl; auto.
    * case_match; simpl; auto.
    * now rewrite -> IHφ1, IHφ2.
    * now rewrite -> IHφ1, IHφ2.
    * now rewrite IHφ.
    * now rewrite IHφ.
  Defined.

  #[global]
  Program Instance Evar_open_morphism (db : db_index) (x : evar) :
     PatternMorphism (evar_open db x) := {
    base_type := db_index ;
    init := db ;
    spec_data := {|
      increase_ex := fun x => S x ;
      increase_mu := id ;
      on_fevar := fun _ x => patt_free_evar x;
      on_fsvar := fun _ X => patt_free_svar X;
      on_bevar := fun dbi n =>
        match compare_nat n dbi with
        | Nat_less _ _ _ => patt_bound_evar n
        | Nat_equal _ _ _ => patt_free_evar x
        | Nat_greater _ _ _ => patt_bound_evar (Nat.pred n)
        end;
      on_bsvar := fun _ N => patt_bound_svar N;
    |}
  }.
  Next Obligation.
    unfold evar_open. intros. rewrite correctness. auto.
  Defined.

  #[global]
  Program Instance Svar_open_morphism (Db : db_index) (X : svar) :
     PatternMorphism (svar_open Db X) := {
   base_type := db_index ;
    init := Db ;
    spec_data := {|
      increase_ex := id ;
      increase_mu := fun x => S x ;
      on_fevar := fun _ x => patt_free_evar x;
      on_fsvar := fun _ X => patt_free_svar X;
      on_bevar := fun _ n => patt_bound_evar n;
      on_bsvar := fun Dbi N =>
        match compare_nat N Dbi with
        | Nat_less _ _ _ => patt_bound_svar N
        | Nat_equal _ _ _ => patt_free_svar X
        | Nat_greater _ _ _ => patt_bound_svar (Nat.pred N)
        end;
    |}
  }.
  Next Obligation.
    unfold svar_open. intros. rewrite correctness. auto.
  Defined.

  #[global]
  Program Instance Free_evar_subst_morphism (x : evar) (ψ : Pattern) :
     PatternMorphism (free_evar_subst x ψ) := {
    base_type := evar ;
    init := x ;
    spec_data := {|
      increase_ex := id ;
      increase_mu := id ;
      on_fevar := fun x x' => if decide (x = x') then ψ else patt_free_evar x';
      on_fsvar := fun _ X => patt_free_svar X;
      on_bevar := fun _ n => patt_bound_evar n;
      on_bsvar := fun _ N => patt_bound_svar N;
    |}
  }.
  Next Obligation.
    intros x' db φ. revert x' db. induction φ; intros x' db; simpl; auto.
    * case_match; simpl; auto.
    * now rewrite -> IHφ1, IHφ2.
    * now rewrite -> IHφ1, IHφ2.
    * now rewrite IHφ.
    * now rewrite IHφ.
  Defined.

  #[global]
  Program Instance Free_svar_subst_morphism (X : svar) (ψ : Pattern) :
     PatternMorphism (free_svar_subst X ψ) := {
    base_type := svar ;
    init := X ;
    spec_data := {|
      increase_ex := id ;
      increase_mu := id ;
      on_fevar := fun _ x => patt_free_evar x ;
      on_fsvar := fun X X' => if decide (X = X') then ψ else patt_free_svar X';
      on_bevar := fun _ n => patt_bound_evar n;
      on_bsvar := fun _ N => patt_bound_svar N;
    |}
  }.
  Next Obligation.
    intros x' db φ. revert x' db. induction φ; intros x' db; simpl; auto.
    * case_match; simpl; auto.
    * now rewrite -> IHφ1, IHφ2.
    * now rewrite -> IHφ1, IHφ2.
    * now rewrite IHφ.
    * now rewrite IHφ.
  Defined.

(**

  Next, we define shifting substitutions for the body of the binders.

*)

Definition shift_exists_subst (f : Pattern -> Pattern) (m : PatternMorphism f)
    : (Pattern -> Pattern)
    := (apply_subst spec_data (increase_ex spec_data init)).

Definition shift_mu_subst (f : Pattern -> Pattern) (m : PatternMorphism f)
    : (Pattern -> Pattern)
    := (apply_subst spec_data (increase_mu spec_data init)).

(**  Shifting preserves the morphism property *)

Lemma shift_exists_morphism (f : Pattern -> Pattern) (m : PatternMorphism f) :
    PatternMorphism (shift_exists_subst m).
Proof.
    destruct m as [A0 i0 d0 corr0].
    simpl.
    exists A0 (increase_ex d0 i0) d0.
    intros phi.
    reflexivity.
Defined.

Lemma shift_mu_morphism (f : Pattern -> Pattern) (m : PatternMorphism f) :
    PatternMorphism (shift_mu_subst m).
Proof.
    destruct m as [A0 i0 d0 corr0].
    simpl.
    exists A0 (increase_mu d0 i0) d0.
    intros phi.
    reflexivity.
Defined.

(**
   * Substitution type classes for the different syntacical cateories

   Every syntactic construct has a category (unary operator, binder etc),
   and has to have certain properties about well-formedness
   and substitution.
*)

Class Binary (binary : Pattern -> Pattern -> Pattern) := {
    binary_morphism :
      forall f (f_morph : PatternMorphism f) (phi1 phi2 : Pattern),
        f (binary phi1 phi2) = binary (f phi1) (f phi2) ;
     binary_wf : forall ψ1 ψ2, well_formed ψ1 -> well_formed ψ2 -> 
        well_formed (binary ψ1 ψ2) ;
}.

Class Unary (unary : Pattern -> Pattern) := {
    unary_morphism :
      forall f (f_morph : PatternMorphism f) (phi : Pattern),
        f (unary phi) = unary (f phi) ;
    unary_wf : forall ψ, well_formed ψ -> well_formed (unary ψ) ;
}.

Class Nullary (nullary : Pattern) := {
    nullary_morphism :
      forall f (f_morph : PatternMorphism f),
        f nullary = nullary ;
    nullary_wf : well_formed nullary ;
}.

Class EBinder (binder : Pattern -> Pattern) := {
    ebinder_morphism :
      forall f (f_morph : PatternMorphism f) (phi : Pattern),
        f (binder phi) = binder (shift_exists_subst f_morph phi) ;
}.

Class SBinder (binder : Pattern -> Pattern) := {
    sbinder_morphism :
      forall f (f_morph : PatternMorphism f) (phi : Pattern),
        f (binder phi) = binder (shift_mu_subst f_morph phi) ;
}.


(** Next, we define the substitution simplification record: *)

Definition mlSimpl' :=
(
  @binary_morphism,
  @unary_morphism,
  @nullary_morphism,
  @ebinder_morphism,
  @sbinder_morphism
).

(** Finally, we define instances for the primitives of matching logic: *)

#[global]
Program Instance EBinder_exists : EBinder patt_exists := {}.
Next Obligation.
  intros f m φ. repeat rewrite correctness.
  simpl. reflexivity.
Defined.

#[global]
Program Instance SBinder_mu : SBinder patt_mu := {}.
Next Obligation.
  intros f m φ. repeat rewrite correctness.
  simpl. reflexivity.
Defined.

#[global]
Program Instance Binary_imp : Binary patt_imp := {}.
Next Obligation.
  intros f m φ1 φ2. repeat rewrite correctness.
  simpl. reflexivity.
Defined.
Next Obligation.
  intros φ1 φ2 WF1 WF2.
  now apply well_formed_imp.
Defined.

#[global]
Program Instance Binary_app : Binary patt_app := {}.
Next Obligation.
  intros f m φ1 φ2. repeat rewrite correctness.
  simpl. reflexivity.
Defined.
Next Obligation.
  intros φ1 φ2 WF1 WF2.
  now apply well_formed_app.
Defined.

#[global]
Program Instance Nullary_bott : Nullary patt_bott := {}.
Next Obligation.
  intros f m. repeat rewrite correctness.
  simpl. reflexivity.
Defined.
Next Obligation.
  auto.
Defined.

#[global]
Program Instance Nullary_sym s : Nullary (patt_sym s) := {}.
Next Obligation.
  intros s f m. repeat rewrite correctness.
  simpl. reflexivity.
Defined.
Next Obligation.
  auto.
Defined.

End with_signature.