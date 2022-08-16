From Coq Require Import ssreflect ssrfun ssrbool.

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
    IndexManipulation
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

  Record SpecificSubst {A : Type} : Type := {
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

  Fixpoint apply_subst {A : Type} (s : SpecificSubst) (st : A) (phi : Pattern) :=
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

  Class PatternMorphism {A : Type} (f : A -> Pattern -> Pattern) := {
      spec_data : SpecificSubst ;
      correctness : forall a (phi : Pattern), f a phi = apply_subst spec_data a phi
  }.

  (** Variable quantifications are such morphisms: *)

  #[global]
  Program Instance Evar_quantify_morphism (x' : evar) :
     PatternMorphism (evar_quantify x') := {
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
  Program Instance Svar_quantify_morphism (x' : svar) :
     PatternMorphism (svar_quantify x') := {
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
  Program Instance Bevar_subst_morphism (ψ : Pattern) :
     PatternMorphism (bevar_subst ψ) := {
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
  Program Instance Bsvar_subst_morphism (ψ : Pattern) :
     PatternMorphism (bsvar_subst ψ) := {
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
  Program Instance Evar_open_morphism (x : evar) :
     PatternMorphism (evar_open x) := {
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
  Program Instance Svar_open_morphism (X : svar) :
     PatternMorphism (svar_open X) := {
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
  Program Instance Free_evar_subst_morphism (ψ : Pattern) :
     PatternMorphism (free_evar_subst ψ) := {
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
  Program Instance Free_svar_subst_morphism (ψ : Pattern) :
     PatternMorphism (free_svar_subst ψ) := {
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

Definition shift_exists_subst {A : Type} (f : A -> Pattern -> Pattern) (m : PatternMorphism f)
    : (A -> Pattern -> Pattern)
    := fun a => apply_subst spec_data (increase_ex spec_data a).

Definition shift_mu_subst {A : Type} (f : A -> Pattern -> Pattern) (m : PatternMorphism f)
    : (A -> Pattern -> Pattern)
    := fun a => apply_subst spec_data (increase_mu spec_data a).

(**
   * Substitution type classes for the different syntacical cateories

   Every syntactic construct has a category (unary operator, binder etc),
   and has to have certain properties about well-formedness
   and substitution.
*)

Class Binary (binary : Pattern -> Pattern -> Pattern) := {
    binary_morphism :
      forall {A : Type} (f : A -> Pattern -> Pattern) (f_morph : PatternMorphism f) (phi1 phi2 : Pattern) a,
        f a (binary phi1 phi2) = binary (f a phi1) (f a phi2) ;
     binary_wf : forall ψ1 ψ2, well_formed ψ1 -> well_formed ψ2 -> 
        well_formed (binary ψ1 ψ2) ;
}.

Class Unary (unary : Pattern -> Pattern) := {
    unary_morphism :
      forall {A : Type} (f : A -> Pattern -> Pattern) (f_morph : PatternMorphism f) (phi : Pattern) a,
        f a (unary phi) = unary (f a phi) ;
    unary_wf : forall ψ, well_formed ψ -> well_formed (unary ψ) ;
}.

Class Nullary (nullary : Pattern) := {
    nullary_morphism :
      forall {A : Type} (f : A -> Pattern -> Pattern) (f_morph : PatternMorphism f) a,
        f a nullary = nullary ;
    nullary_wf : well_formed nullary ;
}.

Class EBinder (binder : Pattern -> Pattern) := {
    ebinder_morphism :
      forall {A : Type} (f : A -> Pattern -> Pattern) (f_morph : PatternMorphism f) (phi : Pattern) a,
        f a (binder phi) = binder (f (increase_ex spec_data a) phi) ;
}.

Class SBinder (binder : Pattern -> Pattern) := {
    sbinder_morphism :
      forall {A : Type} (f : A -> Pattern -> Pattern) (f_morph : PatternMorphism f) (phi : Pattern) a,
        f a (binder phi) = binder (f (increase_mu spec_data a) phi) ;
}.

(** Next, we define instances for the primitives of matching logic: *)

#[global]
Program Instance EBinder_exists : EBinder patt_exists := {}.
Next Obligation.
  intros A f m φ a. repeat rewrite correctness.
  simpl. reflexivity.
Defined.

#[global]
Program Instance SBinder_mu : SBinder patt_mu := {}.
Next Obligation.
  intros A f m φ a. repeat rewrite correctness.
  simpl. reflexivity.
Defined.

#[global]
Program Instance Binary_imp : Binary patt_imp := {}.
Next Obligation.
  intros A f m φ1 φ2 a. repeat rewrite correctness.
  simpl. reflexivity.
Defined.
Next Obligation.
  intros φ1 φ2 WF1 WF2.
  now apply well_formed_imp.
Defined.

#[global]
Program Instance Binary_app : Binary patt_app := {}.
Next Obligation.
  intros A f m φ1 φ2 a. repeat rewrite correctness.
  simpl. reflexivity.
Defined.
Next Obligation.
  intros φ1 φ2 WF1 WF2.
  now apply well_formed_app.
Defined.

#[global]
Program Instance Nullary_bott : Nullary patt_bott := {}.
Next Obligation.
  intros A f m a. repeat rewrite correctness.
  simpl. reflexivity.
Defined.
Next Obligation.
  auto.
Defined.

#[global]
Program Instance Nullary_sym s : Nullary (patt_sym s) := {}.
Next Obligation.
  intros A s f m a. repeat rewrite correctness.
  simpl. reflexivity.
Defined.
Next Obligation.
  auto.
Defined.

Class SwappableEx {A : Type} (f : A -> Pattern -> Pattern) (g : Pattern -> Pattern)
  (m : PatternMorphism f) :=
{
  ezero_increase : forall a,
    on_bevar spec_data (increase_ex spec_data a) 0 = patt_bound_evar 0 ;
  eswap : forall phi a,
    apply_subst spec_data (increase_ex spec_data a) (g phi) =
    g (apply_subst spec_data a phi) ;
}.

#[global]
Program Instance Bevar_subst_swaps_ex_nesting (ψ : Pattern) (p : well_formed_closed ψ) :
  @SwappableEx _ (bevar_subst ψ) nest_ex (Bevar_subst_morphism ψ).
Next Obligation.
  intros. reflexivity.
Defined.
Next Obligation.
  intros ψ WFψ phi a.
  do 2 rewrite <- correctness.
  unfold nest_ex. rewrite <- nest_ex_gt; auto. 2: lia.
  rewrite Nat.add_comm. reflexivity.
Defined.

#[global]
Program Instance Bsvar_subst_swaps_ex_nesting (ψ : Pattern) (p : well_formed_closed ψ) :
  @SwappableEx _ (bsvar_subst ψ) nest_ex (Bsvar_subst_morphism ψ).
Next Obligation.
  intros. reflexivity.
Defined.
Next Obligation.
  intros ψ WFψ phi a.
  do 2 rewrite <- correctness.
  unfold nest_ex.
  rewrite bsvar_subst_nest_ex_aux_comm; auto.
  apply andb_true_iff in WFψ. apply WFψ.
Defined.

#[global]
Program Instance Fevar_subst_swaps_nesting (ψ : Pattern) (p : well_formed_closed ψ) :
  @SwappableEx _ (free_evar_subst ψ) nest_ex (Free_evar_subst_morphism ψ).
Next Obligation.
  intros. reflexivity.
Defined.
Next Obligation.
  intros ψ WFψ phi a.
  do 2 rewrite <- correctness.
  unfold nest_ex.
  rewrite nest_ex_free_evar_subst; auto.
  apply andb_true_iff in WFψ. apply WFψ.
Defined.

#[global]
Program Instance Fsvar_subst_swaps_nesting (ψ : Pattern) (p : well_formed_closed ψ) :
  @SwappableEx _ (free_svar_subst ψ) nest_ex (Free_svar_subst_morphism ψ).
Next Obligation.
  intros. reflexivity.
Defined.
Next Obligation.
  intros ψ WFψ phi a.
  do 2 rewrite <- correctness.
  unfold nest_ex.
  rewrite nest_ex_free_svar_subst; auto.
  apply andb_true_iff in WFψ. apply WFψ.
Defined.

#[global]
Program Instance Evar_quantify_swaps_ex_nesting (x : evar) :
  @SwappableEx _ (evar_quantify x) nest_ex (Evar_quantify_morphism x).
Next Obligation.
  intros. reflexivity.
Defined.
Next Obligation.
  intros ψ phi a.
  do 2 rewrite <- correctness.
  unfold nest_ex. rewrite <- nest_ex_gt_evar_quantify; auto. 2: lia.
  rewrite Nat.add_comm. reflexivity.
Defined.

#[global]
Program Instance Svar_quantify_swaps_ex_nesting (X : svar) :
  @SwappableEx _ (svar_quantify X) nest_ex (Svar_quantify_morphism X).
Next Obligation.
  intros. reflexivity.
Defined.
Next Obligation.
  intros ψ phi a.
  do 2 rewrite <- correctness.
  unfold nest_ex. now rewrite nest_ex_svar_quantify.
Defined.

#[global]
Program Instance Evar_open_swaps_ex_nesting (x : evar) :
  @SwappableEx _ (evar_open x) nest_ex (Evar_open_morphism x).
Next Obligation.
  intros. reflexivity.
Defined.
Next Obligation.
  (* TODO: here type class inference fails without the explicit parameters *)
  intros. rewrite (@eswap _ _ _ _ (Bevar_subst_swaps_ex_nesting (patt_free_evar x) _)); auto.
Defined.

#[global]
Program Instance Svar_open_swaps_ex_nesting (X : svar) :
  @SwappableEx _ (svar_open X) nest_ex (Svar_open_morphism X).
Next Obligation.
  intros. reflexivity.
Defined.
Next Obligation.
  (* TODO: here type class inference fails without the explicit parameters *)
  intros. rewrite (@eswap _ _ _ _ (Bsvar_subst_swaps_ex_nesting (patt_free_svar X) _)); auto.
Defined.

(* TODO: mu operations:

Class SwappableMu {A : Type} (f : A -> Pattern -> Pattern) (g : Pattern -> Pattern)
  (m : PatternMorphism f) :=
{
  szero_increase : forall a,
    apply_subst spec_data (increase_mu spec_data a) (patt_bound_svar 0) = patt_bound_svar 0 ;
  sswap_f_g : forall phi a,
    apply_subst spec_data (increase_mu spec_data a) (g phi) =
    g (apply_subst spec_data a phi) ;
}.

#[global]
Program Instance Bsvar_subst_swaps_nesting (ψ : Pattern) (p : well_formed_closed ψ) :
  @SwappableMu _ (bsvar_subst ψ) nest_mu (Bsvar_subst_morphism ψ).
Next Obligation.
  intros. rewrite <- correctness. reflexivity.
Defined.
Next Obligation.
  intros ψ WFψ phi a.
  do 2 rewrite <- correctness.
  unfold nest_mu. rewrite <- nest_mu_gt; auto. 2: lia.
  rewrite Nat.add_comm. reflexivity.
Defined. *)

Class ESortedBinder (binder : Pattern -> Pattern -> Pattern) (g : Pattern -> Pattern) := {
    esorted_binder_morphism :
      forall {A : Type} (f : A -> Pattern -> Pattern)
         (f_morph : PatternMorphism f)
         (f_swap : SwappableEx f g f_morph) (s phi : Pattern) a,
      f a (binder s phi) = binder (f a s) (f (increase_ex spec_data a) phi) ;
}.

Class SSortedBinder (binder : Pattern -> Pattern -> Pattern) (g : Pattern -> Pattern) := {
    ssorted_binder_morphism :
      forall {A : Type} (f : A -> Pattern -> Pattern)
         (f_morph : PatternMorphism f)
         (f_swap : SwappableEx f g f_morph) (s phi : Pattern) a,
      f a (binder s phi) = binder (f a s) (f (increase_mu spec_data a) phi) ;
}.

(** Next, we define the substitution simplification record: *)

Definition mlSimpl' :=
(
  @binary_morphism,
  @unary_morphism,
  @nullary_morphism,
  @ebinder_morphism,
  @sbinder_morphism,
  @esorted_binder_morphism,
  @ssorted_binder_morphism
).

End with_signature.