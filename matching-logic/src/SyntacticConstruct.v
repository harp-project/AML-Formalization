From Coq Require Import ssreflect ssrfun ssrbool.


From Coq Require Import Btauto.

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
      pm_spec_data : SpecificSubst ;
      pm_ezero_increase : forall a,
        on_bevar pm_spec_data (increase_ex pm_spec_data a) 0 = patt_bound_evar 0 ;
      pm_szero_increase : forall a,
        on_bsvar pm_spec_data (increase_mu pm_spec_data a) 0 = patt_bound_svar 0 ;
      pm_correctness : forall a (phi : Pattern), f a phi = apply_subst pm_spec_data a phi
  }.

  (** Variable quantifications are such morphisms: *)

  #[global]
  Program Instance Evar_quantify_morphism (x' : evar) :
     PatternMorphism (evar_quantify x') := {
    pm_spec_data := {|
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
    cbn. reflexivity.
  Defined.
  Next Obligation.
    cbn. reflexivity.
  Defined.
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
    pm_spec_data := {|
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
    cbn. reflexivity.
  Defined.
  Next Obligation.
    cbn. reflexivity.
  Defined.
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
    pm_spec_data := {|
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
    cbn. reflexivity.
  Defined.
  Next Obligation.
    cbn. reflexivity.
  Defined.
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
    pm_spec_data := {|
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
    cbn. reflexivity.
  Defined.
  Next Obligation.
    cbn. reflexivity.
  Defined.
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
    pm_spec_data := {|
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
    cbn. reflexivity.
  Defined.
  Next Obligation.
    cbn. reflexivity.
  Defined.
  Next Obligation.
    unfold evar_open. intros. rewrite pm_correctness. auto.
  Defined.

  #[global]
  Program Instance Svar_open_morphism (X : svar) :
     PatternMorphism (svar_open X) := {
    pm_spec_data := {|
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
    cbn. reflexivity.
  Defined.
  Next Obligation.
    cbn. reflexivity.
  Defined.
  Next Obligation.
    unfold svar_open. intros. rewrite pm_correctness. auto.
  Defined.

  #[global]
  Program Instance Free_evar_subst_morphism (ψ : Pattern) :
     PatternMorphism (free_evar_subst ψ) := {
    pm_spec_data := {|
      increase_ex := id ;
      increase_mu := id ;
      on_fevar := fun x x' => if decide (x = x') then ψ else patt_free_evar x';
      on_fsvar := fun _ X => patt_free_svar X;
      on_bevar := fun _ n => patt_bound_evar n;
      on_bsvar := fun _ N => patt_bound_svar N;
    |}
  }.
  Next Obligation.
    cbn. reflexivity.
  Defined.
  Next Obligation.
    cbn. reflexivity.
  Defined.
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
    pm_spec_data := {|
      increase_ex := id ;
      increase_mu := id ;
      on_fevar := fun _ x => patt_free_evar x ;
      on_fsvar := fun X X' => if decide (X = X') then ψ else patt_free_svar X';
      on_bevar := fun _ n => patt_bound_evar n;
      on_bsvar := fun _ N => patt_bound_svar N;
    |}
  }.
  Next Obligation.
    cbn. reflexivity.
  Defined.
  Next Obligation.
    cbn. reflexivity.
  Defined.
  Next Obligation.
    intros x' db φ. revert x' db. induction φ; intros x' db; simpl; auto.
    * case_match; simpl; auto.
    * now rewrite -> IHφ1, IHφ2.
    * now rewrite -> IHφ1, IHφ2.
    * now rewrite IHφ.
    * now rewrite IHφ.
  Defined.

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
    binary_wfp :
      forall (ψ1 ψ2 : Pattern),
        well_formed_positive (binary ψ1 ψ2)
        = well_formed_positive ψ1 && well_formed_positive ψ2 ;
    binary_wfcex :
      forall (n : nat) (ψ1 ψ2 : Pattern),
            well_formed_closed_ex_aux (binary ψ1 ψ2) n
            = well_formed_closed_ex_aux ψ1 n && well_formed_closed_ex_aux ψ2 n ;
    binary_wfcmu :
      forall (n : nat) (ψ1 ψ2 : Pattern),
            well_formed_closed_mu_aux (binary ψ1 ψ2) n
            = well_formed_closed_mu_aux ψ1 n && well_formed_closed_mu_aux ψ2 n ;
}.

Lemma binary_wfxy
  (binary : Pattern -> Pattern -> Pattern)
  {_b : Binary binary}
:
forall (x y : nat) (ψ1 ψ2 : Pattern),
  well_formed_xy x y (binary ψ1 ψ2)
  = well_formed_xy x y ψ1 && well_formed_xy x y ψ2.
Proof.
  unfold well_formed_xy.
  intros.
  rewrite binary_wfp.
  rewrite binary_wfcex.
  rewrite binary_wfcmu.
  btauto.
Qed.

Lemma binary_wfxy_compose
  (binary : Pattern -> Pattern -> Pattern)
  {_b : Binary binary}
:
forall (x y : nat) (ψ1 ψ2 : Pattern),
  well_formed_xy x y ψ1 = true /\ well_formed_xy x y ψ2 = true ->
  well_formed_xy x y (binary ψ1 ψ2) = true
.
Proof.
  intros x y ψ1 ψ2 H.
  rewrite binary_wfxy.
  destruct H as [H1 H2].
  rewrite H1 H2.
  reflexivity.
Qed.

Lemma binary_wfxy_decompose
  (binary : Pattern -> Pattern -> Pattern)
  {_b : Binary binary}
:
forall (x y : nat) (ψ1 ψ2 : Pattern),
  well_formed_xy x y (binary ψ1 ψ2) = true ->
  well_formed_xy x y ψ1 = true /\ well_formed_xy x y ψ2 = true
.
Proof.
  intros x y ψ1 ψ2 H.
  rewrite binary_wfxy in H.
  apply andb_true_iff in H.
  exact H.
Qed.

Class Unary (unary : Pattern -> Pattern) := {
    unary_morphism :
      forall {A : Type} (f : A -> Pattern -> Pattern) (f_morph : PatternMorphism f) (phi : Pattern) a,
        f a (unary phi) = unary (f a phi) ;
    unary_wfp :
      forall (ψ : Pattern),
        well_formed_positive (unary ψ) = well_formed_positive ψ ;
    unary_wfcex :
      forall (n : nat) (ψ : Pattern),
        well_formed_closed_ex_aux (unary ψ) n = well_formed_closed_ex_aux ψ n ;
    unary_wfcmu :
      forall (n : nat) (ψ : Pattern),
        well_formed_closed_mu_aux (unary ψ) n = well_formed_closed_mu_aux ψ n ;
}.

Lemma unary_wfxy (unary : Pattern -> Pattern) {_ : Unary unary} :
forall (x y : nat) (ψ : Pattern),
  well_formed_xy x y (unary ψ) = well_formed_xy x y ψ
.
Proof.
  unfold well_formed_xy.
  intros.
  rewrite unary_wfp.
  rewrite unary_wfcex.
  rewrite unary_wfcmu.
  btauto.
Qed.

Lemma unary_wfxy_compose (unary : Pattern -> Pattern) {_ : Unary unary} :
forall (x y : nat) (ψ : Pattern),
  well_formed_xy x y ψ = true ->
  well_formed_xy x y (unary ψ) = true
.
Proof.
  intros x y ψ H'.
  rewrite unary_wfxy.
  exact H'.
Qed.

Lemma unary_wfxy_decompose (unary : Pattern -> Pattern) {_ : Unary unary} :
forall (x y : nat) (ψ : Pattern),
  well_formed_xy x y (unary ψ) = true ->
  well_formed_xy x y ψ = true
.
Proof.
  intros x y ψ H'.
  rewrite unary_wfxy in H'.
  exact H'.
Qed.


Class Nullary (nullary : Pattern) := {
    nullary_morphism :
      forall {A : Type} (f : A -> Pattern -> Pattern) (f_morph : PatternMorphism f) a,
        f a nullary = nullary ;
    nullary_wfp : well_formed_positive nullary = true;
    nullary_wfcex : forall (n : nat), well_formed_closed_ex_aux nullary n = true;
    nullary_wfcmu : forall (n : nat), well_formed_closed_mu_aux nullary n = true;
}.

Lemma nullary_wfxy (nullary : Pattern) {_ : Nullary nullary} :
  forall (x y : nat), well_formed_xy x y nullary = true
.
Proof.
  unfold well_formed_xy.
  intros.
  rewrite nullary_wfp.
  rewrite nullary_wfcex.
  rewrite nullary_wfcmu.
  btauto.
Qed.

Lemma well_formed_positive_foldr_binary
  (binary : Pattern -> Pattern -> Pattern)
  {_bin : Binary binary}
  (g : Pattern)
  (xs : list Pattern)
  :
  well_formed_positive (foldr binary g xs)
  = (well_formed_positive g && lwf_positive xs).
Proof.
  induction xs; simpl.
  {
    unfold lwf_positive. simpl. rewrite andb_true_r. reflexivity.
  }
  {
    unfold lwf_positive in *. simpl.
    rewrite binary_wfp.
    rewrite IHxs.
    btauto.
  }
Qed.


Lemma well_formed_cex_foldr_binary
  (binary : Pattern -> Pattern -> Pattern)
  {_bin : Binary binary}
  (n : nat)
  (g : Pattern)
  (xs : list Pattern)
  :
  well_formed_closed_ex_aux (foldr binary g xs) n
  = (well_formed_closed_ex_aux g n && lwf_cex n xs).
Proof.
  induction xs; simpl.
  {
    unfold lwf_cex. simpl. rewrite andb_true_r. reflexivity.
  }
  {
    unfold lwf_cex in *. simpl.
    rewrite binary_wfcex.
    rewrite IHxs.
    btauto.
  }
Qed.


Lemma well_formed_cmu_foldr_binary
  (binary : Pattern -> Pattern -> Pattern)
  {_bin : Binary binary}
  (n : nat)
  (g : Pattern)
  (xs : list Pattern)
  :
  well_formed_closed_mu_aux (foldr binary g xs) n
  = (well_formed_closed_mu_aux g n && lwf_cmu n xs).
Proof.
  induction xs; simpl.
  {
    unfold lwf_cmu. simpl. rewrite andb_true_r. reflexivity.
  }
  {
    unfold lwf_cmu in *. simpl.
    rewrite binary_wfcmu.
    rewrite IHxs.
    btauto.
  }
Qed.

Lemma well_formed_xy_foldr_binary
  (binary : Pattern -> Pattern -> Pattern)
  {_bin : Binary binary}
  (m n : nat)
  (g : Pattern)
  (xs : list Pattern)
  :
  well_formed_xy m n (foldr binary g xs)
  = (well_formed_xy m n g && lwf_xy m n xs)
.
Proof.
  induction xs; simpl.
  {
    unfold lwf_xy. simpl. rewrite andb_true_r. reflexivity.
  }
  {
    unfold lwf_xy in *. simpl.
    rewrite binary_wfxy.
    rewrite IHxs.
    btauto.
  }
Qed.

Class EBinder (binder : Pattern -> Pattern) := {
    ebinder_morphism :
      forall {A : Type} (f : A -> Pattern -> Pattern) (f_morph : PatternMorphism f) (phi : Pattern) a,
        f a (binder phi) = binder (f (increase_ex pm_spec_data a) phi) ;
}.

Class SBinder (binder : Pattern -> Pattern) := {
    sbinder_morphism :
      forall {A : Type} (f : A -> Pattern -> Pattern) (f_morph : PatternMorphism f) (phi : Pattern) a,
        f a (binder phi) = binder (f (increase_mu pm_spec_data a) phi) ;
}.

(** Next, we define instances for the primitives of matching logic: *)

#[global]
Program Instance EBinder_exists : EBinder patt_exists := {}.
Next Obligation.
  intros A f m φ a. repeat rewrite pm_correctness.
  simpl. reflexivity.
Defined.

#[global]
Program Instance SBinder_mu : SBinder patt_mu := {}.
Next Obligation.
  intros A f m φ a. repeat rewrite pm_correctness.
  simpl. reflexivity.
Defined.

#[global]
Program Instance Binary_imp : Binary patt_imp := {}.
Next Obligation.
  intros A f m φ1 φ2 a. repeat rewrite pm_correctness.
  simpl. reflexivity.
Defined.
Next Obligation.
  intros. simpl. reflexivity.
Qed.
Next Obligation.
  intros. simpl. reflexivity.
Qed.
Next Obligation.
  intros. simpl. reflexivity.
Qed.


#[global]
Program Instance Binary_app : Binary patt_app := {}.
Next Obligation.
  intros A f m φ1 φ2 a. repeat rewrite pm_correctness.
  simpl. reflexivity.
Defined.
Next Obligation.
  intros. simpl. reflexivity.
Qed.
Next Obligation.
  intros. simpl. reflexivity.
Qed.
Next Obligation.
  intros. simpl. reflexivity.
Qed.

#[global]
Program Instance Nullary_bott : Nullary patt_bott := {}.
Next Obligation.
  intros A f m a. repeat rewrite pm_correctness.
  simpl. reflexivity.
Defined.
Next Obligation.
  intros. simpl. reflexivity.
Qed.
Next Obligation.
  intros. simpl. reflexivity.
Qed.
Next Obligation.
  intros. simpl. reflexivity.
Qed.

#[global]
Program Instance Nullary_sym s : Nullary (patt_sym s) := {}.
Next Obligation.
  intros A s f m a. repeat rewrite pm_correctness.
  simpl. reflexivity.
Defined.
Next Obligation.
  intros. simpl. reflexivity.
Qed.
Next Obligation.
  intros. simpl. reflexivity.
Qed.
Next Obligation.
  intros. simpl. reflexivity.
Qed.

Class SwappableEx {A : Type} (f : A -> Pattern -> Pattern) (g : Pattern -> Pattern)
  (m : PatternMorphism f) :=
{
  eswap : forall phi a,
    apply_subst pm_spec_data (increase_ex pm_spec_data a) (g phi) =
    g (apply_subst pm_spec_data a phi) ;
}.

#[global]
Program Instance Bevar_subst_swaps_ex_nesting (ψ : Pattern) (p : well_formed_closed ψ) :
  SwappableEx _ nest_ex (Bevar_subst_morphism ψ).
Next Obligation.
  intros ψ WFψ phi a.
  do 2 rewrite <- pm_correctness.
  unfold nest_ex. rewrite <- nest_ex_gt; auto. 2: lia.
  rewrite Nat.add_comm. reflexivity.
Defined.

#[global]
Program Instance Bsvar_subst_swaps_ex_nesting (ψ : Pattern) (p : well_formed_closed ψ) :
  SwappableEx _ nest_ex (Bsvar_subst_morphism ψ).
Next Obligation.
  intros ψ WFψ phi a.
  do 2 rewrite <- pm_correctness.
  unfold nest_ex.
  rewrite bsvar_subst_nest_ex_aux_comm; auto.
  apply andb_true_iff in WFψ. apply WFψ.
Defined.

#[global]
Program Instance Fevar_subst_swaps_ex_nesting (ψ : Pattern) (p : well_formed_closed ψ) :
  SwappableEx _ nest_ex (Free_evar_subst_morphism ψ).
Next Obligation.
  intros ψ WFψ phi a.
  do 2 rewrite <- pm_correctness.
  unfold nest_ex.
  rewrite nest_ex_free_evar_subst; auto.
  apply andb_true_iff in WFψ. apply WFψ.
Defined.

#[global]
Program Instance Fsvar_subst_swaps_ex_nesting (ψ : Pattern) (p : well_formed_closed ψ) :
  SwappableEx _ nest_ex (Free_svar_subst_morphism ψ).
Next Obligation.
  intros ψ WFψ phi a.
  do 2 rewrite <- pm_correctness.
  unfold nest_ex.
  rewrite nest_ex_free_svar_subst; auto.
  apply andb_true_iff in WFψ. apply WFψ.
Defined.

#[global]
Program Instance Evar_quantify_swaps_ex_nesting (x : evar) :
  SwappableEx _ nest_ex (Evar_quantify_morphism x).
Next Obligation.
  intros ψ phi a.
  do 2 rewrite <- pm_correctness.
  unfold nest_ex. rewrite <- nest_ex_gt_evar_quantify; auto. 2: lia.
  rewrite Nat.add_comm. reflexivity.
Defined.

#[global]
Program Instance Svar_quantify_swaps_ex_nesting (X : svar) :
  SwappableEx _ nest_ex (Svar_quantify_morphism X).
Next Obligation.
  intros ψ phi a.
  do 2 rewrite <- pm_correctness.
  unfold nest_ex. now rewrite nest_ex_svar_quantify.
Defined.

#[global]
Program Instance Evar_open_swaps_ex_nesting (x : evar) :
  SwappableEx _ nest_ex (Evar_open_morphism x).
Next Obligation.
  (* TODO: here type class inference fails without the explicit parameters *)
  intros.
  rewrite (@eswap _ _ _ _ (Bevar_subst_swaps_ex_nesting (patt_free_evar x) _)); auto.
Defined.

#[global]
Program Instance Svar_open_swaps_ex_nesting (X : svar) :
  SwappableEx _ nest_ex (Svar_open_morphism X).
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
      f a (binder s phi) = binder (f a s) (f (increase_ex pm_spec_data a) phi) ;
}.

Class SSortedBinder (binder : Pattern -> Pattern -> Pattern) (g : Pattern -> Pattern) := {
    ssorted_binder_morphism :
      forall {A : Type} (f : A -> Pattern -> Pattern)
         (f_morph : PatternMorphism f)
         (f_swap : SwappableEx f g f_morph) (s phi : Pattern) a,
      f a (binder s phi) = binder (f a s) (f (increase_mu pm_spec_data a) phi) ;
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

End with_signature.

(*
  Hints are needed to automatically infer the SwappableEx instances.
  TODO: there is still a problem when the well_formed_closed assumption is
        missing
  TODO(jan.tusil): I would add the hints to a separate database
*)
#[export]
Hint Resolve Bevar_subst_swaps_ex_nesting : core.
#[export]
Hint Resolve Bsvar_subst_swaps_ex_nesting : core.
#[export]
Hint Resolve Fevar_subst_swaps_ex_nesting : core.
#[export]
Hint Resolve Fsvar_subst_swaps_ex_nesting : core.
#[export]
Hint Resolve Evar_quantify_swaps_ex_nesting : core.
#[export]
Hint Resolve Svar_quantify_swaps_ex_nesting : core.
#[export]
Hint Resolve Evar_open_swaps_ex_nesting : core.
#[export]
Hint Resolve Svar_open_swaps_ex_nesting : core.

(**
  This tactic identifies the sorted binder for simplification (by checking its type).
  Since automatic identification of the instance of the type class is not working
  currently, we identify the correct instance by giving the parameters inferred
  from the context.

  TODO: more strict identification of the point where the simplification has to be
        made, since nested sorted quantifiers can occur, which break the tactic.
        One potential solution is to use Ltac2.
*)
Ltac simpl_sorted_quantification :=
  match goal with
  | |- context G [?f ?arg _ (?binder _ _)] =>
    match type of binder with
    | Pattern -> Pattern -> Pattern =>
      tryif
       unshelve (erewrite (@esorted_binder_morphism _ binder
            _ _ _ (f arg) _ _));
       match goal with
       | |- SwappableEx _ _ _ => auto
       | |- PatternMorphism _ => now typeclasses eauto
       | |- ESortedBinder _ _ => tryif now typeclasses eauto then idtac else fail 3
       | _ => idtac
       end
      then idtac
      else idtac (* "No sorted simplification instance for " binder *)
    end
  end.

Ltac simpl_sorted_quantification_hyp H :=
match type of H with
  | context G [?f ?arg _ (?binder _ _)] => 
    match type of binder with
    | Pattern -> Pattern -> Pattern => 
      tryif
       (let name := fresh "X" in
         unshelve (epose proof (name := @esorted_binder_morphism _ binder
            _ _ _ (f arg) _ _)); try (rewrite name in H; clear name);
            try typeclasses eauto; auto;
            match goal with
             | |- SwappableEx _ _ _ => clear H
             | |- PatternMorphism _ => clear H; now typeclasses eauto
             | |- ESortedBinder _ _ => clear H; tryif now typeclasses eauto then idtac else fail 3
             | _ => idtac
            end
              )
      then idtac
      else idtac (* "No sorted simplification instance for " binder *)
    end
  end.


Section Test.
Import Substitution.Notations.
Open Scope ml_scope.
Context {Σ : Signature}.
Tactic Notation "mlSimpl" :=
  repeat (rewrite mlSimpl' + simpl_sorted_quantification); try rewrite [increase_ex _ _]/=; try rewrite [increase_mu]/=.

Tactic Notation "mlSimpl" "in" hyp(H) :=
  repeat (rewrite mlSimpl' in H + simpl_sorted_quantification_hyp H); try rewrite [increase_ex _ _]/= in H; try rewrite [increase_mu _ _]/= in H.

  Local Definition patt_forall_of_sort (sort phi : Pattern) : Pattern :=
    patt_exists (patt_imp (patt_imp (patt_bound_evar 0) (nest_ex sort)) phi).

  #[local]
  Program Instance sorted_forall_binder : ESortedBinder patt_forall_of_sort nest_ex := {}.
  Next Obligation.
     intros.
     repeat rewrite pm_correctness.
    cbn.
    rewrite eswap.
    now rewrite pm_ezero_increase.
  Defined.

Goal forall s ψ x, (* well_formed_closed ψ -> *)
(patt_forall_of_sort s ψ)^[[evar: x ↦ ψ]] = patt_bott ->
(patt_forall_of_sort s ψ)^{evar: 0 ↦ x} = patt_bott ->
(patt_forall_of_sort s ψ)^{{evar: x ↦ 0}} = patt_bott ->
(patt_forall_of_sort s ψ)^[[evar: x ↦ ψ]] = patt_bott /\ 
(patt_forall_of_sort s ψ)^{evar: 0 ↦ x} = patt_bott /\
(patt_forall_of_sort s ψ)^{{evar: x ↦ 0}} = patt_bott
.
Proof.
  intros.
  mlSimpl.
  2: {
  mlSimpl in H. 2: {
  mlSimpl in H0.
  mlSimpl in H1. }
Abort.

Goal forall s ψ x, (* well_formed_closed ψ -> *)
(patt_forall_of_sort (patt_imp s s) ψ)^[[evar: x ↦ ψ]] = patt_bott
.
Proof.
  intros.
  simpl_sorted_quantification. 2: mlSimpl.
Abort.

End Test.