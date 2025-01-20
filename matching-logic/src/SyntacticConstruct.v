From Coq Require Import Btauto.

From MatchingLogic Require Export
    DerivedOperators_Syntax
    IndexManipulation
.

Import MatchingLogic.Substitution.Notations.

Set Default Proof Mode "Classic".

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

Class Ternary (ternary : Pattern -> Pattern -> Pattern -> Pattern) := {
    ternary_morphism :
      forall {A : Type} (f : A -> Pattern -> Pattern) (f_morph : PatternMorphism f) (phi1 phi2 phi3 : Pattern) a,
        f a (ternary phi1 phi2 phi3) =
          ternary (f a phi1) (f a phi2) (f a phi3);
    ternary_wfp :
      forall (ψ1 ψ2 ψ3: Pattern),
        well_formed_positive (ternary ψ1 ψ2 ψ3)
        = well_formed_positive ψ1 &&
          well_formed_positive ψ2 &&
          well_formed_positive ψ3 ;
    ternary_wfcex :
      forall (n : nat) (ψ1 ψ2 ψ3 : Pattern),
            well_formed_closed_ex_aux (ternary ψ1 ψ2 ψ3) n
            = well_formed_closed_ex_aux ψ1 n &&
              well_formed_closed_ex_aux ψ2 n &&
              well_formed_closed_ex_aux ψ3 n  ;
    ternary_wfcmu :
      forall (n : nat) (ψ1 ψ2 ψ3 : Pattern),
            well_formed_closed_mu_aux (ternary ψ1 ψ2 ψ3) n
            = well_formed_closed_mu_aux ψ1 n &&
              well_formed_closed_mu_aux ψ2 n &&
              well_formed_closed_mu_aux ψ3 n;
}.

Lemma ternary_wfxy
  (ternary : Pattern -> Pattern -> Pattern -> Pattern)
  {_b : Ternary ternary}
:
forall (x y : nat) (ψ1 ψ2 ψ3 : Pattern),
  well_formed_xy x y (ternary ψ1 ψ2 ψ3)
  = well_formed_xy x y ψ1 && well_formed_xy x y ψ2 && well_formed_xy x y ψ3.
Proof.
  unfold well_formed_xy.
  intros.
  rewrite ternary_wfp.
  rewrite ternary_wfcex.
  rewrite ternary_wfcmu.
  btauto.
Qed.

Lemma ternary_wfxy_compose
  (ternary : Pattern -> Pattern -> Pattern -> Pattern)
  {_b : Ternary ternary}
:
forall (x y : nat) (ψ1 ψ2 ψ3 : Pattern),
  well_formed_xy x y ψ1 = true /\
  well_formed_xy x y ψ2 = true /\
  well_formed_xy x y ψ3 = true ->
  well_formed_xy x y (ternary ψ1 ψ2 ψ3) = true
.
Proof.
  intros x y ψ1 ψ2 ψ3 H.
  rewrite ternary_wfxy.
  destruct H as [H1 [H2 H3] ].
  rewrite H1 H2 H3.
  reflexivity.
Qed.

Lemma ternary_wfxy_decompose
  (ternary : Pattern -> Pattern -> Pattern -> Pattern)
  {_b : Ternary ternary}
:
forall (x y : nat) (ψ1 ψ2 ψ3 : Pattern),
  well_formed_xy x y (ternary ψ1 ψ2 ψ3) = true ->
  well_formed_xy x y ψ1 = true /\ well_formed_xy x y ψ2 = true /\ well_formed_xy x y ψ3 = true
.
Proof.
  intros x y ψ1 ψ2 ψ3 H.
  rewrite ternary_wfxy in H.
  apply andb_true_iff in H as [H ?].
  apply andb_true_iff in H as [? ?].
  firstorder.
Qed.

Class Quaternary (quaternary : Pattern -> Pattern -> Pattern -> Pattern -> Pattern) := {
    quaternary_morphism :
      forall {A : Type} (f : A -> Pattern -> Pattern) (f_morph : PatternMorphism f) (phi1 phi2 phi3 phi4 : Pattern) a,
        f a (quaternary phi1 phi2 phi3 phi4) =
          quaternary (f a phi1) (f a phi2) (f a phi3) (f a phi4);
    quaternary_wfp :
      forall (ψ1 ψ2 ψ3 ψ4: Pattern),
        well_formed_positive (quaternary ψ1 ψ2 ψ3 ψ4)
        = well_formed_positive ψ1 &&
          well_formed_positive ψ2 &&
          well_formed_positive ψ3 &&
          well_formed_positive ψ4 ;
    quaternary_wfcex :
      forall (n : nat) (ψ1 ψ2 ψ3 ψ4 : Pattern),
            well_formed_closed_ex_aux (quaternary ψ1 ψ2 ψ3 ψ4) n
            = well_formed_closed_ex_aux ψ1 n &&
              well_formed_closed_ex_aux ψ2 n &&
              well_formed_closed_ex_aux ψ3 n &&
              well_formed_closed_ex_aux ψ4 n  ;
    quaternary_wfcmu :
      forall (n : nat) (ψ1 ψ2 ψ3 ψ4 : Pattern),
            well_formed_closed_mu_aux (quaternary ψ1 ψ2 ψ3 ψ4) n
            = well_formed_closed_mu_aux ψ1 n &&
              well_formed_closed_mu_aux ψ2 n &&
              well_formed_closed_mu_aux ψ3 n &&
              well_formed_closed_mu_aux ψ4 n;
}.

Lemma quaternary_wfxy
  (quaternary : Pattern -> Pattern -> Pattern -> Pattern -> Pattern)
  {_b : Quaternary quaternary}
:
forall (x y : nat) (ψ1 ψ2 ψ3 ψ4 : Pattern),
  well_formed_xy x y (quaternary ψ1 ψ2 ψ3 ψ4)
  = well_formed_xy x y ψ1 && well_formed_xy x y ψ2 && well_formed_xy x y ψ3 && well_formed_xy x y ψ4.
Proof.
  unfold well_formed_xy.
  intros.
  rewrite quaternary_wfp.
  rewrite quaternary_wfcex.
  rewrite quaternary_wfcmu.
  btauto.
Qed.

Lemma quaternary_wfxy_compose
  (quaternary : Pattern -> Pattern -> Pattern -> Pattern -> Pattern)
  {_b : Quaternary quaternary}
:
forall (x y : nat) (ψ1 ψ2 ψ3 ψ4 : Pattern),
  well_formed_xy x y ψ1 = true /\
  well_formed_xy x y ψ2 = true /\
  well_formed_xy x y ψ3 = true /\
  well_formed_xy x y ψ4 = true ->
  well_formed_xy x y (quaternary ψ1 ψ2 ψ3 ψ4) = true
.
Proof.
  intros x y ψ1 ψ2 ψ3 ψ4 H.
  rewrite quaternary_wfxy.
  destruct H as [H1 [H2 [H3 H4] ] ].
  rewrite H1 H2 H3 H4.
  reflexivity.
Qed.

Lemma quaternary_wfxy_decompose
  (quaternary : Pattern -> Pattern -> Pattern -> Pattern -> Pattern)
  {_b : Quaternary quaternary}
:
forall (x y : nat) (ψ1 ψ2 ψ3 ψ4 : Pattern),
  well_formed_xy x y (quaternary ψ1 ψ2 ψ3 ψ4) = true ->
  well_formed_xy x y ψ1 = true /\ well_formed_xy x y ψ2 = true /\ well_formed_xy x y ψ3 = true /\ well_formed_xy x y ψ4 = true
.
Proof.
  intros x y ψ1 ψ2 ψ3 ψ4 H.
  rewrite quaternary_wfxy in H.
  do 2 apply andb_true_iff in H as [H ?].
  apply andb_true_iff in H as [? ?].
  firstorder.
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

Lemma unary_wfxy_compose (unary : Pattern -> Pattern) {_uu : Unary unary} :
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

Lemma well_formed_xy_foldr_binary_compose
  (binary : Pattern -> Pattern -> Pattern)
  {_bin : Binary binary}
  (m n : nat)
  (g : Pattern)
  (xs : list Pattern)
  :
  (well_formed_xy m n g = true /\ lwf_xy m n xs = true) ->
  well_formed_xy m n (foldr binary g xs) = true
.
Proof.
  intros H.
  rewrite well_formed_xy_foldr_binary.
  destruct H as [H1 H2].
  rewrite H1 H2.
  reflexivity.
Qed.

Lemma well_formed_xy_foldr_binary_decompose
  (binary : Pattern -> Pattern -> Pattern)
  {_bin : Binary binary}
  (m n : nat)
  (g : Pattern)
  (xs : list Pattern)
  :
  well_formed_xy m n (foldr binary g xs) = true ->
  (well_formed_xy m n g = true /\ lwf_xy m n xs = true)
.
Proof.
  intros H.
  rewrite well_formed_xy_foldr_binary in H.
  apply andb_true_iff in H.
  exact H.
Qed.

Class EBinder (binder : Pattern -> Pattern) := {
    ebinder_morphism :
      forall {A : Type} (f : A -> Pattern -> Pattern) (f_morph : PatternMorphism f) (phi : Pattern) a,
        f a (binder phi) = binder (f (increase_ex pm_spec_data a) phi) ;
    ebinder_wfp :
      forall φ, well_formed_positive (binder φ) = well_formed_positive φ;
    ebinder_wfcex :
      forall φ n, well_formed_closed_ex_aux (binder φ) n =
        well_formed_closed_ex_aux φ (S n);
    ebinder_wfcmu :
      forall φ n, well_formed_closed_mu_aux (binder φ) n =
        well_formed_closed_mu_aux φ n;
}.

Lemma ebinder_wfxy
  (ebinder : Pattern -> Pattern)
  {_b : EBinder ebinder}
:
forall (x y : nat) (ψ : Pattern),
  well_formed_xy x y (ebinder ψ)
  = well_formed_xy (S x) y ψ.
Proof.
  unfold well_formed_xy.
  intros.
  rewrite ebinder_wfp.
  rewrite ebinder_wfcex.
  rewrite ebinder_wfcmu.
  btauto.
Qed.

Lemma ebinder_wfxy_compose
  (ebinder : Pattern -> Pattern)
  {_b : EBinder ebinder}
:
forall (x y : nat) (ψ : Pattern),
  well_formed_xy (S x) y ψ ->
  well_formed_xy x y (ebinder ψ) = true
.
Proof.
  intros x y ψ H.
  rewrite ebinder_wfxy.
  assumption.
Qed.

Lemma ebinder_wfxy_decompose
  (ebinder : Pattern -> Pattern)
  {_b : EBinder ebinder}
:
forall (x y : nat) (ψ : Pattern),
  well_formed_xy x y (ebinder ψ) = true ->
  well_formed_xy (S x) y ψ = true.
Proof.
  intros x y ψ H.
  rewrite ebinder_wfxy in H.
  assumption.
Qed.

Class SBinder (binder : Pattern -> Pattern) := {
    sbinder_morphism :
      forall {A : Type} (f : A -> Pattern -> Pattern) (f_morph : PatternMorphism f) (phi : Pattern) a,
        f a (binder phi) = binder (f (increase_mu pm_spec_data a) phi) ;
    sbinder_wfp :
      forall φ, well_formed_positive (binder φ) =
                well_formed_positive φ &&
                no_negative_occurrence_db_b 0 φ;
    sbinder_wfcex :
      forall φ n, well_formed_closed_ex_aux (binder φ) n =
        well_formed_closed_ex_aux φ n;
    sbinder_wfcmu :
      forall φ n, well_formed_closed_mu_aux (binder φ) n =
        well_formed_closed_mu_aux φ (S n);
}.

Lemma sbinder_wfxy
  (sbinder : Pattern -> Pattern)
  {_b : SBinder sbinder}
:
forall (x y : nat) (ψ : Pattern),
  well_formed_xy x y (sbinder ψ)
  = well_formed_xy x (S y) ψ && no_negative_occurrence_db_b 0 ψ.
Proof.
  unfold well_formed_xy.
  intros.
  rewrite sbinder_wfp.
  rewrite sbinder_wfcex.
  rewrite sbinder_wfcmu.
  btauto.
Qed.

Lemma sbinder_wfxy_compose
  (sbinder : Pattern -> Pattern)
  {_b : SBinder sbinder}
:
forall (x y : nat) (ψ : Pattern),
  well_formed_xy x (S y) ψ /\
  no_negative_occurrence_db_b 0 ψ ->
  well_formed_xy x y (sbinder ψ) = true
.
Proof.
  intros x y ψ H.
  rewrite sbinder_wfxy.
  destruct H.
  by rewrite H H0.
Qed.

Lemma sbinder_wfxy_decompose
  (sbinder : Pattern -> Pattern)
  {_b : SBinder sbinder}
:
forall (x y : nat) (ψ : Pattern),
  well_formed_xy x y (sbinder ψ) = true ->
  no_negative_occurrence_db_b 0 ψ /\ well_formed_xy x (S y) ψ = true.
Proof.
  intros x y ψ H.
  rewrite sbinder_wfxy in H.
  split; apply andb_true_iff in H as [? ?]; assumption.
Qed.

(** Next, we define instances for the primitives of matching logic: *)

#[global]
Program Instance EBinder_exists : EBinder patt_exists := {}.
Next Obligation.
  intros A f m φ a. repeat rewrite pm_correctness.
  simpl. reflexivity.
Defined.
Next Obligation.
  intros. by simpl.
Defined.
Next Obligation.
  intros. by simpl.
Defined.
Next Obligation.
  intros. by simpl.
Defined.

#[global]
Program Instance SBinder_mu : SBinder patt_mu := {}.
Next Obligation.
  intros A f m φ a. repeat rewrite pm_correctness.
  simpl. reflexivity.
Defined.
Next Obligation.
  intros. simpl. btauto.
Defined.
Next Obligation.
  intros. by simpl.
Defined.
Next Obligation.
  intros. by simpl.
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

(** We define the simplification class instances for the derived operators: *)

#[global]
Program Instance Unary_not : Unary patt_not := {}.
Next Obligation.
   intros A f m φ a.
   unfold patt_not. repeat rewrite pm_correctness.
   simpl. reflexivity.
Defined.
Next Obligation.
  intros. cbn. btauto.
Qed.
Next Obligation.
  intros. cbn. btauto.
Qed.
Next Obligation.
  intros. cbn. btauto.
Qed.


#[global]
Program Instance NVNullary_top : Nullary patt_top := {}.
Next Obligation.
   intros A f m φ.
   unfold patt_top. repeat rewrite pm_correctness.
   simpl. reflexivity.
Defined.
Next Obligation.
  intros. cbn. btauto.
Qed.
Next Obligation.
  intros. cbn. btauto.
Qed.
Next Obligation.
  intros. cbn. btauto.
Qed.

#[global]
Program Instance Binary_or : Binary patt_or := {}.
Next Obligation.
   intros A f m φ1 φ2 a.
   unfold patt_or. repeat rewrite pm_correctness.
   simpl. reflexivity.
Defined.
Next Obligation.
  intros. cbn. btauto.
Qed.
Next Obligation.
  intros. cbn. btauto.
Qed.
Next Obligation.
  intros. cbn. btauto.
Qed.

#[global]
Program Instance Binary_and : Binary patt_and := {}.
Next Obligation.
   intros A f m φ1 φ2 a.
   unfold patt_and. repeat rewrite pm_correctness.
   simpl. reflexivity.
Defined.
Next Obligation.
  intros. cbn. btauto.
Qed.
Next Obligation.
  intros. cbn. btauto.
Qed.
Next Obligation.
  intros. cbn. btauto.
Qed.

#[global]
Program Instance Binary_iff : Binary patt_iff := {}.
Next Obligation.
   intros A f m φ1 φ2 a.
   unfold patt_iff. repeat rewrite pm_correctness.
   simpl. reflexivity.
Defined.
Next Obligation.
  intros. cbn. btauto.
Qed.
Next Obligation.
  intros. cbn. btauto.
Qed.
Next Obligation.
  intros. cbn. btauto.
Qed.

#[global]
Program Instance EBinder_forall : EBinder patt_forall := {}.
Next Obligation.
   intros A f m φ a.
   unfold patt_not. repeat rewrite pm_correctness.
   simpl. reflexivity.
Defined.
Next Obligation.
  intros. cbn. by btauto.
Defined.
Next Obligation.
  intros. cbn. by btauto.
Defined.
Next Obligation.
  intros. cbn. by btauto.
Defined.

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
