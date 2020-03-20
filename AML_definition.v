Require Import String.
Require Import Coq.Init.Datatypes.
Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.
Require Import Coq.Vectors.VectorDef.


Section AML.

Inductive EVar : Set := evar_c (id : string).
Inductive SVar : Set := svar_c (id : string).
Inductive Sigma : Set := sigma_c (id : string).

Inductive Sigma_pattern : Set :=
  | sp_var (x : EVar)
  | sp_set (X : SVar)
  | sp_const (sigma : Sigma)
  | sp_app (phi1 phi2 : Sigma_pattern)
  | sp_bottom
  | sp_impl (phi1 phi2 : Sigma_pattern)
  | sp_exists (x : EVar) (phi : Sigma_pattern)
  | sp_mu (X : SVar) (phi : Sigma_pattern)
.

Notation "a _._ b" := (sp_app a b) (at level 50, left associativity).

Definition evar_eq_dec : forall (x y : EVar), { x = y } + { x <> y }.
Proof.
  decide equality.
  exact (string_dec id id0).
Defined.

Definition svar_eq_dec : forall (x y : SVar), { x = y } + { x <> y }.
Proof.
  decide equality.
  exact (string_dec id id0).
Defined.

Definition sigma_eq_dec : forall (x y : Sigma), { x = y } + { x <> y }.
Proof.
  decide equality.
  exact (string_dec id id0).
Defined.

Fixpoint spos_accumulated (phi : Sigma_pattern) (X : SVar) (nc : nat) : bool :=
  match phi with
  | sp_var x => true
  | sp_set Y => if (svar_eq_dec Y X)
                then (Nat.even nc)
                else true
  | sp_const sigma => true
  | sp_app phi1 phi2 => andb (spos_accumulated phi1 X nc) (spos_accumulated phi2 X nc)
  | sp_bottom => true
  | sp_impl phi1 phi2 => andb (spos_accumulated phi1 X (S nc)) (spos_accumulated phi2 X nc)
  | sp_exists x phi => spos_accumulated phi X nc
  | sp_mu Y phi => if (svar_eq_dec Y X)
                      then true
                      else (spos_accumulated phi X nc)
end.

Fixpoint strictly_positive (phi : Sigma_pattern) (X : SVar) : bool :=  spos_accumulated phi X 0.

Definition sp_eq_dec : forall (x y : Sigma_pattern), { x = y } + { x <> y }.
Proof.
  decide equality.
  - exact (evar_eq_dec x0 x1).
  - exact (svar_eq_dec X X0).
  - exact (sigma_eq_dec sigma sigma0).
  - exact (evar_eq_dec x0 x1).
  - exact (svar_eq_dec X X0).
Defined.

Definition sp_not (phi : Sigma_pattern) := sp_impl phi sp_bottom.
Definition sp_or  (l r : Sigma_pattern) := sp_impl (sp_not l) r.
Definition sp_and (l r : Sigma_pattern) :=
  sp_not (sp_or (sp_not l) (sp_not r)).
Notation "a _&_ b" := (sp_and a b) (right associativity, at level 70). (* TODO: Check associativity level *)
Definition sp_tatu := sp_not sp_bottom.
Definition sp_equiv (l r : Sigma_pattern) := (sp_and (sp_impl (l) (r)) (sp_impl (l) (r))).
Definition sp_forall (x : EVar) (phi : Sigma_pattern) :=
  sp_not (sp_exists x (sp_not phi)).
(*nuX.phi*)

Notation "phi1 <--> phi2" := (sp_equiv phi1 phi2) (at level 100).

Fixpoint e_subst_var (phi : Sigma_pattern) (psi : Sigma_pattern) (x : EVar) :=
  match phi with
  | sp_var x' =>
      if evar_eq_dec x x'
      then psi
      else sp_var x'
  | sp_set X => sp_set X
  | sp_const sigma => sp_const sigma
  | sp_app phi1 phi2 => sp_app (e_subst_var phi1 psi x)
                                (e_subst_var phi2 psi x)
  | sp_bottom => sp_bottom
  | sp_impl phi1 phi2 => sp_impl (e_subst_var phi1 psi x)
                                  (e_subst_var phi2 psi x)
  | sp_exists x' phi' =>
      if (evar_eq_dec x' x)
      then sp_exists x' phi'
      else sp_exists x' (e_subst_var phi' psi x)
  | sp_mu X phi' => sp_mu X (e_subst_var phi' psi x)
end.

Fixpoint e_subst_set (phi : Sigma_pattern) (psi : Sigma_pattern) (X : SVar) :=
  match phi with
  | sp_var x => sp_var x
  | sp_set X' =>
      if svar_eq_dec X X'
      then psi
      else sp_set X'
  | sp_const sigma => sp_const sigma
  | sp_app phi1 phi2 => sp_app (e_subst_set phi1 psi X)
                                (e_subst_set phi2 psi X)
  | sp_bottom => sp_bottom
  | sp_impl phi1 phi2 => sp_impl (e_subst_set phi1 psi X)
                                  (e_subst_set phi2 psi X)
  | sp_exists x' phi' => sp_exists x' (e_subst_set phi' psi X)
  | sp_mu X' phi' =>
      if (svar_eq_dec X' X)
      then sp_mu X' phi'
      else sp_mu X' (e_subst_set phi' psi X)
end.

Definition var (name : string) : Sigma_pattern :=
  sp_var (evar_c name).

Definition set (name : string) : Sigma_pattern :=
  sp_set (svar_c name).

(* Check negb. *)

Definition evar_eq (x y : EVar) : bool :=
  match x, y with
  | evar_c id_x, evar_c id_y => eqb id_x id_y
  end
.

Fixpoint free_vars (phi : Sigma_pattern) : (ListSet.set EVar) :=
  match phi with
 | sp_var x => set_add evar_eq_dec x List.nil
 | sp_set X => List.nil
 | sp_const sigma => List.nil
 | sp_app phi1 phi2 =>
    set_union evar_eq_dec
      (free_vars phi1)
      (free_vars phi2)
 | sp_bottom => List.nil
 | sp_impl phi1 phi2 =>
    set_union evar_eq_dec
      (free_vars phi1)
      (free_vars phi2)
 | sp_exists y phi =>
    set_diff evar_eq_dec
      (free_vars phi)
      (set_add evar_eq_dec y List.nil)
 | sp_mu X phi => free_vars phi
end
.

(* Definition is_free (x : EVar) (phi : Sigma_pattern) : bool :=
  set_mem evar_eq_dec x (free_vars phi). *)

(* Inductive application_context : Set :=
  | pattern (p : Sigma_pattern)
  | box
.
 *)

Inductive context : Set :=
  | box
  | ctx_app_l (cc : context) (sp : Sigma_pattern)
  | ctx_app_r (sp : Sigma_pattern) (cc : context)
.

Fixpoint subst_ctx (cc : context) (sp : Sigma_pattern) : Sigma_pattern :=
  match cc with
  | box => sp
  | ctx_app_l cc' sp' => sp_app (subst_ctx cc' sp) sp'
  | ctx_app_r sp' cc' => sp_app sp' (subst_ctx cc' sp)
  end
.

(* Definition box_context := subst_ctx box sp_bottom.
Eval compute in box_context.

Definition tree_context := subst_ctx (
    ctx_app_l (ctx_app_r sp_bottom box) (sp_app sp_bottom sp_bottom)
  ) sp_bottom.
Eval compute in tree_context. *)

Definition free_vars_ctx (C : context) : (ListSet.set EVar) :=
  match C with
  | box => List.nil
  | ctx_app_l cc sp => free_vars sp
  | ctx_app_r sp cc => free_vars sp
  end
.
(* Inductive got_tau : Sigma_pattern -> Prop :=
  | cons (phi : Sigma_partern) : got_tau (sp_impl sp_bottom phi)
. *)

Inductive got : Sigma_pattern -> Prop :=
  (* Propositional tautology *)
  | E_prop_tau1 (phi : Sigma_pattern) :
      got (sp_impl phi phi)

  | E_prop_tau2 (phi psi : Sigma_pattern) :
      got (sp_impl phi (sp_impl psi phi))

  | E_prop_tau3 (phi psi xi : Sigma_pattern) :
      got (
        sp_impl
          (sp_impl phi (sp_impl psi xi))
          (sp_impl (sp_impl phi psi) (sp_impl phi xi)))

  | E_prop_tau4 (phi psi : Sigma_pattern) :
      got (sp_impl
        (sp_impl (sp_not phi) (sp_not psi))
        (sp_impl (psi) (psi)))

  (* Modus ponens *)
  | E_mod_pon (phi1 phi2 : Sigma_pattern) :
    got phi1 ->
    got (sp_impl phi1 phi2) ->
    got phi2

  (* Existential quantifier *)
  | E_ex_quan {phi : Sigma_pattern} (x y : EVar) :
    got (sp_impl (e_subst_var phi (sp_var y) x) (sp_exists x phi))

  (* Existential generalization *)
  | E_ex_gen (phi1 phi2 : Sigma_pattern) (x : EVar) :
    got (sp_impl phi1 phi2) ->
    negb (set_mem evar_eq_dec x (free_vars phi2)) = true ->
    got (sp_impl (sp_exists x phi1) phi2)

  (* Propagation bottom *)
  | E_prop_bot (C : context) :
    got (sp_impl (subst_ctx C sp_bottom) sp_bottom)

  (* Propagation disjunction *)
  | E_prop_dis (C : context) (phi1 phi2 : Sigma_pattern) :
      (* phi3 = context cs (sp_or phi1 phi2) ->
      phi4 = context cs phi1 ->
      phi5 = context cs phi2 ->
      got_c (sp_impl phi3 (sp_or phi4 phi5)) *)
      got (sp_impl
            (subst_ctx C (sp_or phi1 phi2))
            (sp_or
              (subst_ctx C phi1)
              (subst_ctx C phi2)))

  (* Propagation exist *)
  | E_prop_ex (C : context) (phi : Sigma_pattern) (x : EVar) :
    negb (set_mem evar_eq_dec x (free_vars_ctx C)) = true ->
    got (sp_impl
      (subst_ctx C (sp_exists x phi))
      (sp_exists x (subst_ctx C phi)))

  (* Framing *)
  | E_framing (C : context) (phi1 phi2 : Sigma_pattern) :
    got (sp_impl phi1 phi2) ->
    got (sp_impl (subst_ctx C phi1) (subst_ctx C phi2))

  (* Set Variable Substitution *)
  | E_svar_subst (phi : Sigma_pattern) (psi X : SVar) :
    got phi ->
    got (e_subst_set phi (sp_set psi) X)

  (* Pre-Fixpoint *)
  | E_pre_fixp (phi : Sigma_pattern) (X : SVar) :
    got (sp_impl
          (e_subst_set phi (sp_mu X phi) X)
          (sp_mu X phi))

  (* Knaster-Tarski *)
  | E_knaster_tarski (phi psi : Sigma_pattern) (X : SVar) :
    got (sp_impl (e_subst_set phi psi X) psi) ->
    got (sp_impl (sp_mu X phi) psi)

  (* Existence *)
  | E_existence (x : EVar) : got (sp_exists x (sp_var x))

  (* Singleton *)
  | E_singleton (C1 C2 : context) (x : EVar) (phi : Sigma_pattern) :
    got (sp_not (sp_and
            (subst_ctx C1 (sp_and (sp_var x) phi))
            (subst_ctx C2 (sp_and (sp_var x) (sp_not phi)))))
.

(* Provability
    - can be formalised with the M-valuation, "can be deduced" and can be proved operator
*)

(* Inductive proof_result : ? :=
  | success (?)
  | fail
. *)


(* Definition 7., page 5. *)
(* Definedness: *)
Definition c_definedness := sp_const(sigma_c("definedness")).
Definition Definedness (phi : Sigma_pattern) : Sigma_pattern := (c_definedness _._ phi).
Notation "|^ phi ^|" := (Definedness phi) (at level 100).

(* Totality *)
Definition c_totality := sp_const(sigma_c("totality")).
Definition Totality (phi : Sigma_pattern) := (c_totality _._ phi).
Notation "|_ phi _|" := (Totality phi).

(* Equality *)
Definition c_equality := sp_const(sigma_c("equality")).
(* TODO: it is a legal interpretation? *)
Definition Equality (l r : Sigma_pattern) := ((c_equality _._ l) _._ r).
Notation "phi1 ~=~ phi2" := (Equality phi1 phi2) (at level 100).

(* Non-equality *)
Definition c_non_equality := sp_const(sigma_c("non-equality")).
Definition NonEquality (l r : Sigma_pattern) := ((c_non_equality _._ l) _._ r).
Notation "phi1 !=~ phi2" := (NonEquality phi1 phi2) (at level 100).

(* Variable membership *)
Definition c_membership := sp_const(sigma_c("membership")).
Definition Membership (x : EVar) (phi : Sigma_pattern) := 
  ((c_membership _._ (sp_var x)) _._ phi).
Notation "x -< phi" := (Membership x phi) (at level 100).

(* Non-membership *)
Definition c_non_membership := sp_const(sigma_c("non-membership")).
Definition NonMembership (x : EVar) (phi : Sigma_pattern) := 
  ((c_non_membership _._ (sp_var x)) _._ phi).
Notation "x !-< phi" := (NonMembership x phi) (at level 100).

(* Set inclusion *)
Definition c_set_incl := sp_const(sigma_c("set inclusion")).
Definition SetInclusion (l r : Sigma_pattern) := 
  ((c_set_incl _._ l) _._ r).
Notation "phi1 <: phi2" := (SetInclusion phi1 phi2) (at level 100).

(* Set exclusion *)
Definition c_set_excl := sp_const(sigma_c("set exclusion")).
Definition SetExclusion (l r : Sigma_pattern) := 
  ((c_set_excl _._ l) _._ r).
Notation "phi1 !<: phi2" := (SetExclusion phi1 phi2) (at level 100).

Reserved Notation "phi |-> phi'" (at level 80).
Inductive OneStepTransition : Sigma_pattern -> Sigma_pattern -> Prop :=
| OST_totality {phi : Sigma_pattern} :
    (c_totality _._ phi) |->
    (sp_not (Definedness (sp_not phi)))

| OST_equality {l r : Sigma_pattern} :
    ((c_equality _._ l) _._ r) |->
    (Totality (sp_equiv l r))

| OST_non_equality {l r : Sigma_pattern} :
    ((c_equality _._ l) _._ r) |->
    (sp_not (Equality l r))

| OST_membership {x : EVar} {phi : Sigma_pattern} :
    ((c_membership _._ (sp_var x)) _._ phi) |->
    (Totality (sp_and (sp_var x) phi))

| OST_non_membership {x : EVar} {phi : Sigma_pattern} :
    ((c_non_membership _._ (sp_var x)) _._ phi) |->
    (sp_not (Membership x phi))

| OST_set_inclusion {l r} :
    ((c_set_incl _._ l) _._ r) |->
    (Totality (sp_impl l r))

| OST_set_exclusion {l r} :
    ((c_set_excl _._ l) _._ r) |->
    (sp_not (SetInclusion l r))
where "a |-> b" := (OneStepTransition a b).

(* TODO: tests!!! *)
(* Theorem test01 : (Totality (sp_bottom)) |-> (sp_not (Definedness (sp_not sp_bottom))).
Proof. eapply OST_totality. Qed. *)

Reserved Notation "phi |->* phi'" (at level 100).
Inductive AnyStepTransition : Sigma_pattern -> Sigma_pattern -> Prop :=
| AST_refl {phi : Sigma_pattern} :
    phi |->* phi

| AST_trans {phi phi'' : Sigma_pattern} (phi' : Sigma_pattern) :
    (phi |-> phi') -> (phi' |->* phi'') ->
    (phi |->* phi'')
where "phi |->* phi'" := (AnyStepTransition phi phi').

(* Theorem test02 : (Totality (sp_bottom)) |->* (sp_not (Definedness (sp_not sp_bottom))).
Proof.
  eapply AST_trans.
  - eapply OST_totality.
  - eapply AST_refl.
Qed. *)


(* Many-sorted algebra *)
Section MSA.

(* Sorts of many-sorted algebra*)
Inductive MSA_sorts : Set :=
| Nat
| List
| Cfg
.

(* a function which corresponds constants of AML to sorts of MSA *)
Fixpoint AML_sort_name (s : MSA_sorts) : Sigma_pattern :=
match s with
| Nat => sp_const(sigma_c("Nat"))
| List => sp_const(sigma_c("List"))
| Cfg => sp_const(sigma_c("Cfg"))
end.

(* we can also define them *)
Definition AML_Nat := AML_sort_name(Nat).
Definition AML_List := AML_sort_name(List).
Definition AML_Cfg := AML_sort_name(Cfg).


Definition c_inhabitant_set := sp_const(sigma_c("inhabitant set")).
Definition InhabitantSetOf (s : MSA_sorts) := (c_inhabitant_set _._ (AML_sort_name s)).
Notation "'[[' s ']]'" := (InhabitantSetOf s) (at level 100).

(* Notation "< p1 , p2 , .. , pn >" := (sp_and .. (sp_and p1 p2) .. pn) : core_scope. *)


(* Definition 15, MSA-signature *)
(* Definition S := (set MSA_sorts).
 *)
(* Definition c := ((set_add Nat nil), (set_add Nat nil), .. , (set_add Nat nil)) : (S, S, .. , S). *)
(* Notation "( x * y * .. * z )" := (prod .. (prod x y) .. z) (at level 0). *)

(* Definition a := sp_and .. (sp_and sp_bottom sp_bottom) .. . *)

(* Notation "'MSA_signature' x" := (pair x ( prod .. (prod x x) .. x )) (at level 10). *)

(* f : s1 x s2 x ... x sn -> s *)

(* Ezt nem lehet ugyanazert mint az Y-kombinatort *)
(* Inductive D : Type :=
| Single : set MSA_sorts
| Multiple : (D, set MSA_sorts)
.
 *)

(* Definition MSA_signature (S : set MSA_sorts) := (S, (S*, S)). *)

(* TODO:
  how to emphasize constraints:
  - M is non-empty
  - Sigma depends on M
*)
(* Definition MSA_pair (M : set MSA_sorts) (Sigma : set (set Sigma_pattern)) := (M, Sigma). *)

(* TODO: for all below
    - restrict n > 0
    - rewrite to vector OK
*)
Fixpoint _and_gen (n : nat) (vec : list Sigma_pattern) : Sigma_pattern :=
match n with
| O => sp_bottom
| S O => (List.hd sp_bottom vec)
| S n' => ((List.hd sp_bottom vec) _&_ (_and_gen n' (List.tl vec)))
end.

(* Fixpoint and_gen {n : nat} (vec : VectorDef.t Sigma_pattern n) : Sigma_pattern :=
match n with
| O => sp_bottom
| S O => VectorDef.hd vec
| S n => sp_bottom
end. *)

Fixpoint and_gen {n : nat} (vec : VectorDef.t Sigma_pattern n) : Sigma_pattern :=
  _and_gen n (to_list vec).

(* Fixpoint and_gen (n : nat) (vec : VectorDef.t Sigma_pattern n) : Sigma_pattern :=
match n - 1 with
| O => List.hd sp_bottom (VectorDef.to_list vec)
| S n' => ((List.hd sp_bottom (VectorDef.to_list vec)) _&_ (and_gen n' (VectorDef.of_list (List.tl (VectorDef.to_list vec)))))
end. *)

Lemma zero_eq : (_and_gen 0 (List.nil)) = sp_bottom.
Proof. simpl. reflexivity. Qed.

Definition x1 := sp_var(evar_c("x1")).
Lemma x1_eq : (_and_gen 1 ((List.cons x1) List.nil)) = x1.
Proof. simpl. reflexivity. Qed.

Definition x2 := sp_var(evar_c("x2")).
Lemma x1_x2_eq : (_and_gen 2 ((List.cons x1) (List.cons x2 List.nil))) = (x1 _&_ x2).
Proof. simpl. reflexivity. Qed.

Definition x3 := sp_var(evar_c("x3")).
Lemma x1_x2_x3_eq :
  (_and_gen 3 ((List.cons x1) ((List.cons x2) ((List.cons x3) List.nil))))
= (x1 _&_ x2 _&_ x3).
Proof. simpl. reflexivity. Qed.

Definition x4 := sp_var(evar_c("x4")).
Lemma x1_x2_x3__x4_eq :
  (_and_gen 4 ((List.cons x1) (
    (List.cons x2) ((List.cons x3) ((List.cons x4) List.nil)))))
= (x1 _&_ x2 _&_ x3 _&_ x4).
Proof. simpl. reflexivity. Qed.

Fixpoint _assoc_elem (n : nat) (vars : list EVar) (sorts : list MSA_sorts) : Sigma_pattern :=
match n with
| O => sp_bottom
| S O => ((List.hd (evar_c("x")) vars) -< [[ (List.hd Nat sorts) ]])
| S n' => sp_and
      ( (List.hd (evar_c("x")) vars) -< [[ (List.hd Nat sorts) ]] )
      (_assoc_elem n' (List.tl vars) (List.tl sorts))
end.

Fixpoint assoc_elem {n : nat} (vars : VectorDef.t EVar n) (sorts : VectorDef.t MSA_sorts n) : Sigma_pattern :=
  _assoc_elem n (to_list (vars)) (to_list (sorts)).

Lemma zero_eq_assoc : (_assoc_elem 0 (List.nil) (List.nil)) = sp_bottom.
Proof. simpl. reflexivity. Qed.

Definition x1_e := evar_c("x1").
Lemma x1_eq_assoc : 
  (_assoc_elem 1 ((List.cons x1_e) List.nil) ((List.cons Nat) List.nil))
= (x1_e -< [[ Nat ]]).
Proof. simpl. reflexivity. Qed.

Definition x2_e := evar_c("x2").
Lemma x1_x2_eq_assoc : 
  (_assoc_elem 2
    ((List.cons x1_e) (List.cons x2_e List.nil))
    ((List.cons Nat) (List.cons List List.nil)))
= ((x1_e -< [[ Nat ]]) _&_ (x2_e -< [[ List ]])).
Proof. simpl. reflexivity. Qed.

Definition x3_e := evar_c("x3").
Lemma x1_x2_x3_eq_assoc : 
  (_assoc_elem 3 
    ((List.cons x1_e) ((List.cons x2_e) (List.cons x3_e List.nil)))
    ((List.cons Nat) ((List.cons List) (List.cons Cfg List.nil))))
= ((x1_e -< [[ Nat ]]) _&_ (x2_e -< [[ List ]]) _&_ (x3_e -< [[ Cfg ]])).
Proof. simpl. reflexivity. Qed.

Definition x4_e := evar_c("x4").
Lemma x1_x2_x3__x4_eq_assoc : 
  (_assoc_elem 4 
    ((List.cons x1_e) ((List.cons x2_e) ((List.cons x3_e) (List.cons x4_e List.nil))))
    ((List.cons Nat) ((List.cons List) ((List.cons Cfg) (List.cons Nat List.nil)))))
= ((x1_e -< [[ Nat ]]) _&_ (x2_e -< [[ List ]]) _&_ (x3_e -< [[ Cfg ]]) _&_ 
    (x4_e -< [[ Nat ]])).
Proof. simpl. reflexivity. Qed.

Fixpoint _assoc_params (f : Sigma) (n : nat) (vars : list EVar) : Sigma_pattern :=
match n with
| O => sp_const f
| S O => ((sp_const f) _._ (sp_var (List.nth O vars (evar_c("error singleton fun param list")))))
| S n' => (_assoc_params f n' vars) _._ 
            (sp_var (List.nth n' vars (evar_c("error long fun param list"))))
end.

Fixpoint assoc_params (f : Sigma) {n : nat} (vars : VectorDef.t EVar n) : Sigma_pattern :=
  _assoc_params f n (to_list (vars)).

Definition c_fun_f := sigma_c("fun").
Definition fun_f   := sp_const(c_fun_f).
Lemma zero_eq_par : (_assoc_params c_fun_f 0 (List.nil)) = fun_f.
Proof. simpl. unfold fun_f. reflexivity. Qed.

Lemma x1_eq_par :
  (_assoc_params c_fun_f 1 ((List.cons x1_e) List.nil)) = (fun_f _._ x1).
Proof. simpl. unfold fun_f. unfold x1. reflexivity. Qed.

Lemma x1_x2_eq_par :
  (_assoc_params c_fun_f 2 ((List.cons x1_e) (List.cons x2_e List.nil)))
= (fun_f _._ x1 _._ x2).
Proof. simpl. unfold fun_f. unfold x1. unfold x2. reflexivity. Qed.

Lemma x1_x2_x3_eq_par :
  (_assoc_params c_fun_f 3 ((List.cons x1_e) ((List.cons x2_e) (List.cons x3_e List.nil))))
= (fun_f _._ x1 _._ x2 _._ x3).
Proof. simpl. unfold fun_f. unfold x1. unfold x2. unfold x3. reflexivity. Qed.

Lemma x1_x2_x3__x4_eq_par :
  (_assoc_params c_fun_f 4
    ((List.cons x1_e) ((List.cons x2_e) ((List.cons x3_e) (List.cons x4_e List.nil)))))
= (fun_f _._ x1 _._ x2 _._ x3 _._ x4).
Proof. simpl. reflexivity. Qed.


Definition Nonempty_Sort (s : MSA_sorts) := ([[ s ]] !=~ sp_bottom).

(* if constant function, then sp_bottom will stand on the application's left hand-side, because false implies everything *)
Definition Function (f : Sigma) {n : nat}
            (ss : t MSA_sorts n) (s : MSA_sorts)
            (xs : t EVar n) (y : EVar) :=
  (sp_impl
    (assoc_elem xs ss) (* ((x1 -< [[s1]]) _&_ .. _&_ (xn -< [[sn]])) *)
    (sp_exists y (sp_and
      (y -< [[ s ]])
      ((assoc_params f xs) ~=~ (sp_var y)) (* ((f _._ x1) _._ .. _._ xn) ~=~ y *)))).

Definition Sort (s : MSA_sorts) := s.

End MSA.


Definition vc := VectorDef.cons.
Definition vn := VectorDef.nil.

(* Functional notation of the function *)
Notation "f '::' '-->' s" := (Function f (vn _) s) (at level 0).

(* f : s1 x s2 x ... x sn -> s *)
Notation "f '::' s1 'X' s2 'X' .. 'X' sn '-->' s" :=
  (Function f (vc _ s1 _ (vc _ s2 _ .. (vc _ sn _ (vn _)) .. )) s) (at level 0).

Check (c_fun_f :: Nat X Nat --> Nat).


(* Natural numbers *)
Section NaturalNumbers.

Definition c_zero := (sigma_c("zero")).
Definition zero := c_zero :: --> Nat. (* (Function zero_c (VectorDef.nil _) Nat). *)

Definition c_succ := (sigma_c("succ")).
Definition succ := (c_succ :: Nat X Nat --> Nat). (* (Function succ_c (vc _ Nat 0 (vn _)) Nat). *)

Definition c_plus := (sigma_c("plus")).
Definition plus := (c_plus :: Nat X Nat --> Nat).
(* (Function (sigma_c("plus")) (vc _ Nat 1 (vc _ Nat 0 (vn _))) Nat). *)

Definition c_mult := sigma_c("mult").
Definition mult := (c_mult :: Nat X Nat --> Nat).
(* (Function c_mult (vc _ Nat 1 (vc _ Nat 0 (vn _))) Nat). *)

(* TODO: generalize all definitions to Sigma_pattern, and restrict these to EVar and function (e.g. 0) *)

(* Example: x + 0 = x *)
Definition x := (evar_c("x")).
Definition y := (evar_c("y")).
Definition const_0 := (evar_c("0")).

Definition x_plus_0_eq_x := 
  (sp_forall x (sp_impl (x -< InhabitantSetOf(Nat))
                        (plus (vc _ x 1 (vc _ (zero (vn _) y) 0 (vn _))) x) )).

Check x_plus_0_eq_x.

(* TODO: introduce the notation of ':' *)

(* Inductive Domain *)
(* Axiom Inductive_Domain := 
  ([[ Nat ]]) ~=~ (sp_mu 
                    (svar_c("D")) 
                    (sp_or
                      (zero (evar_c("anything")))
                      (* potential error! *)
                      (succ (svar_c("D")) (evar_c("anything"))))).

Axiom Peano_Induction := (sp_impl () ()). *)

End NaturalNumbers.

End AML.
