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
                      (* x can only be sp_var or sp_const *)
                  (* this can be restricted with operational evaluation rules *)
Definition Membership (x : Sigma_pattern) (phi : Sigma_pattern) := 
  ((c_membership _._ x) _._ phi).
Notation "x -< phi" := (Membership x phi) (at level 100).

(* Variable non-membership *)
Definition c_non_membership := sp_const(sigma_c("non-membership")).
Definition NonMembership (x : EVar) (phi : Sigma_pattern) := 
  ((c_non_membership _._ (sp_var x)) _._ phi).
Notation "x !-< phi" := (NonMembership x phi) (at level 100).

(* Pattern non-membership *)
(* Definition NonMembership (x : Sigma_pattern) (phi : Sigma_pattern) := 
  ((c_non_membership _._ x) _._ phi).
Notation "x !-< phi" := (NonMembership x phi) (at level 100). *)

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

| OST_membership {x : Sigma_pattern} {phi : Sigma_pattern} :
    ((c_membership _._ x) _._ phi) |->
    (Totality (sp_and x phi))

| OST_non_membership {x : Sigma_pattern} {phi : Sigma_pattern} :
    ((c_non_membership _._ x) _._ phi) |->
    (sp_not (Membership x phi))

(* | OST_membership {x : Sigma_pattern} {phi : Sigma_pattern} :
    ((c_membership _._ x) _._ phi) |->
    (Totality (sp_and x phi))

| OST_non_membership {x : Sigma_pattern} {phi : Sigma_pattern} :
    ((c_non_membership _._ x) _._ phi) |->
    (sp_not (Membership x phi)) *)

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

Definition vc := VectorDef.cons.
Definition vn := VectorDef.nil.


Fixpoint _and_gen (n : nat) (vec : list Sigma_pattern) : Sigma_pattern :=
match n with
| O => sp_bottom
| S O => (List.hd sp_bottom vec)
| S n' => ((List.hd sp_bottom vec) _&_ (_and_gen n' (List.tl vec)))
end.

Fixpoint and_gen {n : nat} (vec : VectorDef.t Sigma_pattern n) : Sigma_pattern := 
  _and_gen n (to_list vec).

Lemma zero_eq : (_and_gen 0 (List.nil)) = sp_bottom.
Proof. simpl. reflexivity. Qed.

Lemma zero_eq' : (and_gen (vn _)) = sp_bottom.
Proof. simpl. reflexivity. Qed.

Definition x1 := sp_var(evar_c("x1")).
Lemma x1_eq : (_and_gen 1 ((List.cons x1) List.nil)) = x1.
Proof. simpl. reflexivity. Qed.

Lemma x1_eq' : (and_gen (vc _ x1 0 (vn _))) = x1.
Proof. simpl. reflexivity. Qed.

Definition x2 := sp_var(evar_c("x2")).
Lemma x1_x2_eq : (_and_gen 2 ((List.cons x1) (List.cons x2 List.nil))) = (x1 _&_ x2).
Proof. simpl. reflexivity. Qed.

Lemma x1_x2_eq' : (and_gen (vc _ x1 1 (vc _ x2 0 (vn _)))) = (x1 _&_ x2).
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

Fixpoint _assoc_elem (n : nat) (vars : list Sigma_pattern) (sorts : list MSA_sorts) : Sigma_pattern :=
match n with
| O => sp_bottom
| S O => ((List.hd (sp_const (sigma_c("error at elem assoc S O"))) vars) -< [[ (List.hd Nat sorts) ]])
| S n' => sp_and
      ( (List.hd (sp_const (sigma_c("error at elem assoc S n"))) vars) -< [[ (List.hd Nat sorts) ]] )
      (_assoc_elem n' (List.tl vars) (List.tl sorts))
end.

Fixpoint assoc_elem {n : nat} (vars : VectorDef.t Sigma_pattern n) (sorts : VectorDef.t MSA_sorts n) : Sigma_pattern :=
  _assoc_elem n (to_list (vars)) (to_list (sorts)).

Lemma zero_eq_assoc : (_assoc_elem 0 (List.nil) (List.nil)) = sp_bottom.
Proof. simpl. reflexivity. Qed.

Lemma x1_eq_assoc : 
  (_assoc_elem 1 ((List.cons x1) List.nil) ((List.cons Nat) List.nil))
= (x1 -< [[ Nat ]]).
Proof. simpl. reflexivity. Qed.

Lemma x1_x2_eq_assoc : 
  (_assoc_elem 2
    ((List.cons x1) (List.cons x2 List.nil))
    ((List.cons Nat) (List.cons List List.nil)))
= ((x1 -< [[ Nat ]]) _&_ (x2 -< [[ List ]])).
Proof. simpl. reflexivity. Qed.

Lemma x1_x2_x3_eq_assoc : 
  (_assoc_elem 3 
    ((List.cons x1) ((List.cons x2) (List.cons x3 List.nil)))
    ((List.cons Nat) ((List.cons List) (List.cons Cfg List.nil))))
= ((x1 -< [[ Nat ]]) _&_ (x2 -< [[ List ]]) _&_ (x3 -< [[ Cfg ]])).
Proof. simpl. reflexivity. Qed.

Lemma x1_x2_x3__x4_eq_assoc : 
  (_assoc_elem 4 
    ((List.cons x1) ((List.cons x2) ((List.cons x3) (List.cons x4 List.nil))))
    ((List.cons Nat) ((List.cons List) ((List.cons Cfg) (List.cons Nat List.nil)))))
= ((x1 -< [[ Nat ]]) _&_ (x2 -< [[ List ]]) _&_ (x3 -< [[ Cfg ]]) _&_ 
    (x4 -< [[ Nat ]])).
Proof. simpl. reflexivity. Qed.

Fixpoint _assoc_params (f : Sigma_pattern) (n : nat) (vars : list Sigma_pattern) : Sigma_pattern :=
match n with
| O => f
| S O => (f _._ (List.nth O vars (sp_const (sigma_c("error singleton fun param list")))))
| S n' => (_assoc_params f n' vars) _._ 
            (List.nth n' vars (sp_const (sigma_c("error long fun param list"))))
end.

Fixpoint assoc_params (f : Sigma_pattern) {n : nat} (vars : VectorDef.t Sigma_pattern n) : Sigma_pattern :=
  _assoc_params f n (to_list (vars)).

Definition c'_f := sigma_c("fun").
Definition fun_f   := sp_const(c'_f).
Lemma zero_eq_par : (_assoc_params fun_f 0 (List.nil)) = fun_f.
Proof. simpl. unfold fun_f. reflexivity. Qed.

Lemma x1_eq_par :
  (_assoc_params fun_f 1 ((List.cons x1) List.nil)) = (fun_f _._ x1).
Proof. simpl. unfold fun_f. unfold x1. reflexivity. Qed.

Lemma x1_x2_eq_par :
  (_assoc_params fun_f 2 ((List.cons x1) (List.cons x2 List.nil)))
= (fun_f _._ x1 _._ x2).
Proof. simpl. unfold fun_f. unfold x1. unfold x2. reflexivity. Qed.

Lemma x1_x2_x3_eq_par :
  (_assoc_params fun_f 3 ((List.cons x1) ((List.cons x2) (List.cons x3 List.nil))))
= (fun_f _._ x1 _._ x2 _._ x3).
Proof. simpl. unfold fun_f. unfold x1. unfold x2. unfold x3. reflexivity. Qed.

Lemma x1_x2_x3__x4_eq_par :
  (_assoc_params fun_f 4
    ((List.cons x1) ((List.cons x2) ((List.cons x3) (List.cons x4 List.nil)))))
= (fun_f _._ x1 _._ x2 _._ x3 _._ x4).
Proof. simpl. reflexivity. Qed.


Definition Nonempty_Sort (s : MSA_sorts) := ([[ s ]] !=~ sp_bottom).

(* if constant function, then sp_bottom will stand on the application's left hand-side, because false implies everything *)
(* this is allowed because this is only syntax and not the deduction - we don't need the type restriction at syntax level *)
(* Definition __y := evar_c("__y"). (* we abstract away this variable. in fact it can be anything *) *)
Definition Function (f : Sigma_pattern) {n : nat}
            (ss : t MSA_sorts n) (s : MSA_sorts)
            (xs : t Sigma_pattern n) (y : EVar) : Sigma_pattern :=
  (sp_impl
    (assoc_elem xs ss) (* ((x1 -< [[s1]]) _&_ .. _&_ (xn -< [[sn]])) *)
    (sp_exists y (sp_and
      ((sp_var y) -< [[ s ]])
      ((assoc_params f xs) ~=~ (sp_var y)) (* ((f _._ x1) _._ .. _._ xn) ~=~ y *)))).

Definition Sort (s : MSA_sorts) := s.

End MSA.


(* Functional notation of the function *)
Notation "f '_:_' '-->' s" := (Function f (vn _) s) (at level 0).

Notation "f '_:_' s1 '-->' s" := (Function f (vc _ s1 0 (vn _)) s) (at level 0).

(* f : s1 x s2 x ... x sn -> s *)
Notation "f '_:_' s1 'X' s2 'X' .. 'X' sn '-->' s" :=
  (Function f (vc _ s1 _ (vc _ s2 _ .. (vc _ sn _ (vn _)) .. )) s) (at level 0).

Check (fun_f _:_ Nat X Nat --> Nat).

(* Instead of notation "forall x : Nat . pattern" we introduce: *)
Notation "'for_some' xc 'of_sort' sort 'states' pattern" := 
  (sp_exists xc (sp_and ((sp_var xc) -< InhabitantSetOf(sort)) pattern)) (at level 0).
Notation "'for_all' xc 'of_sort' sort 'states' pattern" := 
  (sp_forall xc (sp_impl ((sp_var xc) -< InhabitantSetOf(sort)) pattern)) (at level 0).

Definition QE_ex_to_all (xc : EVar) (sort : MSA_sorts) (pattern : Sigma_pattern) :=
    (sp_exists xc (sp_and ((sp_var xc) -< InhabitantSetOf(sort)) pattern)).

(* Proposition 18. *)
Inductive QuantificationEquivalence : Sigma_pattern -> Sigma_pattern -> Prop :=
| QE_ex_to_all' (xc : EVar) (sort : MSA_sorts) (pattern : Sigma_pattern) :
   QuantificationEquivalence
    (sp_exists xc (sp_and ((sp_var xc) -< InhabitantSetOf(sort)) pattern))
    (sp_not (sp_forall xc (sp_impl ((sp_var xc) -< InhabitantSetOf(sort)) (sp_not pattern))))
| QE_all_to_ex' (xc : EVar) (sort : MSA_sorts) (pattern : Sigma_pattern) :
  QuantificationEquivalence
    (sp_exists xc (sp_and ((sp_var xc) -< InhabitantSetOf(sort)) pattern))
    (sp_not (sp_forall xc (sp_impl ((sp_var xc) -< InhabitantSetOf(sort)) (sp_not pattern))))
(* where "a |--> b" := (QuantificationEquivalence a b) *).

(* Natural numbers *)
Section NaturalNumbers.

Definition zero : Sigma_pattern := sp_const(sigma_c("zero")).
Definition succ : Sigma_pattern := sp_const (sigma_c("succ")).
Definition plus : Sigma_pattern := sp_const (sigma_c("plus'")).
Definition mult : Sigma_pattern := sp_const (sigma_c("mult")).

(* Inductive Nat_elements : Type :=
| zero (res_var : EVar) : ((c_zero _:_ --> Nat) (vn _) res_var)
. *)

Definition zero_fun := (zero _:_ --> Nat).
Definition succ_fun := (succ _:_ Nat --> Nat).
Definition plus_fun := (plus _:_ Nat X Nat --> Nat).
Definition mult_fun := (mult _:_ Nat X Nat --> Nat).

(* Definition zero''                       := zero_pat (vn _).
Definition succ'' (x : Sigma_pattern)   := succ_pat (vc _ x 0 (vn _)).
Definition plus'' (x y : Sigma_pattern) := plus'_pat (vc _ x 1 (vc _ y 0 (vn _))).
Definition mult'' (x y : Sigma_pattern) := mult_pat (vc _ x 1 (vc _ y 0 (vn _))). *)

Definition succ' (x : Sigma_pattern)   := succ _._ x.
Definition plus' (x y : Sigma_pattern) := plus _._ x _._ y.
Definition mult' (x y : Sigma_pattern) := mult _._ x _._ y.

(* Example: x + 0 = x *)
Definition c_x := (evar_c("x")).
Definition c_y := (evar_c("y")).
Definition c_z := (evar_c("z")).
Definition c_n := evar_c("n").
Definition n := sp_var(c_n).
Definition x := (sp_var (evar_c("x"))).
Definition y := (sp_var (evar_c("y"))).
Definition z := (sp_var (evar_c("z"))).

(* Check (for_some c_x of_sort Nat states sp_bottom). *)

Definition x_plus'_0_eq_x :=
  (for_all c_x of_sort Nat states ((plus' x zero) ~=~ x)).

(* Examples *)

(* we have to specify the type of function parameters, because if not, the
following statement about natural numbers also can be formalised: *)
Definition foo := plus' plus zero.

Definition one := succ' zero.
Definition two := succ' one.
Definition three := succ' two.
Definition five := succ' (succ' three).
Definition six := succ' five.

Definition plus_1_2_eq_3 := ((plus' one two) ~=~ three).
Definition plus_1_plus_2_3_eq_6 := ((plus' one (plus' two three)) ~=~ six).
Definition plus_1_plus_2_3_eq_1_plus_2_plus_3 := ((plus' one (plus' two three)) ~=~ (plus' one (plus' two three))).
Definition plus_1_plus_2_3_eq_1_plus_5 :=
  ((plus' one (plus' two three)) ~=~ (plus' one five)).
Definition x_plus_2_plus_3_eq_x_plus_5 := 
  (for_all c_x of_sort Nat states ((plus' (plus' x two) three) ~=~ (plus' x five))).
Definition x_plus_3_eq_x_plus_3 :=
  (for_all c_x of_sort Nat states (plus' x three) ~=~ (plus' x three)).
Definition x_plus_y_eq_x_plus_y :=
  (for_all c_x of_sort Nat states
    (for_all c_y of_sort Nat states (plus' x y) ~=~ (plus' x y))).

Definition plus_1_2 := plus' one two.
Definition plus_2_3 := plus' two three.
Definition plus_1_plus_2_3 :=  plus' one plus_2_3.
Definition plus_1_plus_2_3_eq_plus_1_plus_2_3 :=
 plus_1_plus_2_3 ~=~ plus' one plus_2_3.
Definition plus_1_plus_2_3_eq_plus_1_plus_2_3' :=
  plus_1_plus_2_3 ~=~ plus_1_plus_2_3.
Definition plus_1_plus_2_3_eq_plus_1_5 := plus_1_plus_2_3 ~=~ plus' one five.

Definition plus_x_1_eq_5 :=
  (for_all c_x of_sort Nat states ((plus' x one) ~=~ five)).

Definition plus_x_1_eq_plus_y_1 :=
  (for_all c_x of_sort Nat states
    (for_all c_y of_sort Nat states
      (plus' x one ~=~ (plus' y one)))).

Definition plus_x_1_eq_y :=
  (for_all c_x of_sort Nat states
    (for_all c_y of_sort Nat states
      ((plus' x one) ~=~ y))).

Definition plus_x_1_eq_plus_y_3 :=
  (for_all c_x of_sort Nat states
    (for_all c_y of_sort Nat states
      ((plus' x one) ~=~ (plus' y three)))).

Definition plus_x_z_eq_y :=
  (for_all c_x of_sort Nat states
    (for_all c_y of_sort Nat states
      (for_all c_z of_sort Nat states
        ((plus' x z) ~=~ y)))).

Definition plus_x_plus_z_3_eq_y :=
  (for_all c_x of_sort Nat states
    (for_all c_y of_sort Nat states
      (for_all c_z of_sort Nat states
        ((plus' x (plus' z three))) ~=~ y))).

Fixpoint SumFromZeroTo (n : Sigma_pattern) : Sigma_pattern :=
match n with
| sp_const _ => zero
(* succ _ *)
| sp_app _ b => plus' (succ' b) (SumFromZeroTo b)
| _ => sp_const(sigma_c("non-exhaustive pattern"))
end.

Lemma until_zero : (SumFromZeroTo zero) = zero.
Proof. simpl. reflexivity. Qed.

Lemma until_one : (SumFromZeroTo one) = (plus' one zero).
Proof. simpl. reflexivity. Qed.

Lemma until_two : (SumFromZeroTo two) = (plus' two (plus' one zero)).
Proof. simpl. reflexivity. Qed.


(* 1 + ... + n = n * (n+1) / 2. *)
Definition Sum_of_first_n := 
  for_all c_n of_sort Nat states (mult' two (SumFromZeroTo n) ~=~ mult' n (succ' n)).


Fixpoint ProdFromOneTo (n : Sigma_pattern) : Sigma_pattern :=
match n with
| sp_const _ => zero
(* succ _ *)
| sp_app a b => 
  match b with
  | sp_const _ => one
  | sp_app _ _ => mult' (succ' b) (ProdFromOneTo b)
  | _ => sp_const(sigma_c("non-exhaustive pattern"))
  end
| _ => sp_const(sigma_c("non-exhaustive pattern"))
end.

Lemma until_zero' : (ProdFromOneTo zero) = zero.
Proof. simpl. reflexivity. Qed.

Lemma until_one' : (ProdFromOneTo one) = one.
Proof. simpl. reflexivity. Qed.

Lemma until_two' : (ProdFromOneTo two) = (mult' two one).
Proof. simpl. reflexivity. Qed.

Lemma until_three' : (ProdFromOneTo three) = (mult' three (mult' two one)).
Proof. simpl. reflexivity. Qed.


Fixpoint SumOfSquaresFromZeroTo (n : Sigma_pattern) : Sigma_pattern :=
match n with
| sp_const _ => zero
(* succ _ *)
| sp_app _ b => plus' (mult' (succ' b) (succ' b)) (SumOfSquaresFromZeroTo b)
| _ => sp_const(sigma_c("non-exhaustive pattern"))
end.

Lemma until_zero'' : (SumOfSquaresFromZeroTo zero) = zero.
Proof. simpl. reflexivity. Qed.

Lemma until_one'' : (SumOfSquaresFromZeroTo one) = (plus' (mult' one one) zero).
Proof. simpl. reflexivity. Qed.

Lemma until_two'' : (SumOfSquaresFromZeroTo two) = (plus' (mult' two two) (plus' (mult' one one) zero)).
Proof. simpl. reflexivity. Qed.


(* 1^2 + ... + n^2 = n(n+1)(2*n + 1) / 6. *)
Definition Sum_of_squares :=
  for_all c_n of_sort Nat states (
    mult' six (SumOfSquaresFromZeroTo n) ~=~ 
    mult' n (mult' (succ' n) (plus' (mult' two n) one))).


End NaturalNumbers.

Section MatchingMuLogic.

Fixpoint _app_inhabitant_sets (n : nat) (vec : list MSA_sorts) : Sigma_pattern :=
match n with
| O => sp_const (sigma_c("cannot operate on empty parameters"))
| S O => InhabitantSetOf (List.hd Nat vec)
| S n' => InhabitantSetOf (List.hd Nat vec) _._ (_app_inhabitant_sets n' (List.tail vec))
end.

Fixpoint app_inhabitant_sets {n : nat} (vec : VectorDef.t MSA_sorts n) : Sigma_pattern :=
  _app_inhabitant_sets n (to_list vec).

Lemma nil_eq_nil : app_inhabitant_sets (vn MSA_sorts) = sp_const (sigma_c("cannot operate on empty parameters")).
Proof. simpl. reflexivity. Qed.

Lemma app_inhabitant_sets_test_one_element :
  (app_inhabitant_sets (vc _ Nat 0 (vn _)) = (InhabitantSetOf(Nat))).
Proof. simpl. reflexivity. Qed.

Lemma app_inhabitant_sets_test_two_elements :
  (app_inhabitant_sets (vc _ Nat 1 (vc _ List 0 (vn _))) = (InhabitantSetOf(Nat) _._ InhabitantSetOf(List))).
Proof. simpl. reflexivity. Qed.

Lemma app_inhabitant_sets_test_three_elements :
  (app_inhabitant_sets (vc _ Nat 2 (vc _ List 1 (vc _ Cfg 0 (vn _)))) = (InhabitantSetOf(Nat)  _._ (InhabitantSetOf(List) _._ InhabitantSetOf(Cfg)))).
Proof. simpl. reflexivity. Qed.

                  (* sp_const only *)
Definition Arity (sigma : Sigma_pattern) {n : nat} (s_vec : VectorDef.t MSA_sorts n) (s : MSA_sorts) :=
  sigma _._ (app_inhabitant_sets s_vec) <: InhabitantSetOf(s).

End MatchingMuLogic.

Section ConstructorsAndTermAlgebras.

(* Definition NoConfusion_I := .
Definition NoConfusion_II := .
(* Inductive Domain *)
Definition Inductive_Domain 
  (D : SVar)
:= 
  (
    [[ Term ]]) ~=~ 
    (sp_mu D (sp_or ...))
  ). *)

End ConstructorsAndTermAlgebras.

Section NaturalNumbers.


Definition Inductive_Domain (D : SVar) := 
  (InhabitantSetOf(Nat)) ~=~ sp_mu D (sp_or zero (succ' (sp_set D))).

Definition Peano_Induction (cn : EVar) (phi : Sigma_pattern -> Sigma_pattern) :=
  (sp_impl
    (sp_and
      (phi  zero)
      (sp_forall cn (
        sp_impl
          (phi (sp_var cn))
          (phi (succ' (sp_var cn))) )))
    (sp_forall cn (phi (sp_var cn)))).

(* Examples *)

(* <= relation *)
Definition less (l r : Sigma_pattern) :=
  for_some c_x of_sort Nat states (plus' l x ~=~ r).

Definition less_or_equal (l r : Sigma_pattern) :=
  sp_or
    (l ~=~ r)
    for_some c_x of_sort Nat states (plus' l x ~=~ r).

(* States that if:
  - zero <= zero and
  - for all n of sort Nat : 0 <= (n+1)
 then for all n of sort Nat states 0 <= n *)
Definition every_number_is_positive : Sigma_pattern :=
  Peano_Induction c_n (less_or_equal zero).

Definition less2 (a b : Sigma_pattern) := less a (succ' b).
(* indukcioval leirhato, hogy ha 0+1 > 0 és minden n>0-ra n+1 > 0 akkor n+1 > 0 *)

(* States that if:
  - zero < zero + 1 and
  - for all n of sort Nat : 0 < ((n+1) + 1)
 then for all n of sort Nat states 0 < (n+1) *)
Definition every_successor_is_strictly_positive : Sigma_pattern :=
  Peano_Induction c_n (less2 zero).

End NaturalNumbers.

End AML.
