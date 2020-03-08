Require Import String.
Require Import Coq.Init.Datatypes.

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
Notation "a _&_ b" := (sp_and a b) (left associativity, at level 40). (* TODO: Check associativity level *)
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

Check negb.

Definition evar_eq (x y : EVar) : bool :=
  match x, y with
  | evar_c id_x, evar_c id_y => eqb id_x id_y
  end
.

Require Import Coq.Lists.ListSet.

Fixpoint free_vars (phi : Sigma_pattern) : (set EVar) :=
  match phi with
 | sp_var x => set_add evar_eq_dec x nil
 | sp_set X => nil
 | sp_const sigma => nil
 | sp_app phi1 phi2 =>
    set_union evar_eq_dec
      (free_vars phi1)
      (free_vars phi2)
 | sp_bottom => nil
 | sp_impl phi1 phi2 =>
    set_union evar_eq_dec
      (free_vars phi1)
      (free_vars phi2)
 | sp_exists y phi =>
    set_diff evar_eq_dec
      (free_vars phi)
      (set_add evar_eq_dec y nil)
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

Definition box_context := subst_ctx box sp_bottom.
Eval compute in box_context.

Definition tree_context := subst_ctx (
    ctx_app_l (ctx_app_r sp_bottom box) (sp_app sp_bottom sp_bottom)
  ) sp_bottom.
Eval compute in tree_context.

Definition free_vars_ctx (C : context) : (set EVar) :=
  match C with
  | box => nil
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
Theorem test01 : (Totality (sp_bottom)) |-> (sp_not (Definedness (sp_not sp_bottom))).
Proof. eapply OST_totality. Qed.

Reserved Notation "phi |->* phi'" (at level 100).
Inductive AnyStepTransition : Sigma_pattern -> Sigma_pattern -> Prop :=
| AST_refl {phi : Sigma_pattern} :
    phi |->* phi

| AST_trans {phi phi'' : Sigma_pattern} (phi' : Sigma_pattern) :
    (phi |-> phi') -> (phi' |->* phi'') ->
    (phi |->* phi'')
where "phi |->* phi'" := (AnyStepTransition phi phi').

Theorem test02 : (Totality (sp_bottom)) |->* (sp_not (Definedness (sp_not sp_bottom))).
Proof.
  eapply AST_trans.
  - eapply OST_totality.
  - eapply AST_refl.
Qed.

(* sp_app will simulate the function application *)


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
Reserved Notation "sp 'states'" (at level 1).

Inductive Statement : Sigma_pattern -> Prop :=
| S_pat {s : Sigma_pattern} : s states
where "sp 'states'" := (Statement sp).

Definition Nonempty_Sort (s : MSA_sorts) := ([[ s ]] !=~ sp_bottom) states.
(* Proof.
  intros.
  eapply S_pat.
Qed.
 *)
Require Import Coq.Lists.List.
Definition sorts_list := cons (List) (cons (Cfg) nil).
Check length sorts_list.
Compute (length sorts_list).

(* TODO: constructors of vector hide constructors of ListSet *)
(* Require Import Coq.Vectors.VectorDef.
Check of_list sorts_list.
Check to_list (of_list sorts_list).

Compute List.nth O (sorts_list) Nat.

Definition v := of_list sorts_list.
Compute (length sorts_list).
Check v.

Check tl v.

Check to_list v.
Check List.tl (to_list v).
 *)

(* TODO: for all below
    - restrict n > 0
    - rewrite to vector
*)
Fixpoint and_gen (n : nat) (vec : list Sigma_pattern) : Sigma_pattern :=
match n - 1 with
| O => (List.hd sp_bottom vec)
| S n' => ((List.hd sp_bottom vec) _&_ (and_gen n' (List.tl vec)))
end.

Compute and_gen 2 (cons ( sp_var(evar_c("x1")) ) (cons ( sp_var(evar_c("x2")) ) nil)).

(* Fixpoint associate_ (n : nat) (vars : list Sigma_pattern) (sorts : list MSA_sorts) : (list (Sigma_pattern * MSA_sorts)):=
match n with
| O => cons ((List.nth O vars sp_bottom), (List.nth O sorts_list Nat)) nil
| S n' => cons
      ((List.nth ((length vars) - n') vars sp_bottom), (List.nth ((length sorts) - n') sorts Nat))
      (associate_ n' vars sorts)
end. *)

(* Definition x1 := sp_var(evar_c("x1")).
Compute associate_ 1 (cons x1 nil) (cons Nat nil). *)

Check evar_c("x").

Fixpoint assoc_type_incl (n : nat) (vars : list EVar) (sorts : list MSA_sorts) : Sigma_pattern :=
match n - 1 with
| O => ((List.hd (evar_c("x")) vars) -< [[ (List.hd Nat sorts_list) ]])
| S n' => sp_and
      ( (List.hd (evar_c("x")) vars) -< [[ (List.hd Nat sorts) ]] )
      (assoc_type_incl n' (List.tl vars) (List.tl sorts))
end.

Definition var_x1 := evar_c("x1").
Compute assoc_type_incl 1 (cons var_x1 nil) (cons Nat nil).

Fixpoint assoc_fun_with_params (f : Sigma) (n : nat) (vars : list EVar) : Sigma_pattern :=
match n - 1 with
| O => ((sp_const f) _._ (sp_var (List.nth O vars (evar_c("x")))))
| S n' => (assoc_fun_with_params f n' vars) _._ (sp_var (List.nth (S n') vars (evar_c("x"))))
end.

Definition fun_f := sigma_c("f").
Compute assoc_fun_with_params fun_f 1 (cons var_x1 nil).
Definition var_x2 := evar_c("x2").
Compute assoc_fun_with_params fun_f 2 (cons var_x1 (cons var_x2 nil)).
Check assoc_fun_with_params fun_f 2 (cons var_x1 (cons var_x2 nil)).

Definition var_y := evar_c("y").
Check (assoc_fun_with_params fun_f 2 (cons var_x1 (cons var_x2 nil))) ~=~ (sp_var var_y).

Definition Function (n : nat) (vars : list EVar) (sorts : list MSA_sorts) (f : Sigma) (y : EVar) (s : MSA_sorts) :=
(sp_impl
  (* (sp_and sp_and (x1 -< [[ s1 ]]) (x2 -< [[ s2 ]])) .. (xn -< [[ sn ]])) *)
  (assoc_type_incl n vars sorts)

  (sp_exists y (
    sp_and
      (y -< [[ s ]])

      (* (sp_app (sp_app f x1) .. xn) ~=~ y *)
      ((assoc_fun_with_params f n vars) ~=~ (sp_var y))
    )
  )
).
(* Proof.
  intros.
  eapply S_pat.
Qed. *)

(* This will be possible only when vector will be used, because of length coercion *)
(* (* f : s1 x s2 x ... x sn -> s *)
Notation "f : s1 x s2 x ... x sn -> s" := Function ... . *)

(* TODO: Sort membership *)
Definition c_sort := sp_const(sigma_c("Sort")). (* represents the sort set, containing all sorts *)
(* Definition Sort (s : MSA_sorts) := s  c_sort. *)

End MSA.

(* Natural numbers *)
Section NaturalNumbers.

Definition zero (y : EVar) := (Function 1 nil nil (sigma_c("0")) y Nat).

Definition succ (x0 y : EVar) := (Function 1 (cons x0 nil) (cons Nat nil) (sigma_c("succ")) y Nat).

Definition plus (x0 x1 y : EVar) := (Function 1 (cons x0 (cons x1 nil)) (cons Nat (cons Nat nil)) (sigma_c("plus")) y Nat).

Definition mult (x0 x1 y : EVar) := (Function 1 (cons x0 (cons x1 nil)) (cons Nat (cons Nat nil)) (sigma_c("mult")) y Nat).

(* TODO: generalize all definitions to Sigma_pattern, and restrict these to EVar and function (e.g. 0) *)

(* Example: x + 0 = x *)
Definition x := (evar_c("x")).
Definition y := (evar_c("y")).
Definition const_0 := (evar_c("0")).
Definition x_plus_0_eq_x := sp_forall x (
  sp_impl
    (x -< InhabitantSetOf(Nat) )
    ((plus x const_0 y) ~=~ (sp_var x))
).

(* TODO: introduce the notation of ':' *)

End NaturalNumbers.

End AML.
