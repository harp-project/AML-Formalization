Require Import String.

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

(* Definition is_svar_box (s : SVar) : bool :=
  match s with
  | svar_c id => eqb id "box"
  end
.

Inductive sp_context_e : Sigma_pattern -> Prop :=
  | c_box (x : SVar) (p : (is_svar_box x) = true ) : sp_context_e (sp_set x)
  | c_cons_l (spl spr : Sigma_pattern) (p : sp_context_e spl) : sp_context_e (sp_app spl spr)
  | s_cons_r (spl spr : Sigma_pattern) (p : sp_context_e spr) : sp_context_e (sp_app spl spr)
. *)

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
Definition sp_or  (phi1 phi2 : Sigma_pattern) := sp_impl (sp_not phi1) phi2.
Definition sp_and (phi1 phi2 : Sigma_pattern) :=
  sp_not (sp_or (sp_not phi1) (sp_not phi2)).
Definition sp_tatu := sp_not sp_bottom.
Definition sp_forall (x : EVar) (phi : Sigma_pattern) :=
  sp_not (sp_exists x (sp_not phi)).
(*nuX.phi*)

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
  (* | E_prop_tau phi : phi is prop tau -> got phi *)

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

(* Inductive proof_result : ? :=
  | success (?)
  | fail
. *)

(* TO DO:
    - free variables: Context -> Set OK
    - eSubstitution for sets OK
x occurs free
x occurs bound
instance of x is bound or not -> identify the location in the tree

box, context : define inductively
 *)

(*
  2019.11.06.:
  Context 3 fajtaja:
    - inductive tipuskent OK
    - az amit Daviddal most elkezdtunk () -
    - a context egy fuggveny -
  Folyamatosan jegyzeteljunk!
*)
(*
  2019.11.13.:
  - the best choice: context as a separate inductive type
        reason: it is much simple to reason about an inductively defined structure, than to reason about a function of which we know nothing
  - discuss about Gamma |- Phi  (soundness theorem)
    - include it between proof rules
*)

End AML.

Section Model.

Require Import Lists.ListSet.
Require Import List.

Definition set_subset {A : Set} (X Y : set A) := forall a : A, set_In a X -> set_In a Y.

Variable A : Set.
Hypothesis A_eq_dec : forall (a b : A), {a = b} + {a <> b}.

Record element (a : set A) := mk_element{
  val_elem : A;
  th_elem  : set_In val_elem a
}.
(* 
Definition th_elem_eq_dec : forall {S : set A} {v : A} (x y : set_In v S), {x = y} + {x <> y}.
Proof.
  intros.  *)

Definition element_eq_dec : forall {S : set A} (x y : element S), {x = y} + {x <> y}. Admitted.

Definition subset (a : set A) : Type := set (element a).

Definition set_A_eq_dec : forall (x y : set A), {x = y} + {x <> y}.
Proof.
  decide equality.
Defined.

Lemma subset_of_self (a : set A) : (set_subset a a).
Proof. unfold set_subset. trivial. Qed.

Lemma element_of_subset_is_element (a b : set A) (e : A) : set_In e a -> set_subset a b -> set_In e b.
Proof. intros. exact (H0 e H). Qed.

Definition ss_to_set {a : set A} (b : subset a) : set A := set_map A_eq_dec (val_elem a) b.

(* Fixpoint set_to_ss (a b : set A) (ssp : set_subset a b) {struct a} : (subset b) :=
match a with
  | nil => nil
  | cons x xs => set_add element_eq_dec (mk_element b x (ssp _ _)) (set_to_ss xs b _)
end. *)

Theorem nil_is_subset (a : set A) : set_subset nil a.
Proof.
  unfold set_subset.
  intros.
  inversion H.
Qed.

Record Sigma_model := {
  M : set A;
  app : element M -> element M -> subset M;
  interpretation : Sigma -> subset M;
}.


Fixpoint pointwise_app_r {sm : Sigma_model} (a : element (M sm)) (B : subset (M sm)) : subset (M sm) := 
match B with
  | nil => nil
  | cons x xs => set_union element_eq_dec ((app sm) a x) (pointwise_app_r a xs)
end.

Fixpoint pointwise_app {sm : Sigma_model} (A B : subset (M sm)) : subset (M sm) :=
match A with
  | nil => nil
  | cons x xs => set_union element_eq_dec (pointwise_app_r x B) (pointwise_app xs B)
end.

SearchPattern (_ -> set_In _ _).

Fixpoint self_subset (a : set A) : subset a. Admitted. (* 
set_map element_eq_dec (fun x : A => mk_element a x _) a. *)
(* match a with?
  | nil => nil
  | cons x xs => set_add element_eq_dec
                         (mk_element a x (set_add_intro2 A_eq_dec xs (eq_refl x)))
                         (*set_map extend container with x*)_
end. *)

Fixpoint complementer {a : set A} (b : subset a) : subset a :=
match b with
  | nil => self_subset a
  | cons x xs => set_remove element_eq_dec x (complementer xs)
end.

Check fold_right.

Fixpoint ext_valuation {sm : Sigma_model}
  (pe : EVar -> element (M sm)) (pv : SVar -> subset (M sm)) (sp : Sigma_pattern) {struct sp}
  : subset (M sm) :=
match sp with
  | sp_var x => cons (pe x) nil
  | sp_set X => pv X
  | sp_const sigma => interpretation sm sigma
  | sp_app phi1 phi2 =>
    pointwise_app (ext_valuation pe pv phi1)
                  (ext_valuation pe pv phi2)
  | sp_bottom => nil
  | sp_impl phi1 phi2 => set_union element_eq_dec
         (complementer (ext_valuation pe pv phi1))
         (ext_valuation pe pv phi2)
  | sp_exists x phi => set_fold_right
            (fun m u => set_union element_eq_dec
              u
              (ext_valuation (fun (y : EVar) => if evar_eq_dec y x then m else pe y) pv phi))
            nil
            (self_subset (M sm))
  | sp_mu X phi => fold_right
            (fun _ xi => ext_valuation pe (fun (Y : SVar) => if svar_eq_dec Y X then xi else pv Y) phi)
            nil
            (repeat tt (length (M sm)))
end.

End Model.

Check cons.