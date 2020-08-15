Require Import Arith.
Require Import ZArith.
Require Import List.
Require Import extralibrary.

Require Export String.
Require Export Coq.Lists.ListSet.
Require Export Ensembles_Ext.

(** * Names and swaps of names *)

Inductive name_kind : Set :=
  | evar_c {id_ev : string}: name_kind
  | svar_c {id_sv : string}: name_kind.

Definition name : Set := (name_kind * Z)%type.

Definition kind (n: name) : name_kind := fst n.

(** Equality between names is decidable. *)

Lemma eq_name: forall (n1 n2: name), {n1 = n2} + {n1 <> n2}.
Proof.
  assert (forall k1 k2: name_kind, {k1 = k2} + {k1 <> k2}).
  decide equality. exact (string_dec id_ev id_ev0).
  assert (forall p1 p2: positive, {p1 = p2} + {p1 <> p2}).
  decide equality. exact (string_dec id_sv id_sv0).
  assert (forall z1 z2: Z, {z1 = z2} + {z1 <> z2}).
  decide equality.
  decide equality.
  decide equality.
  decide equality.
Defined.

(** Moreover, we have the following obvious simplification rules on
  tests over name equality. *)

Lemma eq_name_true:
  forall (A: Set) (n: name) (a b: A), (if eq_name n n then a else b) = a.
Proof.
  intros. case (eq_name n n); congruence.
Qed.

Lemma eq_name_false:
  forall (A: Set) (n m: name) (a b: A), n <> m -> (if eq_name n m then a else b) = b.
Proof.
  intros. case (eq_name n m); congruence.
Qed.

(** The following lemma shows that there always exists a name
  of the given kind that is fresh w.r.t. the given list of names, that is,
  distinct from all the names in this list. *)

Definition find_fresh_name (k: name_kind) (l: list name) : name :=
  (k, 1 + fold_right (fun (n:name) x => Z.max (snd n) x) 0 l)%Z.

Lemma find_fresh_name_is_fresh:
  forall k l, let n := find_fresh_name k l in ~List.In n l /\ kind n = k.
Proof.
  intros.
  set (ident := fun (n: name) => snd n). 
  set (maxid := 
   fold_right (fun (n:name) x => Z.max (ident n) x) 0%Z).
  assert (forall x, List.In x l -> (ident x <= maxid l)%Z).
    generalize l. induction l0; simpl; intros.
    elim H.
    elim H; intros. subst x. apply Zmax1. 
    apply Z.le_trans with (maxid l0). auto. apply Zmax2.
  replace n with (k, 1 + maxid l)%Z. 
  split. red; intro. generalize (H _ H0). unfold ident, snd. omega.
  reflexivity.
  unfold n; reflexivity.
Qed.

Lemma fresh_name:
  forall (k: name_kind) (l: list name), exists n, ~List.In n l /\ kind n = k.
Proof.
  intros. exists (find_fresh_name k l). apply find_fresh_name_is_fresh.
Qed.

(** As argued by Pitts and others, swaps (permutations of two
  names) are an interesting special case of renamings.
  We will use swaps later to prove that our definitions
  are equivariant, that is, insensitive to the choices of fresh identifiers. *)

Definition swap (u v x: name) : name :=
  if eq_name x u then v else if eq_name x v then u else x.

(** The following lemmas are standard properties of swaps:
  self-inverse, injective, kind-preserving. *)

Lemma swap_left: forall x y, swap x y x = y.
Proof. intros. unfold swap. apply eq_name_true. Qed.

Lemma swap_right: forall x y, swap x y y = x.
Proof.
  intros. unfold swap. case (eq_name y x); intro. auto.
  apply eq_name_true. 
Qed.

Lemma swap_other: forall x y z, z <> x -> z <> y -> swap x y z = z.
Proof. intros. unfold swap. repeat rewrite eq_name_false; auto. Qed.

Lemma swap_inv: forall u v x, swap u v (swap u v x) = x.
Proof.
  intros; unfold swap.
  case (eq_name x u); intro. 
    case (eq_name v u); intro. congruence. rewrite eq_name_true. congruence.
  case (eq_name x v); intro.
    rewrite eq_name_true. congruence.
  repeat rewrite eq_name_false; auto.
Qed.

Lemma swap_inj: forall u v x y, swap u v x = swap u v y -> x = y.
Proof.
  intros. rewrite <- (swap_inv u v x). rewrite <- (swap_inv u v y).
  congruence.
Qed.

Lemma swap_kind: forall u v x, kind u = kind v -> kind (swap u v x) = kind x.
Proof.
  intros. unfold swap. case (eq_name x u); intro.
  congruence. case (eq_name x v); intro.
  congruence. auto.
Qed.

(** ** Sigma patterns *)

Inductive Sigma : Type := sigma_c {id_si : string}.

Inductive Sigma_pattern : Type :=
| sp_param (x : name)
| sp_var (n : nat)
| sp_set (n : nat)
| sp_const (sigma : Sigma)
| sp_app (phi1 phi2 : Sigma_pattern)
| sp_bottom
| sp_impl (phi1 phi2 : Sigma_pattern)
| sp_exists (phi : Sigma_pattern)
| sp_mu (phi : Sigma_pattern)
.

Notation "'' x" := (sp_param x) (at level 3).
Notation "' n" := (sp_var n) (at level 3).
Notation "` n" := (sp_set n) (at level 3).
Notation "^ c" := (sp_const c) (at level 3).
Notation "a $ b" := (sp_app a b) (at level 50, left associativity).
Notation "'Bot'" := sp_bottom.
Notation "a ~> b"  := (sp_impl a b) (at level 90, right associativity,
                                      b at level 200).
Notation "'ex' , phi" := (sp_exists phi) (at level 55).
Notation "'mu' , phi" := (sp_mu phi) (at level 55).

Definition sigma_eq_dec : forall (x y : Sigma), { x = y } + { x <> y }.
Proof. decide equality. exact (string_dec id_si0 id_si1). Defined.

Definition sp_eq_dec : forall (x y : Sigma_pattern), { x = y } + { x <> y }.
Proof.
decide equality.
- exact (eq_name x0 x1).
- decide equality.
- decide equality.
- exact (sigma_eq_dec sigma sigma0).
Defined.

(*
Inductive strictly_positive : SVar -> Sigma_pattern -> Prop :=
| sp_sp_var (x : EVar) (X : SVar) : strictly_positive X (sp_var x)
| sp_sp_set (Y : SVar) (X : SVar) : strictly_positive X (sp_set Y)
| sp_sp_const (sigma : Sigma) (X : SVar) : strictly_positive X (sp_const sigma)
| sp_sp_app (phi1 phi2 : Sigma_pattern) (X : SVar) :
  strictly_positive X phi1 -> strictly_positive X phi2 ->
  strictly_positive X (sp_app phi1 phi2)
| sp_sp_bottom (X : SVar) : strictly_positive X sp_bottom
| sp_sp_impl (phi1 phi2 : Sigma_pattern) (X : SVar) :
  strictly_negative X phi1 -> strictly_positive X phi2 ->
  strictly_positive X (sp_impl phi1 phi2)
| sp_sp_exists (x : EVar) (phi : Sigma_pattern) (X : SVar) :
  strictly_positive X phi ->
  strictly_positive X (sp_exists x phi)
| sp_sp_mu (Y : SVar) (phi : Sigma_pattern) (X : SVar) :
  (Y = X) \/ (Y <> X /\ strictly_positive X phi) ->
  strictly_positive X (sp_mu Y phi)
with strictly_negative : SVar -> Sigma_pattern -> Prop :=
| sn_sp_var (x : EVar) (X : SVar) : strictly_negative X (sp_var x)
| sn_sp_set (Y : SVar) (X : SVar) : Y <> X -> strictly_negative X (sp_set Y)
| sn_sp_const (sigma : Sigma) (X : SVar) : strictly_negative X (sp_const sigma)
| sn_sp_app (phi1 phi2 : Sigma_pattern) (X : SVar) :
  strictly_negative X phi1 -> strictly_negative X phi2 ->
  strictly_negative X (sp_app phi1 phi2)
| sn_sp_bottom (X : SVar) : strictly_negative X sp_bottom
| sn_sp_impl (phi1 phi2 : Sigma_pattern) (X : SVar) :
  strictly_positive X phi1 -> strictly_negative X phi2 ->
  strictly_negative X (sp_impl phi1 phi2)
| sn_sp_exists (x : EVar) (phi : Sigma_pattern) (X : SVar) :
  strictly_negative X phi ->
  strictly_negative X (sp_exists x phi)
| sn_sp_mu (Y : SVar) (phi : Sigma_pattern) (X : SVar) :
  (Y = X) \/ (Y <> X /\ strictly_negative X phi) ->
  strictly_negative X (sp_mu Y phi)
.
*)

(** There are two substitution operations over types, written
  [vsubst] and [psubst] in Pollack's talk.  
  [vsubst] substitutes a pattern for a bound variable (a de Bruijn index).
  [psubst] substitutes a pattern for a free variable (a name).

  The crucial observation is that variable capture cannot occur
  during either substitution:
  - Types never contain free de Bruijn indices, since these
    indices are used only for representing bound variables.
    Therefore, [vsubst] does not need to
    perform lifting of de Bruijn indices in the substituted type.
  - Types never bind names, only de Bruijn indices.
    Therefore, [psubst] never needs to perform renaming of
    names in the substituted term when descending below a
    binder.
 *)

(* substitute bound variable x for psi in phi *)
Fixpoint vsubst (phi : Sigma_pattern) (psi : Sigma_pattern) (x : nat) :=
match phi with
| sp_param x' => sp_param x'
| sp_var n => match compare_nat n x with
              | Nat_less _ _ _ => sp_var n
              | Nat_equal _ _ _ => psi
              | Nat_greater _ _ _ => sp_var (pred n)
              end
| sp_set n => match compare_nat n x with
              | Nat_less _ _ _ => sp_var n
              | Nat_equal _ _ _ => psi
              | Nat_greater _ _ _ => sp_set (pred n)
              end
| sp_const sigma => sp_const sigma
| sp_app phi1 phi2 => sp_app (vsubst phi1 psi x)
                             (vsubst phi2 psi x)
| sp_bottom => sp_bottom
| sp_impl phi1 phi2 => sp_impl (vsubst phi1 psi x) (vsubst phi2 psi x)
| sp_exists phi' => sp_exists (vsubst phi' psi (S x))
| sp_mu phi' => sp_mu (vsubst phi' psi (S x))
end.

(* substitute free variable x for psi in phi *)
Fixpoint psubst (phi : Sigma_pattern) (psi : Sigma_pattern) (x : name) :=
match phi with
| sp_param x' => if eq_name x x' then psi else sp_param x'
| sp_var x' => sp_var x'
| sp_set X => sp_set X
| sp_const sigma => sp_const sigma
| sp_app phi1 phi2 => sp_app (psubst phi1 psi x)
                             (psubst phi2 psi x)
| sp_bottom => sp_bottom
| sp_impl phi1 phi2 => sp_impl (psubst phi1 psi x) (psubst phi2 psi x)
| sp_exists phi' => sp_exists (psubst phi' psi x)
| sp_mu phi' => sp_mu (psubst phi' psi x)
end.

(** The free names of a type are defined as follow.  Notice the
  [exists] and [mu] cases: they do not bind any name. *)

Definition set_singleton {T : Type}
  (eq : forall (x y : T), { x = y } + { x <> y })
  := fun x : T => set_add eq x List.nil.

Fixpoint free_vars (phi : Sigma_pattern) : (ListSet.set name) :=
match phi with
| sp_param x => set_singleton eq_name x
| sp_var x => List.nil
| sp_set X => List.nil
| sp_const sigma => List.nil
| sp_app phi1 phi2 => set_union eq_name (free_vars phi1) (free_vars phi2)
| sp_bottom => List.nil
| sp_impl phi1 phi2 => set_union eq_name (free_vars phi1) (free_vars phi2)
| sp_exists phi => free_vars phi
| sp_mu phi => free_vars phi
end.

Definition name_is_evar (x : name) : bool :=
match (fst x) with
| evar_c => true
| svar_c => false
end.

Definition free_evars (phi : Sigma_pattern) : (ListSet.set name) :=
  set_fold_right
    (fun x acc => if (name_is_evar x) then set_add eq_name x acc else acc)
    (free_vars phi)
    (List.nil).

Definition free_svars (phi : Sigma_pattern) : (ListSet.set name) :=
  set_fold_right
    (fun x acc => if (name_is_evar x) then acc else set_add eq_name x acc)
    (free_vars phi)
    (List.nil).

(* Section Derived_operators. *)

Definition sp_not (phi : Sigma_pattern) := phi ~> sp_bottom.
Notation "¬ a"     := (sp_not   a  ) (at level 75).

Definition sp_or  (l r : Sigma_pattern) := (¬ l) ~> r.
Notation "a _|_ b" := (sp_or    a b) (at level 85, right associativity).

Definition sp_and (l r : Sigma_pattern) := ¬ ((¬ l) _|_ (¬ r)).
Notation "a _&_ b" := (sp_and   a b) (at level 80, right associativity).

Definition sp_iff (l r : Sigma_pattern) := ((l ~> r) _&_ (r ~> l)).
Notation "a <~> b" := (sp_iff a b) (at level 95, no associativity).

Definition sp_top := (¬ sp_bottom).
Notation "'Top'" := sp_top.

Definition sp_forall (phi : Sigma_pattern) :=
  ¬ (sp_exists (¬ phi)).
Notation "'all' , phi" := (sp_forall phi) (at level 55).

Definition sp_nu (phi : Sigma_pattern) :=
  ¬ (sp_mu (¬ (vsubst phi (¬ (sp_set 0)) 0))).
Notation "'nu' , phi" := (sp_nu phi) (at level 55).

(* End Derived_operators. *)
Check find_fresh_name.
Definition var (sname : string) : Sigma_pattern :=
  sp_param (find_fresh_name (@evar_c sname) nil). 
Definition set (sname : string) : Sigma_pattern :=
  sp_param (find_fresh_name (@svar_c sname) nil). 
Definition const (sname : string) : Sigma_pattern := sp_const (sigma_c sname).

(* Example patterns *)

Definition simple := var ("x").
Definition more := set ("A") _|_ ¬ (set "A").
Definition complex :=
  var("A") ~> (var("B") ~> ¬(set("C"))) $
  ex , set ("D") $ Bot _&_ Top.
Definition custom_constructor := const ("ctor") $ var ("a").
Definition predicate := const ("p") $ var ("x1") $ var ("x2").
Definition function :=
  const ("f") $ (var ("x")) $ (mu , (sp_set 0)).
Definition free_and_bound :=
  all , (sp_set 0) _&_ var("y"). (* forall x, x /\ y *)

