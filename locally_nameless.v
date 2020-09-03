Require Import Arith.
Require Import ZArith.
Require Import List.
Require Import extralibrary.

Require Export String.
Require Export Coq.Lists.ListSet.
Require Export Ensembles_Ext.

Require Export Coq.Program.Wf.
(* Require Import Equations.Equations. *)

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

Definition name_eqb (x y : name) : bool :=
  match (fst x) with
  | @evar_c s1 => match (fst y) with
                  | @evar_c s2 => if String.eqb s1 s2 then Z.eqb (snd x) (snd y) else false
                  | svar_c => false
                  end
  | @svar_c s1 => match (fst y) with
                  | evar_c => false
                  | @svar_c s2 => if String.eqb s1 s2 then Z.eqb (snd x) (snd y) else false
                  end
  end.

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

Definition db_index := nat.

Record Signature := {
  Symbols : Ensemble Sigma
}.

Inductive Pattern {signature : Signature} : Type :=
| patt_freevar (x : name)
| patt_bound_evar (n : db_index)
| patt_bound_svar (n : db_index)
| patt_sym (sigma : Sigma) : In _ (Symbols signature) sigma -> Pattern
| patt_app (phi1 phi2 : Pattern)
| patt_bott
| patt_imp (phi1 phi2 : Pattern)
| patt_exists (phi : Pattern)
| patt_mu (phi : Pattern)
.

Notation "'' x" := (patt_freevar x) (at level 3).
Notation "' n" := (patt_bound_evar n) (at level 3).
Notation "` n" := (patt_bound_svar n) (at level 3).
Notation "^ c" := (patt_sym c) (at level 3).
Notation "a $ b" := (patt_app a b) (at level 50, left associativity).
Notation "'Bot'" := patt_bott.
Notation "a ~> b"  := (patt_imp a b) (at level 90, right associativity,
                                      b at level 200).
Notation "'ex' , phi" := (patt_exists phi) (at level 55).
Notation "'mu' , phi" := (patt_mu phi) (at level 55).

Definition sigma_eq_dec : forall (x y : Sigma), { x = y } + { x <> y }.
Proof. decide equality. exact (string_dec id_si0 id_si1). Defined.

(*
Definition sp_eq_dec : forall (signature : Signature)
                              (x y : @Pattern signature), { x = y } + { x <> y }.
Proof.
decide equality.
- exact (eq_name x0 x1).
- decide equality.
- decide equality.
- exact (sigma_eq_dec sigma sigma0).
Defined.
*)

Inductive positive_occurrence {signature : Signature} : db_index -> Pattern -> Prop :=
| po_freevar (x : name) (n : db_index) : positive_occurrence n (patt_freevar x)
| po_var (m : db_index) (n : db_index) : positive_occurrence n (patt_bound_evar m)
| po_set (m : db_index) (n : db_index) : positive_occurrence n (patt_bound_svar m)
| po_const (sigma : Sigma) (n : db_index) {in_signature : In _ (Symbols signature) sigma} :
    positive_occurrence n (patt_sym sigma in_signature)
| po_app (phi1 phi2 : Pattern) (n : db_index) :
  positive_occurrence n phi1 -> positive_occurrence n phi2 ->
  positive_occurrence n (patt_app phi1 phi2)
| po_bott (n : db_index) : positive_occurrence n patt_bott
| po_impl (phi1 phi2 : Pattern) (n : db_index) :
  negative_occurrence n phi1 -> positive_occurrence n phi2 ->
  positive_occurrence n (patt_imp phi1 phi2)
| po_exists (phi : Pattern) (n : db_index) :
  positive_occurrence n phi ->
  positive_occurrence (n+1) (patt_exists phi)
| po_mu (phi : Pattern) (n : db_index) :
  positive_occurrence n phi ->
  positive_occurrence (n+1) (patt_mu phi)
with negative_occurrence {signature : Signature} : db_index -> Pattern -> Prop :=
| no_freevar (x : name) (n : db_index) :  negative_occurrence n (patt_freevar x)
| no_var (m : db_index) (n : db_index) :  negative_occurrence n (patt_bound_evar m)
| no_set (m : db_index) (n : db_index) :  negative_occurrence n (patt_bound_svar m)
| no_const (sigma : Sigma) (n : db_index) (in_signature : In _ (Symbols signature) sigma) :
    negative_occurrence n (patt_sym sigma in_signature)
| no_app (phi1 phi2 : Pattern) (n : db_index) :
   negative_occurrence n phi1 ->  negative_occurrence n phi2 ->
   negative_occurrence n (patt_app phi1 phi2)
| no_bott (n : db_index) :  negative_occurrence n patt_bott
| no_impl (phi1 phi2 : Pattern) (n : db_index) :
  positive_occurrence n phi1 ->  negative_occurrence n phi2 ->
   negative_occurrence n (patt_imp phi1 phi2)
| no_exists (phi : Pattern) (n : db_index) :
   negative_occurrence n phi ->
   negative_occurrence (n+1) (patt_exists phi)
| no_mu (phi : Pattern) (n : db_index) :
   negative_occurrence n phi ->
   negative_occurrence (n+1) (patt_mu phi)
.

Fixpoint well_formed {signature : Signature} (phi : @Pattern signature) : Prop :=
  match phi with
  | patt_freevar _ => True
  | patt_bound_evar _ => True
  | patt_bound_svar _ => True
  | patt_sym _ _ => True
  | patt_app psi1 psi2 => well_formed psi1 /\ well_formed psi2
  | patt_bott => True
  | patt_imp psi1 psi2 => well_formed psi1 /\ well_formed psi2
  | patt_exists psi => well_formed psi
  | patt_mu psi => positive_occurrence 0 psi /\ well_formed psi
  end
.

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
Fixpoint bvar_subst {signature : Signature} (phi psi : @Pattern signature) (x : db_index) :=
match phi with
| patt_freevar x' => patt_freevar x'
| patt_bound_evar n => match compare_nat n x with
              | Nat_less _ _ _ => patt_bound_evar n
              | Nat_equal _ _ _ => psi
              | Nat_greater _ _ _ => patt_bound_evar (pred n)
              end
| patt_bound_svar n => match compare_nat n x with
              | Nat_less _ _ _ => patt_bound_svar n
              | Nat_equal _ _ _ => psi
              | Nat_greater _ _ _ => patt_bound_svar (pred n)
              end
| patt_sym sigma pf => patt_sym sigma pf 
| patt_app phi1 phi2 => patt_app (bvar_subst phi1 psi x)
                                 (bvar_subst phi2 psi x)
| patt_bott => patt_bott
| patt_imp phi1 phi2 => patt_imp (bvar_subst phi1 psi x) (bvar_subst phi2 psi x)
| patt_exists phi' => patt_exists (bvar_subst phi' psi (S x))
| patt_mu phi' => patt_mu (bvar_subst phi' psi (S x))
end.

(* substitute free variable x for psi in phi *)
Fixpoint fvar_subst {signature : Signature} (phi psi : @Pattern signature) (x : name) :=
match phi with
| patt_freevar x' => if eq_name x x' then psi else patt_freevar x'
| patt_bound_evar x' => patt_bound_evar x'
| patt_bound_svar X => patt_bound_svar X
| patt_sym sigma in_sig => patt_sym sigma in_sig
| patt_app phi1 phi2 => patt_app (fvar_subst phi1 psi x)
                                 (fvar_subst phi2 psi x)
| patt_bott => patt_bott
| patt_imp phi1 phi2 => patt_imp (fvar_subst phi1 psi x) (fvar_subst phi2 psi x)
| patt_exists phi' => patt_exists (fvar_subst phi' psi x)
| patt_mu phi' => patt_mu (fvar_subst phi' psi x)
end.

(** The free names of a type are defined as follow.  Notice the
  [exists] and [mu] cases: they do not bind any name. *)

Definition set_singleton {T : Type}
  (eq : forall (x y : T), { x = y } + { x <> y })
  := fun x : T => set_add eq x List.nil.

Fixpoint free_vars {signature : Signature} (phi : @Pattern signature) : (ListSet.set name) :=
match phi with
| patt_freevar x => set_singleton eq_name x
| patt_bound_evar x => List.nil
| patt_bound_svar X => List.nil
| patt_sym sigma in_sig => List.nil
| patt_app phi1 phi2 => set_union eq_name (free_vars phi1) (free_vars phi2)
| patt_bott => List.nil
| patt_imp phi1 phi2 => set_union eq_name (free_vars phi1) (free_vars phi2)
| patt_exists phi => free_vars phi
| patt_mu phi => free_vars phi
end.

Definition name_is_bound_evar (x : name) : bool :=
match (fst x) with
| evar_c => true
| svar_c => false
end.

Definition free_bound_evars {signature : Signature} (phi : @Pattern signature) : (ListSet.set name) :=
  set_fold_right
    (fun x acc => if (name_is_bound_evar x) then set_add eq_name x acc else acc)
    (free_vars phi)
    (List.nil).

Definition free_bound_svars {signature : Signature} (phi : @Pattern signature) : (ListSet.set name) :=
  set_fold_right
    (fun x acc => if (name_is_bound_evar x) then acc else set_add eq_name x acc)
    (free_vars phi)
    (List.nil).

(* Section Derived_operators. *)

Definition patt_not {signature : Signature} (phi : @Pattern signature) := phi ~> patt_bott.
Notation "¬ a"     := (patt_not   a  ) (at level 75).

Definition patt_or  {signature : Signature} (l r : @Pattern signature) := (¬ l) ~> r.
Notation "a _|_ b" := (patt_or    a b) (at level 85, right associativity).

Definition patt_and {signature : Signature} (l r : @Pattern signature) :=
  ¬ ((¬ l) _|_ (¬ r)).
Notation "a _&_ b" := (patt_and   a b) (at level 80, right associativity).

Definition patt_iff {signature : Signature} (l r : @Pattern signature) :=
  ((l ~> r) _&_ (r ~> l)).
Notation "a <~> b" := (patt_iff a b) (at level 95, no associativity).

Definition patt_top {signature : Signature} := (¬ (@patt_bott signature)).
Notation "'Top'" := patt_top.

Definition patt_forall {signature : Signature} (phi : @Pattern signature) :=
  ¬ (patt_exists (¬ phi)).
Notation "'all' , phi" := (patt_forall phi) (at level 55).

Definition patt_nu {signature : Signature} (phi : @Pattern signature) :=
  ¬ (patt_mu (¬ (bvar_subst phi (¬ (patt_bound_svar 0)) 0))).
Notation "'nu' , phi" := (patt_nu phi) (at level 55).

(* End Derived_operators. *)
Definition var {signature : Signature} (sname : string) : @Pattern signature :=
  patt_freevar (find_fresh_name (@evar_c sname) nil). 
Definition set {signature : Signature} (sname : string) : @Pattern signature :=
  patt_freevar (find_fresh_name (@svar_c sname) nil). 
Definition const {signature : Signature} (sname : string)
  (in_sig : In _ (Symbols signature) (@sigma_c sname)) : @Pattern signature :=
  patt_sym (sigma_c sname) in_sig.

(* Example patterns *)

Axiom sig : Signature.
Axiom ctor_in_sig : In _ (Symbols sig) (@sigma_c "ctor").
Axiom p_in_sig : In _ (Symbols sig) (@sigma_c "p").
Axiom f_in_sig : In _ (Symbols sig) (@sigma_c "f").

Definition simple := @var sig ("x").
Definition more := @set sig ("A") _|_ ¬ (set "A").
Definition complex :=
  @var sig ("A") ~> (var("B") ~> ¬(set("C"))) $
  ex , set ("D") $ Bot _&_ Top.
Definition custom_constructor := @const sig ("ctor") ctor_in_sig $ var ("a").
Definition predicate := @const sig ("p") p_in_sig $ var ("x1") $ var ("x2").
Definition function :=
  @const sig ("f") f_in_sig $ (var ("x")) $ (mu , (patt_bound_svar 0)).
Definition free_and_bound :=
  all , (patt_bound_svar 0) _&_ @var sig ("y"). (* forall x, x /\ y *)

(* End of examples. *)

(* TODO: change to update_valuation *)
Definition update_valuation {T1 T2 : Type} (eqb : T1 -> T1 -> bool)
           (t1 : T1) (t2 : T2) (f : T1 -> T2) : T1 -> T2 :=
fun x : T1 => if eqb x t1 then t2 else f x.

(* Model of AML ref. snapshot: Definition 2 *)

Record Model := {
  Domain : Type;
  model_sig : Signature;
  nonempty_witness : exists (x : Domain), True;
  Domain_eq_dec : forall (a b : Domain), {a = b} + {a <> b};
  app_interp : Domain -> Domain -> Ensemble Domain;
  sym_interp : Sigma -> Ensemble Domain;
}.

Definition pointwise_ext {m : Model} (l r : Ensemble (Domain m)) :
                         Ensemble (Domain m) :=
fun e:Domain m => exists le re:Domain m, l le /\ r re /\ (app_interp m) le re e.

Compute @pointwise_ext {| Domain := Pattern |}
        (Singleton _ (var "a")) (Singleton _ (var "b")).

(* S . empty = empty *)
Lemma pointwise_app_bot : forall m : Model, forall S : Ensemble (Domain m),
  Same_set (Domain m) (pointwise_ext S (Empty_set (Domain m))) (Empty_set (Domain m)).
Proof.
  intros. unfold pointwise_ext. unfold Same_set. unfold Included. unfold In. split; intros.
  * inversion H. inversion H0. inversion H1. inversion H3. contradiction.
  * contradiction.
Qed.

(* Semantics of AML ref. snapshot: Definition 3 *)

Fixpoint size {signature : Signature} (p : @Pattern signature) : nat :=
match p with
| patt_app ls rs => 1 + (size ls) + (size rs)
| patt_imp ls rs => 1 + (size ls) + (size rs)
| patt_exists p' => 1 + size p'
| patt_mu p' => 1 + size p'
| _ => 0
end.

Fixpoint var_open {signature : Signature} (k : db_index) (n : name)
         (p : @Pattern signature) : Pattern :=
match p with
| patt_freevar x => patt_freevar x
| patt_bound_evar x => if beq_nat x k then patt_freevar n else patt_bound_evar x
| patt_bound_svar X => if beq_nat X k then patt_freevar n else patt_bound_svar X
| patt_sym s pf => patt_sym s pf
| patt_app ls rs => patt_app (var_open k n ls) (var_open k n rs)
| patt_bott => patt_bott
| patt_imp ls rs => patt_imp (var_open k n ls) (var_open k n rs)
| patt_exists p' => patt_exists (var_open (k + 1) n p')
| patt_mu p' => patt_mu (var_open (k + 1) n p')
end.

Lemma var_open_size :
  forall (signature : Signature) (k : db_index) (n : name) (p : @Pattern signature),
    size p = size (var_open k n p).
Proof.
  intros. generalize dependent k.
  induction p; intros; simpl; try reflexivity.
  destruct (n0 =? k); reflexivity.
  destruct (n0 =? k); reflexivity.
  rewrite (IHp1 k); rewrite (IHp2 k); reflexivity.
  rewrite (IHp1 k); rewrite (IHp2 k); reflexivity.
  rewrite (IHp (k + 1)); reflexivity.
  rewrite (IHp (k + 1)); reflexivity.
Qed.

(*
Definition pattern_lt {signature : Signature} (p1 p2 : @Pattern signature) :=
  size p1 < size p2.
Lemma pattern_lt_well_founded {signature : Signature} : well_founded (@pattern_lt signature).
Proof.
  apply well_founded_lt_compat with size; auto.
Qed.

Instance wf_pattern_lt {signature : Signature} : WellFounded (@pattern_lt signature).
apply pattern_lt_well_founded.
Defined.

Variable mysig : Signature.

Equations ext_valuation_aux {m : Model} {signature : Signature}
          (evar_val : name -> Domain m) (svar_val : name -> Ensemble (Domain m))
          (names : list name) (p : @Pattern signature) : Ensemble (Domain m)
  by wf (size p) :=
  ext_valuation_aux evar_val svar_val names (patt_freevar x) :=
    match (fst x) with
                | evar_c => Singleton _ (evar_val x)
                | svar_c => svar_val x
    end;
  ext_valuation_aux evar_val svar_val names (patt_bound_evar x) := Empty_set _;
  ext_valuation_aux evar_val svar_val names (patt_bound_svar x) := Empty_set _;
  ext_valuation_aux evar_val svar_val names (patt_sym s pf) := (sym_interp m) s;
  ext_valuation_aux evar_val svar_val names (patt_app ls rs) :=
    pointwise_ext (ext_valuation_aux evar_val svar_val names ls)
                  (ext_valuation_aux evar_val svar_val names rs);
  ext_valuation_aux evar_val svar_val names patt_bott := Empty_set _;
  ext_valuation_aux evar_val svar_val names (patt_imp ls rs) :=
    Union _ (Complement _ (ext_valuation_aux evar_val svar_val names ls))
            (ext_valuation_aux evar_val svar_val names rs);
  ext_valuation_aux evar_val svar_val names (patt_exists p') :=
    let fname := find_fresh_name (@evar_c "efresh") names in
    FA_Union
      (fun e => ext_valuation_aux (update_valuation name_eqb fname e evar_val) svar_val names
                                  (var_open 0 fname p'));
  ext_valuation_aux evar_val svar_val names (patt_mu p') :=
    let fname := find_fresh_name (@evar_c "sfresh") names in
    Ensembles_Ext.mu
      (fun S => ext_valuation_aux evar_val (update_valuation name_eqb fname S svar_val) names
                                  (var_open 0 fname p')).
Next Obligation. omega. Defined.
Next Obligation. omega. Defined.
Next Obligation. omega. Defined.
Next Obligation. omega. Defined.
Next Obligation. rewrite <- var_open_size. omega. Defined.
Next Obligation. rewrite <- var_open_size. omega. Defined.
*)

Program Fixpoint ext_valuation_aux {m : Model} {signature : Signature}
        (evar_val : name -> Domain m) (svar_val : name -> Ensemble (Domain m))
        (names : list name) (p : @Pattern signature) {measure (@size signature p)} :=
match p with
| patt_freevar x => match (fst x) with
                | evar_c => Singleton _ (evar_val x)
                | svar_c => svar_val x
                end
| patt_bound_evar x => Empty_set _
| patt_bound_svar X => Empty_set _
| patt_sym s pf => (sym_interp m) s
| patt_app ls rs => pointwise_ext (ext_valuation_aux evar_val svar_val names ls)
                                  (ext_valuation_aux evar_val svar_val names rs)
| patt_bott => Empty_set _
| patt_imp ls rs => Union _ (Complement _ (ext_valuation_aux evar_val svar_val names ls))
                           (ext_valuation_aux evar_val svar_val names rs)
| patt_exists p' =>
  let fname := find_fresh_name (@evar_c "efresh") names in
  FA_Union
    (fun e => ext_valuation_aux (update_valuation name_eqb fname e evar_val) svar_val names
                                (var_open 0 fname p'))
| patt_mu p' =>
  let fname := find_fresh_name (@svar_c "sfresh") names in
  Ensembles_Ext.mu
    (fun S => ext_valuation_aux evar_val (update_valuation name_eqb fname S svar_val) names
                                (var_open 0 fname p'))
end.
Next Obligation. simpl; omega. Defined.
Next Obligation. simpl; omega. Defined.
Next Obligation. simpl; omega. Defined.
Next Obligation. simpl; omega. Defined.
Next Obligation. simpl; rewrite <- var_open_size; omega. Defined.
Next Obligation. simpl; rewrite <- var_open_size; omega. Defined.

Definition ext_valuation {m : Model} {signature : Signature}
        (evar_val : name -> Domain m) (svar_val : name -> Ensemble (Domain m))
        (p : @Pattern signature) : Ensemble (Domain m) :=
  ext_valuation_aux evar_val svar_val (free_vars p) p.

(*
Lemma is_monotonic :
  forall (sm : Sigma_model)
         (evar_val : name -> M sm)
         (svar_val : db_index -> Ensemble (M sm)) (phi : Sigma_pattern)
         (x : db_index),
    positive x phi ->
    well_formed phi ->
    forall (l r : Ensemble (M sm)),
      Included (M sm) l r ->
      Included (M sm)
        (ext_valuation evar_val (change_val beq_nat 0 l db_val) phi)
        (ext_valuation freevar_val (change_val beq_nat 0 r db_val) phi).
Proof.
Admitted.
*)

Ltac proof_ext_val :=
simpl;intros;
repeat
  (* Normalize *)
   rewrite (Same_set_to_eq (Union_Empty_l _))
|| rewrite (Same_set_to_eq (Compl_Compl_Ensembles _ _))
|| rewrite
   (Same_set_to_eq (Compl_Union_Compl_Intes_Ensembles_alt _ _ _))
|| rewrite (Same_set_to_eq (FA_rel _ _ _))
  (* Apply *)
|| (eapply (proj1 Same_set_Compl) ; intros)
|| (eapply FA_Inters_same ; intros)
  (* Final step *)
|| exact Complement_Empty_is_Full
|| exact (Symdiff_val _ _)
|| exact (Same_set_refl _).

Section Semantics_of_derived_operators.

  (* TODO: Need to be able to simplify Program Fixpoint definitions *)
  
End Semantics_of_derived_operators.

(**
   Proof of correct semantics for the derived operators
   ref. snapshot: Proposition 4
*)

(* Theory,axiom ref. snapshot: Definition 5 *)

Record Theory := {
  theory_sig : Signature;
  patterns : Ensemble (@Pattern theory_sig)
}.

Definition satisfies_model {signature : Signature}
           (m : Model) (phi : @Pattern signature) : Prop :=
forall (evar_val : name -> Domain m) (svar_val : name -> Ensemble (Domain m)),
  Same_set _ (ext_valuation (m := m) evar_val svar_val phi) (Full_set _).

Notation "M |=M phi" := (satisfies_model M phi) (left associativity, at level 50).

Definition satisfies_theory (m: Model) (theory : Theory)
: Prop := forall axiom : Pattern, In _ (patterns theory) axiom -> (m |=M axiom).

Notation "M |=T Gamma" := (satisfies_theory M Gamma)
    (left associativity, at level 50).

Definition satisfies {signature : Signature} (theory : Theory) (p: @Pattern signature)
: Prop := forall m : Model, (m |=T theory) -> (m |=M p).

Notation "G |= phi" := (satisfies G phi) (left associativity, at level 50).

(* End of definition 5. *)

Inductive Application_context {signature : Signature} : Set :=
| box
| ctx_app_l (cc : Application_context) (p : @Pattern signature)
| ctx_app_r (p : @Pattern signature) (cc : Application_context)
.

Fixpoint subst_ctx {signature : Signature} (C : Application_context) (p : @Pattern signature)
  : Pattern :=
match C with
| box => p
| ctx_app_l C' p' => patt_app (subst_ctx C' p) p'
| ctx_app_r p' C' => patt_app p' (subst_ctx C' p)
end.

Fixpoint free_vars_ctx {signature : Signature} (C : @Application_context signature)
  : (ListSet.set name) :=
match C with
| box => List.nil
| ctx_app_l cc p => set_union eq_name (free_vars_ctx cc) (free_bound_evars p)
| ctx_app_r p cc => set_union eq_name (free_bound_evars p) (free_vars_ctx cc)
end.

(* Proof system for AML ref. snapshot: Section 3 *)

(* Auxiliary axiom schemes for proving propositional tautology *)
Reserved Notation "pattern 'tautology'" (at level 2).
Inductive Tautology_proof_rules {signature : Signature} : @Pattern signature -> Prop :=
| P1 (phi : Pattern) :
    (phi ~> phi) tautology

| P2 (phi psi : Pattern) :
    (phi ~> (psi ~> phi)) tautology

| P3 (phi psi xi : Pattern) :
    ((phi ~> (psi ~> xi)) ~> ((phi ~> psi) ~> (phi ~> xi))) tautology

| P4 (phi psi : Pattern) :
    (((¬ phi) ~> (¬ psi)) ~> (psi ~> phi)) tautology

where "pattern 'tautology'" := (Tautology_proof_rules pattern).

Reserved Notation "pattern 'proved'" (at level 2).
Inductive AML_proof_system : Sigma_pattern -> Prop :=
(* FOL reasoning *)
  (* Propositional tautology *)
  | Prop_tau (phi : Sigma_pattern) :
      phi tautology -> phi proved

  (* Modus ponens *)
  | Mod_pon {phi1 phi2 : Sigma_pattern} :
    phi1 proved -> (phi1 ~> phi2) proved -> phi2 proved

  (* Existential quantifier *)
  | Ex_quan {phi : Sigma_pattern} (x y : EVar) :
    ((e_subst_var phi (sp_var y) x) ~> (sp_exists x phi)) proved

  (* Existential generalization *)
  | Ex_gen (phi1 phi2 : Sigma_pattern) (x : EVar) :
    (phi1 ~> phi2) proved ->
    negb (set_mem evar_eq_dec x (free_evars phi2)) = true ->
    ((ex x, phi1) ~> phi2) proved

(* Frame reasoning *)
  (* Propagation bottom *)
  | Prop_bot (C : Application_context) :
    ((subst_ctx C sp_bottom) ~> sp_bottom) proved

  (* Propagation disjunction *)
  | Prop_disj (C : Application_context) (phi1 phi2 : Sigma_pattern) :
    ((subst_ctx C (phi1 _|_ phi2)) ~>
        ((subst_ctx C phi1) _|_ (subst_ctx C phi2))) proved

  (* Propagation exist *)
  | Prop_ex (C : Application_context) (phi : Sigma_pattern) (x : EVar) :
    negb (set_mem evar_eq_dec x (free_vars_ctx C)) = true ->
    ((subst_ctx C (sp_exists x phi)) ~> (sp_exists x (subst_ctx C phi))) proved

  (* Framing *)
  | Framing (C : Application_context) (phi1 phi2 : Sigma_pattern) :
    (phi1 ~> phi2) proved -> ((subst_ctx C phi1) ~> (subst_ctx C phi2)) proved

(* Fixpoint reasoning *)
  (* Set Variable Substitution *)
  | Svar_subst (phi : Sigma_pattern) (psi X : SVar) :
    phi proved -> (e_subst_set phi (sp_set psi) X) proved

  (* Pre-Fixpoint *)
  | Pre_fixp (phi : Sigma_pattern) (X : SVar) :
    ((e_subst_set phi (sp_mu X phi) X) ~> (sp_mu X phi)) proved

  (* Knaster-Tarski *)
  | Knaster_tarski (phi psi : Sigma_pattern) (X : SVar) :
    ((e_subst_set phi psi X) ~> psi) proved -> ((sp_mu X phi) ~> psi) proved

(* Technical rules *)
  (* Existence *)
  | Existence (x : EVar) : (ex x , ' x) proved

  (* Singleton *)
  | Singleton_ctx (C1 C2 : Application_context) (x : EVar) (phi : Sigma_pattern) :
    (¬ ((subst_ctx C1 ('x _&_ phi)) _&_ (subst_ctx C2 ('x _&_ (¬ phi))))) proved

where "pattern 'proved'" := (AML_proof_system pattern).