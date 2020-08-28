Require Import Arith.
Require Import ZArith.
Require Import List.
Require Import extralibrary.

Require Export String.
Require Export Coq.Lists.ListSet.
Require Export Ensembles_Ext.

Require Export Coq.Program.Wf.

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
| patt_param (x : name)
| patt_evar (n : db_index)
| patt_svar (n : db_index)
| patt_sym (sigma : Sigma) : In _ (Symbols signature) sigma -> Pattern
| patt_app (phi1 phi2 : Pattern)
| patt_bott
| patt_imp (phi1 phi2 : Pattern)
| patt_exists (phi : Pattern)
| patt_mu (phi : Pattern)
.

Notation "'' x" := (patt_param x) (at level 3).
Notation "' n" := (patt_evar n) (at level 3).
Notation "` n" := (patt_svar n) (at level 3).
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
| po_param (x : name) (n : db_index) : positive_occurrence n (patt_param x)
| po_var (m : db_index) (n : db_index) : positive_occurrence n (patt_evar m)
| po_set (m : db_index) (n : db_index) : positive_occurrence n (patt_svar m)
| po_const (sigma : Sigma) (n : db_index) {in_signature : In _ (Symbols signature) sigma} :
    positive_occurrence n (patt_sym sigma in_signature)
| po_app (phi1 phi2 : Pattern) (n : db_index) :
  positive_occurrence n phi1 -> positive_occurrence n phi2 ->
  positive_occurrence n (patt_app phi1 phi2)
| po_bottom (n : db_index) : positive_occurrence n patt_bott
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
| no_param (x : name) (n : db_index) :  negative_occurrence n (patt_param x)
| no_var (m : db_index) (n : db_index) :  negative_occurrence n (patt_evar m)
| no_set (m : db_index) (n : db_index) :  negative_occurrence n (patt_svar m)
| no_const (sigma : Sigma) (n : db_index) (in_signature : In _ (Symbols signature) sigma) :
    negative_occurrence n (patt_sym sigma in_signature)
| no_app (phi1 phi2 : Pattern) (n : db_index) :
   negative_occurrence n phi1 ->  negative_occurrence n phi2 ->
   negative_occurrence n (patt_app phi1 phi2)
| no_bottom (n : db_index) :  negative_occurrence n patt_bott
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
  | patt_param _ => True
  | patt_evar _ => True
  | patt_svar _ => True
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
| patt_param x' => patt_param x'
| patt_evar n => match compare_nat n x with
              | Nat_less _ _ _ => patt_evar n
              | Nat_equal _ _ _ => psi
              | Nat_greater _ _ _ => patt_evar (pred n)
              end
| patt_svar n => match compare_nat n x with
              | Nat_less _ _ _ => patt_svar n
              | Nat_equal _ _ _ => psi
              | Nat_greater _ _ _ => patt_svar (pred n)
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
| patt_param x' => if eq_name x x' then psi else patt_param x'
| patt_evar x' => patt_evar x'
| patt_svar X => patt_svar X
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
| patt_param x => set_singleton eq_name x
| patt_evar x => List.nil
| patt_svar X => List.nil
| patt_sym sigma in_sig => List.nil
| patt_app phi1 phi2 => set_union eq_name (free_vars phi1) (free_vars phi2)
| patt_bott => List.nil
| patt_imp phi1 phi2 => set_union eq_name (free_vars phi1) (free_vars phi2)
| patt_exists phi => free_vars phi
| patt_mu phi => free_vars phi
end.

Definition name_is_evar (x : name) : bool :=
match (fst x) with
| evar_c => true
| svar_c => false
end.

Definition free_evars {signature : Signature} (phi : @Pattern signature) : (ListSet.set name) :=
  set_fold_right
    (fun x acc => if (name_is_evar x) then set_add eq_name x acc else acc)
    (free_vars phi)
    (List.nil).

Definition free_svars {signature : Signature} (phi : @Pattern signature) : (ListSet.set name) :=
  set_fold_right
    (fun x acc => if (name_is_evar x) then acc else set_add eq_name x acc)
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
  ¬ (patt_mu (¬ (bvar_subst phi (¬ (patt_svar 0)) 0))).
Notation "'nu' , phi" := (patt_nu phi) (at level 55).

(* End Derived_operators. *)
Definition var {signature : Signature} (sname : string) : @Pattern signature :=
  patt_param (find_fresh_name (@evar_c sname) nil). 
Definition set {signature : Signature} (sname : string) : @Pattern signature :=
  patt_param (find_fresh_name (@svar_c sname) nil). 
Definition const {signature : Signature} (sname : string)
  (in_sig : In _ (Symbols signature) (@sigma_c sname)) : @Pattern signature :=
  patt_sym (sigma_c sname) in_sig.

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

(* End of examples. *)

(* TODO: change to update_valuation *)
Definition change_val {T1 T2 : Type} (eqb : T1 -> T1 -> bool)
                      (t1 : T1) (t2 : T2) (f : T1 -> T2) : T1 -> T2 :=
fun x : T1 => if eqb x t1 then t2 else f x.

(* Model of AML ref. snapshot: Definition 2 *)

(* TODO: model should have signature *)

(* make example like A_eq_dec : exists (x : M), True *)
(* change M to Domain *)

Record Sigma_model := {
  Domain : Type;
  example : Domain; (* so Domain can not be empty *)
  Domain_eq_dec : forall (a b : Domain), {a = b} + {a <> b};
  app_interp : Domain -> Domain -> Ensemble Domain;
  sym_interp : Sigma -> Ensemble Domain;
}.

(* TODO: change to pointwise_ext *)
Definition pointwise_app {sm : Sigma_model} (l r : Ensemble (Domain sm)) :
                         Ensemble (Domain sm) :=
fun e:Domain sm => exists le re:Domain sm, l le /\ r re /\ (app_interp sm) le re e.

Compute @pointwise_app {| Domain := Sigma_pattern |}
        (Singleton _ (var "a")) (Singleton _ (var "b")).

(* S . empty = empty *)
Lemma pointwise_app_bot : forall sm : Sigma_model, forall S : Ensemble (M sm),
  Same_set (M sm) (pointwise_app S (Empty_set (M sm))) (Empty_set (M sm)).
Proof.
  intros. unfold pointwise_app. unfold Same_set. unfold Included. unfold In. split; intros.
  * inversion H. inversion H0. inversion H1. inversion H3. contradiction.
  * contradiction.
Qed.

(* Semantics of AML ref. snapshot: Definition 3 *)

Fixpoint size (sp : Sigma_pattern) : nat :=
match sp with
| sp_app ls rs => 1 + (size ls) + (size rs)
| sp_impl ls rs => 1 + (size ls) + (size rs)
| sp_exists sp' => 1 + size sp'
| sp_mu sp' => 1 + size sp'
| _ => 0
end.

Fixpoint var_open (k : db_index) (n : name) (sp : Sigma_pattern) : Sigma_pattern :=
match sp with
| sp_param x => sp_param x
| sp_var x => if beq_nat x k then sp_param n else sp_var x
| sp_set X => if beq_nat X k then sp_param n else sp_set X
| sp_const s => sp_const s
| sp_app ls rs => sp_app (var_open k n ls) (var_open k n rs)
| sp_bottom => sp_bottom
| sp_impl ls rs => sp_impl (var_open k n ls) (var_open k n rs)
| sp_exists sp' => sp_exists (var_open (k + 1) n sp')
| sp_mu sp' => sp_mu (var_open (k + 1) n sp')
end.

Lemma var_open_size :
  forall (k : db_index) (n : name) (sp : Sigma_pattern),
    size sp = size (var_open k n sp).
Proof.
  intros. generalize dependent k.
  induction sp; intros; simpl; try reflexivity.
  destruct (n0 =? k); reflexivity.
  destruct (n0 =? k); reflexivity.
  rewrite (IHsp1 k); rewrite (IHsp2 k); reflexivity.
  rewrite (IHsp1 k); rewrite (IHsp2 k); reflexivity.
  rewrite (IHsp (k + 1)); reflexivity.
  rewrite (IHsp (k + 1)); reflexivity.
Qed.

Program Fixpoint ext_valuation_aux {sm : Sigma_model}
        (evar_val : name -> M sm) (svar_val : name -> Ensemble (M sm))
        (names : list name) (sp : Sigma_pattern) {measure (size sp)} :=
match sp with
| sp_param x => match (fst x) with
                | evar_c => Singleton _ (evar_val x)
                | svar_c => svar_val x
                end
| sp_var x => Empty_set _
| sp_set X => Empty_set _
| sp_const s => (interpretation sm) s
| sp_app ls rs => pointwise_app (ext_valuation_aux evar_val svar_val names ls)
                                (ext_valuation_aux evar_val svar_val names rs)
| sp_bottom => Empty_set _
| sp_impl ls rs => Union _ (Complement _ (ext_valuation_aux evar_val svar_val names ls))
                           (ext_valuation_aux evar_val svar_val names rs)
| sp_exists sp' =>
  let fname := find_fresh_name (@evar_c "efresh") names in
  FA_Union
    (fun e => ext_valuation_aux (change_val name_eqb fname e evar_val) svar_val names
                                (var_open 0 fname sp'))
| sp_mu sp' =>
  let fname := find_fresh_name (@svar_c "sfresh") names in
  Ensembles_Ext.mu
    (fun S => ext_valuation_aux evar_val (change_val name_eqb fname S svar_val) names
                                (var_open 0 fname sp'))
end.
Next Obligation. simpl; omega. Qed.
Next Obligation. simpl; omega. Qed.
Next Obligation. simpl; omega. Qed.
Next Obligation. simpl; omega. Qed.
Next Obligation. simpl; rewrite <- var_open_size; omega. Qed.
Next Obligation. simpl; rewrite <- var_open_size; omega. Qed.

Definition ext_valuation {sm : Sigma_model}
        (evar_val : name -> M sm) (svar_val : name -> Ensemble (M sm))
        (sp : Sigma_pattern) : Ensemble (M sm) :=
  ext_valuation_aux evar_val svar_val (free_vars sp) sp.

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

(**
   Proof of correct semantics for the derived operators
   ref. snapshot: Proposition 4
*)

Lemma not_ext_val_correct
{sm : Sigma_model} {freevar_val : name -> Ensemble (M sm)} {db_val : db_index -> Ensemble _} :
forall sp : Sigma_pattern, Same_set _
  (ext_valuation freevar_val db_val (sp_not sp))
  (Complement _ (ext_valuation freevar_val db_val sp)).
Proof. proof_ext_val. Qed.

Lemma or_ext_val_correct
{sm : Sigma_model} {freevar_val : name -> Ensemble (M sm)} {db_val : db_index -> Ensemble _} :
forall spl spr : Sigma_pattern, Same_set _
  (ext_valuation freevar_val db_val (sp_or spl spr))
  (Union _ (ext_valuation freevar_val db_val spl)
           (ext_valuation freevar_val db_val spr)).
Proof. proof_ext_val. Qed.

Lemma and_ext_val_correct
{sm : Sigma_model} {freevar_val : name -> Ensemble (M sm)} {db_val : db_index -> Ensemble _} :
forall spl spr : Sigma_pattern, Same_set _
  (ext_valuation freevar_val db_val (sp_and spl spr))
  (Intersection _ (ext_valuation freevar_val db_val spl)
                  (ext_valuation freevar_val db_val spr)).
Proof. proof_ext_val. Qed.

Lemma top_ext_val_correct
{sm : Sigma_model} {freevar_val : name -> Ensemble (M sm)} {db_val : db_index -> Ensemble _} :
Same_set _ (ext_valuation freevar_val db_val (sp_top)) (Full_set _).
Proof. proof_ext_val. Qed.

Lemma only_if_ext_val_correct
{sm : Sigma_model} {freevar_val : name -> Ensemble (M sm)} {db_val : db_index -> Ensemble _} :
forall spl spr : Sigma_pattern, Same_set _
  (ext_valuation freevar_val db_val (sp_iff spl spr))
  (Complement _ (Symmetric_difference (ext_valuation freevar_val db_val spl)
                                      (ext_valuation freevar_val db_val spr))).
Proof. proof_ext_val. Qed.

Lemma forall_ext_val_correct
{sm : Sigma_model} {freevar_val : name -> Ensemble (M sm)} {db_val : db_index -> Ensemble _} :
forall sp : Sigma_pattern, Same_set _
  (ext_valuation freevar_val db_val (sp_forall sp))
  (FA_Intersection
    (fun a => ext_valuation freevar_val (change_val beq_nat 0 a db_val) sp)).
Proof. proof_ext_val. Qed.

Lemma nu_ext_val_correct
{sm : Sigma_model} {freevar_val : name -> Ensemble (M sm)} {db_val : db_index -> Ensemble _} :
forall sp : Sigma_pattern, Same_set _
  (ext_valuation freevar_val db_val (sp_nu sp))
  (Ensembles_Ext.nu
    (fun S => ext_valuation freevar_val (change_val beq_nat 0 S db_val) sp)).
Proof.
proof_ext_val.

unfold Ensembles_Ext.mu. unfold Ensembles_Ext.nu. unfold FA_Union_cond.
unfold FA_Inters_cond.

apply Same_set_symmetric. apply Same_set_Compl.
rewrite (Same_set_to_eq (Compl_Compl_Ensembles _ _)).
rewrite (Same_set_to_eq (FA_rel _ _ _)).
eapply FA_Inters_same. intros.
proof_ext_val.
unfold Same_set. unfold Included. unfold Complement. unfold not. unfold In.
eapply conj.
* intros. eapply H0. intros. refine (H _). split.
  - intros.
Admitted.

End Semantics_of_derived_operators.

(* Theory,axiom ref. snapshot: Definition 5 *)

(* TODO: theory will be pair of signature and set of patterns from the signature *)

Definition satisfies_model (sm : Sigma_model) (phi : Sigma_pattern) : Prop :=
forall (freevar_val : name -> Ensemble (M sm)) (db_val : db_index -> Ensemble (M sm)),
  Same_set _ (ext_valuation (sm := sm) freevar_val db_val phi) (Full_set _).

Notation "M |=M phi" := (satisfies_model M phi) (left associativity, at level 50).

Definition satisfies_theory (sm : Sigma_model) (theory : Ensemble Sigma_pattern)
: Prop := forall axiom : Sigma_pattern, In _ theory axiom -> (sm |=M axiom).

Notation "M |=T Gamma" := (satisfies_theory M Gamma)
    (left associativity, at level 50).

Definition satisfies (theory : Ensemble Sigma_pattern) (sp : Sigma_pattern)
: Prop := forall sm : Sigma_model, (sm |=T theory) -> (sm |=M sp).

Notation "G |= phi" := (satisfies G phi) (left associativity, at level 50).

Definition AML_theories : Ensemble Sigma_pattern := Empty_set Sigma_pattern.

(* End of definition 5. *)


(* Definition 6. Definedness and derived operators *)
Definition definedness_symbol : Sigma := {| id_si := "definedness"|}.
Definition defined (x : Sigma_pattern) := (^ definedness_symbol $ x).
Notation "|^ phi ^|" := (defined phi) (at level 100).

(* Definition Definedness_meta (x : EVar) : Sigma_pattern :=
  |^ 'x ^|. *)

Definition Definedness_forall : Sigma_pattern :=
  all , |^ sp_var 0 ^|.

(* Totality *)
Definition total (sp : Sigma_pattern) := (¬ (|^ (¬ sp) ^|)).
Notation "|_ phi _|" := (total phi) (at level 100).

(* Equality *)
Definition equal (a b : Sigma_pattern) := (|_ (a <~> b) _|).
Notation "a ~=~ b" := (equal a b) (at level 100).

(* Non-equality *)
Definition not_equal (a b : Sigma_pattern) := (¬ (equal a b)).
Notation "a !=~ b" := (not_equal a b) (at level 100).

(* Membership *)
Definition member (x sp : Sigma_pattern) := (|^ (x _&_ sp) ^|).
Notation "x -< phi" := (member x phi) (at level 100).

(* Non-membership *)
Definition non_member (x sp : Sigma_pattern) := (¬ (member x sp)).
Notation "x !-< phi" := (non_member x phi) (at level 100).

(* Set inclusion *)
Definition includes (a b : Sigma_pattern) := (|_ (a ~> b) _|).
Notation "a <: b" := (includes a b) (at level 100).

(* Set exclusion *)
Definition not_includes (a b : Sigma_pattern) := (¬ (includes a b)).
Notation "a !<: b" := (not_includes a b) (at level 100).


(* Functional Constant axiom *)
Definition Functional_Constant (constant : Sigma) : Sigma_pattern :=
  (ex , (^constant ~=~ sp_var 0)).

