Require Import Arith.
Require Import ZArith.
Require Import List.
Require Import extralibrary.
Require Import names.

Require Export String.
Require Export Coq.Lists.ListSet.
Require Export Ensembles_Ext.

Require Export Coq.Program.Wf.

(** ** Matching Logic Syntax *)

Inductive Sigma : Type := sigma_c {id_si : string}.
Definition Power (Sigma : Type) := Ensemble Sigma.

Definition db_index := nat.

Record Signature := {
  symbols : Power Sigma
}.

Parameter signature : Signature.

Inductive Pattern : Type :=
| patt_free_evar (x : evar_name)
| patt_free_svar (x : svar_name)
| patt_bound_evar (n : db_index)
| patt_bound_svar (n : db_index)
| patt_sym (sigma : Sigma) : In _ (symbols signature) sigma -> Pattern
| patt_app (phi1 phi2 : Pattern)
| patt_bott
| patt_imp (phi1 phi2 : Pattern)
| patt_exists (phi : Pattern)
| patt_mu (phi : Pattern)
.

(* TODO: change Bot and Top to unicode symbols *)
Notation "a $ b" := (patt_app a b) (at level 50, left associativity).
Notation "'Bot'" := patt_bott.
Notation "a --> b"  := (patt_imp a b) (at level 90, right associativity,
                                      b at level 200).
Notation "'ex' , phi" := (patt_exists phi) (at level 55).
Notation "'mu' , phi" := (patt_mu phi) (at level 55).

Definition sigma_eq_dec : forall (x y : Sigma), { x = y } + { x <> y }.
Proof. decide equality. exact (string_dec id_si0 id_si1). Defined.

(*
Definition sp_eq_dec : forall (signature : Signature)
                              (x y : Pattern), { x = y } + { x <> y }.
Proof.
decide equality.
- exact (eq_name x0 x1).
- decide equality.
- decide equality.
- exact (sigma_eq_dec sigma sigma0).
Defined.
*)

Inductive positive_occurrence : db_index -> Pattern -> Prop :=
| po_free_evar (x : evar_name) (n : db_index) : positive_occurrence n (patt_free_evar x)
| po_free_svar (x : svar_name) (n : db_index) : positive_occurrence n (patt_free_svar x)
| po_bound_evar (m : db_index) (n : db_index) : positive_occurrence n (patt_bound_evar m)
| po_bound_svar (m : db_index) (n : db_index) : positive_occurrence n (patt_bound_svar m)
| po_const (sigma : Sigma) (n : db_index) {in_signature : In _ (symbols signature) sigma} :
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
with negative_occurrence : db_index -> Pattern -> Prop :=
| no_free_evar (x : evar_name) (n : db_index) : negative_occurrence n (patt_free_evar x)
| no_free_svar (x : svar_name) (n : db_index) : negative_occurrence n (patt_free_svar x)
| no_bound_evar (m : db_index) (n : db_index) :  negative_occurrence n (patt_bound_evar m)
| no_bound_svar (m : db_index) (n : db_index) :  negative_occurrence n (patt_bound_svar m)
| no_const (sigma : Sigma) (n : db_index) (in_signature : In _ (symbols signature) sigma) :
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

Fixpoint well_formed (phi : Pattern) : Prop :=
  match phi with
  | patt_free_evar _ => True
  | patt_free_svar _ => True
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
Fixpoint bvar_subst (phi psi : Pattern) (x : db_index) :=
match phi with
| patt_free_evar x' => patt_free_evar x'
| patt_free_svar x' => patt_free_svar x'
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

(* substitute free element variable x for psi in phi *)
Fixpoint free_evar_subst (phi psi : Pattern) (x : evar_name) :=
match phi with
| patt_free_evar x' => if eq_evar_name x x' then psi else patt_free_evar x'
| patt_free_svar X => patt_free_svar X
| patt_bound_evar x' => patt_bound_evar x'
| patt_bound_svar X => patt_bound_svar X
| patt_sym sigma in_sig => patt_sym sigma in_sig
| patt_app phi1 phi2 => patt_app (free_evar_subst phi1 psi x)
                                 (free_evar_subst phi2 psi x)
| patt_bott => patt_bott
| patt_imp phi1 phi2 => patt_imp (free_evar_subst phi1 psi x) (free_evar_subst phi2 psi x)
| patt_exists phi' => patt_exists (free_evar_subst phi' psi x)
| patt_mu phi' => patt_mu (free_evar_subst phi' psi x)
end.

Fixpoint free_svar_subst (phi psi : Pattern) (X : svar_name) :=
match phi with
| patt_free_evar x => patt_free_evar x
| patt_free_svar X' => if eq_svar_name X X' then psi else patt_free_svar X'
| patt_bound_evar x => patt_bound_evar x
| patt_bound_svar X' => patt_bound_svar X'
| patt_sym sigma in_sig => patt_sym sigma in_sig
| patt_app phi1 phi2 => patt_app (free_svar_subst phi1 psi X)
                                 (free_svar_subst phi2 psi X)
| patt_bott => patt_bott
| patt_imp phi1 phi2 => patt_imp (free_svar_subst phi1 psi X) (free_svar_subst phi2 psi X)
| patt_exists phi' => patt_exists (free_svar_subst phi' psi X)
| patt_mu phi' => patt_mu (free_svar_subst phi' psi X)
end.

(* instantiate exists x. p or mu x. p with psi for p *)
Definition instantiate (phi psi : Pattern) :=
match phi with
| patt_exists phi' => bvar_subst phi' psi 0
| patt_mu phi' => bvar_subst phi' psi 0
| _ => phi
end.

(** The free names of a type are defined as follow.  Notice the
  [exists] and [mu] cases: they do not bind any name. *)

Definition set_singleton {T : Type}
  (eq : forall (x y : T), { x = y } + { x <> y })
  := fun x : T => set_add eq x List.nil.

Fixpoint free_evars (phi : Pattern)
  : (ListSet.set evar_name) :=
match phi with
| patt_free_evar x => set_singleton eq_evar_name x
| patt_free_svar X => List.nil
| patt_bound_evar x => List.nil
| patt_bound_svar X => List.nil
| patt_sym sigma in_sig => List.nil
| patt_app phi1 phi2 => set_union eq_evar_name (free_evars phi1) (free_evars phi2)
| patt_bott => List.nil
| patt_imp phi1 phi2 => set_union eq_evar_name (free_evars phi1) (free_evars phi2)
| patt_exists phi => free_evars phi
| patt_mu phi => free_evars phi
end.

Fixpoint free_svars (phi : Pattern)
  : (ListSet.set svar_name) :=
match phi with
| patt_free_evar x => List.nil
| patt_free_svar X => set_singleton eq_svar_name X
| patt_bound_evar x => List.nil
| patt_bound_svar X => List.nil
| patt_sym sigma in_sig => List.nil
| patt_app phi1 phi2 => set_union eq_svar_name (free_svars phi1) (free_svars phi2)
| patt_bott => List.nil
| patt_imp phi1 phi2 => set_union eq_svar_name (free_svars phi1) (free_svars phi2)
| patt_exists phi => free_svars phi
| patt_mu phi => free_svars phi
end.

(* Section Derived_operators. *)

Definition patt_not (phi : Pattern) := phi --> patt_bott.
Notation "¬ a"     := (patt_not   a  ) (at level 75).

Definition patt_or  (l r : Pattern) := (¬ l) --> r.
Notation "a 'or' b" := (patt_or    a b) (at level 85, right associativity).

Definition patt_and (l r : Pattern) :=
  ¬ ((¬ l) or (¬ r)).
Notation "a 'and' b" := (patt_and   a b) (at level 80, right associativity).

Definition patt_iff (l r : Pattern) :=
  ((l --> r) and (r --> l)).
Notation "a <--> b" := (patt_iff a b) (at level 95, no associativity).

Definition patt_top := (¬ patt_bott).
Notation "'Top'" := patt_top.

Definition patt_forall (phi : Pattern) :=
  ¬ (patt_exists (¬ phi)).
Notation "'all' , phi" := (patt_forall phi) (at level 55).

Definition patt_nu (phi : Pattern) :=
  ¬ (patt_mu (¬ (bvar_subst phi (¬ (patt_bound_svar 0)) 0))).
Notation "'nu' , phi" := (patt_nu phi) (at level 55).

(* End Derived_operators. *)
Definition evar (sname : string) : Pattern :=
  patt_free_evar (find_fresh_evar_name (@evar_c sname) nil). 
Definition svar (sname : string) : Pattern :=
  patt_free_svar (find_fresh_svar_name (@svar_c sname) nil). 
Definition sym (sname : string)
  (in_sig : In _ (symbols signature) (@sigma_c sname)) : Pattern :=
  patt_sym (sigma_c sname) in_sig.

(* Example patterns *)

Axiom sig : Signature.
Axiom sym_in_sig : In _ (symbols signature) (@sigma_c "ctor").
Axiom p_in_sig : In _ (symbols signature) (@sigma_c "p").
Axiom f_in_sig : In _ (symbols signature) (@sigma_c "f").

Definition more := svar ("A") or ¬ (svar ("A") ). (* A \/ ~A *)

(* A -> (B -> ~C) (exists x. D (bot /\ top)) *)
Definition complex :=
  evar ("A") --> (evar("B") --> ¬(svar("C"))) $
       ex , svar ("D") $ Bot and Top.

Definition custom_constructor := sym ("ctor") sym_in_sig $ evar ("a").

(* p x1 x2 *)
Definition predicate := sym ("p") p_in_sig $ evar ("x1") $ evar ("x2").

(* f x (mu y . y) *)
Definition function :=
  sym ("f") f_in_sig $ (evar ("x")) $ (mu , (patt_bound_svar 0)).

(* forall x, x /\ y *)
Definition free_and_bound :=
  all , (patt_bound_evar 0) and evar ("y").

(* End of examples. *)

Definition update_valuation {T1 T2 : Type} (eqb : T1 -> T1 -> bool)
           (t1 : T1) (t2 : T2) (f : T1 -> T2) : T1 -> T2 :=
fun x : T1 => if eqb x t1 then t2 else f x.

(* Model of AML ref. snapshot: Definition 2 *)

Record Model := {
  Domain : Type;
  nonempty_witness : exists (x : Domain), True;
  Domain_eq_dec : forall (a b : Domain), {a = b} + {a <> b};
  app_interp : Domain -> Domain -> Power Domain;
  sym_interp (sigma : Sigma) : In _ (symbols signature) sigma -> Power Domain;
}.

Definition pointwise_ext {m : Model}
           (l r : Power (Domain m)) :
  Power (Domain m) :=
fun e:Domain m => exists le re:Domain m, l le /\ r re /\ (app_interp m) le re e.

Compute @pointwise_ext {| Domain := Pattern |}
        (Singleton _ (evar "a")) (Singleton _ (evar "b")).

(* S . empty = empty *)
Lemma pointwise_app_bot : forall (m : Model),
    forall S : Power (Domain m),
  Same_set (Domain m) (pointwise_ext S (Empty_set (Domain m))) (Empty_set (Domain m)).
Proof.
  intros. unfold pointwise_ext. unfold Same_set. unfold Included. unfold In. split; intros.
  * inversion H. inversion H0. inversion H1. inversion H3. contradiction.
  * contradiction.
Qed.

(* Semantics of AML ref. snapshot: Definition 3 *)

Fixpoint evar_quantify (x : evar_name) (level : db_index)
         (p : Pattern) : Pattern :=
match p with
| patt_free_evar x' => if eq_evar_name x x' then patt_bound_evar level else patt_free_evar x'
| patt_free_svar x' => patt_free_svar x'
| patt_bound_evar x' => patt_bound_evar x'
| patt_bound_svar X => patt_bound_svar X
| patt_sym s pf => patt_sym s pf
| patt_app ls rs => patt_app (evar_quantify x level ls) (evar_quantify x level rs)
| patt_bott => patt_bott
| patt_imp ls rs => patt_imp (evar_quantify x level ls) (evar_quantify x level rs)
| patt_exists p' => patt_exists (evar_quantify x (level + 1) p')
| patt_mu p' => patt_mu (evar_quantify x (level + 1) p')
end.

Definition exists_quantify (x : evar_name)
           (p : Pattern) : Pattern :=
  patt_exists (evar_quantify x 0 p).

Fixpoint size (p : Pattern) : nat :=
match p with
| patt_app ls rs => 1 + (size ls) + (size rs)
| patt_imp ls rs => 1 + (size ls) + (size rs)
| patt_exists p' => 1 + size p'
| patt_mu p' => 1 + size p'
| _ => 0
end.

Fixpoint evar_open (k : db_index) (n : evar_name)
         (p : Pattern) : Pattern :=
match p with
| patt_free_evar x => patt_free_evar x
| patt_free_svar x => patt_free_svar x
| patt_bound_evar x => if beq_nat x k then patt_free_evar n else patt_bound_evar x
| patt_bound_svar X => patt_bound_svar X
| patt_sym s pf => patt_sym s pf
| patt_app ls rs => patt_app (evar_open k n ls) (evar_open k n rs)
| patt_bott => patt_bott
| patt_imp ls rs => patt_imp (evar_open k n ls) (evar_open k n rs)
| patt_exists p' => patt_exists (evar_open (k + 1) n p')
| patt_mu p' => patt_mu (evar_open (k + 1) n p')
end.

Fixpoint svar_open (k : db_index) (n : svar_name)
         (p : Pattern) : Pattern :=
match p with
| patt_free_evar x => patt_free_evar x
| patt_free_svar x => patt_free_svar x
| patt_bound_evar x => patt_bound_evar x
| patt_bound_svar X => if beq_nat X k then patt_free_svar n else patt_bound_svar X
| patt_sym s pf => patt_sym s pf
| patt_app ls rs => patt_app (svar_open k n ls) (svar_open k n rs)
| patt_bott => patt_bott
| patt_imp ls rs => patt_imp (svar_open k n ls) (svar_open k n rs)
| patt_exists p' => patt_exists (svar_open (k + 1) n p')
| patt_mu p' => patt_mu (svar_open (k + 1) n p')
end.

Lemma evar_open_size :
  forall (signature : Signature) (k : db_index) (n : evar_name) (p : Pattern),
    size p = size (evar_open k n p).
Proof.
  intros. generalize dependent k.
  induction p; intros; simpl; try reflexivity.
  destruct (n0 =? k); reflexivity.
  rewrite (IHp1 k); rewrite (IHp2 k); reflexivity.
  rewrite (IHp1 k); rewrite (IHp2 k); reflexivity.
  rewrite (IHp (k + 1)); reflexivity.
  rewrite (IHp (k + 1)); reflexivity.
Qed.

Lemma svar_open_size :
  forall (signature : Signature) (k : db_index) (n : svar_name) (p : Pattern),
    size p = size (svar_open k n p).
Proof.
  intros. generalize dependent k.
  induction p; intros; simpl; try reflexivity.
  destruct (n0 =? k); reflexivity.
  rewrite (IHp1 k); rewrite (IHp2 k); reflexivity.
  rewrite (IHp1 k); rewrite (IHp2 k); reflexivity.
  rewrite (IHp (k + 1)); reflexivity.
  rewrite (IHp (k + 1)); reflexivity.
Qed.

(*
Definition pattern_lt (p1 p2 : Pattern) :=
  size p1 < size p2.
Lemma pattern_lt_well_founded : well_founded (@pattern_lt).
Proof.
  apply well_founded_lt_compat with size; auto.
Qed.

Instance wf_pattern_lt : WellFounded (@pattern_lt).
apply pattern_lt_well_founded.
Defined.

Check sym_interp.

Equations ext_valuation_aux {m : Model}
          (evar_val : evar_name -> Domain m) (svar_val : svar_name -> Power (Domain m))
          (evar_names : list evar_name) (svar_names : list svar_name)
          (p : Pattern) : Power (Domain m)
  by wf p pattern_lt :=
  ext_valuation_aux evar_val svar_val evar_names svar_names (patt_free_evar x) := Singleton _ (evar_val x);
  ext_valuation_aux evar_val svar_val evar_names svar_names (patt_free_svar X) := svar_val X;
  ext_valuation_aux evar_val svar_val evar_names svar_names (patt_bound_evar x) := Empty_set _;
  ext_valuation_aux evar_val svar_val evar_names svar_names (patt_bound_svar x) := Empty_set _;
  ext_valuation_aux evar_val svar_val evar_names svar_names (patt_sym s pf) := (sym_interp m) s pf;
  ext_valuation_aux evar_val svar_val evar_names svar_names (patt_app ls rs) :=
    pointwise_ext (ext_valuation_aux evar_val svar_val evar_names svar_names ls)
                  (ext_valuation_aux evar_val svar_val evar_names svar_names rs);
  ext_valuation_aux evar_val svar_val evar_names svar_names patt_bott := Empty_set _;
  ext_valuation_aux evar_val svar_val evar_names svar_names (patt_imp ls rs) :=
    Union _ (Complement _ (ext_valuation_aux evar_val svar_val evar_names svar_names ls))
            (ext_valuation_aux evar_val svar_val evar_names svar_names rs);
  ext_valuation_aux evar_val svar_val evar_names svar_names (patt_exists p') :=
    let fname := find_fresh_evar_name (@evar_c "efresh") evar_names in
    FA_Union
      (fun e => ext_valuation_aux (update_valuation evar_name_eqb fname e evar_val) svar_val
                                  evar_names svar_names
                                  (evar_open 0 fname p'));
  ext_valuation_aux evar_val svar_val evar_names svar_names (patt_mu p') :=
    let fname := find_fresh_svar_name (@svar_c "sfresh") svar_names in
    Ensembles_Ext.mu
      (fun S => ext_valuation_aux evar_val (update_valuation svar_name_eqb fname S svar_val)
                                  evar_names svar_names
                                  (svar_open 0 fname p')).
Next Obligation. unfold pattern_lt. simpl. omega. Defined.
Next Obligation. unfold pattern_lt. simpl. omega. Defined.
Next Obligation. unfold pattern_lt. simpl. omega. Defined.
Next Obligation. unfold pattern_lt. simpl. omega. Defined.
Next Obligation. unfold pattern_lt. simpl. rewrite <- evar_open_size. omega. apply signature. Defined.
Next Obligation. unfold pattern_lt. simpl. rewrite <- svar_open_size. omega. apply signature. Defined.
*)

Program Fixpoint ext_valuation_aux {m : Model}
        (evar_val : evar_name -> Domain m) (svar_val : svar_name -> Power (Domain m))
        (evar_names : list evar_name) (svar_names : list svar_name)
        (p : Pattern) {measure (size p)} :=
match p with
| patt_free_evar x => Singleton _ (evar_val x)
| patt_free_svar X => svar_val X
| patt_bound_evar x => Empty_set _
| patt_bound_svar X => Empty_set _
| patt_sym s pf => (sym_interp m) s pf
| patt_app ls rs => pointwise_ext (ext_valuation_aux evar_val svar_val evar_names svar_names ls)
                                  (ext_valuation_aux evar_val svar_val evar_names svar_names rs)
| patt_bott => Empty_set _
| patt_imp ls rs => Union _ (Complement _ (ext_valuation_aux evar_val svar_val
                                                             evar_names svar_names ls))
                          (ext_valuation_aux evar_val svar_val evar_names svar_names rs)
| patt_exists p' =>
  let fname := find_fresh_evar_name (@evar_c "efresh") evar_names in
  FA_Union
    (fun e => ext_valuation_aux (update_valuation evar_name_eqb fname e evar_val) svar_val
                                evar_names svar_names
                                (evar_open 0 fname p'))
| patt_mu p' =>
  let fname := find_fresh_svar_name (@svar_c "sfresh") svar_names in
  Ensembles_Ext.mu
    (fun S => ext_valuation_aux evar_val (update_valuation svar_name_eqb fname S svar_val)
                                evar_names svar_names
                                (svar_open 0 fname p'))
end.
Next Obligation. simpl; omega. Defined.
Next Obligation. simpl; omega. Defined.
Next Obligation. simpl; omega. Defined.
Next Obligation. simpl; omega. Defined.
Next Obligation. simpl; rewrite <- evar_open_size. omega. apply signature. Defined.
Next Obligation. simpl; rewrite <- svar_open_size. omega. apply signature. Defined.

Definition ext_valuation {m : Model}
           (evar_val : evar_name -> Domain m) (svar_val : svar_name -> Power (Domain m))
           (p : Pattern) : Power (Domain m) :=
  ext_valuation_aux evar_val svar_val (free_evars p) (free_svars p) p.

Lemma ext_valuation_aux_free_evar_simpl {m : Model}
      (evar_val : evar_name -> Domain m) (svar_val : svar_name -> Power (Domain m))
      (evar_names : list evar_name) (svar_names : list svar_name) (x : evar_name) :
  ext_valuation_aux evar_val svar_val evar_names svar_names (patt_free_evar x) =
  Singleton _ (evar_val x).
Admitted.

Lemma ext_valuation_aux_free_svar_simpl {m : Model}
      (evar_val : evar_name -> Domain m) (svar_val : svar_name -> Power (Domain m))
      (evar_names : list evar_name) (svar_names : list svar_name) (X : svar_name) :
  ext_valuation_aux evar_val svar_val evar_names svar_names (patt_free_svar X) =
  svar_val X.
Admitted.

Lemma ext_valuation_aux_bound_evar_simpl {m : Model}
      (evar_val : evar_name -> Domain m) (svar_val : svar_name -> Power (Domain m))
      (evar_names : list evar_name) (svar_names : list svar_name) (x : db_index) :
  ext_valuation_aux evar_val svar_val evar_names svar_names (patt_bound_evar x) = Empty_set _ .
Admitted.

Lemma ext_valuation_aux_bound_svar_simpl {m : Model}
      (evar_val : evar_name -> Domain m) (svar_val : svar_name -> Power (Domain m))
      (evar_names : list evar_name) (svar_names : list svar_name) (X : db_index) :
  ext_valuation_aux evar_val svar_val evar_names svar_names (patt_bound_svar X) = Empty_set _ .
Admitted.

Lemma ext_valuation_aux_app_simpl {m : Model}
      (evar_val : evar_name -> Domain m) (svar_val : svar_name -> Power (Domain m))
      (evar_names : list evar_name) (svar_names : list svar_name)
      (ls rs : Pattern) :
  ext_valuation_aux evar_val svar_val evar_names svar_names (patt_app ls rs) =
  pointwise_ext (ext_valuation_aux evar_val svar_val evar_names svar_names ls)
                (ext_valuation_aux evar_val svar_val evar_names svar_names rs).
Admitted.

Lemma ext_valuation_aux_bott_simpl {m : Model}
      (evar_val : evar_name -> Domain m) (svar_val : svar_name -> Power (Domain m))
      (evar_names : list evar_name) (svar_names : list svar_name) :
  ext_valuation_aux evar_val svar_val evar_names svar_names patt_bott = Empty_set _ .
Admitted.

Lemma ext_valuation_aux_imp_simpl {m : Model}
      (evar_val : evar_name -> Domain m) (svar_val : svar_name -> Power (Domain m))
      (evar_names : list evar_name) (svar_names : list svar_name)
      (ls rs : Pattern) :
  ext_valuation_aux evar_val svar_val evar_names svar_names (patt_imp ls rs) =
  Union _ (Complement _ (ext_valuation_aux evar_val svar_val evar_names svar_names ls))
        (ext_valuation_aux evar_val svar_val evar_names svar_names rs).
Admitted.

Lemma ext_valuation_aux_exists_simpl {m : Model}
      (evar_val : evar_name -> Domain m) (svar_val : svar_name -> Power (Domain m))
      (evar_names : list evar_name) (svar_names : list svar_name)
      (p : Pattern) :
  ext_valuation_aux evar_val svar_val evar_names svar_names (patt_exists p) =
  let fname := find_fresh_evar_name (@evar_c "efresh") evar_names in
  FA_Union
    (fun e => ext_valuation_aux (update_valuation evar_name_eqb fname e evar_val) svar_val
                                evar_names svar_names
                                (evar_open 0 fname p)).
Admitted.

Lemma ext_valuation_aux_mu_simpl {m : Model}
      (evar_val : evar_name -> Domain m) (svar_val : svar_name -> Power (Domain m))
      (evar_names : list evar_name) (svar_names : list svar_name)
      (p : Pattern) :
  ext_valuation_aux evar_val svar_val evar_names svar_names (patt_mu p) =
  let fname := find_fresh_svar_name (@svar_c "sfresh") svar_names in
  Ensembles_Ext.mu
    (fun S => ext_valuation_aux evar_val (update_valuation svar_name_eqb fname S svar_val)
                                evar_names svar_names
                                (svar_open 0 fname p)).
Admitted.

(*
Lemma is_monotonic :
  forall (sm : Sigma_model)
         (evar_val : name -> M sm)
         (svar_val : db_index -> Power (M sm)) (phi : Sigma_pattern)
         (x : db_index),
    positive x phi ->
    well_formed phi ->
    forall (l r : Power (M sm)),
      Included (M sm) l r ->
      Included (M sm)
        (ext_valuation evar_val (change_val beq_nat 0 l db_val) phi)
        (ext_valuation freevar_val (change_val beq_nat 0 r db_val) phi).
Proof.
Admitted.
*)

(*
Ltac proof_ext_val :=
simpl;intros;
repeat
  (* Normalize *)
   rewrite (Same_set_to_eq (Union_Empty_l _))
|| rewrite (Same_set_to_eq (Compl_Compl_Powers _ _))
|| rewrite
   (Same_set_to_eq (Compl_Union_Compl_Intes_Powers_alt _ _ _))
|| rewrite (Same_set_to_eq (FA_rel _ _ _))
  (* Apply *)
|| (eapply (proj1 Same_set_Compl) ; intros)
|| (eapply FA_Inters_same ; intros)
  (* Final step *)
|| exact Complement_Empty_is_Full
|| exact (Symdiff_val _ _)
|| exact (Same_set_refl _).
*)

Section Semantics_of_derived_operators.

  (* TODO: Need to be able to simplify Program Fixpoint definitions *)
  
End Semantics_of_derived_operators.

(**
   Proof of correct semantics for the derived operators
   ref. snapshot: Proposition 4
*)

(* Theory,axiom ref. snapshot: Definition 5 *)

Record Theory := {
  patterns : Power (Pattern)
}.

Definition satisfies_model (m : Model) (phi : Pattern) : Prop :=
forall (evar_val : evar_name -> Domain m) (svar_val : svar_name -> Power (Domain m)),
  Same_set _ (ext_valuation (m := m) evar_val svar_val phi) (Full_set _).

Notation "M |=M phi" := (satisfies_model M phi) (left associativity, at level 50).

Definition satisfies_theory (m : Model) (theory : Theory)
: Prop := forall axiom : Pattern, In _ (patterns theory) axiom -> (m |=M axiom).

Notation "M |=T Gamma" := (satisfies_theory M Gamma)
    (left associativity, at level 50).

Definition satisfies (theory : Theory) (p: Pattern)
: Prop := forall m : Model, (m |=T theory) -> (m |=M p).

Notation "G |= phi" := (satisfies G phi) (left associativity, at level 50).

(* End of definition 5. *)

Inductive Application_context : Set :=
| box
| ctx_app_l (cc : Application_context) (p : Pattern)
| ctx_app_r (p : Pattern) (cc : Application_context)
.

Fixpoint subst_ctx (C : Application_context) (p : Pattern)
  : Pattern :=
match C with
| box => p
| ctx_app_l C' p' => patt_app (subst_ctx C' p) p'
| ctx_app_r p' C' => patt_app p' (subst_ctx C' p)
end.

Fixpoint free_evars_ctx (C : Application_context)
  : (ListSet.set evar_name) :=
match C with
| box => List.nil
| ctx_app_l cc p => set_union eq_evar_name (free_evars_ctx cc) (free_evars p)
| ctx_app_r p cc => set_union eq_evar_name (free_evars p) (free_evars_ctx cc)
end.

(* Proof system for AML ref. snapshot: Section 3 *)
(* TODO: all propogation rules, framing, use left and right rules (no contexts) like in bott *)
(* Reserved Notation "pattern 'proved'" (at level 2). *)
Reserved Notation "theory |- pattern" (at level 1).
Inductive ML_proof_system (theory : Theory) :
  Pattern -> Prop :=

(* Hypothesis *)
  | hypothesis (axiom : Pattern) :
    (In _ (patterns theory) axiom) -> theory |- axiom
  
(* FOL reasoning *)
  (* Propositional tautology *)
  | P1 (phi psi : Pattern) :
      theory |- (phi --> (psi --> phi))
  | P2 (phi psi xi : Pattern) :
      theory |- ((phi --> (psi --> xi)) --> ((phi --> psi) --> (phi --> xi)))
  | P3 (phi : Pattern) :
      theory |- (((phi --> Bot) --> Bot) --> phi)

  (* Modus ponens *)
  | Modus_ponens {phi1 phi2 : Pattern} :
      theory |- phi1 ->
      theory |- (phi1 --> phi2) ->
      theory |- phi2

  (* Existential quantifier *)
  | Ex_quan {phi : Pattern} (y : evar_name) :
      theory |- (instantiate (patt_exists phi) (patt_free_evar y) --> (patt_exists phi))

  (* Existential generalization *)
  | Ex_gen (phi1 phi2 : Pattern) (x : evar_name) :
      theory |- (phi1 --> phi2) ->
      set_mem eq_evar_name x (free_evars phi2) = false ->
      theory |- (exists_quantify x phi1 --> phi2)

(* Frame reasoning *)
  (* Propagation bottom *)
  | Prop_bott_left (phi : Pattern) :
      theory |- (patt_bott $ phi --> patt_bott)

  | Prop_bott_right (phi : Pattern) :
      theory |- (phi $ patt_bott --> patt_bott)

  (* Propagation disjunction *)
  | Prop_disj (C : Application_context) (phi1 phi2 : Pattern) :
      theory |- ((subst_ctx C (phi1 or phi2)) -->
                ((subst_ctx C phi1) or (subst_ctx C phi2)))

  (* Propagation exist *)
  | Prop_ex (C : Application_context) (phi : Pattern) :
      theory |- ((subst_ctx C (patt_exists phi)) --> (patt_exists (subst_ctx C phi)))

  (* Framing *)
  | Framing (C : Application_context) (phi1 phi2 : Pattern) :
      theory |- (phi1 --> phi2) ->
      theory |- ((subst_ctx C phi1) --> (subst_ctx C phi2))

(* Fixpoint reasoning *)
  (* Set Variable Substitution *)
  | Svar_subst (phi psi : Pattern) (X : svar_name) :
      theory |- phi -> theory |- (free_svar_subst phi psi X)

  (* Pre-Fixpoint *)
  (* TODO: is this correct? *)
  | Pre_fixp (phi : Pattern) :
      theory |- (instantiate (patt_mu phi) (patt_mu phi) --> (patt_mu phi))

  (* Knaster-Tarski *)
  | Knaster_tarski (phi psi : Pattern) :
      theory |- ((instantiate (patt_mu phi) psi) --> psi) ->
      theory |- ((patt_mu phi) --> psi)

(* Technical rules *)
  (* Existence *)
  | Existence : theory |- (ex , patt_bound_evar 0)

  (* Singleton *)
  | Singleton_ctx (C1 C2 : Application_context) (phi : Pattern) (x : evar_name) : 
      theory |- (¬ ((subst_ctx C1 (patt_free_evar x and phi)) and
                    (subst_ctx C2 (patt_free_evar x and (¬ phi)))))

where "theory |- pattern" := (ML_proof_system theory pattern).

(* Soundness theorem *)
Theorem Soundness :
  forall phi : Pattern, forall theory : Theory,
  (theory |- phi) -> (theory |= phi).
Proof.
  intros. unfold "|=". unfold "|=T", "|=M".
  intros.
  induction H.
  * apply H0. assumption.
  * unfold ext_valuation. repeat rewrite ext_valuation_aux_imp_simpl.
    remember (ext_valuation_aux evar_val svar_val (free_evars (phi --> psi --> phi))
                                (free_svars (phi --> psi --> phi)) phi) as Xphi.
    remember (ext_valuation_aux evar_val svar_val (free_evars (phi --> psi --> phi))
                                 (free_svars (phi --> psi --> phi)) psi) as Xpsi.
    constructor. constructor.
    assert (Union (Domain m) (Complement (Domain m) Xphi) Xphi = Full_set (Domain m)).
    apply Same_set_to_eq. apply Union_Compl_Fullset. rewrite <- H; clear H.
    unfold Included; intros; apply Union_is_or.
    inversion H. left. assumption. right. apply Union_intror. assumption.
  * admit.
  * unfold ext_valuation. repeat rewrite ext_valuation_aux_imp_simpl.
    rewrite ext_valuation_aux_bott_simpl.
    epose proof Union_Empty_l; eapply Same_set_to_eq in H; rewrite H; clear H.
    epose proof Union_Empty_l; eapply Same_set_to_eq in H; rewrite H; clear H.
    pose proof Compl_Compl_Ensembles; eapply Same_set_to_eq in H; rewrite H; clear H.
    apply Union_Compl_Fullset.
  * 
Admitted.