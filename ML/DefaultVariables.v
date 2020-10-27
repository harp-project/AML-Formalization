Require Import Arith.
Require Import ZArith.
Require Import List.
Require Import String.

Require Import Signature.
Require Import extralibrary.

Inductive evar_name_kind : Type := evar_c {id_ev : string}.
Inductive svar_name_kind : Type := svar_c {id_sv : string}.

Definition evar_name : Set := (evar_name_kind * Z)%type.
Definition svar_name : Set := (svar_name_kind * Z)%type.

Definition evar_kind (n: evar_name) : evar_name_kind := fst n.
Definition svar_kind (n: svar_name) : svar_name_kind := fst n.

(** Equality between names is decidable. *)

Lemma eq_evar_name: forall (n1 n2: evar_name), {n1 = n2} + {n1 <> n2}.
Proof.
  assert (forall k1 k2: evar_name_kind, {k1 = k2} + {k1 <> k2}).
  decide equality. exact (string_dec id_ev0 id_ev1).
  assert (forall p1 p2: positive, {p1 = p2} + {p1 <> p2}).
  decide equality. 
  decide equality.
  decide equality.
Defined.

Lemma eq_svar_name: forall (n1 n2: svar_name), {n1 = n2} + {n1 <> n2}.
Proof.
  assert (forall k1 k2: svar_name_kind, {k1 = k2} + {k1 <> k2}).
  decide equality. exact (string_dec id_sv0 id_sv1).
  assert (forall p1 p2: positive, {p1 = p2} + {p1 <> p2}).
  decide equality. 
  decide equality.
  decide equality.
Defined.

(** Moreover, we have the following obvious simplification rules on
  tests over name equality. *)

Lemma eq_evar_name_true:
  forall (A: Set) (n: evar_name) (a b: A), (if eq_evar_name n n then a else b) = a.
Proof.
  intros. case (eq_evar_name n n); congruence.
Qed.

Lemma eq_evar_name_false:
  forall (A: Set) (n m: evar_name) (a b: A), n <> m -> (if eq_evar_name n m then a else b) = b.
Proof.
  intros. case (eq_evar_name n m); congruence.
Qed.

Definition evar_name_eqb (x y : evar_name) : bool :=
  match (evar_kind x) with
  | @evar_c s1 => match (evar_kind y) with
                  | @evar_c s2 => if String.eqb s1 s2 then Z.eqb (snd x) (snd y) else false
                  end
  end.

Lemma eq_svar_name_true:
  forall (A: Set) (n: svar_name) (a b: A), (if eq_svar_name n n then a else b) = a.
Proof.
  intros. case (eq_svar_name n n); congruence.
Qed.

Lemma eq_svar_name_false:
  forall (A: Set) (n m: svar_name) (a b: A), n <> m -> (if eq_svar_name n m then a else b) = b.
Proof.
  intros. case (eq_svar_name n m); congruence.
Qed.

Definition svar_name_eqb (x y : svar_name) : bool :=
  match (svar_kind x) with
  | @svar_c s1 => match (svar_kind y) with
                  | @svar_c s2 => if String.eqb s1 s2 then Z.eqb (snd x) (snd y) else false
                  end
  end.

(** The following lemma shows that there always exists a name
  of the given kind that is fresh w.r.t. the given list of names, that is,
  distinct from all the names in this list. *)

Definition find_fresh_evar_name (k: evar_name_kind) (l: list evar_name) : evar_name :=
  (k, 1 + fold_right (fun (n:evar_name) x => Z.max (snd n) x) 0 l)%Z.

Lemma find_fresh_evar_name_is_fresh:
  forall k l, let n := find_fresh_evar_name k l in ~List.In n l /\ evar_kind n = k.
Proof.
  intros.
  set (ident := fun (n: evar_name) => snd n). 
  set (maxid := 
   fold_right (fun (n:evar_name) x => Z.max (ident n) x) 0%Z).
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

Definition find_fresh_evar_name' (l : list evar_name) : evar_name :=
  find_fresh_evar_name (evar_c "auto") l.

Lemma find_fresh_evar_name'_is_fresh:
  forall l, ~List.In (find_fresh_evar_name' l) l.
Proof.
  intros.
  remember (find_fresh_evar_name_is_fresh (evar_c "auto") l) as H.
  unfold find_fresh_evar_name'.
  clear HeqH.
  destruct H.
  assumption.
Qed.

Lemma fresh_evar_name:
  forall (k: evar_name_kind) (l: list evar_name), exists n, ~List.In n l /\ evar_kind n = k.
Proof.
  intros. exists (find_fresh_evar_name k l). apply find_fresh_evar_name_is_fresh.
Qed.

Definition find_fresh_svar_name (k: svar_name_kind) (l: list svar_name) : svar_name :=
  (k, 1 + fold_right (fun (n:svar_name) x => Z.max (snd n) x) 0 l)%Z.

Lemma find_fresh_svar_name_is_fresh:
  forall k l, let n := find_fresh_svar_name k l in ~List.In n l /\ svar_kind n = k.
Proof.
  intros.
  set (ident := fun (n: svar_name) => snd n). 
  set (maxid := 
   fold_right (fun (n:svar_name) x => Z.max (ident n) x) 0%Z).
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


Definition find_fresh_svar_name' (l : list svar_name) : svar_name :=
  find_fresh_svar_name (svar_c "Auto") l.

Lemma find_fresh_svar_name'_is_fresh:
  forall l, ~List.In (find_fresh_svar_name' l) l.
Proof.
  intros.
  remember (find_fresh_svar_name_is_fresh (svar_c "Auto") l) as H.
  unfold find_fresh_svar_name'.
  clear HeqH.
  destruct H.
  assumption.
Qed.

Lemma fresh_svar_name:
  forall (k: svar_name_kind) (l: list svar_name), exists n, ~List.In n l /\ svar_kind n = k.
Proof.
  intros. exists (find_fresh_svar_name k l). apply find_fresh_svar_name_is_fresh.
Qed.

(** As argued by Pitts and others, swaps (permutations of two
  names) are an interesting special case of renamings.
  We will use swaps later to prove that our definitions
  are equivariant, that is, insensitive to the choices of fresh identifiers. *)

Definition swap_evar (u v x: evar_name) : evar_name :=
  if eq_evar_name x u then v else if eq_evar_name x v then u else x.

(** The following lemmas are standard properties of swaps:
  self-inverse, injective, kind-preserving. *)

Lemma swap_evar_left: forall x y, swap_evar x y x = y.
Proof. intros. unfold swap_evar. apply eq_evar_name_true. Qed.

Lemma swap_evar_right: forall x y, swap_evar x y y = x.
Proof.
  intros. unfold swap_evar. case (eq_evar_name y x); intro. auto.
  apply eq_evar_name_true. 
Qed.

Lemma swap_evar_other: forall x y z, z <> x -> z <> y -> swap_evar x y z = z.
Proof. intros. unfold swap_evar. repeat rewrite eq_evar_name_false; auto. Qed.

Lemma swap_evar_inv: forall u v x, swap_evar u v (swap_evar u v x) = x.
Proof.
  intros; unfold swap_evar.
  case (eq_evar_name x u); intro. 
    case (eq_evar_name v u); intro. congruence. rewrite eq_evar_name_true. congruence.
  case (eq_evar_name x v); intro.
    rewrite eq_evar_name_true. congruence.
  repeat rewrite eq_evar_name_false; auto.
Qed.

Lemma swap_evar_inj: forall u v x y, swap_evar u v x = swap_evar u v y -> x = y.
Proof.
  intros. rewrite <- (swap_evar_inv u v x). rewrite <- (swap_evar_inv u v y).
  congruence.
Qed.

Lemma swap_evar_kind: forall u v x, evar_kind u = evar_kind v ->
                                    evar_kind (swap_evar u v x) = evar_kind x.
Proof.
  intros. unfold swap_evar. case (eq_evar_name x u); intro.
  congruence. case (eq_evar_name x v); intro.
  congruence. auto.
Qed.

Definition swap_svar (u v x: svar_name) : svar_name :=
  if eq_svar_name x u then v else if eq_svar_name x v then u else x.

(** The following lemmas are standard properties of swaps:
  self-inverse, injective, string-preserving. *)

Lemma swap_svar_left: forall x y, swap_svar x y x = y.
Proof. intros. unfold swap_svar. apply eq_svar_name_true. Qed.

Lemma swap_svar_right: forall x y, swap_svar x y y = x.
Proof.
  intros. unfold swap_svar. case (eq_svar_name y x); intro. auto.
  apply eq_svar_name_true. 
Qed.

Lemma swap_svar_other: forall x y z, z <> x -> z <> y -> swap_svar x y z = z.
Proof. intros. unfold swap_svar. repeat rewrite eq_svar_name_false; auto. Qed.

Lemma swap_svar_inv: forall u v x, swap_svar u v (swap_svar u v x) = x.
Proof.
  intros; unfold swap_svar.
  case (eq_svar_name x u); intro. 
    case (eq_svar_name v u); intro. congruence. rewrite eq_svar_name_true. congruence.
  case (eq_svar_name x v); intro.
    rewrite eq_svar_name_true. congruence.
  repeat rewrite eq_svar_name_false; auto.
Qed.

Lemma swap_svar_inj: forall u v x y, swap_svar u v x = swap_svar u v y -> x = y.
Proof.
  intros. rewrite <- (swap_svar_inv u v x). rewrite <- (swap_svar_inv u v y).
  congruence.
Qed.

Lemma swap_svar_kind: forall u v x, svar_kind u = svar_kind v ->
                                    svar_kind (swap_svar u v x) = svar_kind x.
Proof.
  intros. unfold swap_svar. case (eq_svar_name x u); intro.
  congruence. case (eq_svar_name x v); intro.
  congruence. auto.
Qed.

Definition DefaultMLVariables : MLVariables :=
  {| evar := evar_name;
     svar := svar_name;
     evar_eq := eq_evar_name;
     svar_eq := eq_svar_name;
     evar_fresh := find_fresh_evar_name';
     svar_fresh := find_fresh_svar_name';
     evar_fresh_is_fresh := find_fresh_evar_name'_is_fresh;
     svar_fresh_is_fresh := find_fresh_svar_name'_is_fresh;
  |}.
