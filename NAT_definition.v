(* ************************************************************************** *)
(*                           ~= Natural numbers =~                            *)
(* ************************************************************************** *)
Require Import AML_definition.
Import AML_notations.
Require Import MSFOL_definition.
Import MSFOL_notations.
Require Import FOL_helpers.
Require Import String.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Lists.ListSet.

Section Natural_numbers.

Definition Nat_is_Sort := (sort_constant Nat) -< MSAFOL_Sort.

Definition zero : Sigma := sigma_c("zero").
Definition succ : Sigma := sigma_c("succ").
Definition plus : Sigma := sigma_c("plus'").
Definition mult : Sigma := sigma_c("mult").

Definition zero_fun := (zero : --> Nat).
Definition succ_fun := (succ : Nat --> Nat).
Definition plus_fun := (plus : Nat X Nat --> Nat).
Definition mult_fun := (mult : Nat X Nat --> Nat).

(* Helper functions definition and notations for natural numbers *)
Definition succ' (x : Sigma_pattern) := ^succ $ x.
Definition plus' (x y : Sigma_pattern) := ^plus $ x $ y.
Definition mult' (x y : Sigma_pattern) := ^mult $ x $ y.

Definition one := succ' ^zero.
Definition two := succ' one.
Definition three := succ' two.
Definition five := succ' (succ' three).
Definition six := succ' five.

Notation "00" := (^zero) (at level 0).
Notation "'S' a" := (succ' a) (at level 50).
Notation "a +' b" := (plus' a b) (at level 40).
Notation "a *' b" := (mult' a b) (at level 50).
(* End helper functions *)


(* Example: x + 0 = x *)
Definition plus_right_id :=
let x := (evar_c("x")) in
   (all_S x : Nat, (( 'x +' 00 ) ~=~ 'x)).

(* we have to specify the type of function parameters, because if not, the
 * following statement about natural numbers could also be formalised: *)
Definition x_plus_0_eq_x_no_type := plus' ^plus ^zero ~=~ ^plus.

(* Natural numbers additional axioms: Peano axioms: *)

Definition zero_is_nat := (00 -< [[ Nat ]]).

Definition nat_eq_closed :=
let x := (evar_c("x")) in let y := (evar_c("y")) in
  all x, (all y, (('x -< [[ Nat ]]) ~> ('x ~=~ 'y)) ~> ('y -< [[ Nat ]])).

Definition succ_closed := all_S x:Nat, ((S 'x) -< [[ Nat ]]).

Definition succ_inj :=
let x := (evar_c("x")) in let y := (evar_c("y")) in
  all_S x:Nat, (all_S y:Nat, (('x ~=~ 'y) <~> ((S 'x) ~=~ (S 'x)))).

Definition succ_rec :=
let x := (evar_c("x")) in let y := (evar_c("y")) in
  all_S x:Nat, (all_S y:Nat, (('x +' (S 'y)) ~=~ (S ('x +' 'y)))).


(* Axioms for mult *)
Definition mult_zero_elem :=
let x := (evar_c("x")) in
  all_S x:Nat, ('x *' 00 ~=~ 00).
Definition mult_rec :=
let x := (evar_c("x")) in let y := (evar_c("y")) in
  all_S x:Nat, (all_S y:Nat,
    (('x *' (S 'y)) ~=~ ('x +' ('x *' 'y)))).

Definition mult_left (x y : EVar) :=
let x := (evar_c("x")) in let y := (evar_c("y")) in
  all x, (all y, (('x *' (S 'y)) ~=~ (('x *' 'y) +' 'x))).

Definition mult_right_id :=
let x := (evar_c("x")) in
  all_S x:Nat, (('x *' one) ~=~ ('x +' ('x *' 00))).

(* one is also the lefft identity elem for mult *)
Definition mult_left_id :=
let x := (evar_c("x")) in
  all_S x:Nat, ((one *' 'x) ~=~ (('x *' 00) +' 'x)).

(* distributivity *)
Definition distributivity :=
let x := (evar_c("x")) in let y := (evar_c("y")) in let z := evar_c("z") in
  all_S x:Nat, (all_S y:Nat, (all_S z:Nat,
    (('x *' ('y +' 'z)) ~=~ (('x *' 'y) +' ('x *' 'z))))).


(* Natural numbers with induction *)

(* states that zero and succ build different terms *)
Definition No_Confusion1 :=
let x := (evar_c("x")) in
  all_S x : Nat, ((S 'x) !=~ 00).

(* states that succ is an injective funxtion *)
Definition No_Confusion2 (x y : EVar) :=
let x := (evar_c("x")) in let y := (evar_c("y")) in
  all_S x : Nat, (all_S y : Nat,
    ((((S 'x) ~=~ (S 'y))) ~> ((' x) ~=~ (' y)))).


(* forces [[ Nat ]] to be the smallest set closed under zero and succ, yielding
 * exactly the standard natural numbers |N *)
Definition Inductive_Domain (D : SVar) :=
  [[ Nat ]] ~=~ (mu D, (00 _|_ (S `D))).

(* This is an axiom schema. Before use it needs to be instanctiated, by giving
 * a pattern as parameter to it. *)
Definition Peano_Induction (phi : Sigma_pattern -> Sigma_pattern) :=
let x := (evar_c("x")) in
  ((phi 00) _&_ (all x, ((phi 'x) ~> (phi (S 'x))))) ~>
  (all x, (phi 'x)).


(* Proposition 17. *)
(* It intuitively says that if SX is closed under zero and succ, then it contains
 * all natural numbers. *)
Lemma PeanoNat :
  forall Gamma : (Ensemble Sigma_pattern), forall SX : SVar,
  Gamma |- ((00 -< `SX) _&_ (all_S y : Nat, ('y -< `SX)) ~>
           (all_S x : Nat, ('x -< `SX))).
Admitted.

End Natural_numbers.

(* Examples of natural number patterns and proofs: *)
Section Nat_examples.

Definition plus_1_2 := plus' one two.
Definition plus_1_2_eq_3 := ((plus' one two) ~=~ three).
Definition plus_1_plus_2_3_eq_6 := ((plus' one (plus' two three)) ~=~ six).

Definition plus_x_1_eq_5 :=
let x := (evar_c("x")) in
  (all_S x : Nat, ((plus' 'x one) ~=~ five)).

Definition plus_x_z_eq_y :=
let x := (evar_c("x")) in let y := (evar_c("y")) in let z := evar_c("z") in
  (all_S x : Nat, (all_S y : Nat, (all_S z : Nat,
        ((plus' 'x 'z) ~=~ 'y)))).

Definition plus_x_plus_z_3_eq_y :=
let x := (evar_c("x")) in let y := (evar_c("y")) in let z := evar_c("z") in
  (all_S x : Nat, (all_S y : Nat, (all_S z : Nat,
        ((plus' 'x (plus' 'z three))) ~=~ 'y))).


Fixpoint SumFromZeroTo (n : Sigma_pattern) : Sigma_pattern :=
match n with
| sp_const zero => ^zero
| sp_app ^succ    b => plus' (succ' b) (SumFromZeroTo b)
| _ => const ("non-exhaustive pattern")
end.

(* 1 + ... + n = n * (n+1) / 2. *)
Definition Sum_of_first_n : Sigma_pattern :=
let n := evar_c("n") in
  all_S n : Nat, (mult' two (SumFromZeroTo 'n) ~=~
  mult' 'n (succ' 'n)).


Fixpoint ProdFromOneTo (n : Sigma_pattern) : Sigma_pattern :=
match n with
| sp_const zero => ^zero

| sp_app ^succ    b =>
  match b with
  | sp_const zero => one
  | sp_app ^succ _ => mult' (succ' b) (ProdFromOneTo b)
  | _ => const ("non-exhaustive pattern")
  end
| _ => const ("non-exhaustive pattern")
end.

Fixpoint SumOfSquaresFromZeroTo (n : Sigma_pattern) : Sigma_pattern :=
match n with
| sp_const zero => ^zero
      (* succ b *)
| sp_app ^succ b => plus' (mult' (succ' b) (succ' b)) (SumOfSquaresFromZeroTo b)
| _ => const ("non-exhaustive pattern")
end.

(* 1^2 + ... + n^2 = n(n+1)(2*n + 1) / 6. *)
Definition Sum_of_squares :=
let n := evar_c("n") in
  all_S n : Nat, (
    mult' six (SumOfSquaresFromZeroTo 'n) ~=~
    mult' 'n (mult' (succ' 'n) (plus' (mult' two 'n) one))).


(* <= relation *)
Definition less (l r : Sigma_pattern) :=
let n := evar_c("n") in
  ex_S n : Nat, (plus' l 'n ~=~ r).

Definition less_or_equal (l r : Sigma_pattern) :=
let n := evar_c("n") in
  (l ~=~ r) _|_ (ex_S n : Nat, (plus' l ('n) ~=~ r)).

(* States that if:
- zero <= zero and
- for all n of sort Nat : 0 <= (n+1)
then for all n of sort Nat states 0 <= n *)
Definition every_number_is_positive : Sigma_pattern :=
  Peano_Induction (less_or_equal ^zero).

Definition less2 (a b : Sigma_pattern) := less a (succ' b).

(* States that if:
- zero < zero + 1 and
- for all n of sort Nat : 0 < ((n+1) + 1)
then for all n of sort Nat states 0 < (n+1) *)
Definition every_successor_is_strictly_positive : Sigma_pattern :=
  Peano_Induction (less2 ^zero).

Definition strong_induction (f : Sigma_pattern -> Sigma_pattern) :=
let n := (evar_c("n")) in let k := (evar_c("k")) in
(((f ^zero) _&_ all_S x : Nat, (all_S k : Nat,
    ((less 'k 'n) ~> (f 'k)) ~> (f (succ' 'n)))) ~>
  (all_S n : Nat, (f 'n))).
(* with this can be shown that natural unmbers are ordered, thus every subset
 * has a least element *)


(* Proof examples *)
Lemma ex1 : ('x ~> 'x) proved.
Proof. apply Prop_tau. apply P1. Qed.

Lemma ex2 : (Bot ~> ('x ~> Bot)) proved.
Proof. apply Prop_tau. apply P2. Qed.

Lemma ex3 : (('x ~> ('y ~> 'z)) ~> (('x ~> 'y) ~> ('x ~> 'z))) proved.
Proof. apply Prop_tau. apply P3. Qed.

Lemma ex4 : (((¬ 'x) ~> (¬ 'y)) ~> ('y ~> 'x)) proved.
Proof. apply Prop_tau. apply P4. Qed.

Lemma ex5 : (e_subst_var Bot 'y x ~> (ex x, Bot)) proved.
Proof. apply Ex_quan. Qed.

Lemma ex6 :
  ('x ~> 'y) proved ->
  negb (set_mem evar_eq_dec z (free_vars 'y)) = true ->
  (ex z, 'x ~> 'y) proved.
Proof. apply Ex_gen. Qed.

Lemma zero_eq_zero : empty_theory |- (^zero ~=~ ^zero).
Proof. eapply E_refl. Qed.

End Nat_examples.


Section Nat_proofs.

(* Proof of commutativity of addition over natural numbers *)
Definition comm_theory := Empty_set Sigma_pattern. (* this can be extended *)
Lemma nat_plus_comm :
  forall x y : EVar, comm_theory |-
    (all_S x : Nat, (all_S y : Nat, ((plus' 'x 'y) ~=~ (plus' 'y 'x)))).
Admitted.

(* Proof of 0 + x = x, for all natural number x *)
Definition pli_theory := Empty_set Sigma_pattern. (* this can be extended *)
Lemma plus_left_id :
let x := (evar_c("x")) in
  pli_theory |- (all_S x:Nat, (plus' ^zero 'x ~=~ 'x)).
Admitted.

(* These proofs aren't correct in this form, because they don't have sorted
 * quantification, by are kept to state a structure for the quantified version
 *)
(*
Definition axiom_set (a : EVar) :=
  Add _ (Add _ (Add _ (Add _ (Add _ (Add _ (Add _ (Add _ (Add _ (Add _
    empty_theory
    (succ_inj (plus' 'a two) (succ' (succ' (plus' 'a ^zero)))))
    (succ_inj (plus' 'a (succ' ^zero)) (succ' (plus' 'a ^zero))))
    (succ_inj (succ' (succ' (plus' 'a ^zero))) (succ' (succ' 'a))))
    (succ_inj (succ' (plus' 'a ^zero)) (succ' 'a)))
    (succ_inj (plus' 'a ^zero) 'a))
    (id_elem_right 'a))
    (succ_rec 'a ^zero))
    (succ_rec 'a one))
    (succ_rec 'a two))
    (succ_rec 'a three).

Lemma plus_one (a : EVar) :
let G := (axiom_set a) in
  G |- (plus' 'a one ~=~ succ' 'a).
Proof.
  intros.
  unfold G. unfold axiom_set. unfold id_elem_right. unfold succ_rec.
  unfold succ_inj.

  unfold one. (* by definition *)
  eapply E_trans.
  - eapply hypothesis. in_hyp.
  - eapply E_mod_pon.
    (* using id_intro_right *)
    + eapply (hypothesis (id_elem_right 'a)). in_hyp.
    + eapply (hypothesis (succ_inj (plus' 'a ^zero) 'a)). in_hyp.
Qed.


Lemma plus_two' (a : EVar) :
let G := (axiom_set a) in
  G |- (plus' 'a two ~=~ succ' (succ' (plus' 'a ^zero))).
Proof.
  intros.
  unfold G. unfold axiom_set. unfold id_elem_right. unfold succ_rec. unfold succ_inj.

  eapply (E_trans (plus' 'a two) (succ' (plus' 'a one)) (succ' (succ' (plus' 'a ^zero)))).
  - eapply (hypothesis (succ_rec 'a (succ' ^zero))). in_hyp.
  - eapply E_mod_pon.
    + eapply (hypothesis ((succ_rec 'a ^zero))). in_hyp.
    + unfold id_elem_right. eapply (hypothesis
        (succ_inj (plus' 'a (succ' ^zero)) (succ' (plus' 'a ^zero)))).
      in_hyp.
Qed.


Lemma plus_two (a : EVar) :
let G := (axiom_set a) in
  G |- (plus' 'a two ~=~ succ' (succ' 'a)).
Proof.
  intros.
  unfold G. unfold axiom_set. unfold id_elem_right. unfold succ_rec.
  unfold succ_inj.

  eapply (E_trans (plus' 'a two)
                  (succ' (succ' (plus' 'a ^zero)))
                  (succ' (succ' 'a))).
  - eapply plus_two'.
  - eapply E_mod_pon.
    + eapply E_mod_pon.
      * eapply (hypothesis (id_elem_right 'a)). in_hyp.
      * eapply (hypothesis (succ_inj (plus' 'a ^zero) 'a)). in_hyp.
    + eapply (hypothesis (succ_inj (succ' (plus' 'a ^zero)) (succ' 'a))).
      in_hyp.
Qed.


Lemma plus_three' (a : EVar) :
let G := (axiom_set a) in
  G |- (plus' 'a three ~=~ succ' (succ' (succ' (plus' 'a ^zero)))).
Proof.
  eapply (E_trans (plus' 'a three)
                  (succ' (plus' 'a (succ' (succ' ^zero))))
                  (succ' (succ' (succ' (plus' 'a ^zero))))).
  - eapply (hypothesis (succ_rec 'a two)). in_hyp.
  - eapply E_mod_pon.
    + eapply (plus_two' a).
    + eapply (hypothesis
                (succ_inj (plus' 'a two) (succ' (succ' (plus' 'a ^zero))))).
      in_hyp.
Qed.

Lemma plus_three (a : EVar) :
let G := (axiom_set a) in
  G |- (plus' 'a three ~=~ succ' (succ' (succ' 'a))).
Proof.
  intros.
  unfold G. unfold axiom_set. unfold id_elem_right. unfold succ_rec.
  unfold succ_inj.

  eapply (E_trans
   (plus' 'a three)
   (succ' (succ' (succ' (plus' 'a ^zero))))
   (succ' (succ' (succ' 'a)))).
  - eapply (plus_three' a).
  - eapply E_mod_pon.
    + eapply E_mod_pon.
      * eapply E_mod_pon.
         -- eapply (hypothesis (plus' 'a ^zero ~=~ 'a)). in_hyp.
         -- eapply (hypothesis (succ_inj (plus' 'a ^zero) 'a)). in_hyp.
      * eapply (hypothesis (succ_inj (succ' (plus' 'a ^zero)) (succ' 'a))).
        in_hyp.
    + eapply (hypothesis
                (succ_inj (succ' (succ' (plus' 'a ^zero))) (succ' (succ' 'a)))).
      in_hyp.
Qed.


Lemma plus_comm (n m : Sigma_pattern) (theory : Ensemble Sigma_pattern) :
  theory |- (plus' n m ~=~ plus' m n).
Admitted.


Definition theory :=
  Add _ (Add _ (Add _ (Add _ (Add _ (Add _ (axiom_set x)
    (Peano_Induction x
      (fun var => ((var -'< [[ Nat ]]) ~> ((^plus $ var $ ^zero) ~=~ var)))))
    zero_is_nat)
    (succ_closed 'x))
    (succ_inj 'x 'y))
    (contra 'x))
    (id_elem_right ^zero).

Lemma plus_x_0_eq_x_with_env :
  theory |-  x_plus_0_eq_x.
Proof.
  unfold x_plus_0_eq_x. unfold theory.

  eapply E_mod_pon.
  2: {
  - eapply (hypothesis (Peano_Induction x (fun var =>
    ((var -'< [[ Nat ]]) ~> ((^plus $ var $ ^zero) ~=~ var)))) theory).
    unfold Add. eapply Union_introl. eapply Union_introl. eapply Union_introl.
    eapply Union_introl. eapply Union_introl. unfold Peano_Induction.
    eapply Union_intror. reflexivity.
  }
  - unfold Peano_Induction. eapply conj_intro_t.
    + eapply E_mod_pon.
      * (* ^ plus $ ^ zero $ ^ zero ~=~ ^ zero *) (* from hypothesis *)
        eapply (hypothesis (plus' ^zero ^zero ~=~ ^zero)).
        eapply Union_intror. reflexivity.
      * eapply ext. eapply Prop_tau. eapply (P2 (plus' ^zero ^zero ~=~ ^zero)
                                    (^zero -'< [[Nat]])).
    + unfold sp_forall.

Admitted.
 *)

End Nat_proofs.
