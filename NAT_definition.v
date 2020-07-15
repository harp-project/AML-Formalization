(* ************************************************************************** *)
(*                           ~= Natural numbers =~                            *)
(* ************************************************************************** *)
Require Export MSFOL_definition.
Import AML_notations.
Import MSFOL_notations.
Require Import Coq.Sets.Ensembles.


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

Definition x := (evar_c("x")).
Definition y := (evar_c("y")).
Definition z := (evar_c("z")).

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
  Gamma |- ((00 -< `SX) _&_ (all_S y : Nat, ('y -< `SX) ~> S 'y -< `SX) ~>
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
  negb (set_mem evar_eq_dec z (free_evars 'y)) = true ->
  (ex z, 'x ~> 'y) proved.
Proof. apply Ex_gen. Qed.

Lemma zero_eq_zero : empty_theory |- (^zero ~=~ ^zero).
Proof. eapply eq_refl. Qed.

End Nat_examples.


Section Nat_proofs.

Ltac in_hyp := (
  unfold Add;
  repeat (
    try (eapply Union_intror; reflexivity);
    eapply Union_introl
  )).

(* Proof of 0 + x = x, for all natural number x *)
Definition pli_theory :=
let plus_0_x := fun x => (x -< [[ Nat ]]) ~> plus' ^zero x ~=~ x in
  Add _ (Empty_set Sigma_pattern)
  (Peano_Induction plus_0_x).

Lemma plus_left_id :
let x := (evar_c("x")) in
  pli_theory |- (all_S x:Nat, (plus' ^zero 'x ~=~ 'x)).
Proof.
  simpl.
  unfold pli_theory.
  eapply E_mod_pon.
  2: {
    eapply hypothesis. unfold Add. eapply Union_intror. unfold Peano_Induction.
    unfold sorted_all_quan. reflexivity.
  }
  1: {
    eapply conj_intro_meta_e.

Abort.

Check sp_var(evar_c("x")).
(* Proof of commutativity of addition over natural numbers *)
Definition comm_theory := Empty_set Sigma_pattern. (* this can be extended *)
Lemma nat_plus_comm :
  forall x y : EVar, comm_theory |-
    (all_S x : Nat, (all_S y : Nat, ((plus' 'x 'y) ~=~ (plus' 'y 'x)))).
Admitted.


End Nat_proofs.
