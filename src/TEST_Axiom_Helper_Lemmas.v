Require Import AML_definition.
Import AML_notations.
Require Import String.
Require Import Coq.Vectors.VectorDef.
Require Import NAT_definition.


Lemma until_zero : (SumFromZeroTo ^zero) = ^zero.
Proof. simpl. reflexivity. Qed.

Lemma until_one : (SumFromZeroTo one) = (plus' one ^zero).
Proof. simpl. reflexivity. Qed.

Lemma until_two : (SumFromZeroTo two) = (plus' two (plus' one ^zero)).
Proof. simpl. reflexivity. Qed.

Lemma until_zero' : (ProdFromOneTo ^zero) = ^zero.
Proof. simpl. reflexivity. Qed.

Lemma until_one' : (ProdFromOneTo one) = one.
Proof. simpl. reflexivity. Qed.

Lemma until_two' : (ProdFromOneTo two) = (mult' two one).
Proof. simpl. reflexivity. Qed.

Lemma until_three' : (ProdFromOneTo three) = (mult' three (mult' two one)).
Proof. simpl. reflexivity. Qed.

Lemma until_zero'' : (SumOfSquaresFromZeroTo ^zero) = ^zero.
Proof. simpl. reflexivity. Qed.

Lemma until_one'' :
  (SumOfSquaresFromZeroTo one) = (plus' (mult' one one) ^zero).
Proof. simpl. reflexivity. Qed.

Lemma until_two'' :
  (SumOfSquaresFromZeroTo two) =
  (plus' (mult' two two) (plus' (mult' one one) ^zero)).
Proof. simpl. reflexivity. Qed.