Require Import String.
Require Import Coq.Vectors.VectorDef.
Require Import AML_definition.

Lemma TEST_OneStepTransition_01 :
  (Totality (sp_bottom)) |-> (sp_not (Definedness (sp_not sp_bottom))).
Proof. eapply OST_totality. Qed.

Lemma TEST_AnyStepTransition_01 :
  (Totality (sp_bottom)) |->* (sp_not (Definedness (sp_not sp_bottom))).
Proof.
  eapply AST_trans.
  - eapply OST_totality.
  - eapply AST_refl.
Qed.

(* Test for fixpoint _and_gen and and_gen *)
Lemma zero_eq : (_and_gen 0 (List.nil)) = sp_bottom.
Proof. simpl. reflexivity. Qed.

Lemma zero_eq' : (and_gen (vn _)) = sp_bottom.
Proof. simpl. reflexivity. Qed.

Definition x1 := evar_c("x1").
Lemma x1_eq : (_and_gen 1 ((List.cons (sp_var x1)) List.nil)) = (sp_var x1).
Proof. simpl. reflexivity. Qed.

Lemma x1_eq' : (and_gen (vc _ (sp_var x1) 0 (vn _))) = (sp_var x1).
Proof. simpl. reflexivity. Qed.

Definition x2 := evar_c("x2").
Lemma x1_x2_eq :
  (_and_gen 2 ((List.cons (sp_var x1)) (List.cons (sp_var x2) List.nil))) =
  ((sp_var x1) _&_ (sp_var x2)).
Proof. simpl. reflexivity. Qed.

Lemma x1_x2_eq' :
  (and_gen (vc _ (sp_var x1) 1 (vc _ (sp_var x2) 0 (vn _)))) =
  ((sp_var x1) _&_ (sp_var x2)).
Proof. simpl. reflexivity. Qed.

Definition x3 := evar_c("x3").
Lemma x1_x2_x3_eq :
  (_and_gen 3 
    ((List.cons (sp_var x1))
      ((List.cons (sp_var x2)) ((List.cons (sp_var x3)) List.nil)))) =
  ((sp_var x1) _&_ (sp_var x2) _&_ (sp_var x3)).
Proof. simpl. reflexivity. Qed.

Definition x4 := evar_c("x4").
Lemma x1_x2_x3__x4_eq :
  (_and_gen 4 
    ((List.cons (sp_var x1)) ((List.cons (sp_var x2))
      ((List.cons (sp_var x3)) ((List.cons (sp_var x4)) List.nil))))) =
  ((sp_var x1) _&_ (sp_var x2) _&_ (sp_var x3) _&_ (sp_var x4)).
Proof. simpl. reflexivity. Qed.

(* tests for fixpoint _assoc_elem and assoc_elem *)
Lemma zero_eq_assoc : (_assoc_elem 0 (List.nil) (List.nil)) = sp_bottom.
Proof. simpl. reflexivity. Qed.

Lemma zero_eq_assoc' : (assoc_elem (vn _) (vn _)) = sp_bottom.
Proof. simpl. reflexivity. Qed.

Lemma x1_eq_assoc : 
  (_assoc_elem 1 ((List.cons x1) List.nil) ((List.cons Nat) List.nil)) = 
  (x1 -< [[ Nat ]]).
Proof. simpl. reflexivity. Qed.

Lemma x1_eq_assoc' : 
  (assoc_elem (vc _ x1 0 (vn _)) (vc _ Nat 0 (vn _))) =
  (x1 -< [[ Nat ]]).
Proof. simpl. reflexivity. Qed.

Lemma x1_x2_eq_assoc :
  (_assoc_elem 2
    ((List.cons x1) (List.cons x2 List.nil))
    ((List.cons Nat) (List.cons List List.nil))) =
  ((x1 -< [[ Nat ]]) _&_ (x2 -< [[ List ]])).
Proof. simpl. reflexivity. Qed.

Lemma x1_x2_eq_assoc' :
  (assoc_elem
    (vc _ x1 1 (vc _ x2 0 (vn _ )))
    (vc _ Nat 1 (vc _ List 0 (vn _))) ) =
  ((x1 -< [[ Nat ]]) _&_ (x2 -< [[ List ]])).
Proof. simpl. reflexivity. Qed.

Lemma x1_x2_x3_eq_assoc :
  (_assoc_elem 3
    ((List.cons x1) ((List.cons x2) (List.cons x3 List.nil)))
    ((List.cons Nat) ((List.cons List) (List.cons Cfg List.nil)))) =
  ((x1 -< [[ Nat ]]) _&_ (x2 -< [[ List ]]) _&_ (x3 -< [[ Cfg ]])).
Proof. simpl. reflexivity. Qed.

Lemma x1_x2_x3_eq_assoc' :
  (assoc_elem
    (vc _ x1 2 (vc _ x2 1 (vc _ x3 0 (vn _))))
    (vc _ Nat 2 (vc _ List 1 (vc _ Cfg 0 (vn _))))) =
  ((x1 -< [[ Nat ]]) _&_ (x2 -< [[ List ]]) _&_ (x3 -< [[ Cfg ]])).
Proof. simpl. reflexivity. Qed.

Lemma x1_x2_x3__x4_eq_assoc :
  (_assoc_elem 4
    ((List.cons x1)
      ((List.cons x2) ((List.cons x3) (List.cons x4 List.nil))))
    ((List.cons Nat)
      ((List.cons List) ((List.cons Cfg) (List.cons Nat List.nil))))) =
  ((x1 -< [[ Nat ]]) _&_
    (x2 -< [[ List ]]) _&_ (x3 -< [[ Cfg ]]) _&_ (x4 -< [[ Nat ]])).
Proof. simpl. reflexivity. Qed.

Lemma x1_x2_x3__x4_eq_assoc' :
  (assoc_elem
    (vc _ x1 3 (vc _ x2 2 (vc _ x3 1 (vc _ x4 0 (vn _)))))
    (vc _ Nat 3 (vc _ List 2 (vc _ Cfg 1 (vc _ Nat 0 (vn _))))) ) =
  ((x1 -< [[ Nat ]]) _&_
    (x2 -< [[ List ]]) _&_ (x3 -< [[ Cfg ]]) _&_ (x4 -< [[ Nat ]])).
Proof. simpl. reflexivity. Qed.


(* tests for fixpoints _assoc_params and assoc_params *)
Definition fun_f := sigma_c("fun").
Lemma zero_eq_par : (_assoc_params fun_f 0 (List.nil)) = (sp_const fun_f).
Proof. simpl. unfold fun_f. reflexivity. Qed.

Lemma zero_eq_par' : (assoc_params fun_f (vn _)) = (sp_const fun_f).
Proof. simpl. unfold fun_f. reflexivity. Qed.

Lemma x1_eq_par :
  (_assoc_params fun_f 1 ((List.cons x1) List.nil)) =
  ((sp_const fun_f) _._ (sp_var x1)).
Proof. simpl. unfold fun_f. unfold x1. reflexivity. Qed.

Lemma x1_eq_par' :
  (assoc_params fun_f (vc _ x1 0 (vn _))) =
  ((sp_const fun_f) _._ (sp_var x1)).
Proof. simpl. unfold fun_f. unfold x1. reflexivity. Qed.

Lemma x1_x2_eq_par :
  (_assoc_params fun_f 2 ((List.cons x1) (List.cons x2 List.nil))) = 
  ((sp_const fun_f) _._ (sp_var x1) _._ (sp_var x2)).
Proof. simpl. unfold fun_f. unfold x1. unfold x2. reflexivity. Qed.

Lemma x1_x2_eq_par' :
  (assoc_params fun_f (vc _ x1 1 (vc _ x2 0 (vn _)))) =
  ((sp_const fun_f) _._ (sp_var x1) _._ (sp_var x2)).
Proof. simpl. unfold fun_f. unfold x1. unfold x2. reflexivity. Qed.

Lemma x1_x2_x3_eq_par :
  (_assoc_params fun_f 3
    ((List.cons x1) ((List.cons x2) (List.cons x3 List.nil)))) = 
  ((sp_const fun_f) _._ (sp_var x1) _._ (sp_var x2) _._ (sp_var x3)).
Proof. simpl. unfold fun_f. unfold x1. unfold x2. unfold x3. reflexivity. Qed.

Lemma x1_x2_x3_eq_par' :
  (assoc_params fun_f (vc _ x1 2 (vc _ x2 1 (vc _ x3 0 (vn _))))) = 
  ((sp_const fun_f) _._ (sp_var x1) _._ (sp_var x2) _._ (sp_var x3)).
Proof. simpl. unfold fun_f. unfold x1. unfold x2. unfold x3. reflexivity. Qed.

Lemma x1_x2_x3__x4_eq_par :
  (_assoc_params fun_f 4
    ((List.cons x1) ((List.cons x2) ((List.cons x3) (List.cons x4 List.nil))))) =
    ((sp_const fun_f) _._ (sp_var x1) _._ (sp_var x2) _._ (sp_var x3) _._ (sp_var x4)).
Proof. simpl. reflexivity. Qed.

Lemma x1_x2_x3__x4_eq_par' :
  (assoc_params fun_f (vc _ x1 3 (vc _ x2 2 (vc _ x3 1 (vc _ x4 0 (vn _)))))) =
  ((sp_const fun_f) _._ (sp_var x1) _._ (sp_var x2) _._ (sp_var x3) _._ (sp_var x4)).
Proof. simpl. reflexivity. Qed.

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