Require Import AML_definition.
Import AML_notations.
Import MSFOL_notations.
Import String.

Definition vec := (vc _ x _ (vc _ y _ (vn _))).
Definition sorts := (vc _ Nat _ (vc _ Term _ (vn _))).

Definition vec' := (vn EVar).
Definition sorts' := (vn MSFOL_sorts).

Definition f := sigma_c("f").
Definition p := sigma_c("p").

(* Test Function notation *)
Lemma empty_fun :
  f : --> Nat =
  ex_S y:Nat, ^f ~=~ 'y.
Proof. reflexivity. Qed.

Lemma singleton_fun :
  f : List --> Nat =
  all_S (evar_c("x1")):List, ex_S y:Nat, ^f $ (var("x1")) ~=~ 'y.
Proof. reflexivity. Qed.

Lemma general_fun :
  f : Nat X List X List --> List =
  all_S (evar_c("x1")):Nat, all_S (evar_c("x2")):List, all_S (evar_c("x3")):List,
    ex_S y:List, ((^f $ var("x1") $ var("x2") $ var("x3")) ~=~ 'y).
Proof. reflexivity. Qed.


(* Test Predicate notation *)
Lemma empty_pred :
  p pred =
  ((^p ~=~ Top) _|_ (^p ~=~ Bot)).
Proof. reflexivity. Qed.

Lemma singleton_pred :
  p <:: Nat =
  all_S (evar_c("x1")):Nat, 
    (((^p $ var("x1")) ~=~ Top) _|_ ((^p $ var("x1")) ~=~ Bot)).
Proof. reflexivity. Qed.

Lemma general_pred :
  (p =< Nat X Nat) =
  all_S (evar_c("x1")):Nat, all_S (evar_c("x2")):Nat, 
    (((^p $ var("x1") $ var("x2")) ~=~ Top) _|_ 
     ((^p $ var("x1") $ var("x2") ~=~ Bot))).
Proof. reflexivity. Qed.

Lemma zero_ok : zero_fun = ex_S (evar_c "y") : Nat, ^zero ~=~ (var "y").
Proof. reflexivity. Qed.
