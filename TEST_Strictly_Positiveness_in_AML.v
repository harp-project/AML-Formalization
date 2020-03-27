Require Import String.
Require Import AML_definition.

Definition set (s : string) : Sigma_pattern := sp_set (svar_c s).

Definition simple_neg := (sp_not (set "X")).
Definition X_i_X_i_nX := (sp_impl (set "X") ((sp_impl (set "X") (sp_not (set "X"))))).
Definition X_imp_X := (sp_impl (set "X") (set "X")).
Definition X_i_X_i_X := (sp_impl (set "X") ((sp_impl (set "X") (set "X")))).

Section StrictlyPositivenessTest.
Lemma test1: (strictly_positive simple_neg (svar_c "X") = false).
Proof. reflexivity. Qed.
Lemma test2: (strictly_positive X_imp_X (svar_c "X") = false).
Proof. reflexivity. Qed.
Lemma test3: (strictly_positive (sp_not X_imp_X) (svar_c "X") = false).
Proof. reflexivity. Qed.
Lemma test4: (strictly_positive X_i_X_i_X (svar_c "X") = false).
Proof. reflexivity. Qed.
Lemma test5: (strictly_positive (sp_not X_i_X_i_X)(svar_c "X") = false).
Proof. reflexivity. Qed.
Lemma test6: (strictly_positive X_i_X_i_nX (svar_c "X") = false).
Proof. reflexivity. Qed.
Lemma test7: (strictly_positive (sp_not X_i_X_i_nX) (svar_c "X") = true).
Proof. reflexivity. Qed.
End StrictlyPositivenessTest.

Section FreeVarsTest.
Lemma fv_case1: (free_vars sp_bottom) = nil.
Proof. reflexivity. Qed.
Lemma fv_case2: (free_vars X_imp_X) = nil.
Proof. reflexivity. Qed.
Lemma fv_case3: (free_vars (sp_app X_imp_X X_imp_X)) = nil.
Proof. reflexivity. Qed.


Lemma fv_case4: (free_vars (sp_exists (evar_c "x") (sp_var (evar_c "x")))) = nil.
Proof. reflexivity. Qed.
Lemma fv_case5: (free_vars (sp_exists (evar_c "x") (sp_var (evar_c "y")))) = (evar_c "y" :: nil)%list.
Proof. reflexivity. Qed.
Lemma fv_case6: (free_vars (sp_exists (evar_c "x") sp_bottom)) = nil.
Proof. reflexivity. Qed.

(* \x.(\y.(x y)) *)
Lemma fv_case7: (free_vars (sp_app X_imp_X (
  sp_exists (evar_c "x") (sp_exists (evar_c "y") (sp_app (sp_var (evar_c "x")) (sp_var (evar_c "y"))))
))) = nil.
Proof. reflexivity. Qed.

(* (X -> X) (\x.(\y.(z y))) *)
Lemma fv_case8: (free_vars (sp_app X_imp_X (
  sp_exists (evar_c "x") (sp_exists (evar_c "y") (sp_app (sp_var (evar_c "z")) (sp_var (evar_c "y"))))
))) = (evar_c "z" :: nil)%list.
Proof. reflexivity. Qed.

(* \x.x x *)
Lemma fv_case9: (free_vars (
  sp_app
    (sp_exists (evar_c "x") (sp_var (evar_c "x")))
    (sp_var (evar_c "x"))
)) = (evar_c "x" :: nil)%list.
Proof. reflexivity. Qed.

(* \x.x y *)
Lemma fv_case10: (free_vars (
  sp_app
    (sp_exists (evar_c "x") (sp_var (evar_c "x")))
    (sp_var (evar_c "y"))
)) = (evar_c "y" :: nil)%list.
Proof. reflexivity. Qed.

(* \x.y x *)
Lemma fv_case11: (free_vars (
  sp_app
    (sp_exists (evar_c "x") (sp_var (evar_c "y")))
    (sp_var (evar_c "x"))
)) = (evar_c "y" :: evar_c "x" :: nil)%list.
Proof. reflexivity. Qed.

(* \x.y y *)
Lemma fv_case12: (free_vars (
  sp_app
    (sp_exists (evar_c "x") (sp_var (evar_c "y")))
    (sp_var (evar_c "y"))
)) = (evar_c "y" :: nil)%list.
Proof. reflexivity. Qed.


End FreeVarsTest.
