Require Import String.
Require Import AML_definition.

Definition simple_neg := (sp_not (set "X")).
Definition X_i_X_i_nX := (sp_impl (set "X") ((sp_impl (set "X") (sp_not (set "X"))))).
Definition X_imp_X := (sp_impl (set "X") (set "X")).
Definition X_i_X_i_X := (sp_impl (set "X") ((sp_impl (set "X") (set "X")))).

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
