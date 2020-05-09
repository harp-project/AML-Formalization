Require Import String.
Require Import AML_definition.

Definition set (s : string) : Sigma_pattern := sp_set (svar_c s).

Definition simple_neg := (sp_not (set "X")).
Definition X_i_X_i_nX := (sp_impl (set "X") ((sp_impl (set "X") (sp_not (set "X"))))).
Definition X_imp_X := (sp_impl (set "X") (set "X")).
Definition X_i_X_i_X := (sp_impl (set "X") ((sp_impl (set "X") (set "X")))).

Section StrictlyPositivenessTest.
Lemma test1: (strictly_negative (svar_c "X") simple_neg).
Proof.
unfold simple_neg. unfold sp_not.
eapply sn_sp_impl.
{
  eapply sp_sp_set.
}
{
  eapply sn_sp_bottom.
}
Qed.

Lemma test2: ~(strictly_positive (svar_c "X") X_imp_X) /\
             ~(strictly_negative (svar_c "X") X_imp_X).
Proof.
unfold X_imp_X.
split;unfold not;intros.
{
  inversion H. inversion H3. case H7. reflexivity.
}
{
  inversion H. inversion H4. case H7. reflexivity.
}
Qed.

Lemma test3: (strictly_positive (svar_c "X") (sp_not X_i_X_i_nX)).
Proof.
unfold X_i_X_i_nX. unfold sp_not.
eapply sp_sp_impl.
{
  eapply sn_sp_impl.
  {
    apply sp_sp_set.
  }
  {
    eapply sn_sp_impl.
    apply sp_sp_set.
    eapply sn_sp_impl.
    apply sp_sp_set.
    apply sn_sp_bottom.
  }
}
apply sp_sp_bottom.
Qed.
End StrictlyPositivenessTest.

Section FreeVarsTest.
Lemma fv_case1: (free_evars sp_bottom) = nil.
Proof. reflexivity. Qed.
Lemma fv_case2: (free_evars X_imp_X) = nil.
Proof. reflexivity. Qed.
Lemma fv_case3: (free_evars (sp_app X_imp_X X_imp_X)) = nil.
Proof. reflexivity. Qed.


Lemma fv_case4: (free_evars (sp_exists (evar_c "x") (sp_var (evar_c "x")))) = nil.
Proof. reflexivity. Qed.
Lemma fv_case5: (free_evars (sp_exists (evar_c "x") (sp_var (evar_c "y")))) = (evar_c "y" :: nil)%list.
Proof. reflexivity. Qed.
Lemma fv_case6: (free_evars (sp_exists (evar_c "x") sp_bottom)) = nil.
Proof. reflexivity. Qed.

(* \x.(\y.(x y)) *)
Lemma fv_case7: (free_evars (sp_app X_imp_X (
  sp_exists (evar_c "x") (sp_exists (evar_c "y") (sp_app (sp_var (evar_c "x")) (sp_var (evar_c "y"))))
))) = nil.
Proof. reflexivity. Qed.

(* (X -> X) (\x.(\y.(z y))) *)
Lemma fv_case8: (free_evars (sp_app X_imp_X (
  sp_exists (evar_c "x") (sp_exists (evar_c "y") (sp_app (sp_var (evar_c "z")) (sp_var (evar_c "y"))))
))) = (evar_c "z" :: nil)%list.
Proof. reflexivity. Qed.

(* \x.x x *)
Lemma fv_case9: (free_evars (
  sp_app
    (sp_exists (evar_c "x") (sp_var (evar_c "x")))
    (sp_var (evar_c "x"))
)) = (evar_c "x" :: nil)%list.
Proof. reflexivity. Qed.

(* \x.x y *)
Lemma fv_case10: (free_evars (
  sp_app
    (sp_exists (evar_c "x") (sp_var (evar_c "x")))
    (sp_var (evar_c "y"))
)) = (evar_c "y" :: nil)%list.
Proof. reflexivity. Qed.

(* \x.y x *)
Lemma fv_case11: (free_evars (
  sp_app
    (sp_exists (evar_c "x") (sp_var (evar_c "y")))
    (sp_var (evar_c "x"))
)) = (evar_c "y" :: evar_c "x" :: nil)%list.
Proof. reflexivity. Qed.

(* \x.y y *)
Lemma fv_case12: (free_evars (
  sp_app
    (sp_exists (evar_c "x") (sp_var (evar_c "y")))
    (sp_var (evar_c "y"))
)) = (evar_c "y" :: nil)%list.
Proof. reflexivity. Qed.


End FreeVarsTest.
