Require Import AML_definition.
Import AML_notations.
Import String.


(* Examples of context usage: *)
Definition box_context := subst_ctx box sp_bottom.
Eval compute in box_context.

Definition tree_context :=
  subst_ctx
    (ctx_app_l (ctx_app_r sp_bottom box) (sp_app sp_bottom sp_bottom))
    sp_bottom.

Lemma TEST_tree_context :
  tree_context = Bot $ Bot $ (Bot $ Bot).
Proof. reflexivity. Qed.


Definition definedness_context :=
  (ctx_app_r definedness_symbol box).

Lemma TEST_definedness_context :
  subst_ctx definedness_context 'x = defined 'x.
Proof. reflexivity. Qed.


Definition y := evar_c("y").
Definition parameters_context :=
  ctx_app_l box ('x $ const("sigma") $ 'y $ Bot).

Definition f := const("f").
Definition g := const("g").

Lemma TEST_parameters_context :
  subst_ctx parameters_context f = f $ ('x $ const("sigma") $ 'y $ Bot).
Proof. reflexivity. Qed.

Lemma TEST_parameters_context' :
  subst_ctx parameters_context g = g $ ('x $ const("sigma") $ 'y $ Bot).
Proof. reflexivity. Qed.


Definition function_context :=
  ctx_app_r (f $ 'x) (ctx_app_l box (const("sigma") $ 'y)).

Lemma TEST_function_context :
  subst_ctx function_context 'x = f $ 'x $ ('x $ const("sigma") $ 'y).
Proof. simpl. reflexivity. Qed.