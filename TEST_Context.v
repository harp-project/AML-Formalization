Require Import AML_definition.

(* Examples of context usage: *)
Definition box_context := subst_ctx box sp_bottom.
Eval compute in box_context.

Definition tree_context :=
  subst_ctx
    (ctx_app_l (ctx_app_r sp_bottom box) (sp_app sp_bottom sp_bottom))
    sp_bottom.
Eval compute in tree_context.
