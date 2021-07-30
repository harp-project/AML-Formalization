(* Taken from https://github.com/proofengineering/regmatch/blob/qed-at-large/regmatch.v#L67 *)
From Coq Require Import ssreflect ssrfun ssrbool.

Section lexprod'.

Variable A B : Type.

Variable ltA : A -> A -> Prop.
Variable ltB : B -> B -> Prop.

Inductive lexprod' : A * B -> A * B -> Prop :=
| left_lex' : forall (x1 x2 : A) (y1 y2 : B), ltA x1 x2 -> lexprod' (x1, y1) (x2, y2)
| right_lex' : forall (x : A) (y1 y2 : B), ltB y1 y2 -> lexprod' (x, y1) (x, y2).

Lemma lexprod'_Acc :
  well_founded ltA ->
  well_founded ltB ->
  forall x, Acc ltA x -> forall y, Acc ltB y -> Acc lexprod' (x, y).
Proof.
intros wfltA wfltB x Hx.
induction Hx as [x _ IHacc].
intros y Hy.
induction Hy as [y _ IHacc0].
apply Acc_intro.
intros (x1, y1) HA.
inversion HA; subst.
- apply IHacc; auto.
- apply IHacc0; auto.
Defined.

Theorem wf_lexprod' : well_founded ltA -> well_founded ltB -> well_founded lexprod'.
Proof.
intros H_wfA H_wfB (x, y).
by auto using lexprod'_Acc.
Defined.

End lexprod'.
