Require Import String.
Require Import Ensembles.

Require Import Signature.

Inductive Sigma : Type := sigma_c {id_si : string}.

Definition ConcreteSignature : Signature :=
  {| symbols := Power Sigma;
  |}.

Definition sigma_eq_dec : forall (x y : Sigma), { x = y } + { x <> y }.
Proof. decide equality. exact (string_dec id_si0 id_si1). Defined.


