Require Import AML_definition.
Require Import String.

(* Record Sigma_model := {
  M : Set;
  app : M -> M -> PowerSet M;
  interpretation : Sigma -> PowerSet M
}.

Definition pointwise_app {sm : Sigma_model} (A B : PowerSet (M sm)) : PowerSet (M sm) :=
  fun (c : M sm) => exists (a b : M sm), A a -> B b -> app sm a b c.

Fixpoint ext_valuation {sm : Sigma_model}
  (eqM : M sm -> M sm -> Prop) (pe : EVar -> M sm) (pv : SVar -> PowerSet (M sm)) (sp : Sigma_pattern) *)

Definition model := Build_Sigma_model String (fun (l r c: String) => string_dec (append l r) c) id.

Lemma test1 forall (phi : Sigma_pattern) : ext_valuation 
