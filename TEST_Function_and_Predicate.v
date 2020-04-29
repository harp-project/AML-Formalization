Require Import AML_definition.

Definition y := evar_c("y").
Definition vec := (VectorDef.cons _ x _ (VectorDef.cons _ y _ (VectorDef.nil _))).
Definition sorts := (VectorDef.cons _ Nat _ (VectorDef.cons _ Term _ (VectorDef.nil _))).

Definition vec' := (VectorDef.nil EVar).
Definition sorts' := (VectorDef.nil MSA_sorts).

Compute Function (sigma_c("f")) vec sorts y List.
Compute Function (sigma_c("f")) vec' sorts' y List.

Lemma zero_ok : zero_fun = ex_S (evar_c "y") : Nat, ^zero ~=~ (var "y").
Proof. reflexivity. Qed.

Compute Predicate (sigma_c("p")) vec sorts.
Compute Predicate (sigma_c("p")) vec' sorts'.

Compute well_sorted vec sorts.
Compute well_sorted vec' sorts'. (* TODO check if its result is good enough *)
